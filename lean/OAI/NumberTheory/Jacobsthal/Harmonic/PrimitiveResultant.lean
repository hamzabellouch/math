import Mathlib
import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates

namespace OAI

namespace Erdos970

section

namespace ErdosBivariateResultant

abbrev Bivariate := Polynomial (Polynomial ℂ)

noncomputable def specialize (P : Bivariate) (x : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom x)

noncomputable def pointEvalHom (x y : ℂ) : Bivariate →+* ℂ :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))

noncomputable def beval (P : Bivariate) (x y : ℂ) : ℂ := pointEvalHom x y P

noncomputable def xResultant (P Q : Bivariate) : Polynomial ℂ := P.resultant Q

theorem beval_eq_specialize (P : Bivariate) (x y : ℂ) :
    beval P x y = (specialize P x).eval y := rfl

@[simp] theorem beval_add (P Q : Bivariate) (x y : ℂ) :
    beval (P+Q) x y = beval P x y+beval Q x y := (pointEvalHom x y).map_add P Q
@[simp] theorem beval_mul (P Q : Bivariate) (x y : ℂ) :
    beval (P*Q) x y = beval P x y*beval Q x y := (pointEvalHom x y).map_mul P Q
@[simp] theorem beval_C (p : Polynomial ℂ) (x y : ℂ) :
    beval (Polynomial.C p) x y = p.eval x := by
  simp [beval, pointEvalHom]

theorem resultant_bezout (P Q : Bivariate) (hdeg : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    ∃ U V : Bivariate, P*U+Q*V = Polynomial.C (xResultant P Q) := by
  obtain ⟨U,V,_,_,h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant P Q le_rfl le_rfl hdeg
  exact ⟨U,V,h⟩

theorem common_zero_resultant_zero (P Q : Bivariate)
    (hdeg : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) (x y : ℂ)
    (hP : beval P x y = 0) (hQ : beval Q x y = 0) :
    (xResultant P Q).eval x = 0 := by
  obtain ⟨U,V,h⟩ := resultant_bezout P Q hdeg
  have he := congrArg (fun R : Bivariate => beval R x y) h
  simpa only [beval_add, beval_mul, beval_C, hP, hQ, zero_mul, zero_add] using he.symm

theorem specialize_degree_le (P : Bivariate) (x : ℂ) :
    (specialize P x).natDegree ≤ P.natDegree := Polynomial.natDegree_map_le

theorem common_zero_resultant_zero_of_fiber (P Q : Bivariate) (x y : ℂ)
    (hPx : specialize P x ≠ 0) (hP : beval P x y = 0) (hQ : beval Q x y = 0) :
    (xResultant P Q).eval x = 0 := by
  have hd : 0 < (specialize P x).natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root hPx (RingHom.id ℂ) hP (fun z hz => hz)
  have hdeg : 0 < P.natDegree := hd.trans_le (specialize_degree_le P x)
  exact common_zero_resultant_zero P Q (Or.inl hdeg.ne') x y hP hQ

end ErdosBivariateResultant

end

section

open scoped BigOperators
namespace ErdosBivariateResultant

theorem determinant_degree_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial ℂ)) (D : n → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D j) : M.det.natDegree ≤ ∑ j, D j := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma _
  apply (Polynomial.natDegree_smul_le (Equiv.Perm.sign sigma) _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  exact Finset.sum_le_sum fun j _ => hM (sigma j) j

theorem resultant_degree_from_coefficients (P Q : Bivariate) (m n A B : ℕ)
    (hP : ∀ k, (P.coeff k).natDegree ≤ A) (hQ : ∀ k, (Q.coeff k).natDegree ≤ B) :
    (P.resultant Q m n).natDegree ≤ m*B+n*A := by
  let D : Fin (m+n) → ℕ := Fin.addCases (fun _ : Fin m => B) (fun _ : Fin n => A)
  have hcol (i j : Fin (m+n)) : (P.sylvester Q m n i j).natDegree ≤ D j := by
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, D]
        split_ifs
        · exact hQ _
        · simp
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, D]
        split_ifs
        · exact hP _
        · simp
  have h := determinant_degree_le (P.sylvester Q m n) D hcol
  change (P.resultant Q m n).natDegree ≤ _ at h
  have hsum : (∑ j, D j) = m*B+n*A := by
    rw [Fin.sum_univ_add]
    simp [D]
  rwa [hsum] at h

noncomputable def coefficientDegree (P : Bivariate) : ℕ :=
  P.support.sup fun k => (P.coeff k).natDegree

theorem coeff_degree_le (P : Bivariate) (k : ℕ) : (P.coeff k).natDegree ≤ coefficientDegree P := by
  classical
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => (P.coeff k).natDegree) hk
  · rw [Polynomial.notMem_support_iff.mp hk]
    exact Nat.zero_le _

theorem xResultant_degree_le (P Q : Bivariate) :
    (xResultant P Q).natDegree ≤
      P.natDegree*coefficientDegree Q+Q.natDegree*coefficientDegree P :=
  resultant_degree_from_coefficients P Q _ _ _ _ (coeff_degree_le P) (coeff_degree_le Q)

theorem xResultant_degree_uniform (P Q : Bivariate) (d : ℕ)
    (hPy : P.natDegree ≤ d) (hQy : Q.natDegree ≤ d)
    (hPx : ∀ k, (P.coeff k).natDegree ≤ d) (hQx : ∀ k, (Q.coeff k).natDegree ≤ d) :
    (xResultant P Q).natDegree ≤ 2*d^2 := by
  have h := resultant_degree_from_coefficients P Q P.natDegree Q.natDegree d d hPx hQx
  change (xResultant P Q).natDegree ≤ _ at h
  nlinarith

end ErdosBivariateResultant

end

section

open scoped BigOperators
namespace ErdosBivariateResultant

attribute [local instance] Classical.propDecidable

noncomputable def resultantRoots (P Q : Bivariate) : Finset ℂ := (xResultant P Q).roots.toFinset
noncomputable def verticalRoots (P : Bivariate) (x : ℂ) : Finset ℂ := (specialize P x).roots.toFinset

noncomputable def rootPairs (P Q : Bivariate) : Finset (ℂ × ℂ) :=
  (resultantRoots P Q).biUnion fun x => (verticalRoots P x).image fun y => (x,y)

noncomputable def commonZeroFinset (P Q : Bivariate) : Finset (ℂ × ℂ) :=
  (rootPairs P Q).filter fun p => beval Q p.1 p.2 = 0

def commonZeroSet (P Q : Bivariate) : Set (ℂ × ℂ) :=
  {p | beval P p.1 p.2 = 0 ∧ beval Q p.1 p.2 = 0}

theorem mem_resultantRoots (P Q : Bivariate) (hR : xResultant P Q ≠ 0) (x : ℂ) :
    x ∈ resultantRoots P Q ↔ (xResultant P Q).eval x = 0 := by
  simp only [resultantRoots, Multiset.mem_toFinset, Polynomial.mem_roots hR, Polynomial.IsRoot.def]

theorem mem_verticalRoots (P : Bivariate) (x y : ℂ) (hPx : specialize P x ≠ 0) :
    y ∈ verticalRoots P x ↔ beval P x y = 0 := by
  simp only [verticalRoots, Multiset.mem_toFinset, Polynomial.mem_roots hPx,
    Polynomial.IsRoot.def, beval_eq_specialize]

theorem mem_rootPairs (P Q : Bivariate) (p : ℂ × ℂ) :
    p ∈ rootPairs P Q ↔ p.1 ∈ resultantRoots P Q ∧ p.2 ∈ verticalRoots P p.1 := by
  rcases p with ⟨a,b⟩
  simp only [rootPairs, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x,hx,y,hy,hp⟩
    cases hp
    exact ⟨hx,hy⟩
  · intro h
    exact ⟨a,h.1,b,h.2,rfl⟩

theorem mem_commonZeroFinset (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) (p : ℂ × ℂ) :
    p ∈ commonZeroFinset P Q ↔ p ∈ commonZeroSet P Q := by
  simp only [commonZeroFinset, Finset.mem_filter, mem_rootPairs, commonZeroSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_,hy⟩,hQ⟩
    exact ⟨(mem_verticalRoots P p.1 p.2 (hP p.1)).mp hy,hQ⟩
  · rintro ⟨hp,hq⟩
    refine ⟨⟨(mem_resultantRoots P Q hR p.1).mpr ?_,
      (mem_verticalRoots P p.1 p.2 (hP p.1)).mpr hp⟩,hq⟩
    exact common_zero_resultant_zero_of_fiber P Q p.1 p.2 (hP p.1) hp hq

theorem coe_commonZeroFinset (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) :
    (commonZeroFinset P Q : Set (ℂ × ℂ)) = commonZeroSet P Q := by
  ext p
  exact mem_commonZeroFinset P Q hR hP p

theorem commonZeroSet_finite (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) : (commonZeroSet P Q).Finite := by
  rw [← coe_commonZeroFinset P Q hR hP]
  exact Finset.finite_toSet _

theorem resultantRoots_card_le (P Q : Bivariate) :
    (resultantRoots P Q).card ≤ (xResultant P Q).natDegree :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)

theorem verticalRoots_card_le (P : Bivariate) (x : ℂ) : (verticalRoots P x).card ≤ P.natDegree :=
  (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (specialize_degree_le P x))

theorem commonZeroFinset_card_le (P Q : Bivariate) :
    (commonZeroFinset P Q).card ≤ (xResultant P Q).natDegree*P.natDegree := by
  calc
    _ ≤ (rootPairs P Q).card := Finset.card_filter_le _ _
    _ ≤ ∑ x ∈ resultantRoots P Q, ((verticalRoots P x).image fun y => (x,y)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ resultantRoots P Q, P.natDegree := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.card_image_le.trans (verticalRoots_card_le P x)
    _ = (resultantRoots P Q).card*P.natDegree := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (resultantRoots_card_le P Q)

theorem common_zero_finite_count (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) :
    (commonZeroSet P Q).Finite ∧
      (commonZeroSet P Q).ncard ≤ (xResultant P Q).natDegree*P.natDegree := by
  refine ⟨commonZeroSet_finite P Q hR hP, ?_⟩
  rw [← coe_commonZeroFinset P Q hR hP, Set.ncard_coe_finset]
  exact commonZeroFinset_card_le P Q

theorem common_zero_count_coefficient_bound (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) :
    (commonZeroSet P Q).ncard ≤
      (P.natDegree*coefficientDegree Q+Q.natDegree*coefficientDegree P)*P.natDegree :=
  (common_zero_finite_count P Q hR hP).2.trans (Nat.mul_le_mul_right _ (xResultant_degree_le P Q))

theorem common_zero_count_uniform (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) (d : ℕ)
    (hPy : P.natDegree ≤ d) (hQy : Q.natDegree ≤ d)
    (hPx : ∀ k, (P.coeff k).natDegree ≤ d) (hQx : ∀ k, (Q.coeff k).natDegree ≤ d) :
    (commonZeroSet P Q).ncard ≤ 2*d^3 := by
  calc
    _ ≤ (xResultant P Q).natDegree*P.natDegree := (common_zero_finite_count P Q hR hP).2
    _ ≤ (2*d^2)*d := Nat.mul_le_mul (xResultant_degree_uniform P Q d hPy hQy hPx hQx) hPy
    _ = _ := by ring

end ErdosBivariateResultant

end

section

namespace ErdosBivariateResultant

attribute [local instance] Classical.propDecidable

noncomputable def commonAbscissae (P Q : Bivariate) : Finset ℂ :=
  (commonZeroFinset P Q).image Prod.fst

noncomputable def commonVerticalRoots (P Q : Bivariate) (x : ℂ) : Finset ℂ :=
  (verticalRoots P x).filter fun y => beval Q x y = 0

theorem mem_commonAbscissae (P Q : Bivariate) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, specialize P x ≠ 0) (x : ℂ) :
    x ∈ commonAbscissae P Q ↔ ∃ y : ℂ, beval P x y = 0 ∧ beval Q x y = 0 := by
  constructor
  · intro hx
    obtain ⟨⟨a,b⟩,hp,he⟩ := Finset.mem_image.mp hx
    change a = x at he
    subst a
    exact ⟨b,(mem_commonZeroFinset P Q hR hP (x,b)).mp hp⟩
  · rintro ⟨y,hp,hq⟩
    exact Finset.mem_image.mpr ⟨(x,y),(mem_commonZeroFinset P Q hR hP (x,y)).mpr ⟨hp,hq⟩,rfl⟩

theorem commonAbscissae_card_le (P Q : Bivariate) :
    (commonAbscissae P Q).card ≤ (xResultant P Q).natDegree := by
  apply (Finset.card_le_card (show commonAbscissae P Q ⊆ resultantRoots P Q from ?_)).trans
    (resultantRoots_card_le P Q)
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  exact ((mem_rootPairs P Q p).mp (Finset.mem_filter.mp hp).1).1

theorem mem_commonVerticalRoots (P Q : Bivariate) (x y : ℂ) (hPx : specialize P x ≠ 0) :
    y ∈ commonVerticalRoots P Q x ↔ beval P x y = 0 ∧ beval Q x y = 0 := by
  simp only [commonVerticalRoots, Finset.mem_filter, mem_verticalRoots P x y hPx]

theorem commonVerticalRoots_card_le (P Q : Bivariate) (x : ℂ) :
    (commonVerticalRoots P Q x).card ≤ P.natDegree :=
  (Finset.card_filter_le _ _).trans (verticalRoots_card_le P x)

theorem coe_commonZeroFinset_on_resultant (P Q : Bivariate)
    (hdeg : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, (xResultant P Q).eval x = 0 → specialize P x ≠ 0) :
    (commonZeroFinset P Q : Set (ℂ × ℂ)) = commonZeroSet P Q := by
  ext p
  simp only [commonZeroFinset, Finset.mem_coe, Finset.mem_filter, mem_rootPairs,
    commonZeroSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hx,hy⟩,hq⟩
    have hr := (mem_resultantRoots P Q hR p.1).mp hx
    exact ⟨(mem_verticalRoots P p.1 p.2 (hP p.1 hr)).mp hy,hq⟩
  · rintro ⟨hp,hq⟩
    have hr := common_zero_resultant_zero P Q hdeg p.1 p.2 hp hq
    exact ⟨⟨(mem_resultantRoots P Q hR p.1).mpr hr,
      (mem_verticalRoots P p.1 p.2 (hP p.1 hr)).mpr hp⟩,hq⟩

theorem common_zero_finite_count_on_resultant (P Q : Bivariate)
    (hdeg : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) (hR : xResultant P Q ≠ 0)
    (hP : ∀ x : ℂ, (xResultant P Q).eval x = 0 → specialize P x ≠ 0) :
    (commonZeroSet P Q).Finite ∧
      (commonZeroSet P Q).ncard ≤ (xResultant P Q).natDegree*P.natDegree := by
  rw [← coe_commonZeroFinset_on_resultant P Q hdeg hR hP]
  exact ⟨Finset.finite_toSet _, by simpa using commonZeroFinset_card_le P Q⟩

end ErdosBivariateResultant

end

section

namespace ErdosCriticalGeometry

open ErdosBivariateResultant

theorem primitive_specialize_ne_zero (P : Nested ℂ) (hP : P.IsPrimitive) (x : ℂ) :
    specialize P x ≠ 0 := by
  intro hz
  have hcoeff (k : ℕ) : (P.coeff k).eval x = 0 := by
    have h := congrArg (fun p : Polynomial ℂ => p.coeff k) hz
    change (Polynomial.evalRingHom x) (P.coeff k) = 0
    simpa only [specialize, Polynomial.coeff_map, Polynomial.coeff_zero] using h
  have hdiv : Polynomial.C (Polynomial.X-Polynomial.C x) ∣ P := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro k
    exact Polynomial.dvd_iff_isRoot.mpr (hcoeff k)
  exact Polynomial.not_isUnit_X_sub_C x
    ((Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hP) _ hdiv)


theorem irreducible_resultant_ne_zero (P G : Nested ℂ) (hP : Irreducible P)
    (hdeg : P.natDegree ≠ 0) (hnd : ¬P ∣ G) : xResultant P G ≠ 0 := by
  classical
  let K := FractionRing (Polynomial ℂ)
  let : IsPrincipalIdealRing (Polynomial K) := by
    let := Polynomial.instEuclideanDomain (R := K)
    exact EuclideanDomain.instIsPrincipalIdealRing
  let phi : Polynomial ℂ →+* K := algebraMap (Polynomial ℂ) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial ℂ) K
  have hprim := hP.isPrimitive hdeg
  have hirr : Irreducible (P.map phi) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hnd' : ¬P.map phi ∣ G.map phi := by
    intro h
    exact hnd (hprim.dvd_of_fraction_map_dvd_fraction_map (K := K) h)
  have hcop : IsCoprime (P.map phi) (G.map phi) :=
    hirr.coprime_iff_not_dvd.mpr hnd'
  have hres := Polynomial.resultant_ne_zero (P.map phi) (G.map phi) hcop
  intro hz
  apply hres
  rw [Polynomial.natDegree_map_eq_of_injective hphi, Polynomial.natDegree_map_eq_of_injective hphi,
    Polynomial.resultant_map_map]
  simpa only [xResultant, map_zero] using congrArg phi hz

end ErdosCriticalGeometry

end

end Erdos970

end OAI
