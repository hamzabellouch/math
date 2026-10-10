import OAI.NumberTheory.Jacobsthal.Harmonic.PrimitiveResultant
import OAI.NumberTheory.Jacobsthal.Partitions.NonlinearCoordinateDegree

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

open ErdosBivariateResultant

@[simp] theorem beval_nested (Q : MV ℂ) (x y : ℂ) :
    beval (nestedY ℂ Q) x y = MvPolynomial.eval ![x,y] Q := eval_nestedY ℂ Q x y

def intersectionPoints (Q G : MV ℂ) : Set (ℂ × ℂ) :=
  {p | MvPolynomial.eval ![p.1,p.2] Q = 0 ∧ MvPolynomial.eval ![p.1,p.2] G = 0}

def intersectionAbscissae (Q G : MV ℂ) : Set ℂ := Prod.fst '' intersectionPoints Q G

theorem intersectionPoints_eq_nested (Q G : MV ℂ) :
    intersectionPoints Q G = commonZeroSet (nestedY ℂ Q) (nestedY ℂ G) := by
  ext p
  simp only [intersectionPoints, commonZeroSet, Set.mem_ofPred_eq, beval_nested]

theorem nonlinear_fibers_nonzero (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    ∀ x : ℂ, specialize (nestedY ℂ Q) x ≠ 0 := by
  have hi : Irreducible (nestedY ℂ Q) := (MulEquiv.irreducible_iff (nestedY ℂ).toMulEquiv).mpr hQ
  exact primitive_specialize_ne_zero _ (hi.isPrimitive (nonlinear_nestedY_degree_pos Q hQ hdeg).ne')

theorem nonlinear_resultant_nonzero (Q G : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ G) : xResultant (nestedY ℂ Q) (nestedY ℂ G) ≠ 0 := by
  have hi : Irreducible (nestedY ℂ Q) := (MulEquiv.irreducible_iff (nestedY ℂ).toMulEquiv).mpr hQ
  apply irreducible_resultant_ne_zero _ _ hi (nonlinear_nestedY_degree_pos Q hQ hdeg).ne'
  rintro ⟨H,hH⟩
  apply hnd
  refine ⟨(nestedY ℂ).symm H, ?_⟩
  apply (nestedY ℂ).injective
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using hH

theorem mv_resultant_degree_le (Q G : MV ℂ) :
    (xResultant (nestedY ℂ Q) (nestedY ℂ G)).natDegree ≤ 2*Q.totalDegree*G.totalDegree := by
  have h := resultant_degree_from_coefficients (nestedY ℂ Q) (nestedY ℂ G)
    (nestedY ℂ Q).natDegree (nestedY ℂ G).natDegree Q.totalDegree G.totalDegree
    (nestedY_coefficient_degree_le ℂ Q) (nestedY_coefficient_degree_le ℂ G)
  change (xResultant (nestedY ℂ Q) (nestedY ℂ G)).natDegree ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ Q.totalDegree*G.totalDegree+G.totalDegree*Q.totalDegree := Nat.add_le_add
      (Nat.mul_le_mul_right _ (nestedY_degree_le ℂ Q))
      (Nat.mul_le_mul_right _ (nestedY_degree_le ℂ G))
    _ = _ := by ring

theorem irreducible_intersection_bound (Q G : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ G) :
    (intersectionPoints Q G).Finite ∧
      (intersectionPoints Q G).ncard ≤ 2*Q.totalDegree^2*G.totalDegree := by
  rw [intersectionPoints_eq_nested]
  obtain ⟨hfin,hcard⟩ := common_zero_finite_count (nestedY ℂ Q) (nestedY ℂ G)
    (nonlinear_resultant_nonzero Q G hQ hdeg hnd) (nonlinear_fibers_nonzero Q hQ hdeg)
  refine ⟨hfin, hcard.trans ?_⟩
  calc
    _ ≤ (2*Q.totalDegree*G.totalDegree)*Q.totalDegree :=
      Nat.mul_le_mul (mv_resultant_degree_le Q G) (nestedY_degree_le ℂ Q)
    _ = _ := by ring

theorem irreducible_abscissa_bound (Q G : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ G) :
    (intersectionAbscissae Q G).Finite ∧
      (intersectionAbscissae Q G).ncard ≤ 2*Q.totalDegree*G.totalDegree := by
  have hR := nonlinear_resultant_nonzero Q G hQ hdeg hnd
  have hF := nonlinear_fibers_nonzero Q hQ hdeg
  have hsub : intersectionAbscissae Q G ⊆
      (resultantRoots (nestedY ℂ Q) (nestedY ℂ G) : Set ℂ) := by
    rintro x ⟨p,hp,rfl⟩
    apply (mem_resultantRoots _ _ hR p.1).mpr
    apply common_zero_resultant_zero_of_fiber _ _ p.1 p.2 (hF p.1)
    · simpa only [beval_nested] using hp.1
    · simpa only [beval_nested] using hp.2
  have hfinite := (Finset.finite_toSet (resultantRoots (nestedY ℂ Q) (nestedY ℂ G))).subset hsub
  refine ⟨hfinite, ?_⟩
  calc
    _ ≤ (resultantRoots (nestedY ℂ Q) (nestedY ℂ G) : Set ℂ).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (resultantRoots (nestedY ℂ Q) (nestedY ℂ G)).card := Set.ncard_coe_finset _
    _ ≤ _ := (resultantRoots_card_le _ _).trans (mv_resultant_degree_le Q G)

end ErdosCriticalGeometry

end

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry

noncomputable def affineLine (A B : ℂ) : MV ℂ :=
  MvPolynomial.X 1-(MvPolynomial.C A*MvPolynomial.X 0+MvPolynomial.C B)

noncomputable def affineInner (A B : ℂ) : Polynomial ℂ :=
  Polynomial.C A*Polynomial.X+Polynomial.C B

theorem nested_affineLine (A B : ℂ) :
    nestedY ℂ (affineLine A B) = Polynomial.X-Polynomial.C (affineInner A B) := by
  simp [affineLine,affineInner,map_sub,map_add,map_mul]

theorem eval_affine_substitution (P : Nested ℂ) (A B x : ℂ) :
    (P.eval (affineInner A B)).eval x =
      ErdosBivariateResultant.beval P x (A*x+B) := by
  have h := Polynomial.eval₂_at_apply (p := P) (Polynomial.evalRingHom x) (affineInner A B)
  rw [← Polynomial.eval_map] at h
  simpa [affineInner,ErdosBivariateResultant.beval_eq_specialize,
    ErdosBivariateResultant.specialize] using h.symm

theorem affine_interval_factor (Q : MV ℂ) (A B : ℂ) (a b : ℝ) (hab : a < b)
    (hzero : ∀ t ∈ Set.Ioo a b,
      MvPolynomial.eval ![(t : ℂ),A*(t : ℂ)+B] Q = 0) : affineLine A B ∣ Q := by
  let P := nestedY ℂ Q
  let R := P.eval (affineInner A B)
  have hz (t : ℝ) (ht : t ∈ Set.Ioo a b) : R.eval (t : ℂ) = 0 := by
    rw [show R = P.eval (affineInner A B) from rfl, eval_affine_substitution]
    exact (beval_nested Q (t : ℂ) (A*(t : ℂ)+B)).trans (hzero t ht)
  have hR : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Ioo_infinite hab).image Complex.ofReal_injective.injOn).mono
    rintro z ⟨t,ht,rfl⟩
    exact hz t ht
  have hdiv : Polynomial.X-Polynomial.C (affineInner A B) ∣ P := Polynomial.dvd_iff_isRoot.mpr hR
  obtain ⟨H,hH⟩ := hdiv
  refine ⟨(nestedY ℂ).symm H, ?_⟩
  apply (nestedY ℂ).injective
  simpa only [map_mul,AlgEquiv.apply_symm_apply,nested_affineLine] using hH

theorem affineLine_not_unit (A B : ℂ) : ¬IsUnit (affineLine A B) := by
  intro h
  have hmap := h.map (nestedY ℂ).toRingHom
  change IsUnit (nestedY ℂ (affineLine A B)) at hmap
  rw [nested_affineLine] at hmap
  exact Polynomial.not_isUnit_X_sub_C _ hmap

theorem affineLine_degree_le (A B : ℂ) : (affineLine A B).totalDegree ≤ 1 := by
  have he : affineLine A B = MvPolynomial.X 1 +
      MvPolynomial.C (-A)*MvPolynomial.X 0+MvPolynomial.C (-B) := by
    simp only [affineLine,map_neg]
    ring
  rw [he]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · simp

theorem no_affine_interval (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (A B : ℂ) (a b : ℝ) (hab : a < b)
    (hzero : ∀ t ∈ Set.Ioo a b,
      MvPolynomial.eval ![(t : ℂ),A*(t : ℂ)+B] Q = 0) : False := by
  obtain ⟨H,hH⟩ := affine_interval_factor Q A B a b hab hzero
  have hunit : IsUnit H := (hQ.2 hH).resolve_left (affineLine_not_unit A B)
  have hD : H.totalDegree = 0 := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have hle : Q.totalDegree ≤ 1 := by
    rw [hH]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by rw [hD,add_zero]; exact affineLine_degree_le A B)
  omega

end ErdosDivisibleInflection

end

section

namespace ErdosCriticalGeometry

def criticalPoints (Q : MV ℂ) : Set (ℂ × ℂ) :=
  intersectionPoints Q (MvPolynomial.pderiv 0 Q) ∪ intersectionPoints Q (MvPolynomial.pderiv 1 Q)

def criticalAbscissae (Q : MV ℂ) : Set ℂ := Prod.fst '' criticalPoints Q

theorem mem_criticalPoints (Q : MV ℂ) (p : ℂ × ℂ) : p ∈ criticalPoints Q ↔
    MvPolynomial.eval ![p.1,p.2] Q = 0 ∧
      (MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 0 Q) = 0 ∨
       MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 1 Q) = 0) := by
  constructor
  · rintro (h | h)
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1, Or.inr h.2⟩
  · rintro ⟨h, h' | h'⟩
    · exact Or.inl ⟨h,h'⟩
    · exact Or.inr ⟨h,h'⟩

theorem partial_intersection_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (i : Fin 2) :
    (intersectionPoints Q (MvPolynomial.pderiv i Q)).Finite ∧
      (intersectionPoints Q (MvPolynomial.pderiv i Q)).ncard ≤ 2*Q.totalDegree^3 := by
  obtain ⟨hfin,hcard⟩ := irreducible_intersection_bound Q (MvPolynomial.pderiv i Q)
    hQ hdeg (nonlinear_partial_not_dvd Q hQ hdeg i)
  refine ⟨hfin,hcard.trans ?_⟩
  calc
    _ ≤ (2*Q.totalDegree^2)*Q.totalDegree := Nat.mul_le_mul_left _
      ((partial_totalDegree_le ℂ Q i).trans (Nat.sub_le _ _))
    _ = _ := by ring

theorem partial_abscissa_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (i : Fin 2) :
    (intersectionAbscissae Q (MvPolynomial.pderiv i Q)).Finite ∧
      (intersectionAbscissae Q (MvPolynomial.pderiv i Q)).ncard ≤ 2*Q.totalDegree^2 := by
  obtain ⟨hfin,hcard⟩ := irreducible_abscissa_bound Q (MvPolynomial.pderiv i Q)
    hQ hdeg (nonlinear_partial_not_dvd Q hQ hdeg i)
  refine ⟨hfin,hcard.trans ?_⟩
  calc
    _ ≤ (2*Q.totalDegree)*Q.totalDegree := Nat.mul_le_mul_left _
      ((partial_totalDegree_le ℂ Q i).trans (Nat.sub_le _ _))
    _ = _ := by ring

theorem critical_points_bound (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    (criticalPoints Q).Finite ∧ (criticalPoints Q).ncard ≤ 4*Q.totalDegree^3 := by
  obtain ⟨h0,c0⟩ := partial_intersection_bound Q hQ hdeg 0
  obtain ⟨h1,c1⟩ := partial_intersection_bound Q hQ hdeg 1
  refine ⟨h0.union h1, ?_⟩
  have h := Set.ncard_union_le (intersectionPoints Q (MvPolynomial.pderiv 0 Q))
    (intersectionPoints Q (MvPolynomial.pderiv 1 Q))
  change (criticalPoints Q).ncard ≤ _ at h
  omega

theorem critical_abscissae_bound (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    (criticalAbscissae Q).Finite ∧ (criticalAbscissae Q).ncard ≤ 4*Q.totalDegree^2 := by
  obtain ⟨h0,c0⟩ := partial_abscissa_bound Q hQ hdeg 0
  obtain ⟨h1,c1⟩ := partial_abscissa_bound Q hQ hdeg 1
  have he : criticalAbscissae Q = intersectionAbscissae Q (MvPolynomial.pderiv 0 Q) ∪
      intersectionAbscissae Q (MvPolynomial.pderiv 1 Q) := Set.image_union _ _ _
  rw [he]
  refine ⟨h0.union h1, ?_⟩
  have h := Set.ncard_union_le (intersectionAbscissae Q (MvPolynomial.pderiv 0 Q))
    (intersectionAbscissae Q (MvPolynomial.pderiv 1 Q))
  omega

end ErdosCriticalGeometry

end

section

namespace ErdosCriticalGeometry

noncomputable def inflection (Q : MV ℂ) : MV ℂ :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Q)*(MvPolynomial.pderiv 1 Q)^2 +
    MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)*
      MvPolynomial.pderiv 0 Q*MvPolynomial.pderiv 1 Q +
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 Q)*(MvPolynomial.pderiv 0 Q)^2

theorem inflection_degree_le (Q : MV ℂ) : (inflection Q).totalDegree ≤ 3*Q.totalDegree := by
  have h1 (i : Fin 2) : (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree :=
    (partial_totalDegree_le ℂ Q i).trans (Nat.sub_le _ _)
  have h2 (i j : Fin 2) : (MvPolynomial.pderiv i (MvPolynomial.pderiv j Q)).totalDegree ≤ Q.totalDegree :=
    ((partial_totalDegree_le ℂ _ i).trans (Nat.sub_le _ _)).trans (h1 j)
  have hp (i : Fin 2) : ((MvPolynomial.pderiv i Q)^2).totalDegree ≤ 2*Q.totalDegree :=
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (h1 i))
  have ha : (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Q)*(MvPolynomial.pderiv 1 Q)^2).totalDegree ≤
      3*Q.totalDegree := (MvPolynomial.totalDegree_mul _ _).trans (by linarith [h2 0 0,hp 1])
  have hb : (MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)*
      MvPolynomial.pderiv 0 Q*MvPolynomial.pderiv 1 Q).totalDegree ≤ 3*Q.totalDegree := by
    have hA := MvPolynomial.totalDegree_mul (MvPolynomial.C (-2 : ℂ)) (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q))
    have hB := MvPolynomial.totalDegree_mul (MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)) (MvPolynomial.pderiv 0 Q)
    have hC := MvPolynomial.totalDegree_mul (MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)*MvPolynomial.pderiv 0 Q) (MvPolynomial.pderiv 1 Q)
    simp only [MvPolynomial.totalDegree_C, zero_add] at hA
    linarith [h2 0 1,h1 0,h1 1]
  have hc : (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 Q)*(MvPolynomial.pderiv 0 Q)^2).totalDegree ≤
      3*Q.totalDegree := (MvPolynomial.totalDegree_mul _ _).trans (by linarith [h2 1 1,hp 0])
  unfold inflection
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le ha hb)) hc)

theorem inflection_intersection_bounds (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ inflection Q) :
    (intersectionPoints Q (inflection Q)).Finite ∧
      (intersectionPoints Q (inflection Q)).ncard ≤ 6*Q.totalDegree^3 ∧
      (intersectionAbscissae Q (inflection Q)).Finite ∧
      (intersectionAbscissae Q (inflection Q)).ncard ≤ 6*Q.totalDegree^2 := by
  obtain ⟨hp,cp⟩ := irreducible_intersection_bound Q (inflection Q) hQ hdeg hnd
  obtain ⟨ha,ca⟩ := irreducible_abscissa_bound Q (inflection Q) hQ hdeg hnd
  refine ⟨hp,cp.trans ?_,ha,ca.trans ?_⟩
  · calc
      _ ≤ (2*Q.totalDegree^2)*(3*Q.totalDegree) := Nat.mul_le_mul_left _ (inflection_degree_le Q)
      _ = _ := by ring
  · calc
      _ ≤ (2*Q.totalDegree)*(3*Q.totalDegree) := Nat.mul_le_mul_left _ (inflection_degree_le Q)
      _ = _ := by ring

theorem inflection_zero_divisible (Q : MV ℂ) (h : inflection Q = 0) : Q ∣ inflection Q := by
  rw [h]
  exact dvd_zero Q

theorem inflection_alternative (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    Q ∣ inflection Q ∨
      ((intersectionPoints Q (inflection Q)).Finite ∧
      (intersectionPoints Q (inflection Q)).ncard ≤ 6*Q.totalDegree^3 ∧
      (intersectionAbscissae Q (inflection Q)).Finite ∧
      (intersectionAbscissae Q (inflection Q)).ncard ≤ 6*Q.totalDegree^2) := by
  by_cases h : Q ∣ inflection Q
  · exact Or.inl h
  · exact Or.inr (inflection_intersection_bounds Q hQ hdeg h)

def exceptionalPoints (Q : MV ℂ) : Set (ℂ × ℂ) := criticalPoints Q ∪ intersectionPoints Q (inflection Q)

def exceptionalAbscissae (Q : MV ℂ) : Set ℂ := Prod.fst '' exceptionalPoints Q

theorem exceptional_points_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ inflection Q) :
    (exceptionalPoints Q).Finite ∧ (exceptionalPoints Q).ncard ≤ 10*Q.totalDegree^3 := by
  obtain ⟨hc,cc⟩ := critical_points_bound Q hQ hdeg
  obtain ⟨hi,ci,_,_⟩ := inflection_intersection_bounds Q hQ hdeg hnd
  refine ⟨hc.union hi, ?_⟩
  have h := Set.ncard_union_le (criticalPoints Q) (intersectionPoints Q (inflection Q))
  change (exceptionalPoints Q).ncard ≤ _ at h
  omega

theorem exceptional_abscissae_bound (Q : MV ℂ) (hQ : Irreducible Q)
    (hdeg : 1 < Q.totalDegree) (hnd : ¬Q ∣ inflection Q) :
    (exceptionalAbscissae Q).Finite ∧ (exceptionalAbscissae Q).ncard ≤ 10*Q.totalDegree^2 := by
  obtain ⟨hc,cc⟩ := critical_abscissae_bound Q hQ hdeg
  obtain ⟨_,_,hi,ci⟩ := inflection_intersection_bounds Q hQ hdeg hnd
  have he : exceptionalAbscissae Q = criticalAbscissae Q ∪ intersectionAbscissae Q (inflection Q) :=
    Set.image_union _ _ _
  rw [he]
  refine ⟨hc.union hi, ?_⟩
  have h := Set.ncard_union_le (criticalAbscissae Q) (intersectionAbscissae Q (inflection Q))
  omega

end ErdosCriticalGeometry

end

section

namespace ErdosCriticalGeometry

noncomputable def complexify (Q : MV ℝ) : MV ℂ := MvPolynomial.map (algebraMap ℝ ℂ) Q

theorem complexify_totalDegree (Q : MV ℝ) : (complexify Q).totalDegree = Q.totalDegree := by
  unfold complexify MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective Q (show Function.Injective (algebraMap ℝ ℂ) from
    Complex.ofReal_injective)]

theorem complexify_partial (Q : MV ℝ) (i : Fin 2) :
    complexify (MvPolynomial.pderiv i Q) = MvPolynomial.pderiv i (complexify Q) :=
  MvPolynomial.pderiv_map.symm

theorem complexify_eval (Q : MV ℝ) (x y : ℝ) :
    MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (complexify Q) = (MvPolynomial.eval ![x,y] Q : ℂ) := by
  have he : (algebraMap ℝ ℂ) ∘ (![x,y] : Fin 2 → ℝ) = ![(x : ℂ),(y : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.map_eval (algebraMap ℝ ℂ) ![x,y] Q
  rw [he] at h
  exact h.symm

def realCriticalPoints (Q : MV ℝ) : Set (ℝ × ℝ) :=
  {p | MvPolynomial.eval ![p.1,p.2] Q = 0 ∧
    (MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 0 Q) = 0 ∨
     MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 1 Q) = 0)}

def realCriticalAbscissae (Q : MV ℝ) : Set ℝ := Prod.fst '' realCriticalPoints Q

def complexPoint (p : ℝ × ℝ) : ℂ × ℂ := ((p.1 : ℂ),(p.2 : ℂ))

theorem complexPoint_injective : Function.Injective complexPoint := by
  intro p q h
  apply Prod.ext
  · exact Complex.ofReal_injective (congrArg Prod.fst h)
  · exact Complex.ofReal_injective (congrArg Prod.snd h)

theorem real_critical_iff (Q : MV ℝ) (p : ℝ × ℝ) :
    complexPoint p ∈ criticalPoints (complexify Q) ↔ p ∈ realCriticalPoints Q := by
  rw [mem_criticalPoints]
  simp only [complexPoint, realCriticalPoints, Set.mem_ofPred_eq, ← complexify_partial,
    complexify_eval, Complex.ofReal_eq_zero]

theorem real_critical_points_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) :
    (realCriticalPoints Q).Finite ∧ (realCriticalPoints Q).ncard ≤ 4*Q.totalDegree^3 := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := critical_points_bound (complexify Q) hQ hd
  have he : realCriticalPoints Q = complexPoint ⁻¹' criticalPoints (complexify Q) := by
    ext p
    exact (real_critical_iff Q p).symm
  have hrfin : (realCriticalPoints Q).Finite := by
    rw [he]
    exact hfin.preimage (fun _ _ _ _ h => complexPoint_injective h)
  refine ⟨hrfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn complexPoint
    (fun p hp => (real_critical_iff Q p).mpr hp) complexPoint_injective.injOn hfin
  apply hle.trans
  simpa only [complexify_totalDegree] using hcard

theorem real_critical_abscissae_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) :
    (realCriticalAbscissae Q).Finite ∧ (realCriticalAbscissae Q).ncard ≤ 4*Q.totalDegree^2 := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := critical_abscissae_bound (complexify Q) hQ hd
  have hrfin := (real_critical_points_bound Q hQ hdeg).1.image Prod.fst
  refine ⟨hrfin, ?_⟩
  have hmap : ∀ x ∈ realCriticalAbscissae Q, (x : ℂ) ∈ criticalAbscissae (complexify Q) := by
    rintro x ⟨p,hp,he⟩
    exact ⟨complexPoint p,(real_critical_iff Q p).mpr hp,congrArg Complex.ofReal he⟩
  have hle := Set.ncard_le_ncard_of_injOn Complex.ofReal hmap Complex.ofReal_injective.injOn hfin
  apply hle.trans
  simpa only [complexify_totalDegree] using hcard

end ErdosCriticalGeometry

end

end Erdos970

end OAI
