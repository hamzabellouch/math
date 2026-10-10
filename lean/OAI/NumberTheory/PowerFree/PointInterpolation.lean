import OAI.NumberTheory.PowerFree.DegreeBudgets

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem exists_mv_interpolate {ι σ K : Type*} [Fintype ι] [Field K]
    (z : ι → σ → K) (hz : Function.Injective z) (v : ι → K) :
    ∃ p : MvPolynomial σ K, ∀ i, eval (z i) p = v i := by
  classical
  have hsep : ∀ i j : ι, i ≠ j → ∃ a, z i a ≠ z j a := by
    intro i j hij
    by_contra! h
    exact hij (hz (funext h))
  let L : ι → ι → MvPolynomial σ K := fun i j =>
    if hij : i = j then 1 else
      let a := (hsep i j hij).choose
      C ((z i a - z j a)⁻¹) * (X a - C (z j a))
  have hLi : ∀ i j, eval (z i) (L i j) = 1 := by
    intro i j
    by_cases h : i = j
    · simp [L, h]
    · simp only [L, h, ↓reduceDIte, map_mul, eval_C, map_sub, eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep i j h).choose_spec)
  have hLj : ∀ i j, i ≠ j → eval (z j) (L i j) = 0 := by
    intro i j h
    simp [L, h]
  refine ⟨∑ i, C (v i) * ∏ j, L i j, ?_⟩
  intro a
  rw [map_sum, Finset.sum_eq_single a]
  · simp [hLi]
  · intro i _ hia
    rw [map_mul, eval_C, map_prod]
    have hp : (∏ j, eval (z a) (L i j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (hLj i a hia)
    rw [hp, mul_zero]
  · simp

theorem card_points_le_hilbert_constant {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : ι → Fin n → K)
    (hz : Function.Injective z) (hroot : ∀ i p, p ∈ I → eval (z i) p = 0)
    (P : Polynomial ℚ) (hdeg : P.natDegree = 0)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ)) :
    (Fintype.card ι : ℚ) ≤ P.coeff 0 := by
  classical
  choose p hp using fun i : ι => exists_mv_interpolate z hz (Pi.single i 1)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hP
  let T := max N (Finset.univ.sup (fun i => (p i).totalDegree))
  have hpd : ∀ i, p i ∈ totalSpace T := by
    intro i
    apply mem_totalSpace.mpr
    exact (Finset.le_sup (f := fun j => (p j).totalDegree) (Finset.mem_univ i)).trans (le_max_right _ _)
  let W := (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let L : (ι → K) →ₗ[K] W :=
    { toFun := fun x => ⟨Ideal.Quotient.mk I (∑ i, x i • p i),
        ⟨∑ i, x i • p i, Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hpd i)), rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change Ideal.Quotient.mk I (∑ i, (x i+y i) • p i) =
          Ideal.Quotient.mk I (∑ i, x i • p i) + Ideal.Quotient.mk I (∑ i, y i • p i)
        simp only [add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := by
        intro c x
        apply Subtype.ext
        change Ideal.Quotient.mk I (∑ i, (c*x i) • p i) =
          c • Ideal.Quotient.mk I (∑ i, x i • p i)
        have hs : (∑ i, (c*x i) • p i) = c • (∑ i, x i • p i) := by
          rw [Finset.smul_sum]
          simp only [smul_smul]
        rw [hs]
        exact (Ideal.Quotient.mkₐ K I).toLinearMap.map_smul c _ }
  have hev (x : ι → K) (i : ι) : eval (z i) (∑ j, x j • p j) = x i := by
    change (aeval (z i)).toLinearMap (∑ j, x j • p j) = x i
    have he (j : ι) : (aeval (z i)).toLinearMap (p j) = (if j=i then (1 : K) else 0) := by
      change eval (z i) (p j) = _
      simpa [Pi.single_apply, eq_comm] using hp j i
    simp only [map_sum, LinearMap.map_smul, he, smul_eq_mul]
    simp
  have hL : Function.Injective L := by
    intro x y hxy
    have hm : (∑ i, x i • p i) - (∑ i, y i • p i) ∈ I :=
      Ideal.Quotient.eq.mp (congrArg Subtype.val hxy)
    funext i
    have he := hroot i _ hm
    rw [map_sub, hev, hev, sub_eq_zero] at he
    exact he
  let := totalSpace_finite (n := n) (K := K) T
  have hc : Fintype.card ι ≤ Module.finrank K W := by
    simpa only [Module.finrank_fintype_fun_eq_card] using LinearMap.finrank_le_finrank_of_injective hL
  have he := hN T (le_max_left _ _)
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.eval_C] at he
  exact (Nat.cast_le.mpr hc).trans_eq he

end
section
open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem affineDimension_independent_coordinates {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) :
    ∃ j : Fin (affineDimension I) → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) := by
  obtain ⟨P,j,hj,hi,_,N,hN⟩ := coordinate_hilbert_degree_independent I hI
  have he : P = coordinateHilbert I := by
    apply polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Filter.eventually_atTop.mpr ⟨N,hN⟩,coordinateHilbert_eventually I] with T hp hq
    exact hp.symm.trans hq
  subst P
  exact ⟨j,hj,hi⟩

theorem determined_bounded_patch {n D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hD : affineDegree I ≤ D) (z : ι → Fin n → ℤ)
    (hdet : DeterminedInDegree I z D)
    (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    ∃ J : Set (Fin n), Nat.card J = affineDimension I ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) ℤ,
        (∀ i, (G i).totalDegree ≤ D) ∧
        (∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ integralKernelHeight ((D+n).choose n) (H^D)) ∧
        (∀ i, MvPolynomial.map (Int.castRingHom K) (G i) ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (MvPolynomial.map (Int.castRingHom K) (G i))) ∉ I := by
  obtain ⟨j,_,hj⟩ := affineDimension_independent_coordinates I (Ideal.IsPrime.ne_top inferInstance)
  obtain hc | hp := bounded_patch_or_cut I (coordinateHilbert I) le_rfl
    (coordinateHilbert_eventually I) hD j hj z hzI H hH hz
  · obtain ⟨G,hG,_,hvan,hnot⟩ := hc
    have hd : (MvPolynomial.map (Int.castRingHom K) G).totalDegree ≤ D := by
      simpa only [totalDegree, support_map_of_injective G (f := Int.castRingHom K) (Int.cast_injective (α := K))] using hG
    have hv : ∀ i, eval (fun l => (z i l : K)) (MvPolynomial.map (Int.castRingHom K) G) = 0 := by
      intro i
      have he := map_eval (Int.castRingHom K) (z i) G
      rw [hvan i, map_zero] at he
      exact he.symm
    exact (hnot ((hdet _ hd).mp hv)).elim
  · exact hp

theorem point_on_minimal_component {n : ℕ} {K : Type*} [Field K]
    (J : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → K)
    (hz : ∀ p ∈ J, eval z p = 0) :
    ∃ Q ∈ J.minimalPrimes, ∀ p ∈ Q, eval z p = 0 := by
  let P := RingHom.ker (eval z)
  have hP : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le (show J ≤ P from hz)
  exact ⟨Q,hQ,fun p hp => hQP hp⟩

theorem proper_cut_components {n h : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hd : affineDimension I = h+1) :
    ∃ Q : Finset (Ideal (MvPolynomial (Fin n) K)),
      (∀ J ∈ Q, J.IsPrime ∧ affineDimension J = h) ∧
      (∑ J ∈ Q, affineDegree J) ≤ (p.totalDegree : ℚ) * affineDegree I ∧
      (Q.card : ℚ) ≤ (p.totalDegree : ℚ) * affineDegree I ∧
      (∀ z : Fin n → K, (∀ F ∈ I, eval z F = 0) → eval z p = 0 →
        ∃ J ∈ Q, ∀ F ∈ J, eval z F = 0) := by
  classical
  let J := I ⊔ Ideal.span {p}
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) J).toFinset
  have hQ : ∀ q : Q, q.val ∈ J.minimalPrimes := fun q => by
    exact (Set.Finite.mem_toFinset _).mp q.property
  refine ⟨Q,?_,?_,?_,?_⟩
  · intro q hq
    have hm := hQ ⟨q,hq⟩
    have := hm.isPrime
    exact ⟨hm.isPrime,proper_cut_component_dimension I q p hp hm hd⟩
  · simpa only [Finset.univ_eq_attach, Finset.sum_attach] using proper_cut_sum_affineDegree_le I p hp hd (fun q : Q => q.val) hQ Subtype.val_injective
  · simpa using proper_cut_component_card_le I p hp hd (fun q : Q => q.val) hQ Subtype.val_injective
  · intro z hI hz
    have hvan : ∀ F ∈ J, eval z F = 0 := by
      change J ≤ RingHom.ker (eval z)
      apply sup_le hI
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hz)
    obtain ⟨q,hq,hzq⟩ := point_on_minimal_component J z hvan
    exact ⟨q,(Set.Finite.mem_toFinset _).mpr hq,hzq⟩

end
open MvPolynomial

theorem zeroDim_isMaximal {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I = 0) : I.IsMaximal := by
  have ht := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
  change (affineDimension I : Cardinal) = _ at ht
  rw [hd, Nat.cast_zero] at ht
  let : Algebra.IsAlgebraic K (MvPolynomial (Fin n) K ⧸ I) := trdeg_eq_zero_iff.mp ht.symm
  exact Ideal.Quotient.maximal_of_isField I (isField_of_isIntegral_of_isField' (R := K)
    (S := MvPolynomial (Fin n) K ⧸ I) (Field.toIsField K))

theorem zeroDim_eq_point {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I = 0) (z : Fin n → K)
    (hz : ∀ p ∈ I, eval z p = 0) : I = RingHom.ker (eval z) := by
  apply (zeroDim_isMaximal I hd).eq_of_le (RingHom.ker_isPrime _).ne_top
  exact hz

theorem zeroDim_determined {n D : ℕ} {ι K : Type*} [Nonempty ι] [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I = 0) (z : ι → Fin n → ℤ)
    (hz : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0) : DeterminedInDegree I z D := by
  intro p _
  constructor
  · intro hp
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [zeroDim_eq_point I hd (fun l => (z i l : K)) (fun q hq => hz q hq i)]
    exact hp i
  · exact hz p

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure IntegerPatch (n : ℕ) where
  free : Set (Fin n)
  equations : ↥(freeᶜ) → MvPolynomial (Fin n) ℤ

noncomputable def IntegerPatch.minor {n : ℕ} (P : IntegerPatch n) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (fun i j : ↥(P.freeᶜ) => pderiv j.val (P.equations i))

def IntegerPatch.On {n : ℕ} {K : Type*} [Field K]
    (P : IntegerPatch n) (I : Ideal (MvPolynomial (Fin n) K)) : Prop :=
  Nat.card P.free = affineDimension I ∧
  (∀ i, MvPolynomial.map (Int.castRingHom K) (P.equations i) ∈ I) ∧
  MvPolynomial.map (Int.castRingHom K) P.minor ∉ I

def IntegerPatch.Bounded {n : ℕ} (P : IntegerPatch n) (D : ℕ) (H : ℝ) : Prop :=
  ∃ d ≤ D, (∀ i, (P.equations i).totalDegree ≤ d) ∧
    ∀ i m, |(((P.equations i).coeff m : ℤ) : ℝ)| ≤
      integralKernelHeight ((d+n).choose n) (H^d)

def PointOn {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) : Prop :=
  ∀ p ∈ I, eval (fun l => (z l : K)) p = 0

theorem IntegerPatch.Bounded.mono {n D E : ℕ} {P : IntegerPatch n} {H : ℝ}
    (h : P.Bounded D H) (hDE : D ≤ E) : P.Bounded E H := by
  obtain ⟨d,hd,hdeg,hheight⟩ := h
  exact ⟨d,hd.trans hDE,hdeg,hheight⟩

theorem map_integer_minor {n : ℕ} {K : Type*} [Field K] (P : IntegerPatch n) :
    MvPolynomial.map (Int.castRingHom K) P.minor =
      Matrix.det (fun i j : ↥(P.freeᶜ) => pderiv j.val
        (MvPolynomial.map (Int.castRingHom K) (P.equations i))) := by
  let M : Matrix ↥(P.freeᶜ) ↥(P.freeᶜ) (MvPolynomial (Fin n) ℤ) :=
    fun i j => pderiv j.val (P.equations i)
  have he := (MvPolynomial.map (Int.castRingHom K)).map_det M
  calc
    MvPolynomial.map (Int.castRingHom K) P.minor =
      Matrix.det (fun i j => MvPolynomial.map (Int.castRingHom K) (M i j)) := he
    _ = _ := by congr 1; funext i j; exact pderiv_map.symm

theorem determined_integer_patch {n D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hD : affineDegree I ≤ D) (z : ι → Fin n → ℤ)
    (hdet : DeterminedInDegree I z D)
    (hzI : ∀ i, PointOn I (z i))
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    ∃ P : IntegerPatch n, P.On I ∧ P.Bounded D H := by
  obtain ⟨J,hJ,G,hdeg,hheight,hGI,hminor⟩ := determined_bounded_patch I hD z hdet
    (fun p hp i => hzI i p hp) H hH hz
  let P : IntegerPatch n := ⟨J,G⟩
  refine ⟨P,⟨hJ,hGI,?_⟩,D,le_rfl,hdeg,hheight⟩
  simpa only [map_integer_minor] using hminor

theorem IntegerPatch.minor_degree_le {n D : ℕ} {P : IntegerPatch n} {H : ℝ}
    (h : P.Bounded D H) : P.minor.totalDegree ≤ n * D := by
  obtain ⟨d,hd,hdeg,_⟩ := h
  apply (jacobian_minor_degree P.equations Subtype.val d hdeg).trans
  apply Nat.mul_le_mul
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ∈ P.freeᶜ)
  · exact (Nat.sub_le _ _).trans hd

theorem bounded_cut_components {n h e D : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (he : affineDegree I ≤ e) (p : MvPolynomial (Fin n) K)
    (hp : p ∉ I) (hpD : p.totalDegree ≤ D) (hd : affineDimension I = h+1) :
    ∃ Q : Finset (Ideal (MvPolynomial (Fin n) K)),
      Q.card ≤ D*e ∧
      (∀ J ∈ Q, J.IsPrime ∧ I ≤ J ∧ affineDimension J = h ∧ affineDegree J ≤ D*e) ∧
      (∀ z : Fin n → K, (∀ F ∈ I, eval z F = 0) → eval z p = 0 →
        ∃ J ∈ Q, ∀ F ∈ J, eval z F = 0) := by
  classical
  let J := I ⊔ Ideal.span {p}
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) J).toFinset
  have hQ : ∀ q : Q, q.val ∈ J.minimalPrimes := fun q =>
    (Set.Finite.mem_toFinset _).mp q.property
  have hsum : ∑ q ∈ Q, affineDegree q ≤ (D*e : ℕ) := by
    calc
      ∑ q ∈ Q, affineDegree q ≤ (p.totalDegree : ℚ) * affineDegree I := by
        simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
          proper_cut_sum_affineDegree_le I p hp hd (fun q : Q => q.val) hQ Subtype.val_injective
      _ ≤ (D : ℚ) * e := mul_le_mul (by exact_mod_cast hpD) he
        ((one_le_affineDegree I Ideal.IsPrime.ne_top').trans' zero_le_one) (Nat.cast_nonneg _)
      _ = (D*e : ℕ) := by norm_cast
  have hnonneg : ∀ q ∈ Q, (0 : ℚ) ≤ affineDegree q := fun q hq =>
    zero_le_one.trans (one_le_affineDegree q (hQ ⟨q,hq⟩).isPrime.ne_top)
  refine ⟨Q,?_,?_,?_⟩
  · have hc : (Q.card : ℚ) ≤ ∑ q ∈ Q, affineDegree q := by
      calc
        (Q.card : ℚ) = ∑ _q ∈ Q, (1 : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun q hq => one_le_affineDegree q (hQ ⟨q,hq⟩).isPrime.ne_top
    exact_mod_cast hc.trans hsum
  · intro q hq
    have hm := hQ ⟨q,hq⟩
    let := hm.isPrime
    refine ⟨hm.isPrime,?_,proper_cut_component_dimension I q p hp hm hd,?_⟩
    · exact le_sup_left.trans hm.1.2
    · simpa only [Nat.cast_mul] using (Finset.single_le_sum hnonneg hq).trans hsum
  · intro z hz hpz
    obtain ⟨q,hq,hzq⟩ := point_on_minimal_component J z (show J ≤ RingHom.ker (eval z) from
      sup_le hz (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpz)))
    exact ⟨q,(Set.Finite.mem_toFinset _).mpr hq,hzq⟩

end QuarticPowerFree

end OAI
