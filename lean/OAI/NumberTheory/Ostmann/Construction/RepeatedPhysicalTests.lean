import OAI.NumberTheory.Ostmann.Construction.RepeatedTuplePoisson
import OAI.NumberTheory.Ostmann.Construction.PhaseGiantMean
import OAI.NumberTheory.Ostmann.Preliminaries.WeightedNormTriangle

namespace OAI

/-! # Repeated local tests with normalized probability energy -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- The physical giant need not be bounded by one; its normalized energy
still gives the exact square-root bound needed for repeated factors. -/
theorem localTest_bound_of_energy {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (hF : ∑ x, ‖F x‖ ^ 2 ≤ (q : ℝ)) (x : ZMod q) :
    ‖F x‖ ≤ Real.sqrt q := by
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun y _ => sq_nonneg ‖F y‖) (Finset.mem_univ x)).trans hF

/-- Two repeated factors use Cauchy; all remaining factors use the
square-root bound. The local tests may belong to different roles. -/
theorem sum_norm_product_le_sqrt_pow {I : Type*} {q : ℕ} [NeZero q]
    (S : Finset I) (F : I → ZMod q → ℂ) (hS : 2 ≤ S.card)
    (hF : ∀ i ∈ S, ∑ x, ‖F i x‖ ^ 2 ≤ (q : ℝ)) :
    (∑ x : ZMod q, ‖∏ i ∈ S, F i x‖) ≤ (Real.sqrt q) ^ S.card := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  let R := (S.erase i).erase j
  have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hR : R.card + 2 = S.card := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hrest (x : ZMod q) : (∏ l ∈ R, ‖F l x‖) ≤ Real.sqrt q ^ R.card := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod₀
      (fun l _ => norm_nonneg (F l x)) (fun l hl =>
        localTest_bound_of_energy (F l) (hF l
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))) x)
  have htwo : (∑ x : ZMod q, ‖F i x‖ * ‖F j x‖) ≤ (q : ℝ) := by
    apply (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun x => ‖F i x‖) (fun x => ‖F j x‖)).trans
    calc
      _ ≤ Real.sqrt q * Real.sqrt q := mul_le_mul
        (Real.sqrt_le_sqrt (hF i hi)) (Real.sqrt_le_sqrt (hF j hj))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg q)
  calc
    _ = ∑ x : ZMod q, (‖F i x‖ * ‖F j x‖) * ∏ l ∈ R, ‖F l x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [norm_prod, ← Finset.mul_prod_erase S (fun l => ‖F l x‖) hi,
        ← Finset.mul_prod_erase (S.erase i) (fun l => ‖F l x‖) hj']
      ring
    _ ≤ ∑ x : ZMod q, (‖F i x‖ * ‖F j x‖) * Real.sqrt q ^ R.card := by
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrest x) (by positivity))
    _ = (∑ x : ZMod q, ‖F i x‖ * ‖F j x‖) * Real.sqrt q ^ R.card :=
      (Finset.sum_mul ..).symm
    _ ≤ (q : ℝ) * Real.sqrt q ^ R.card :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = Real.sqrt q ^ 2 * Real.sqrt q ^ R.card := by rw [Real.sq_sqrt (Nat.cast_nonneg q)]
    _ = _ := by rw [← pow_add, Nat.add_comm 2, hR]

theorem product_complete_mean_norm_le {I : Type*} {q : ℕ} [NeZero q]
    (S : Finset I) (F : I → ZMod q → ℂ) (hS : 2 ≤ S.card)
    (hF : ∀ i ∈ S, ∑ x, ‖F i x‖ ^ 2 ≤ (q : ℝ)) :
    ‖additiveFourier (fun x => ∏ i ∈ S, F i x) 0‖ ≤
      (q : ℝ)⁻¹ * Real.sqrt q ^ S.card := by
  rw [additiveFourier_apply]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
    (sum_norm_product_le_sqrt_pow S F hS hF)) (by positivity)

noncomputable def groupedPhysicalTest {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (q : P) (x : ZMod (q : ℕ)) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => p i = q), F i q x

theorem groupedPhysicalTest_product {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ) (a : ℤ) :
    (∏ q : P, groupedPhysicalTest P p F q (a : ZMod (q : ℕ))) =
      ∏ i, F i (p i) (a : ZMod (p i : ℕ)) := by
  unfold groupedPhysicalTest
  have he (q : P) :
      (∏ i ∈ Finset.univ.filter (fun i => p i = q), F i q (a : ZMod (q : ℕ))) =
      ∏ i ∈ Finset.univ.filter (fun i => p i = q), F i (p i) (a : ZMod (p i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [he]
  exact Finset.prod_fiberwise Finset.univ p _

theorem groupedPhysicalTest_singleton {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (i : I) (hi : ∀ j, p j = p i → j = i) :
    groupedPhysicalTest P p F (p i) = F i (p i) := by
  have hf : Finset.univ.filter (fun j => p j = p i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hi j, fun h => by rw [h]⟩
  funext x
  simp only [groupedPhysicalTest, hf, Finset.prod_singleton]

/-- Grouping at each distinct prime preserves the original physical product,
including when a prime occurs in several different roles. -/
noncomputable def physicalTupleSum {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑' a : ℤ, (∏ i, F i (p i) (a : ZMod (p i : ℕ))) * ψ ((a : ℝ) / X)

/-- A single occurrence of a mean-zero test annihilates the entire short-
period sum, without any character assumption. -/
theorem physicalTupleSum_singleton_zero {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (i : I) (hi : ∀ j, p j = p i → j = i) (hmean : ∑ x, F i (p i) x = 0)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    physicalTupleSum P p F ψ X = 0 := by
  let q : P → ℕ := fun q => q
  let : NeZero (∏ q : P, (q : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ))
      (fun q _ => (hP q q.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  have hz : additiveFourier (tupleCRTFunction q hc (groupedPhysicalTest P p F)) 0 = 0 := by
    rw [tupleCRTFunction_fourier]
    apply Finset.prod_eq_zero (Finset.mem_univ (p i))
    simp only [map_zero, Pi.zero_apply, mul_zero, groupedPhysicalTest_singleton P p F i hi]
    rw [additiveFourier_apply]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, hmean]
  have hs := periodic_poisson_complete_mean (tupleCRTFunction q hc (groupedPhysicalTest P p F))
    ψ X H hX hperiod hsupp
  simp_rw [tupleCRTFunction_intCast, groupedPhysicalTest_product] at hs
  rw [physicalTupleSum, hs, hz, mul_zero]

theorem groupedPhysicalTest_sqrt_product {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) :
    (∏ q : P, Real.sqrt (q : ℝ) ^ (Finset.univ.filter (fun i => p i = q)).card) =
      Real.sqrt (∏ i, (p i : ℝ)) := by
  have he (q : P) : (∏ i ∈ Finset.univ.filter (fun i => p i = q), Real.sqrt (p i : ℝ)) =
      Real.sqrt (q : ℝ) ^ (Finset.univ.filter (fun i => p i = q)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [← he]
  rw [Finset.prod_fiberwise, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg (p i).val)]

/-- The repeated tuple estimate needed in Section 7.3. Its dependence on
the product counted with multiplicity is exact. -/
theorem physicalTupleSum_multiple_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmultiple : ∀ q : P, 2 ≤ (Finset.univ.filter (fun i => p i = q)).card)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) / ∏ q : P, (q : ℝ)) := by
  let q : P → ℕ := fun q => q
  let : NeZero (∏ q : P, (q : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ))
      (fun q _ => (hP q q.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  have hlocal (a : P) : ‖additiveFourier (groupedPhysicalTest P p F a) 0‖ ≤
      (a : ℝ)⁻¹ * Real.sqrt (a : ℝ) ^ (Finset.univ.filter (fun i => p i = a)).card := by
    apply product_complete_mean_norm_le _ _ (hmultiple a)
    intro i hi
    have ha := (Finset.mem_filter.mp hi).2
    subst a
    exact henergy i
  have hm : ‖additiveFourier (tupleCRTFunction q hc (groupedPhysicalTest P p F)) 0‖ ≤
      Real.sqrt (∏ i, (p i : ℝ)) / ∏ a : P, (a : ℝ) := by
    rw [tupleCRTFunction_fourier]
    simp only [map_zero, Pi.zero_apply, mul_zero, norm_prod]
    apply (Finset.prod_le_prod₀ (fun a _ => norm_nonneg _) (fun a _ => hlocal a)).trans_eq
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, groupedPhysicalTest_sqrt_product,
      div_eq_mul_inv, mul_comm]
  have hs := periodic_poisson_complete_mean (tupleCRTFunction q hc (groupedPhysicalTest P p F))
    ψ X H hX hperiod hsupp
  simp_rw [tupleCRTFunction_intCast, groupedPhysicalTest_product] at hs
  rw [physicalTupleSum, hs, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]
  exact mul_le_mul_of_nonneg_left hm (mul_nonneg hX.le (norm_nonneg _))

/-- Either every used prime occurs twice, or a singleton mean-zero test
makes the complete residue mean vanish. This is the uniform short-period
bound before any summation over repeated tuples. -/
theorem physicalTupleSum_short_period_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (hP : ∀ q ∈ P, q.Prime) (p : I → P) (hp : Function.Surjective p)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i, ∑ x, F i (p i) x = 0)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) / ∏ q : P, (q : ℝ)) := by
  by_cases hm : ∀ q : P, 2 ≤ (Finset.univ.filter (fun i => p i = q)).card
  · exact physicalTupleSum_multiple_bound P hP p F hm henergy ψ X H hX hperiod hsupp
  · obtain ⟨q, hq⟩ := not_forall.mp hm
    obtain ⟨i, hi⟩ := hp q
    have hpos : 0 < (Finset.univ.filter (fun j => p j = q)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hone : (Finset.univ.filter (fun j => p j = q)).card = 1 := by omega
    have hsingle (j : I) (hj : p j = p i) : j = i := by
      apply Finset.card_le_one.mp hone.le j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.trans hi⟩) i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    rw [physicalTupleSum_singleton_zero P hP p F i hsingle (hmean i) ψ X H hX hperiod hsupp,
      norm_zero]
    positivity

/-- Repeating one prime makes the true period short at the initial product
scale. The resulting bound uses the actual physical tests throughout. -/
theorem physicalTupleSum_repeated_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (hP : ∀ q ∈ P, q.Prime) (p : I → P) (hp : Function.Surjective p)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i, ∑ x, F i (p i) x = 0)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < (p i : ℝ)) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) / ∏ q : P, (q : ℝ)) := by
  have hs := repeated_tuple_short_period (fun i => (p i : ℕ))
    (fun i => hP (p i) (p i).property) X H R hR hsmall hprod i j hij
    (congrArg Subtype.val heq)
  have he : sampledPrimeSet (fun i => (p i : ℕ)) = P := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (p i).property
    · intro hq
      obtain ⟨i, hi⟩ := hp ⟨q, hq⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, congrArg Subtype.val hi⟩
  rw [he] at hs
  have hperiod : H < X / (∏ q : P, (q : ℕ)) := by
    rw [Finset.prod_coe_sort P (fun q : ℕ => q)]
    exact hs
  exact physicalTupleSum_short_period_bound P hP p hp F hmean henergy ψ X H hX hperiod hsupp

/-- The ambient prime set may contain unused values. Restricting to the
actual image gives the true squarefree period and leaves every test unchanged. -/
theorem physicalTupleSum_repeated_bound_used {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i, ∑ x, F i (p i) x = 0)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < (p i : ℝ)) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) /
        ∏ q ∈ Finset.univ.image p, (q : ℝ)) := by
  let Q := sampledPrimeSet (fun i => (p i : ℕ))
  have hQP : Q ⊆ P := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact (p i).property
  let toP : Q → P := fun q => ⟨q.val, hQP q.property⟩
  let p' : I → Q := fun i => ⟨(p i : ℕ), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let F' : I → (q : Q) → ZMod (q : ℕ) → ℂ := fun i q => F i (toP q)
  let : ∀ q : Q, NeZero (q : ℕ) := fun q => ⟨(hP q (hQP q.property)).ne_zero⟩
  have hback (i : I) : toP (p' i) = p i := Subtype.ext rfl
  have hp' : Function.Surjective p' := by
    intro q
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp q.property
    exact ⟨i, Subtype.ext hi⟩
  have hm' (i : I) : (∑ x, F' i (p' i) x) = 0 := by
    simpa only [F', hback] using hmean i
  have he' (i : I) : (∑ x, ‖F' i (p' i) x‖ ^ 2) ≤ (p' i : ℝ) := by
    simpa only [F', hback] using henergy i
  have hij' : p' i = p' j :=
    Subtype.ext (congrArg (fun z : P => (z : ℕ)) heq)
  have h := physicalTupleSum_repeated_bound Q (fun q hq => hP q (hQP hq)) p' hp' F'
    hm' he' ψ X H R hX hR hsupp hsmall hprod i j hij hij'
  have hsum : physicalTupleSum Q p' F' ψ X = physicalTupleSum P p F ψ X := by
    unfold physicalTupleSum
    apply tsum_congr
    intro a
    congr 1
  have hperiod : (∏ q : Q, (q : ℝ)) = ∏ q ∈ Finset.univ.image p, (q : ℝ) := by
    rw [Finset.prod_coe_sort Q (fun q : ℕ => (q : ℝ))]
    have hQ : Q = (Finset.univ.image p).image (fun z : P => (z : ℕ)) := by
      simp only [Q, sampledPrimeSet, Finset.image_image, Function.comp_def]
    rw [hQ]
    rw [Finset.prod_image]
    exact fun a _ b _ hab => Subtype.ext hab
  simpa only [hsum, hperiod, p'] using h

end Ostmann

end OAI
