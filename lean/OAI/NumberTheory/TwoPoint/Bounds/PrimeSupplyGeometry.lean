import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeBands

namespace OAI

/-! Actual disjoint prime supplies at geometric logarithmic scales. Their
mass follows from the published fixed-modulus input through the proved
partial-summation chain, and all support assertions are finite identities. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeSupplyEndpoint (A W : ℝ) (i : ℕ) : ℝ :=
  A * Real.exp (6 * W * i)

noncomputable def centeredPrimeSupply (E : Finset ℕ) (A W : ℝ) (i : ℕ) : Finset ℕ :=
  modFivePrimeBand E true (Real.exp (primeSupplyEndpoint A W i))
    (Real.exp (primeSupplyEndpoint A W (i + 1)))

noncomputable def paddingPrimeSupply (E : Finset ℕ) (L : ℝ) : Finset ℕ :=
  deletedModFivePrimes E false (Real.exp L)

lemma primeSupplyEndpoint_zero (A W : ℝ) : primeSupplyEndpoint A W 0 = A := by
  simp [primeSupplyEndpoint]

lemma primeSupplyEndpoint_succ (A W : ℝ) (i : ℕ) :
    primeSupplyEndpoint A W (i + 1) = primeSupplyEndpoint A W i * Real.exp (6 * W) := by
  unfold primeSupplyEndpoint
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  ring

lemma primeSupplyEndpoint_mono (A W : ℝ) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    Monotone (primeSupplyEndpoint A W) := by
  intro i j hij
  unfold primeSupplyEndpoint
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity)

lemma centeredPrimeSupply_mem {E : Finset ℕ} {A W : ℝ} {i p : ℕ}
    (hp : p ∈ centeredPrimeSupply E A W i) :
    p.Prime ∧ p % 5 = 1 ∧ p ∉ E ∧
      primeSupplyEndpoint A W i < Real.log p ∧
      Real.log p ≤ primeSupplyEndpoint A W (i + 1) := by
  obtain ⟨hlo, hhi, hs, he⟩ := (modFivePrimeBand_mem (Real.exp_pos _).le
    (Real.exp_pos _).le).mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hs.1.pos
  refine ⟨hs.1, hs.2, he, ?_, ?_⟩
  · simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hlo
  · simpa only [Real.log_exp] using Real.log_le_log hp0 hhi

lemma centeredPrimeSupply_pairwise_disjoint (E : Finset ℕ) (A W : ℝ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) :
    Pairwise (fun i j => Disjoint (centeredPrimeSupply E A W i) (centeredPrimeSupply E A W j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := centeredPrimeSupply_mem hpi
  have hj := centeredPrimeSupply_mem hpj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hh := primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hlt)
    linarith [hi.2.2.2.2, hj.2.2.2.1]
  · have hh := primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hgt)
    linarith [hj.2.2.2.2, hi.2.2.2.1]

lemma centered_padding_disjoint (E : Finset ℕ) (A W L : ℝ) (i : ℕ) :
    Disjoint (centeredPrimeSupply E A W i) (paddingPrimeSupply E L) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hpc := (centeredPrimeSupply_mem hp).2.1
  have hqc := (mem_filter.mp (mem_sdiff.mp hq).1).2.2
  exact hqc hpc

lemma centeredPrimeSupply_global_bounds {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 ≤ A) (hW : 0 ≤ W) {J i p : ℕ} (hi : i < J)
    (hL : primeSupplyEndpoint A W J ≤ L) (hp : p ∈ centeredPrimeSupply E A W i) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  have hh := centeredPrimeSupply_mem hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
  have hlo : A < Real.log p := by
    have hmono := primeSupplyEndpoint_mono A W hA hW (Nat.zero_le i)
    rw [primeSupplyEndpoint_zero] at hmono
    exact hmono.trans_lt hh.2.2.2.1
  have hhi : Real.log p ≤ L := hh.2.2.2.2.trans
    ((primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hi)).trans hL)
  constructor
  · simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hlo
  · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hhi

lemma primeSupplyEndpoint_sum_lt (A W : ℝ) (hA : 0 < A) (hW : 1 ≤ W) (J : ℕ) :
    (∑ i ∈ range J, primeSupplyEndpoint A W (i + 1)) < 2 * primeSupplyEndpoint A W J := by
  have hratio : 2 ≤ Real.exp (6 * W) := by
    linarith [Real.add_one_le_exp (6 * W)]
  induction J with
  | zero => simp [primeSupplyEndpoint, hA]
  | succ J ih =>
    have he : 0 ≤ primeSupplyEndpoint A W J := by unfold primeSupplyEndpoint; positivity
    have hstep : 2 * primeSupplyEndpoint A W J ≤ primeSupplyEndpoint A W (J + 1) := by
      rw [primeSupplyEndpoint_succ]
      nlinarith [mul_le_mul_of_nonneg_right hratio he]
    rw [sum_range_succ]
    linarith

lemma centeredPrimeSupply_tuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    (p : Fin J → ℕ) (hp : ∀ i : Fin J, p i ∈ centeredPrimeSupply E A W i.val) :
    Real.log ((∏ i, p i : ℕ) : ℝ) < 2 * L := by
  have hlog : Real.log ((∏ i, p i : ℕ) : ℝ) = ∑ i, Real.log (p i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (centeredPrimeSupply_mem (hp i)).1.ne_zero
  rw [hlog]
  calc
    _ ≤ ∑ i : Fin J, primeSupplyEndpoint A W (i.val + 1) :=
      sum_le_sum (fun i _ => (centeredPrimeSupply_mem (hp i)).2.2.2.2)
    _ = ∑ i ∈ range J, primeSupplyEndpoint A W (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => primeSupplyEndpoint A W (i + 1)) J
    _ < 2 * primeSupplyEndpoint A W J := primeSupplyEndpoint_sum_lt A W hA hW J
    _ ≤ 2 * L := by linarith

/-- Every centered supply is nonempty and has the required reciprocal mass.
The threshold is independent of the number of supplies and their indices. -/
theorem ModFiveThetaInput.centered_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ i : ℕ,
      (centeredPrimeSupply E A W i).Nonempty ∧
      W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨A₀, hA₀, hmass⟩ := hP.centered_band_mass E W hW
  refine ⟨A₀, hA₀, fun A hA i => ?_⟩
  have hA0 : 0 ≤ A := (zero_le_one.trans hA₀).trans hA
  have hlower : A₀ ≤ primeSupplyEndpoint A W i := by
    calc
      A₀ ≤ A := hA
      _ = primeSupplyEndpoint A W 0 := (primeSupplyEndpoint_zero A W).symm
      _ ≤ _ := primeSupplyEndpoint_mono A W hA0 hW.le (Nat.zero_le _)
  have hh := hmass (primeSupplyEndpoint A W i) hlower
  rw [← primeSupplyEndpoint_succ] at hh
  change W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W at hh
  refine ⟨?_, hh⟩
  by_contra he
  rw [not_nonempty_iff_eq_empty.mp he, sum_empty] at hh
  linarith [hh.1]

end TwoPointCorrelations

end OAI
