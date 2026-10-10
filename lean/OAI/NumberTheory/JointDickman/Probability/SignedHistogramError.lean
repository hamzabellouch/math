import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass
import OAI.NumberTheory.JointDickman.Amplification.CellAverageOscillation

namespace OAI

/-! # Histogram replacement for the actual signed fair-split measure -/

namespace JointDickman
open Finset MeasureTheory

/-- Replacing a test on one cell only costs its oscillation times the
positive half-prime mass of that cell. -/
theorem signedSplitProductMass_cell_error {A : Type*} [DecidableEq A]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : Finset ℕ → ℝ) (hg : ∀ S ⊆ P, |g S| ≤ 1)
    (cell : ℕ → Option A) (a : A) (F : ℕ → ℂ) (c : ℂ) (E : ℝ)
    (hosc : ∀ n ∈ primeSplitProductSupport P, cell n = some a → ‖F n-c‖ ≤ E) :
    ‖(∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        (signedSplitProductMass P g n : ℂ)*F n else 0) -
      ((∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        signedSplitProductMass P g n else 0) : ℝ)*c‖ ≤
      E * ∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        primeProductMass P (1/2) n else 0 := by
  classical
  have he : (∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        (signedSplitProductMass P g n : ℂ)*F n else 0) -
      ((∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        signedSplitProductMass P g n else 0) : ℝ)*c =
      ∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        (signedSplitProductMass P g n : ℂ)*(F n-c) else 0 := by
    simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,
      sum_mul,← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hn : cell n = some a
    · simp only [hn,ite_true]
      ring
    · simp only [hn,ite_false,zero_mul,sub_self]
  rw [he,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  by_cases hcell : cell n = some a
  · simp only [hcell,ite_true,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (signedSplitProductMass_abs_le hP hg n) (hosc n hn hcell)
      (norm_nonneg _) ((abs_nonneg _).trans (signedSplitProductMass_abs_le hP hg n))).trans_eq
        (mul_comm _ _)
  · simp [hcell]

/-- The per-cell error in (38), with exactly the delta/phi channel normalization. -/
theorem manuscriptChannel_cell_average_error {m₁ B q : ℕ} [NeZero q]
    (hm : 0 < m₁) (hB : 0 < B)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ)
    (F : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hF : IntervalIntegrable F volume (channelLower (channelFineCount m₁ B) a.1)
      (channelUpper (channelFineCount m₁ B) a.1))
    (hLip : ∀ u ∈ Set.Icc (channelLower (channelFineCount m₁ B) a.1)
        (channelUpper (channelFineCount m₁ B) a.1),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m₁ B) a.1)
        (channelUpper (channelFineCount m₁ B) a.1), ‖F u-F v‖ ≤ L*|u-v|) :
    let n := channelFineCount m₁ B
    let cell := logResidueCell B q (channelLower n) (channelUpper n)
    let μ := channelMesh n/(q.totient : ℝ)
    ‖(∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B), if cell k = some a then
        (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) k : ℂ)*
          F (Real.log k/B) else 0) -
      (μ*manuscriptChannel m₁ B q g a : ℝ)*
        complexCellAverage (channelLower n a.1) (channelUpper n a.1) F‖ ≤
      (L*channelMesh n)*μ*manuscriptChannel m₁ B q (fun _ => 1) a := by
  classical
  dsimp only
  let n := channelFineCount m₁ B
  let cell := logResidueCell B q (channelLower n) (channelUpper n)
  have hn := channelFineCount_pos hm hB
  have hwidth := channel_width n a.1
  have hab : channelLower n a.1 < channelUpper n a.1 := by
    linarith [channelMesh_pos hn]
  have h := signedSplitProductMass_cell_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (subsetSiteTest (auxiliaryPrimes B) g) (fun S _ => hg _) cell a
    (fun k => F (Real.log k/B))
    (complexCellAverage (channelLower n a.1) (channelUpper n a.1) F)
    (L*channelMesh n) (by
      intro k _ hk
      have hx := (logResidueCell_eq_some B q (channelLower n) (channelUpper n)
        (channelCells_disjoint hn) k a.1 a.2).mp hk
      have herr := complexCellAverage_lipschitz_error hab hL hF
        (Set.Ioc_subset_Icc_self hx.1) hLip
      rwa [hwidth] at herr)
  rw [manuscriptChannel_cell_mass hm hB] at h
  have hone : (∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B), if cell k = some a then
      primeProductMass (auxiliaryPrimes B) (1/2) k else 0) =
      (channelMesh n/(q.totient : ℝ))*manuscriptChannel m₁ B q (fun _ => 1) a := by
    have hh := manuscriptChannel_cell_mass hm hB (fun _ => 1) a
    have he : subsetSiteTest (auxiliaryPrimes B) (fun _ => 1) = (fun _ => 1) := rfl
    rw [he] at hh
    simpa only [signedSplitProductMass_one] using hh
  rw [hone] at h
  exact h.trans_eq (by ring)

end JointDickman

end OAI
