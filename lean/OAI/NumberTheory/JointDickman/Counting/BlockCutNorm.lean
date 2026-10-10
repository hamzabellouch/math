import OAI.NumberTheory.JointDickman.Counting.ArithmeticBlockMatrix

namespace OAI

/-! # The finite cut norm controls every choice of bounded block labels -/

namespace JointDickman
open Finset

theorem complexEnergy_cutMaximum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16*kernelCutMaximum K := by
  classical
  apply complexEnergy_le_sixteen K (kernelCutMaximum K) _ z hz
  intro f g hf hg
  apply realBilinear_bound_of_signs K (kernelCutMaximum K) _ f g hf hg
  intro s t
  exact le_sup' (fun st : (ι → Bool) × (ι → Bool) =>
    |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)
    (mem_univ (s,t))

theorem complexEnergy_re_cutNorm_le (M : ℕ) (K : Fin M → Fin M → ℝ)
    (z : Fin M → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    |(complexEnergy K z).re|/(M : ℝ) ≤ 16*kernelCutNorm K := by
  have h := (Complex.abs_re_le_norm (complexEnergy K z)).trans
    (complexEnergy_cutMaximum_le K z hz)
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  simpa only [kernelCutNorm,Fintype.card_fin,mul_div_assoc] using hd

theorem arithmeticBlockAverage_cutNorm (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |arithmeticBlockAverage B L τ C T N H M F| ≤
      16*∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        kernelCutNorm (arithmeticBlockMatrix B L τ C T N H M s) := by
  rw [arithmeticBlockAverage_matrix,abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M)]
  calc
    _ ≤ (∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        |(complexEnergy (arithmeticBlockMatrix B L τ C T N H M s)
          (blockLabels M s F)).re|)/(M : ℝ) :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
    _ = ∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        |(complexEnergy (arithmeticBlockMatrix B L τ C T N H M s)
          (blockLabels M s F)).re|/(M : ℝ) := sum_div _ _ _
    _ ≤ ∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        16*kernelCutNorm (arithmeticBlockMatrix B L τ C T N H M s) := by
      apply sum_le_sum
      intro s _
      exact complexEnergy_re_cutNorm_le M _ _ (fun i => hF _)
    _ = _ := (mul_sum ..).symm

theorem positive_block_forces_cut_mass (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) {e : ℝ}
    (he : e ≤ arithmeticBlockAverage B L τ C T N H M F) :
    e/16 ≤ ∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
      kernelCutNorm (arithmeticBlockMatrix B L τ C T N H M s) := by
  have h := (le_abs_self (arithmeticBlockAverage B L τ C T N H M F)).trans
    (arithmeticBlockAverage_cutNorm B L τ C T N H M F hF)
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  linarith only [he,h]

end JointDickman

end OAI
