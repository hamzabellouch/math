import OAI.Analysis.MarkovType.FiniteBoundedEnergy
import OAI.Analysis.MarkovType.FinitePredictableTransform

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteUpperL2_bounded_energy_scale {a r χ s : ℝ}
    (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ) (hs : 0 < s)
    (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖))
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ s ^ a) :
    finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N, d n ω) ≤
      boundedEnergyConstant a r χ * s := by
  let e : ℕ → Ω → E := fun n ω => s⁻¹ • d n ω
  have hscale (n : ℕ) (ω : Ω) : ‖e n ω‖ ^ a = (s⁻¹) ^ a * ‖d n ω‖ ^ a := by
    dsimp only [e]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
      Real.mul_rpow (inv_nonneg.mpr hs.le) (norm_nonneg _)]
  have headapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (e n) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    rw [hadapt n hn hnN hωη]
  have hezero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (e n) := by
    intro n hn hnN
    exact (hzero n hn hnN).predictable_smul (fun _ => s⁻¹) (fun _ => rfl)
  have hepred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖e n ω‖) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [norm_smul, norm_smul, hnorm]
  have heenergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖e n ω‖ ^ a) ≤ 1 := by
    intro ω
    simp_rw [hscale]
    rw [← Finset.mul_sum]
    calc
      _ ≤ (s⁻¹) ^ a * s ^ a :=
        mul_le_mul_of_nonneg_left (henergy ω) (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _)
      _ = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hs.le) hs.le, inv_mul_cancel₀ hs.ne']
        exact Real.one_rpow a
  have h := finiteUpperL2_bounded_energy ha har hχ hUpper μ F e N headapt hezero hepred heenergy
  have hsum : (fun ω => ∑ n ∈ Finset.Icc 1 N, e n ω) =
      fun ω => s⁻¹ • ∑ n ∈ Finset.Icc 1 N, d n ω := by
    funext ω
    simp only [e, Finset.smul_sum]
  rw [hsum, finiteL2Norm_smul, abs_of_pos (inv_pos.mpr hs)] at h
  have hmul := mul_le_mul_of_nonneg_left h hs.le
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hmul
  simpa only [mul_comm] using hmul

theorem finiteUpperL2_budget_L2 {a r χ s : ℝ}
    (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ) (hs : 0 < s)
    (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖)) :
    finiteL2Norm μ
      (partialSumProcess (fun n ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) (s ^ a) n ω • d n ω) N) ≤
      boundedEnergyConstant a r χ * s := by
  let w : ℕ → Ω → ℝ := fun n ω => ‖d n ω‖ ^ a
  let c : ℕ → Ω → ℝ := budgetCoefficient w (s ^ a)
  let e : ℕ → Ω → E := fun n ω => c n ω • d n ω
  have hw : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (w n) := by
    intro n hn hnN ω η hωη
    dsimp only [w]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [hnorm]
  have hc : ∀ n, n ≤ N → F.AdaptedAt (n - 1) (c n) :=
    fun n hnN => budgetCoefficient_predictable F w N (s ^ a) hw hnN
  have headapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (e n) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    rw [hc n hnN (F.refines (Nat.sub_le n 1) hωη), hadapt n hn hnN hωη]
  have hezero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (e n) := by
    intro n hn hnN
    exact (hzero n hn hnN).predictable_smul (c n) (hc n hnN)
  have hepred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖e n ω‖) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [norm_smul, norm_smul, hc n hnN hωη, hnorm]
  have heenergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖e n ω‖ ^ a) ≤ s ^ a := by
    intro ω
    rw [sum_Icc_one_eq_sum_range_succ]
    exact budgetTransform_energy_le d ha (Real.rpow_nonneg hs.le _) N ω
  have h := finiteUpperL2_bounded_energy_scale ha har hχ hs hUpper μ F e N
    headapt hezero hepred heenergy
  have hsum : (fun ω => ∑ n ∈ Finset.Icc 1 N, e n ω) = partialSumProcess e N := by
    funext ω
    unfold partialSumProcess
    exact sum_Icc_one_eq_sum_range_succ (fun n => e n ω) N
  rw [hsum] at h
  exact h

end MarkovSuperreflexivity

end

end OAI
