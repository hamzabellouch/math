import OAI.NumberTheory.CubicMoment.Estimates.ProfilePoissonDyadic
import OAI.NumberTheory.CubicMoment.Estimates.ProfilePoissonTail
import OAI.NumberTheory.CubicMoment.Estimates.SmallBPoissonScale

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem smallB_poisson_total_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z : ℕ) (A T u : ℝ),
      4 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(3/4:ℝ) → (Z:ℝ)^(1/50:ℝ) ≤ T →
      (Z:ℝ)^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      (∀ j, H j ⊆ frequencyDyad j) →
      dyadicHeightMean (fun t => ‖∑' j : ℕ, finitePoissonContribution S (H j) β (u+t) P.V A‖) T ≤
        (K*P.cost)*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨L₁,hL₁,hshort₀⟩ := smallB_poisson_dyadic_height_power hMV hC hHuxley

  obtain ⟨L₂,hL₂,htail₀⟩ := smallB_poisson_tail_power_unbounded
  obtain ⟨L₀,hL₀,henv₀⟩ := arbitrary_poisson_dyad_energy 3 (by norm_num)
  refine ⟨L₁*(3*(2:ℝ)^(1/3:ℝ))+2*L₂,by positivity,?_⟩
  intro P S H β Z A T u hZ₄ hlarge hT hAlo hS hH
  let K₁ := L₁*P.cost
  let K₂ := L₂*P.cost
  let K₀ := L₀*P.cost
  have hK₁ : 0 < K₁ := mul_pos hL₁ P.cost_pos
  have hK₂ : 0 < K₂ := mul_pos hL₂ P.cost_pos
  have hK₀ : 0 < K₀ := mul_pos hL₀ P.cost_pos
  have hshort := hshort₀ P
  have htail := htail₀ P
  have henv := henv₀ P
  have hZ : 1 ≤ (Z:ℝ) := by linarith
  have hZp : 0 < (Z:ℝ) := by linarith
  have hN : 0 < (Z:ℝ)/2 := by positivity
  have hN₁ : 1 ≤ (Z:ℝ)/2 := by linarith
  have hNZ : (Z:ℝ)/2 ≤ (Z:ℝ) := by linarith
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  have hA₁ : 1 ≤ A := (Real.one_le_rpow hZ (by norm_num)).trans hAlo
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hp : ∀ b ∈ S, primary b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ) :=
    fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩
  have hrange : ∀ b ∈ S, norm b/((Z:ℝ)/2) ∈ Set.Icc (1:ℝ) 2 := by
    intro b hb
    exact ⟨(le_div_iff₀ hN).mpr (by simpa using (hp b hb).2.1),
      (div_le_iff₀ hN).mpr (by nlinarith [(hp b hb).2.2])⟩
  obtain ⟨n,hn,hprefix⟩ := smallB_poisson_cutoff hZp hlarge
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) P.V A
  let t := A/(27*(Z:ℝ)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have htotal : Continuous (fun v => ∑' j : ℕ, F j v) :=
    continuous_poisson_series S H β P.V A u
      (C := K₀*(A/((Z:ℝ)/2))*(Z:ℝ)*∑ b ∈ S, ‖β b‖^2) ht (fun j v => by
        convert henv S (H j) β A ((Z:ℝ)/2) (Z:ℝ) (u+v) j hA hN hNZ hp (hH j) using 1
        dsimp [t]
        ring)
  have hpre := hshort S H (Finset.range n) β Z A T u ((Z:ℝ)/2) hZ hT hA hN
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩)
    hrange (fun j hj => hprefix j (Finset.mem_range.mp hj)) hH
  have hpre' : dyadicHeightMean (fun v => ‖∑ j ∈ Finset.range n, F j v‖) T ≤
      (K₁*(3*(2:ℝ)^(1/3:ℝ)))*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply hpre.trans_eq
    calc
      _ = K₁*((A/((Z:ℝ)/2))*(Z:ℝ)^(1-1/40000:ℝ)*
          (A/(27*((Z:ℝ)/2)^2))^(-(1/3:ℝ)))*(∑ b ∈ S, ‖β b‖^2) := by ring
      _ = _ := by rw [smallB_dyadic_poisson_scale hA hZp]; ring
  have hpoint (v : ℝ) : ‖∑' j : ℕ, F j v‖ ≤
      ‖∑ j ∈ Finset.range n, F j v‖+K₂*(Z:ℝ)^(-2:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    obtain ⟨hfs,hft⟩ := htail S H β A ((Z:ℝ)/2) (Z:ℝ) (u+v) n hN₁ hNZ hAlo hn hp hH
    exact norm_tsum_prefix_tail n hfs le_rfl hft
  have hfc (j : ℕ) : Continuous (F j) :=
    (finitePoissonContribution_continuous_height S (H j) β P.V A).comp
      (show Continuous (fun v : ℝ => u+v) from continuous_const.add continuous_id)
  have hsumc : Continuous (fun v => ∑ j ∈ Finset.range n, F j v) :=
    continuous_finsetSum (Finset.range n) (fun j _ => hfc j)
  have hm := dyadicHeightMean_mono htotal.norm (hsumc.norm.add continuous_const) hTp
    (fun v _ => hpoint v)
  change dyadicHeightMean _ T ≤ dyadicHeightMean (fun v =>
    ‖∑ j ∈ Finset.range n, F j v‖+K₂*(Z:ℝ)^(-2:ℝ)*∑ b ∈ S, ‖β b‖^2) T at hm
  rw [dyadicHeightMean_add hsumc.norm continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  have hdecay : (Z:ℝ)^(-2:ℝ) ≤ A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ) := by
    apply (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : (-2:ℝ) ≤ 2/3-1/40000)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hZp.le _)
      (Real.one_le_rpow hA₁ (by norm_num))
  apply hm.trans
  calc
    _ ≤ (K₁*(3*(2:ℝ)^(1/3:ℝ)))*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2+
        2*(K₂*(A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ))*∑ b ∈ S, ‖β b‖^2) := by
      exact add_le_add hpre' (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hK₂.le)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num))
    _ = _ := by dsimp [K₁,K₂]; ring

end CubicFirstMoment.ProfileControl

end

end OAI
