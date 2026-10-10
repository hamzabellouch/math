import OAI.NumberTheory.CubicMoment.Estimates.LowProfilePoissonDyadic
import OAI.NumberTheory.CubicMoment.Estimates.ProfilePoissonTail
import OAI.NumberTheory.CubicMoment.Estimates.LowPoissonTailScale

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_poisson_total_height_log_saving (hpnt : PrimaryPrimePNT) (k : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z : ℕ) (A T M u : ℝ),
      65536 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(3/4:ℝ) → 0 ≤ M → (1+Real.log Z)^Ct ≤ T →
      (Z:ℝ)^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      (∀ j, H j ⊆ frequencyDyad j) →
      dyadicHeightMean (fun t => ‖∑' j : ℕ, finitePoissonContribution S (H j) β (u+t) P.V A‖) T ≤
        (K*P.cost)*M^2*A^(2/3:ℝ)*(Z:ℝ)^(5/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨L₁,Ct,hL₁,hshort₀⟩ := low_poisson_dyadic_height_log_saving hpnt k hMV hC hHuxley

  obtain ⟨L₂,hL₂,htail₀⟩ := smallB_poisson_tail_power_unbounded
  obtain ⟨L₀,hL₀,henv₀⟩ := arbitrary_poisson_dyad_energy 3 (by norm_num)
  obtain ⟨D,hD,hlogtail⟩ := low_poisson_tail_log_scale k
  refine ⟨L₁*(3*(2:ℝ)^(1/3:ℝ))+36*L₂*D,Ct,by positivity,?_⟩
  intro P S H β Z A T M u hZ₄ hlarge hM hT hAlo hS hβ hH
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
  have hlog : 0 < 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hZ]
  have hTp : 0 < T := (pow_pos hlog _).trans_le hT
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
  have hpre := hshort S H (Finset.range n) β Z A T M u ((Z:ℝ)/2) hZ₄ hM hT hA hN
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩)
    hrange hβ (fun j hj => hprefix j (Finset.mem_range.mp hj)) hH
  have hpre' : dyadicHeightMean (fun v => ‖∑ j ∈ Finset.range n, F j v‖) T ≤
      (K₁*(3*(2:ℝ)^(1/3:ℝ)))*M^2*A^(2/3:ℝ)*(Z:ℝ)^(5/3:ℝ)/(1+Real.log Z)^k := by
    apply hpre.trans_eq
    calc
      _ = K₁*((A/((Z:ℝ)/2))*(Z:ℝ)^2*
          (A/(27*((Z:ℝ)/2)^2))^(-(1/3:ℝ)))*(M^2/(1+Real.log Z)^k) := by ring
      _ = _ := by rw [low_dyadic_poisson_scale hA hZp]; ring
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
  have henergy : (∑ b ∈ S, ‖β b‖^2) ≤ 18*(Z:ℝ)*M^2 := by
    have hcard := primary_support_card_le S hZp.le
      (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2.2⟩)
    calc
      _ ≤ ∑ _b ∈ S, M^2 := Finset.sum_le_sum (fun b hb =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ b hb) 2)
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  have hnorm : (Z:ℝ)^(-2:ℝ)*(Z:ℝ) = (Z:ℝ)^(-1:ℝ) := by
    nth_rw 2 [←Real.rpow_one (Z:ℝ)]
    rw [←Real.rpow_add hZp]
    norm_num
  have htailbound : 2*(K₂*(Z:ℝ)^(-2:ℝ)*∑ b ∈ S, ‖β b‖^2) ≤
      (36*K₂*D)*M^2*A^(2/3:ℝ)*(Z:ℝ)^(5/3:ℝ)/(1+Real.log Z)^k := by
    calc
      _ ≤ 2*(K₂*(Z:ℝ)^(-2:ℝ)*(18*(Z:ℝ)*M^2)) := by gcongr
      _ = (36*K₂*M^2)*(Z:ℝ)^(-1:ℝ) := by rw [←hnorm]; ring
      _ ≤ (36*K₂*M^2)*(D*A^(2/3:ℝ)*(Z:ℝ)^(5/3:ℝ)/(1+Real.log Z)^k) :=
        mul_le_mul_of_nonneg_left (hlogtail A (Z:ℝ) hA₁ hZ) (by positivity)
      _ = _ := by ring
  apply hm.trans
  exact (add_le_add hpre' htailbound).trans_eq (by dsimp [K₁,K₂]; ring)

end CubicFirstMoment.ProfileControl

end

end OAI
