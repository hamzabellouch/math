import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary

namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

def coordinateL2 (i : Fin 3) :
    Lp Space 2 (volume : Measure Space) →L[ℝ] Lp ℝ 2 (volume : Measure Space) :=
  ContinuousLinearMap.compLpL 2 volume (ContinuousLinearMap.proj i)

lemma coordinateL2_coe (i : Fin 3) (V : Lp Space 2 (volume : Measure Space)) :
    (coordinateL2 i V : Space → ℝ) =ᵐ[volume] fun x => (V : Space → Space) x i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma coordinateL2_hasDerivWithinAt
    {V W : ℝ → Lp Space 2 (volume : Measure Space)} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt V (W t) s t) (i : Fin 3) :
    HasDerivWithinAt (fun t => coordinateL2 i (V t)) (coordinateL2 i (W t)) s t :=
  (coordinateL2 i).hasFDerivAt.comp_hasDerivWithinAt t h

def l2Energy (V : Lp Space 2 (volume : Measure Space)) : ℝ :=
  ∑ i : Fin 3, ‖coordinateL2 i V‖ ^ 2

def l2EnergyRate (V W : Lp Space 2 (volume : Measure Space)) : ℝ :=
  2 * ∑ i : Fin 3, inner ℝ (coordinateL2 i V) (coordinateL2 i W)

lemma l2Energy_nonneg (V : Lp Space 2 (volume : Measure Space)) : 0 ≤ l2Energy V :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma l2Energy_continuous : Continuous l2Energy := by
  unfold l2Energy
  fun_prop

lemma l2Energy_hasDerivWithinAt
    {V W : ℝ → Lp Space 2 (volume : Measure Space)} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt V (W t) s t) :
    HasDerivWithinAt (fun t => l2Energy (V t)) (l2EnergyRate (V t) (W t)) s t := by
  simpa only [l2Energy, l2EnergyRate, Finset.mul_sum] using
    HasDerivWithinAt.fun_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) =>
      (coordinateL2_hasDerivWithinAt h i).norm_sq)

lemma l2Inner_integral {V W : Lp Space 2 (volume : Measure Space)}
    {v w : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v)
    (hw : (W : Space → Space) =ᵐ[volume] w) (i : Fin 3) :
    inner ℝ (coordinateL2 i V) (coordinateL2 i W) = ∫ x, v x i * w x i := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateL2_coe i V, coordinateL2_coe i W, hv, hw] with x hv' hw' hx hy
  simp only [hv', hw', hx, hy, RCLike.inner_apply, conj_trivial]
  ring

lemma l2Energy_integral {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) :
    l2Energy V = ∑ i : Fin 3, ∫ x, (v x i)^2 := by
  unfold l2Energy
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, l2Inner_integral hv hv]
  simp only [pow_two]

lemma l2Energy_eq_zero_of_bound
    {V W : ℝ → Lp Space 2 (volume : Measure Space)}
    (hV : ContinuousOn V (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt V (W t) (Ici 0) t)
    (hzero : V 0 = 0) {T K : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T, l2EnergyRate (V t) (W t) ≤ K * l2Energy (V t)) :
    l2Energy (V T) = 0 := by
  have hec : ContinuousOn (fun t => l2Energy (V t)) (Icc 0 T) :=
    l2Energy_continuous.comp_continuousOn (hV.mono (fun _ ht => ht.1))
  have he0 : l2Energy (V 0) ≤ 0 := by simp [hzero, l2Energy]
  have he' : ∀ x ∈ Ico (0 : ℝ) T, ∀ r : ℝ, l2EnergyRate (V x) (W x) < r →
      ∃ᶠ z in 𝓝[>] x, (z-x)⁻¹ * (l2Energy (V z) - l2Energy (V x)) < r := by
    intro x hx r hr
    have hh : HasDerivWithinAt (fun t => l2Energy (V t))
        (l2EnergyRate (V x) (W x)) (Ici x) x :=
      (l2Energy_hasDerivWithinAt (hderiv x hx.1)).mono (Ici_subset_Ici.mpr hx.1)
    simpa only [slope_def_field, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.liminf_right_slope_le hr
  have H := le_gronwallBound_of_liminf_deriv_right_le (K := K) (ε := 0) hec he' he0
    (fun t ht => by simpa only [add_zero] using hbound t ht) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at H
  exact le_antisymm H (l2Energy_nonneg _)

lemma l2Energy_zero_pointwise {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) (hc : Continuous v)
    (he : l2Energy V = 0) : v = 0 := by
  have hz (i : Fin 3) : coordinateL2 i V = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖coordinateL2 j V‖)).mp he i (Finset.mem_univ _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  ext x i
  have hae : (fun x => v x i) =ᵐ[volume] (0 : Space → ℝ) := by
    filter_upwards [coordinateL2_coe i V, hv, Lp.coeFn_zero ℝ 2 (volume : Measure Space)] with x h₁ h₂ h₃
    rw [hz, h₃, h₂] at h₁
    exact h₁.symm
  have hi := ((Continuous.ae_eq_iff_eq volume ((continuous_apply i).comp hc) continuous_const).mp hae)
  exact congrFun hi x

end BalancedTransport.Analysis
end

end OAI
