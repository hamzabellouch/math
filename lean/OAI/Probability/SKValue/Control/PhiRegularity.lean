import Mathlib
import OAI.Probability.SKValue.Evolution.SmoothApproxBounds
import OAI.Probability.SKValue.Equations.StripIntegralLimit

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma phi_bulk_jets (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t∈Icc (0 : ℝ) S, ∀ x,
      |iteratedDeriv k (deriv (phi W γ t)) x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS k
  refine ⟨C,hC,?_⟩
  intro t ht x
  exact le_of_tendsto (phi_jet_limit W γ hS ht k x).abs
    (Eventually.of_forall (fun n ↦ hb n t ht k le_rfl x))

lemma phi_bulk_temporal (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s∈Icc (0 : ℝ) S, ∀ t∈Icc (0 : ℝ) S, ∀ x,
      |iteratedDeriv k (deriv (phi W γ s)) x-iteratedDeriv k (deriv (phi W γ t)) x| ≤ L*|s-t| := by
  obtain ⟨L,hL,hb⟩ := smoothApprox_bulk_temporal γ hS k
  refine ⟨L,hL,?_⟩
  intro s hs t ht x
  exact le_of_tendsto ((phi_jet_limit W γ hS hs k x).sub (phi_jet_limit W γ hS ht k x)).abs
    (Eventually.of_forall (fun n ↦ hb n s hs t ht x))

lemma phi_smoothTerminal (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) : SmoothTerminal (phi W γ t) := by
  have hs := (phi_smooth_and_jet_limits W γ ht).2 t ⟨ht.1,le_rfl⟩
  refine ⟨phi_lipschitz W γ ⟨ht.1,ht.2.le⟩,hs,(contDiff_infty_iff_deriv.mp hs).2,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := phi_bulk_jets W γ ht k
  exact ⟨C,hC,hb t ⟨ht.1,le_rfl⟩⟩

lemma phi_time_jet_continuous (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (k : ℕ) (x : ℝ) :
    ContinuousOn (fun t ↦ iteratedDeriv k (phi W γ t) x) (Icc (0 : ℝ) S) := by
  have hh := ((phi_smooth_and_jet_limits W γ hS).1 k).comp
    (fun t : Icc (0 : ℝ) S ↦ (t,x))
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hh.continuous
  apply Eventually.frequently (Eventually.of_forall _)
  intro n
  have hc : ContinuousOn (fun t ↦ iteratedDeriv k (smoothApprox γ n t) x) (Icc (0 : ℝ) S) := by
    have hsub : Icc (0 : ℝ) S⊆Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hS.2.le
    cases k with
    | zero => simpa only [iteratedDeriv_zero] using ((smoothApprox_evolution γ n).continuous_value x).mono hsub
    | succ k => simpa only [iteratedDeriv_succ'] using ((smoothApprox_evolution γ n).continuous_jet k x).mono hsub
  exact continuousOn_iff_continuous_domRestrict.mp hc

lemma smoothApprox_time_jet_continuous (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (n k : ℕ) (x : ℝ) :
    ContinuousOn (fun t ↦ iteratedDeriv k (deriv (smoothApprox γ n t)) x) (Icc (0 : ℝ) S) :=
  ((smoothApprox_evolution γ n).continuous_jet k x).mono (Icc_subset_Icc le_rfl hS.2.le)

lemma OrderParameter.grid_bulk_bound (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (n : ℕ) {t : ℝ} (ht : t∈Icc (0 : ℝ) S) :
    |profileCoeff (γ.grid n) t| ≤ γ.coeff S := by
  rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
  exact (γ.grid_le n ⟨ht.1,ht.2.trans_lt hS.2⟩).trans
    (γ.monotone ⟨ht.1,ht.2.trans_lt hS.2⟩ hS ht.2)

lemma OrderParameter.grid_bulk_ae_tendsto (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) :
    ∀ᵐ t ∂volume, t∈Icc (0 : ℝ) S →
      Tendsto (fun n ↦ profileCoeff (γ.grid n) t) atTop (𝓝 (γ.coeff t)) := by
  filter_upwards [γ.grid_ae_tendsto,Measure.ae_ne volume (0 : ℝ)] with t hc hne ht
  have ht' : t∈Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 hne.symm,ht.2.trans hS.2.le⟩
  simpa only [OrderParameter.cutoff,indicator_of_mem (show t∈Ico (0 : ℝ) 1 from ⟨ht.1,ht.2.trans_lt hS.2⟩)] using hc ht'

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma phi_value_pde (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) {t s : ℝ} (ht : t∈Icc (0 : ℝ) S) (hs : s∈Icc (0 : ℝ) S) (x : ℝ) :
    phi W γ s x-phi W γ t x = -(∫ r in t..s,
      (1/2 : ℝ)*deriv (deriv (phi W γ r)) x+
        γ.coeff r*((1/2 : ℝ)*(deriv (phi W γ r) x)^2)) := by
  obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS 1
  have hD := strip_integral_limit (c := fun n ↦ profileCoeff (γ.grid n)) (γ := γ.coeff)
    (f := fun n r ↦ (1/2 : ℝ)*iteratedDeriv 1 (deriv (smoothApprox γ n r)) x)
    (g := fun n r ↦ (1/2 : ℝ)*(iteratedDeriv 0 (deriv (smoothApprox γ n r)) x)^2)
    (F := fun r ↦ (1/2 : ℝ)*iteratedDeriv 1 (deriv (phi W γ r)) x)
    (G := fun r ↦ (1/2 : ℝ)*(iteratedDeriv 0 (deriv (phi W γ r)) x)^2)
    (Γ := γ.coeff S) (A := C/2) (B := C^2/2) ht hs
    (fun n ↦ profileCoeff_measurable _) (fun n ↦ continuousOn_const.mul (smoothApprox_time_jet_continuous γ hS n 1 x))
    (fun n ↦ continuousOn_const.mul ((smoothApprox_time_jet_continuous γ hS n 0 x).pow 2))
    (fun n r hr ↦ γ.grid_bulk_bound hS n hr)
    (fun n r hr ↦ by
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith [hb n r hr 1 le_rfl x])
    (fun n r hr ↦ by
      rw [abs_mul,abs_pow,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      have hh := hb n r hr 0 (by omega) x
      nlinarith [abs_nonneg (iteratedDeriv 0 (deriv (smoothApprox γ n r)) x)])
    (γ.nonneg _ hS) (γ.grid_bulk_ae_tendsto hS)
    (fun r hr ↦ (phi_jet_limit W γ hS hr 1 x).const_mul (1/2 : ℝ))
    (fun r hr ↦ ((phi_jet_limit W γ hS hr 0 x).pow 2).const_mul (1/2 : ℝ))
  simp only [iteratedDeriv_one,iteratedDeriv_zero] at hD
  have hvs := (smoothApprox_tendsto W γ).tendsto_at (⟨s,⟨hs.1,hs.2.trans_lt hS.2⟩⟩,x)
  have hvt := (smoothApprox_tendsto W γ).tendsto_at (⟨t,⟨ht.1,ht.2.trans_lt hS.2⟩⟩,x)
  have he (n : ℕ) := (smoothApprox_evolution γ n).value_pde t ⟨ht.1,ht.2.trans hS.2.le⟩ s ⟨hs.1,hs.2.trans hS.2.le⟩ x
  exact tendsto_nhds_unique (hvs.sub hvt) (hD.neg.congr (fun n ↦ (he n).symm))

lemma phi_gradient_pde (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) {t s : ℝ} (ht : t∈Icc (0 : ℝ) S) (hs : s∈Icc (0 : ℝ) S) (x : ℝ) :
    deriv (phi W γ s) x-deriv (phi W γ t) x = -(∫ r in t..s,
      (1/2 : ℝ)*deriv (deriv (deriv (phi W γ r))) x+
        γ.coeff r*(deriv (phi W γ r) x*deriv (deriv (phi W γ r)) x)) := by
  obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS 2
  have hD := strip_integral_limit (c := fun n ↦ profileCoeff (γ.grid n)) (γ := γ.coeff)
    (f := fun n r ↦ (1/2 : ℝ)*iteratedDeriv 2 (deriv (smoothApprox γ n r)) x)
    (g := fun n r ↦ iteratedDeriv 0 (deriv (smoothApprox γ n r)) x*iteratedDeriv 1 (deriv (smoothApprox γ n r)) x)
    (F := fun r ↦ (1/2 : ℝ)*iteratedDeriv 2 (deriv (phi W γ r)) x)
    (G := fun r ↦ iteratedDeriv 0 (deriv (phi W γ r)) x*iteratedDeriv 1 (deriv (phi W γ r)) x)
    (Γ := γ.coeff S) (A := C/2) (B := C^2) ht hs
    (fun n ↦ profileCoeff_measurable _) (fun n ↦ continuousOn_const.mul (smoothApprox_time_jet_continuous γ hS n 2 x))
    (fun n ↦ (smoothApprox_time_jet_continuous γ hS n 0 x).mul (smoothApprox_time_jet_continuous γ hS n 1 x))
    (fun n r hr ↦ γ.grid_bulk_bound hS n hr)
    (fun n r hr ↦ by
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith [hb n r hr 2 le_rfl x])
    (fun n r hr ↦ by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hb n r hr 0 (by omega) x) (hb n r hr 1 (by omega) x) (abs_nonneg _) hC)
    (γ.nonneg _ hS) (γ.grid_bulk_ae_tendsto hS)
    (fun r hr ↦ (phi_jet_limit W γ hS hr 2 x).const_mul (1/2 : ℝ))
    (fun r hr ↦ (phi_jet_limit W γ hS hr 0 x).mul (phi_jet_limit W γ hS hr 1 x))
  simp only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hD
  have hvs := phi_jet_limit W γ hS hs 0 x
  have hvt := phi_jet_limit W γ hS ht 0 x
  simp only [iteratedDeriv_zero] at hvs hvt
  have he (n : ℕ) := (smoothApprox_evolution γ n).gradient_pde t ⟨ht.1,ht.2.trans hS.2.le⟩ s ⟨hs.1,hs.2.trans hS.2.le⟩ x
  exact tendsto_nhds_unique (hvs.sub hvt) (hD.neg.congr (fun n ↦ (he n).symm))

lemma phi_evolution (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) : SmoothEvolution S γ.coeff (phi W γ) := by
  refine ⟨fun t ht ↦ phi_smoothTerminal W γ ⟨ht.1,ht.2.trans_lt hS.2⟩,?_,?_,
    phi_bulk_jets W γ hS,phi_bulk_temporal W γ hS,?_,?_⟩
  · intro x
    simpa only [iteratedDeriv_zero] using phi_time_jet_continuous W γ hS 0 x
  · intro n x
    simpa only [iteratedDeriv_succ'] using phi_time_jet_continuous W γ hS (n+1) x
  · exact fun t ht s hs x ↦ phi_value_pde W γ hS ht hs x
  · exact fun t ht s hs x ↦ phi_gradient_pde W γ hS ht hs x

end SKValue

end

end OAI
