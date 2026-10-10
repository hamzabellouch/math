import Mathlib
import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def thermalEnergy {N : ℕ} (β : ℝ) (J : Disorder N) : ℝ :=
  ∑ s : Config N, gibbs β J s*hamiltonian J s

def equilibriumEnergy (β : ℝ) (N : ℕ) : ℝ :=
  (∫ J, thermalEnergy β J ∂disorderLaw N)/(N:ℝ)

theorem logPartition_hasDerivAt_temperature {N : ℕ} (β : ℝ) (J : Disorder N) :
    HasDerivAt (fun γ => logPartition γ J) (thermalEnergy β J) β := by
  have H : HasDerivAt (fun γ => partition γ J)
      (∑ s : Config N, Real.exp (β*hamiltonian J s)*hamiltonian J s) β := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun config _ =>
      (hasDerivAt_mul_const (hamiltonian J config) (x := β)).exp)
  have HL := H.log (partition_pos β J).ne'
  apply HL.congr_deriv
  unfold thermalEnergy gibbs
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem thermalEnergy_continuous {N : ℕ} (β : ℝ) : Continuous (thermalEnergy (N := N) β) :=
  continuous_finsetSum _ (fun s _ => (continuous_gibbs β s).mul (continuous_hamiltonian s))

theorem thermalEnergy_norm_le {N : ℕ} (β : ℝ) (J : Disorder N) :
    ‖thermalEnergy β J‖ ≤ ∑ s : Config N, |hamiltonian J s| := by
  unfold thermalEnergy
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (gibbs_pos β J s),Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (gibbs_le_one β J s)

theorem energyBound_integrable (N : ℕ) :
    Integrable (fun J : Disorder N => ∑ s : Config N, |hamiltonian J s|) (disorderLaw N) :=
  integrable_finsetSum _ (fun s _ => (hamiltonian_integrable s).norm)

theorem thermalEnergy_integrable {N : ℕ} (β : ℝ) :
    Integrable (thermalEnergy (N := N) β) (disorderLaw N) :=
  (energyBound_integrable N).mono' (thermalEnergy_continuous β).aestronglyMeasurable
    (Eventually.of_forall (thermalEnergy_norm_le β))

theorem quenchedPressure_hasDerivAt {N : ℕ} (hN : 0 < N) (β : ℝ) :
    HasDerivAt (fun γ => quenchedPressure γ N) (equilibriumEnergy β N) β := by
  have H := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun γ (J : Disorder N) => logPartition γ J)
    (F' := fun γ J => thermalEnergy γ J)
    (bound := fun J => ∑ s : Config N, |hamiltonian J s|)
    (by simp) (Eventually.of_forall (fun γ => (continuous_logPartition γ).aestronglyMeasurable))
    (logPartition_integrable hN β) (thermalEnergy_continuous β).aestronglyMeasurable
    (Eventually.of_forall (fun J γ _ => thermalEnergy_norm_le γ J))
    (energyBound_integrable N)
    (Eventually.of_forall (fun J γ _ => logPartition_hasDerivAt_temperature γ J))).2
  exact H.div_const (N:ℝ)

theorem logPartition_convex_temperature {N : ℕ} (J : Disorder N) :
    ConvexOn ℝ Set.univ (fun β => logPartition β J) := by
  let L : Config N → ℝ →L[ℝ] ℝ := fun s => (hamiltonian J s) • ContinuousLinearMap.id ℝ ℝ
  have he : (fun β => logPartition β J) = affineLogPartition (fun _ : Config N => 0) L := by
    funext β
    simp only [logPartition,partition,affineLogPartition,L,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul,zero_add,mul_comm]
  rw [he]
  exact affineLogPartition_convex _ _

theorem quenchedPressure_convex {N : ℕ} (hN : 0 < N) :
    ConvexOn ℝ Set.univ (fun β => quenchedPressure β N) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have H := integral_mono (logPartition_integrable hN (a*x+b*y))
    (((logPartition_integrable hN x).const_mul a).add ((logPartition_integrable hN y).const_mul b))
    (fun J => (logPartition_convex_temperature J).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)
  simp only [Pi.add_apply] at H
  rw [integral_add ((logPartition_integrable hN x).const_mul a) ((logPartition_integrable hN y).const_mul b),
    integral_const_mul,integral_const_mul] at H
  have H' := div_le_div_of_nonneg_right H (show (0:ℝ) ≤ N by positivity)
  simpa only [quenchedPressure,smul_eq_mul,add_div,mul_div_assoc] using H'

theorem equilibriumEnergy_le_secant {N : ℕ} (hN : 0 < N) {β γ : ℝ} (hβγ : β < γ) :
    equilibriumEnergy β N ≤ (quenchedPressure γ N-quenchedPressure β N)/(γ-β) := by
  have H := (quenchedPressure_convex hN).le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _)
    hβγ (quenchedPressure_hasDerivAt hN β)
  simpa only [slope_def_field] using H
end SK.Analytic

end
end

end

end OAI
