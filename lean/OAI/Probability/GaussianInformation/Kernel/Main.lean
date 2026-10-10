import Mathlib
import OAI.Probability.GaussianInformation.Kernel.LocalEnergy

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.FiniteMessage
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MassPotential NoisyDrift Bayes Coercivity
lemma component_le_sphere {d N : ℕ} (μ : Measure (Ambient d × Fin N))
    (hμ : μ.map Prod.fst=sphereProbability d) (v : Fin N) : component μ v ≤ sphereProbability d := by
  rw [← hμ]
  exact component_le μ v
lemma component_masses_sum {d N : ℕ} (μ : Measure (Ambient d × Fin N)) [IsFiniteMeasure μ]
    (hμ : μ.map Prod.fst=sphereProbability d) : ∑ v,(component μ v univ).toReal=1 := by
  have (v : Fin N) := component_finite μ v
  rw [← ENNReal.toReal_sum (f := fun v => component μ v univ) (fun v _ => measure_ne_top _ _)]
  rw [← Measure.finsetSum_apply,sum_components,hμ,measure_univ,ENNReal.toReal_one]
lemma averagePhi_energy {d N : ℕ} (μ : Measure (Ambient d × Fin N)) :
    averagePhi μ=∑ v,energy (component μ v) := rfl
lemma entropy_charge {d N : ℕ} (hd : 0 < d) (hN : 0 < N) (a : Fin N → ℝ)
    (ha : ∀ v,0 ≤ a v) (h1 : ∑ v,a v=1) :
    (∑ v,a v*(95*(d:ℝ)+6*Real.log (1/a v)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ))) ≤
      95*(d:ℝ)+6*Real.log (N:ℝ)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have he : (∑ v,a v*Real.log (1/a v))=∑ v,-a v*Real.log (a v) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [one_div,Real.log_inv]
    ring
  have hh := finite_entropy_bound hN a ha h1
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hb := mul_le_mul_of_nonneg_left hh (show 0 ≤ 6/(d:ℝ) by positivity)
  have hid : (∑ v,a v*(95*(d:ℝ)+6*Real.log (1/a v)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ))) =
      95*(d:ℝ)+(6/(d:ℝ))*(∑ v,a v*Real.log (1/a v))+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,h1,one_mul]
    congr 3
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hid,he]
  have he6 : 6/(d:ℝ)*Real.log (N:ℝ)=6*Real.log (N:ℝ)/(d:ℝ) := by ring
  rw [he6] at hb
  linarith
lemma actual_row_drift_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (μ : Measure (Ambient d × Fin N)) [IsProbabilityMeasure μ]
    (hμ : μ.map Prod.fst=sphereProbability d) (rule : BlockRule d N) :
    averagePhi (outgoingLaw μ rule) ≤ averagePhi μ+95*(d:ℝ)+6*Real.log (N:ℝ)/(d:ℝ)+
      2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have (v : Fin N) := component_finite μ v
  let ρ := fun v w => (component μ v).withDensity (fun s => ENNReal.ofReal ((localRule rule v).response w s))
  have hρf (v w) : IsFiniteMeasure (ρ v w) := density_finite _ _ (fun s => ((localRule rule v).response_bounds w s).2)
  have hρ (v w) : ρ v w ≤ sphereProbability d :=
    (density_le _ _ (fun s => ((localRule rule v).response_bounds w s).2)).trans (component_le_sphere μ hμ v)
  have hforget : averagePhi (outgoingLaw μ rule) ≤ ∑ w : Fin N,∑ v : Fin N,energy (ρ v w) := by
    rw [averagePhi_energy]
    apply Finset.sum_le_sum
    intro w _
    rw [component_outgoing,rowSlice_eq]
    exact energy_mixture hd (fun v => ρ v w) (fun v => hρf v w) (fun v => hρ v w)
  have hlocal := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    local_energy_bound hd hN (component μ v) (component_le_sphere μ hμ v) (localRule rule v))
  have hcharge := entropy_charge (d := d) (by omega) hN (fun v => (component μ v univ).toReal)
    (fun v => ENNReal.toReal_nonneg) (component_masses_sum μ hμ)
  rw [Finset.sum_comm] at hforget
  have hsum := hforget.trans hlocal
  rw [Finset.sum_add_distrib,← averagePhi_energy] at hsum
  linarith
end KernelPotential.FiniteMessage
namespace KernelPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
lemma numeric_drift_charge {d N : ℕ} (hd : 32 ≤ d) (hN : 1 ≤ N) (hlog : Real.log N ≤ (d:ℝ)^2) :
    95*(d:ℝ)+6*Real.log (N:ℝ)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) ≤ 135*(d:ℝ) := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hk : 0 < d/16 := by omega
  have hkR : (0:ℝ) < (d/16:ℕ) := by exact_mod_cast hk
  have hdk : d ≤ 32*(d/16) := by omega
  have hdkR : (d:ℝ) ≤ 32*(d/16:ℕ) := by exact_mod_cast hdk
  have h6 : 6*Real.log (N:ℝ)/(d:ℝ) ≤ 6*(d:ℝ) := (div_le_iff₀ hdR).mpr (by nlinarith)
  have h2 : 2*Real.log (N:ℝ)/(d:ℝ) ≤ 2*(d:ℝ) := (div_le_iff₀ hdR).mpr (by nlinarith)
  have h32 : Real.log (N:ℝ)/(d/16:ℕ) ≤ 32*(d:ℝ) := by
    calc
      Real.log (N:ℝ)/(d/16:ℕ) ≤ Real.log (N:ℝ)/((d:ℝ)/32) :=
        div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hN))
          (by positivity) ((div_le_iff₀ (by norm_num)).mpr (by simpa only [mul_comm] using hdkR))
      _ ≤ 32*(d:ℝ) := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  linarith

theorem actual_row_drift : DriftStatement := by
  refine ⟨135,by norm_num,32,?_⟩
  intro d hd N hN hlog μ hμp hμ rule
  have := hμp
  have hh := FiniteMessage.actual_row_drift_bound (by omega : 16 ≤ d) (by omega : 0 < N) μ hμ rule
  have hb := numeric_drift_charge hd hN hlog
  linarith
end KernelPotential

end OAI
