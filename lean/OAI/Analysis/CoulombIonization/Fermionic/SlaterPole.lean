import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombNear
import OAI.Analysis.CoulombIonization.Fermionic.SlaterRepulsion

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma orbital_pole_integrable {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) (a : Space) :
    Integrable (fun z => ‖φ z‖^2 / ‖a-z.2‖) slaterParticleMeasure := by
  have hm : Measurable (fun z : SlaterParticle => ‖φ z‖^2 / ‖a-z.2‖) :=
    (((continuous_prod_of_discrete_left.mpr (fun s => (hφ s).continuous)).measurable.norm).pow_const 2).div
      ((measurable_const.sub measurable_snd).norm)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun s => ?_),Integrable.of_finite⟩
  have hs : HasCompactSupport (fun x : Space => ‖φ (s,x)‖^2) := compact_norm_sq (hc s)
  have hd : Continuous (fun x : Space => ‖φ (s,x)‖^2) := (hφ s).continuous.norm.pow 2
  exact CoulombAnalysis.tfPotential_integrable (hd.integrable_of_hasCompactSupport hs)
    (hd.memLp_of_hasCompactSupport hs) a

lemma slater_pole_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (a : Space) (j : Fin n) :
    Integrable (fun z : Fin n → SlaterParticle => ‖slater φ z‖^2 / ‖a-(z j).2‖)
      (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (i : Fin n) : Integrable (fun z => ‖a-z.2‖⁻¹*‖φ i z‖^2) slaterParticleMeasure := by
    simpa only [div_eq_mul_inv,mul_comm] using orbital_pole_integrable (hφ i) (hc i) a
  have hv (i : Fin n) : MemLp (fun z : SlaterParticle =>
      (Real.sqrt (‖a-z.2‖⁻¹) : ℂ)*φ i z) 2 slaterParticleMeasure := memLp_potential_mul
    (continuous_prod_of_discrete_left.mpr (fun s => (hφ i s).continuous)).measurable
    (measurable_const.sub measurable_snd).norm.inv
    (fun z : SlaterParticle => inv_nonneg.mpr (norm_nonneg (a-z.2))) (hi i)
  have ht := (memLp_slaterCoordinate hl hv j).norm.integrable_sq
  simp only [slaterCoordinate_mul] at ht
  simpa only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (inv_nonneg.mpr (norm_nonneg _)),
    div_eq_mul_inv,mul_comm] using ht

lemma slaterForm_pole_trace {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (a : Space) :
    (∑ s : Spins n, ∑ j : Fin n, ∫ x : Configuration n,
      ‖(slaterForm φ).value s x‖^2 / ‖a-x j‖) =
      ∑ i : Fin n, ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖a-z.2‖ ∂slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (i : Fin n) : Integrable (fun z => ‖a-z.2‖⁻¹*‖φ i z‖^2) slaterParticleMeasure := by
    simpa only [div_eq_mul_inv,mul_comm] using orbital_pole_integrable (hφ i) (hc i) a
  have hv (i : Fin n) : MemLp (fun z : SlaterParticle =>
      (Real.sqrt (‖a-z.2‖⁻¹) : ℂ)*φ i z) 2 slaterParticleMeasure := memLp_potential_mul
    (continuous_prod_of_discrete_left.mpr (fun s => (hφ i s).continuous)).measurable
    (measurable_const.sub measurable_snd).norm.inv
    (fun z : SlaterParticle => inv_nonneg.mpr (norm_nonneg (a-z.2))) (hi i)
  have ht := slater_nonnegative_potential hl ho (fun z : SlaterParticle => ‖a-z.2‖⁻¹)
    (fun z => inv_nonneg.mpr (norm_nonneg _)) hv
  have his (j : Fin n) := slater_pole_integrable hφ hc a j
  have he : (∫ z : Fin n → SlaterParticle, (∑ j, ‖a-(z j).2‖⁻¹)*‖slater φ z‖^2
      ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure)) =
      ∑ s : Spins n, ∑ j : Fin n, ∫ x : Configuration n,
        ‖(slaterForm φ).value s x‖^2 / ‖a-x j‖ := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => by
      simpa only [div_eq_mul_inv,mul_comm] using his j), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∫ z : Fin n → SlaterParticle, ‖slater φ z‖^2 / ‖a-(z j).2‖
          ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [div_eq_mul_inv,mul_comm]
      _ = _ := spinSpace_integral _ (his j)
  rw [he] at ht
  simpa only [div_eq_mul_inv,mul_comm] using ht

end CoulombAtom

end

end OAI
