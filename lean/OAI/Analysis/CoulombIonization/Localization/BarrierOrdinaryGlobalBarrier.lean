import Mathlib
import OAI.Analysis.CoulombIonization.Localization.OrdinaryDensity
import OAI.Analysis.CoulombIonization.Variational.AllSectorEnergy

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma formRawLaw_lintegral_eq_spin_sum {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {w : Configuration N → ℝ} (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x) ∂formRawLaw ψ) =
      ∑ s : Spins N, ∫⁻ x, ENNReal.ofReal (w x)*ENNReal.ofReal (‖ψ.value s x‖^2) := by
  have hm (s : Spins N) : AEMeasurable (fun x : Configuration N => ENNReal.ofReal (‖ψ.value s x‖^2)) volume :=
    ((hψ.1 s).norm.integrable_sq).aemeasurable.ennreal_ofReal
  rw [formRawLaw,lintegral_withDensity_eq_lintegral_mul₀
    (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal hw.ennreal_ofReal.aemeasurable]
  simp only [Pi.mul_apply,formRawDensity,ENNReal.ofReal_sum_of_nonneg (fun s _ => sq_nonneg _),Finset.sum_mul]
  rw [lintegral_finsetSum' (f := fun s x => ENNReal.ofReal (‖ψ.value s x‖^2)*ENNReal.ofReal (w x)) Finset.univ (fun s _ =>
    ((hm s).mul hw.ennreal_ofReal.aemeasurable))]
  exact Finset.sum_congr rfl (fun s _ => lintegral_congr (fun x => mul_comm _ _))

lemma rawOneParticleLaw_weighted_lintegral {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {w : Space → ℝ} (hw : Measurable w) :
    (∫⁻ z, ENNReal.ofReal (w z) ∂rawOneParticleLaw (formRawLaw ψ)) =
      ∑ i : Fin N, ∑ s : Spins N, ∫⁻ x,
        ENNReal.ofReal (w (x i))*ENNReal.ofReal (‖ψ.value s x‖^2) := by
  rw [rawOneParticleLaw,Measure.sum_fintype,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_map hw.ennreal_ofReal (measurable_pi_apply i)]
  exact formRawLaw_lintegral_eq_spin_sum hψ (hw.comp (measurable_pi_apply i))

namespace Pauli
open CoulombLT

theorem oneParticleDensity_measure {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevVector ψ) :
    volume.withDensity (oneParticleDensity ψ hψ.1) =
      rawOneParticleLaw (formRawLaw ψ) := by
  apply Measure.ext
  intro A hA
  let w : Space → ℝ := A.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hA
  have he := density_weighted_lintegral (toMany ψ hψ.1) w hw
  have hr := rawOneParticleLaw_weighted_lintegral hψ hw
  have hs : (∑ i : Fin (N+1), ∫⁻ q,
      ENNReal.ofReal (w (q i).1)*ENNReal.ofReal (‖toMany ψ hψ.1 q‖^2)
        ∂CoulombPauli.configMeasure (N+1) oneMeasure) =
      ∑ i : Fin (N+1), ∑ s : Spins (N+1), ∫⁻ x,
        ENNReal.ofReal (w (x i))*ENNReal.ofReal (‖ψ.value s x‖^2) :=
    Finset.sum_congr rfl (fun i _ => toMany_coordinate_lintegral ψ hψ.1 i w hw)
  have hwl : (fun x => ENNReal.ofReal (w x)*oneParticleDensity ψ hψ.1 x) =
      A.indicator (oneParticleDensity ψ hψ.1) := by
    funext x
    by_cases hx : x ∈ A <;> simp [w,hx]
  have hwr : (fun x => ENNReal.ofReal (w x)) = A.indicator (fun _ => (1:ENNReal)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [w,hx]
  change (∫⁻ x, ENNReal.ofReal (w x)*oneParticleDensity ψ hψ.1 x) = _ at he
  rw [hwl,lintegral_indicator hA] at he
  rw [hwr,lintegral_indicator hA,lintegral_const,one_mul,Measure.restrict_apply_univ] at hr
  rw [withDensity_apply _ hA]
  exact he.trans (hs.trans hr.symm)

theorem ordinaryDensity_eq_density {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevVector ψ) : ordinaryDensity ψ =ᵐ[volume] density ψ hψ.1 := by
  have he := Measure.rnDeriv_withDensity₀ volume
    (fermionDensity_aemeasurable (toMany ψ hψ.1))
  rw [show volume.withDensity (fermionDensity (toMany ψ hψ.1)) =
    rawOneParticleLaw (formRawLaw ψ) from oneParticleDensity_measure hψ] at he
  exact he.mono (fun x hx => congrArg ENNReal.toReal hx)

theorem ordinaryDensity_eq_spatialDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) : ordinaryDensity ψ =ᵐ[volume] spatialDensity ψ hψ.1 := by
  cases N with
  | zero =>
    filter_upwards [Measure.rnDeriv_zero (volume : Measure Space)] with x hx
    simpa [ordinaryDensity,rawOneParticleLaw,Measure.sum_fintype,spatialDensity] using congrArg ENNReal.toReal hx
  | succ N => exact ordinaryDensity_eq_density hψ

end Pauli

theorem ordinaryDensity_memLp {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    MemLp (ordinaryDensity ψ) (5/3) := by
  have hae := Pauli.ordinaryDensity_eq_spatialDensity hψ.sobolevFermion.sobolevVector
  have hi : Integrable (fun x => (ordinaryDensity ψ x)^(5/3:ℝ)) := by
    apply Integrable.congr (f := fun x => (Pauli.spatialDensity ψ hψ.1 x)^(5/3:ℝ))
    · cases N with
      | zero => simp [Pauli.spatialDensity,Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
      | succ N => exact Pauli.density_power_integrable ψ hψ
    · exact hae.symm.mono (fun x hx => congrArg (fun a : ℝ => a^(5/3:ℝ)) hx)
  apply (integrable_norm_rpow_iff (ordinaryDensity_measurable ψ).aestronglyMeasurable
    (by norm_num : (5/3:ENNReal) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,
    Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hi

theorem ordinaryDensity_global_unshifted {N : ℕ} {Z δ : ℝ}
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
    (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (he : formEnergy Z ψ ≤ allSectorEnergy Z+δ) :
    (∫ x, (ordinaryDensity ψ x)^(5/3:ℝ)) ≤
      Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ) := by
  have hae := Pauli.ordinaryDensity_eq_spatialDensity hψ.sobolevFermion.sobolevVector
  calc
    _ = ∫ x, (Pauli.spatialDensity ψ hψ.1 x)^(5/3:ℝ) :=
      integral_congr_ae (hae.mono (fun x hx => congrArg (fun a : ℝ => a^(5/3:ℝ)) hx))
    _ ≤ _ := Pauli.global_density_unshifted hZ hδ hN ψ hψ he

end CoulombAtom

end

end OAI
