import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.IntegrableIntegralAeTendsto

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma add_power_five_thirds_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^(5/3:ℝ) ≤ 4*(a^(5/3:ℝ)+b^(5/3:ℝ)) := by
  have h2 : (2:ℝ)^(5/3:ℝ) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have h (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
      (a+b)^(5/3:ℝ) ≤ 4*(a^(5/3:ℝ)+b^(5/3:ℝ)) := by
    calc
      _ ≤ (2*b)^(5/3:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2:ℝ)^(5/3:ℝ)*b^(5/3:ℝ) := Real.mul_rpow (by norm_num) hb
      _ ≤ 4*b^(5/3:ℝ) := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hb _)
      _ ≤ _ := by nlinarith [Real.rpow_nonneg ha (5/3:ℝ)]
  rcases le_total a b with hab | hba
  · exact h a b ha hb hab
  · simpa only [add_comm] using h b a hb ha hba

noncomputable def flatOneBodyDensity {n : ℕ} (ψ : H1Vector (n+1)) (x : Fin 3 → ℝ) : ℝ :=
  ∑ s : Fin 2, firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x)

noncomputable def oneBodyDensity {n : ℕ} (ψ : H1Vector (n+1)) (x : Space) : ℝ :=
  flatOneBodyDensity ψ (WithLp.ofLp x)

lemma flatOneBodyDensity_nonneg {n : ℕ} (ψ : H1Vector (n+1)) (x : Fin 3 → ℝ) :
    0 ≤ flatOneBodyDensity ψ x :=
  Finset.sum_nonneg (fun _ _ => firstParticleDensity_nonneg _ _)

lemma flatOneBodyDensity_integrable {n : ℕ} (ψ : H1Vector (n+1)) :
    Integrable (flatOneBodyDensity ψ) volume := by
  have hs := (firstParticleDensity_integrable ψ.cubeState_full_memLp).prod_right_ae
  rw [Measure.ae_count_iff] at hs
  exact integrable_finsetSum _ (fun s _ => hs s)

lemma flatOneBodyDensity_mass {n : ℕ} (ψ : H1Vector (n+1)) :
    (∫ x, flatOneBodyDensity ψ x) = ((n+1:ℕ):ℝ)*mass ψ := by
  have hi := firstParticleDensity_integrable ψ.cubeState_full_memLp
  calc
    _ = ∑ s : Fin 2, ∫ x, firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x) := by
      unfold flatOneBodyDensity
      apply integral_finsetSum
      have hs := hi.prod_right_ae
      rw [Measure.ae_count_iff] at hs
      exact fun s _ => hs s
    _ = ∫ sx, firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) sx
        ∂spinSpaceMeasure := by
      symm
      exact (integral_prod _ hi).trans (integral_count _)
    _ = _ := by rw [firstParticleDensity_integral ψ.cubeState_full_memLp, cubeState_full_mass]

lemma flatOneBodyDensity_power_bound {n : ℕ} (ψ : H1Vector (n+1))
    (hψ : Antisymmetric ψ) (hm : mass ψ ≤ 1) :
    Integrable (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ)) volume ∧
    (∫ x, (flatOneBodyDensity ψ x)^(5/3:ℝ)) ≤ (32768/(3*Real.pi^2))*kinetic ψ := by
  obtain ⟨hi,hb⟩ := global_spin_density_power_bound ψ hψ hm
  have hs := hi.prod_right_ae
  rw [Measure.ae_count_iff] at hs
  let B (x : Fin 3 → ℝ) := 4*∑ s : Fin 2,
    (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x))^(5/3:ℝ)
  have hB : Integrable B volume := (integrable_finsetSum _ (fun s _ => hs s)).const_mul _
  have hle (x) : (flatOneBodyDensity ψ x)^(5/3:ℝ) ≤ B x := by
    simpa only [B, flatOneBodyDensity, Fin.sum_univ_two] using add_power_five_thirds_le
      (firstParticleDensity_nonneg (cubeState ψ) (0,x))
      (firstParticleDensity_nonneg (cubeState ψ) (1,x))
  have hd : AEStronglyMeasurable (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ)) volume :=
    ((flatOneBodyDensity_integrable ψ).aemeasurable.pow_const _).aestronglyMeasurable
  have hI : Integrable (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ)) volume :=
    hB.mono' hd (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (flatOneBodyDensity_nonneg ψ x) _)]
      exact hle x))
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x, B x := integral_mono hI hB hle
    _ = 4*∑ s : Fin 2, ∫ x,
        (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x))^(5/3:ℝ) := by
      simp only [B, integral_const_mul]
      rw [integral_finsetSum _ (fun s _ => hs s)]
    _ = 4*∫ sx, (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) sx)^(5/3:ℝ)
        ∂spinSpaceMeasure := by
      congr 1
      exact ((integral_prod _ hi).trans (integral_count _)).symm
    _ ≤ 4*((8192/(3*Real.pi^2))*kinetic ψ) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

lemma oneBodyDensity_integrable {n : ℕ} (ψ : H1Vector (n+1)) :
    Integrable (oneBodyDensity ψ) volume :=
  (PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable
    (flatOneBodyDensity_integrable ψ)

lemma oneBodyDensity_mass {n : ℕ} (ψ : H1Vector (n+1)) :
    (∫ x, oneBodyDensity ψ x) = ((n+1:ℕ):ℝ)*mass ψ := by
  change (∫ x : Space, flatOneBodyDensity ψ ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x)) = _
  rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp']
  exact flatOneBodyDensity_mass ψ

lemma oneBodyDensity_power_bound {n : ℕ} (ψ : H1Vector (n+1))
    (hψ : Antisymmetric ψ) (hm : mass ψ ≤ 1) :
    Integrable (fun x => (oneBodyDensity ψ x)^(5/3:ℝ)) volume ∧
    (∫ x, (oneBodyDensity ψ x)^(5/3:ℝ)) ≤ (32768/(3*Real.pi^2))*kinetic ψ := by
  obtain ⟨hi,hb⟩ := flatOneBodyDensity_power_bound ψ hψ hm
  refine ⟨(PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable hi, ?_⟩
  change (∫ x : Space, (flatOneBodyDensity ψ ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x))^(5/3:ℝ)) ≤ _
  rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ))]
  exact hb

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
