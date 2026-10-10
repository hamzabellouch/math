import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CorrelatedFiniteInsertion

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma spinSpace_map_spatial : Measure.map Prod.snd slaterParticleMeasure = (2:ENNReal) • (volume : Measure Space) := by
  rw [show slaterParticleMeasure = Measure.count.prod volume from rfl,Measure.map_snd_prod]
  simp

lemma spinPair_map_spatial :
    Measure.map (Prod.map Prod.snd Prod.snd) (slaterParticleMeasure.prod slaterParticleMeasure) =
      (4:ENNReal) • (volume : Measure (Space × Space)) := by
  rw [← Measure.map_prod_map _ _ measurable_snd measurable_snd,spinSpace_map_spatial]
  norm_num [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.volume_eq_prod]

lemma spinPair_integral_spatial {F : Space × Space → ℝ} (hF : Measurable F) :
    (∫ z : SlaterParticle × SlaterParticle, F (z.1.2,z.2.2)
      ∂slaterParticleMeasure.prod slaterParticleMeasure) = 4 * ∫ x : Space × Space, F x := by
  have h := integral_map (μ := slaterParticleMeasure.prod slaterParticleMeasure)
    ((measurable_snd.prodMap measurable_snd).aemeasurable) hF.aestronglyMeasurable
  rw [spinPair_map_spatial,integral_smul_measure] at h
  simpa only [ENNReal.toReal_ofNat,smul_eq_mul,Prod.map_apply'] using h.symm

def spatialFiniteDensity {ι : Type*} [Fintype ι] (p : ι → ℝ) (u : ι → Space → ℂ) (x : Space) : ℝ :=
  ∑ i, p i * ‖u i x‖^2

lemma spinFinite_density {ι : Type*} [Fintype ι] (p : ι → ℝ) (u : ι → Space → ℂ) (z : SlaterParticle) :
    finiteOrbitalDensity (fun i : Fin 2 × ι => p i.2) (fun i => spinLift (u i.2) i.1) z =
      spatialFiniteDensity p u z.2 := by
  classical
  rcases z with ⟨σ,x⟩
  simp only [finiteOrbitalDensity,Fintype.sum_prod_type,spinLift]
  rw [Finset.sum_comm]
  fin_cases σ <;> simp [spatialFiniteDensity]

lemma spinFinite_kinetic {ι : Type*} [Fintype ι] (p : ι → ℝ) (u : ι → Space → ℂ) :
    finiteOrbitalKinetic (fun i : Fin 2 × ι => p i.2) (fun i => spinLift (u i.2) i.1) =
      ∑ a : Fin 3, ∑ i, p i * ∫ x : Space, ‖fderiv ℝ (u i) x (EuclideanSpace.single a 1)‖^2 := by
  simp only [finiteOrbitalKinetic,Fintype.sum_prod_type,spinLift_derivative_mass,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma spinFinite_orthonormal {ι : Type*} [DecidableEq ι] {u : ι → Space → ℂ}
    (hu : ∀ i j, (∫ x : Space, conj (u i x) * u j x) = if i=j then 1 else 0)
    (i j : Fin 2 × ι) :
    (∫ z, conj (spinLift (u i.2) i.1 z)*spinLift (u j.2) j.1 z ∂slaterParticleMeasure) =
      if i=j then 1 else 0 := by
  rw [spinLift_inner,hu]
  by_cases h : i.1=j.1 <;> by_cases k : i.2=j.2 <;> simp [h,k,Prod.ext_iff]

end CoulombAtom

end

end OAI
