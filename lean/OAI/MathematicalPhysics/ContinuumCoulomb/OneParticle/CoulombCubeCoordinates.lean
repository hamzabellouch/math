import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeMeasure
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedRawDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabSections

namespace OAI

/-! Exact Lebesgue coordinates for the two-particle finite Coulomb box. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb
open UniformQuadrature

def twoParticleCoordinates : (Fin 6 → ℝ) ≃ᵐ Position × Position :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ⊕ Fin 3 => ℝ)
    (finSumFinEquiv (m := 3) (n := 3)).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)).trans
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))))

theorem twoParticleCoordinates_fst (v : Fin 6 → ℝ) (i : Fin 3) :
    (twoParticleCoordinates v).1 i = v (i.castAdd 3) := by
  fin_cases i <;> rfl

theorem twoParticleCoordinates_snd (v : Fin 6 → ℝ) (i : Fin 3) :
    (twoParticleCoordinates v).2 i = v (i.natAdd 3) := by
  fin_cases i <;> rfl

theorem slabDomain_cube (L : ℝ) : slabDomain L L = coulombNumericalBox L := by
  ext x
  simp only [slabDomain, coulombNumericalBox, Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2⟩

theorem twoParticleCoordinates_measurePreserving (L : ℝ) :
    MeasurePreserving twoParticleCoordinates (cubeMeasure (-L) L 6)
      (volume.restrict (coulombNumericalBox L ×ˢ coulombNumericalBox L)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-L) L)
  have hindex := measurePreserving_piCongrLeft (fun _ : Fin 3 ⊕ Fin 3 => μ)
    (finSumFinEquiv (m := 3) (n := 3)).symm
  have hsplit := measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => μ)
  have hcube : cubeMeasure (-L) L 3 = slabProductMeasure L L := by
    unfold cubeMeasure slabProductMeasure slabAxisMeasure
    congr 1
    funext i
    simp only [slabSide, ite_self]
  have hslot : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (cubeMeasure (-L) L 3) (volume.restrict (coulombNumericalBox L)) := by
    rw [hcube, ← slabDomain_cube]
    exact slabProduct_measurePreserving L L
  have h := (hslot.prod hslot).comp (hsplit.comp hindex)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

theorem localizedRawCoulombBox_cube {freq ε L : ℝ}
    (hf : 0 < freq) (hε : 0 < ε) (hL : 0 ≤ L) (u : PlanarPosition) :
    localizedRawCoulombBox freq ε L u = cubeIntegral (-L) L 6
      (fun v => cappedPairIntegrand ε (planarCenter u)
        (localizedRawDensity freq) (localizedRawDensity freq) (twoParticleCoordinates v)) := by
  let f := cappedPairIntegrand ε (planarCenter u)
    (localizedRawDensity freq) (localizedRawDensity freq)
  have hfi : Integrable f := cappedPairIntegrand_integrable hε (planarCenter u)
    (localizedRawDensity_integrable hf) (localizedRawDensity_integrable hf)
  have hp := twoParticleCoordinates_measurePreserving L
  have hcomp : Integrable (fun v => f (twoParticleCoordinates v)) (cubeMeasure (-L) L 6) :=
    (hp.integrable_comp_emb twoParticleCoordinates.measurableEmbedding).mpr hfi.restrict
  rw [cubeIntegral_eq_integral 6 (by linarith) hcomp]
  exact (hp.integral_comp' f).symm

end ContinuumCoulomb

end

end OAI
