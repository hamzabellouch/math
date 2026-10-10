import OAI.Analysis.CircleDomains.Sobolev.ComplexWeakDirectionalTransport
import OAI.Analysis.CircleDomains.Rigidity.PrincipalRealBeltrami
import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals

namespace OAI

/-! Package actual complex weak directional fields as the physical local
Sobolev witness required by the principal-map construction. -/
open MeasureTheory Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma complex_memLp_physical_ball {g : ℂ → ℂ} {R : ℝ}
    (hg : MemLp g 2 (volume.restrict (Metric.ball 0 R))) :
    MemLp (g ∘ complexPlaneCoordinates) 2
      (volume.restrict (Metric.ball 0 R)) := by
  have hmp := complexPlaneCoordinates_measurePreserving.restrict_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding (Metric.ball 0 R)
  simpa only [complexPlaneCoordinates_preimage_ball] using hg.comp_measurePreserving hmp

def localWeakComplexOfDirectionalFields (f : ℂ → ℂ) (V : Fin 2 → ℂ → ℂ)
    (hf : LocallyIntegrable f volume) (hV : ∀ i, LocallyIntegrable (V i) volume)
    (hweak : ∀ i (ψ : SchwartzMap ℂ ℂ), HasCompactSupport (ψ : ℂ → ℂ) →
      (∫ z, ψ z * V i z) = -(∫ z, fderiv ℝ (ψ : ℂ → ℂ) z
        (complexPlaneCoordinates (EuclideanSpace.single i 1)) * f z))
    (hL : ∀ R i, MemLp (V i) 2 (volume.restrict (Metric.ball 0 R))) :
    PlaneLocalWeakComplex (fun x => f (complexPlaneCoordinates x)) where
  realGradient := fun x => WithLp.toLp 2 (fun i => (V i (complexPlaneCoordinates x)).re)
  imagGradient := fun x => WithLp.toLp 2 (fun i => (V i (complexPlaneCoordinates x)).im)
  real_weak := fun i => weakPartial_of_complex_directional_identity hf (hV i) i _ rfl
    (hweak i) Complex.reCLM
  imag_weak := fun i => weakPartial_of_complex_directional_identity hf (hV i) i _ rfl
    (hweak i) Complex.imCLM
  real_memLp := fun R i => Complex.reCLM.comp_memLp' (complex_memLp_physical_ball (hL R i))
  imag_memLp := fun R i => Complex.imCLM.comp_memLp' (complex_memLp_physical_ball (hL R i))

lemma planarDz_of_complex_directions (a b : ℂ) :
    planarDz a.re b.re a.im b.im = (a - Complex.I * b) / 2 := by
  apply Complex.ext <;> simp [planarDz]

lemma planarDbar_of_complex_directions (a b : ℂ) :
    planarDbar a.re b.re a.im b.im = (a + Complex.I * b) / 2 := by
  apply Complex.ext <;> simp [planarDbar, add_comm, sub_eq_add_neg]

end CircleDomainRigidity

end

end OAI
