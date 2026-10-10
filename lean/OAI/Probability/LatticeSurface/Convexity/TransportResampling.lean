import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.IntervalResampling

namespace OAI

open Set MeasureTheory

namespace IntervalResampling

lemma transport {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (μ : Measure X) [SFinite μ] (mW : Measure W) [SFinite mW]
    (e : X ≃ᵐ W×ℝ) (he : MeasurePreserving e μ (mW.prod volume))
    (K : Set X) {R : Set W} (hR : MeasurableSet R) {l u : W → ℝ} (hl : Measurable l) (hu : Measurable u)
    (hK : e.symm ⁻¹' K=region R l u)
    (T : X×ℝ → X) (hT : Measurable T)
    (hcomm : ∀ z,e (T z)=((e z.1).1,l (e z.1).1+(u (e z.1).1-l (e z.1).1)*z.2)) :
    Measure.map T ((μ.restrict K).prod (volume.restrict (Icc (0:ℝ) 1)))=μ.restrict K := by
  let S : (W×ℝ)×ℝ → W×ℝ := fun z => (z.1.1,l z.1.1+(u z.1.1-l z.1.1)*z.2)
  have hS : Measurable S := by dsimp [S];fun_prop
  have hm : Measure.map e (μ.restrict K)=(mW.prod volume).restrict (region R l u) := by
    rw [← hK,← he.map_eq,e.restrict_map]
    congr 2
    ext x
    simp
  have hc : e ∘ T=S ∘ Prod.map e id := funext hcomm
  apply e.measurableEmbedding.map_injective
  rw [Measure.map_map e.measurable hT,hc,← Measure.map_map hS (e.measurable.prodMap measurable_id),
    ← Measure.map_prod_map _ _ e.measurable measurable_id,Measure.map_id,hm]
  exact invariant mW hR hl hu

end IntervalResampling

end OAI
