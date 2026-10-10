import Mathlib
import OAI.Computability.VertexCover.Analysis.BlockLawAc
import OAI.Computability.VertexCover.Analysis.LawNegInvariant

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product
open MeasureTheory

theorem piMap_measurePreserving {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (f : X → Y) (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (fun s : ι → X => fun i => f (s i))
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : ι => ν)) := by
  refine ⟨Measurable.of_eval (fun index => hf.measurable.comp (measurable_pi_apply index)), ?_⟩
  let : SigmaFinite (Measure.map f μ) := by rw [hf.map_eq]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hf.map_eq]

end VertexCover.Product

namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem pi_uniformOn_univ {ι E : Type*} [Fintype ι] [Fintype E] [Nonempty E]
    [MeasurableSpace E] [MeasurableSingletonClass E] :
    Measure.pi (fun _ : ι => uniformOn (Set.univ : Set E)) =
      uniformOn (Set.univ : Set (ι → E)) := by
  classical
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.pi_singleton]
  rw [uniformOn_univ]
  simp [uniformOn_univ, ENNReal.inv_pow]

theorem vector_measurePreserving {ι : Type*} [Fintype ι] (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (fun s : ι → ℝ => fun i => index p hp (s i))
      (VertexCover.Cube.law ι) (uniformOn (Set.univ : Set (ι → Fin p))) := by
  let : NeZero p := ⟨hp.ne'⟩
  have h := VertexCover.Product.piMap_measurePreserving (ι := ι)
    VertexCover.Cube.intervalLaw (uniformOn (Set.univ : Set (Fin p)))
    (index p hp) (index_measurePreserving p hp)
  simpa only [pi_uniformOn_univ, VertexCover.Cube.law] using h

theorem integral_uniform_finite {E : Type*} [Fintype E] [Nonempty E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (f : E → ℝ) :
    (∫ x, f x ∂uniformOn (Set.univ : Set E)) = (∑ x, f x) / Fintype.card E := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast, smul_eq_mul]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_comm, mul_one]

end VertexCover.GridCoupling

namespace VertexCover.Cube
open MeasureTheory
instance blockLaw_negInvariant (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (blockLaw ι κ).IsNegInvariant := by
  unfold blockLaw
  exact Measure.pi.isNegInvariant (fun _ : ι => law κ)
end VertexCover.Cube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
