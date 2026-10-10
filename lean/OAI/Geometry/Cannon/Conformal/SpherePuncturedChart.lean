import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Plane

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonPolygonal
open CannonRegularDisk

variable {X : Type*} [TopologicalSpace X]

theorem sphere_punctured_chart
    (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (p : X) :
    ∃ e : Plane → X, IsOpenEmbedding e ∧ range e={p}ᶜ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let h := stereographic' 2 (φ p)
  have ht : h.target=univ := stereographic'_target _
  have hs : h.source={φ p}ᶜ := stereographic'_source _
  let e : Plane → X := φ.symm ∘ h.symm
  have he : IsOpenEmbedding e := φ.symm.isOpenEmbedding.comp (h.symm.isOpenEmbedding ht)
  refine ⟨e,he,?_⟩
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    change φ.symm (h.symm z)≠p
    intro hh
    have hz : h.symm z∈h.source := h.map_target (by rw [ht]; trivial)
    rw [hs] at hz
    apply hz
    have hh' := congrArg φ hh
    simpa only [φ.apply_symm_apply,mem_singleton_iff] using hh'
  · intro hx
    have hxp : φ x∈h.source := by
      rw [hs]
      exact fun hh => hx (mem_singleton_iff.mpr (φ.injective (mem_singleton_iff.mp hh)))
    refine ⟨h (φ x),?_⟩
    dsimp only [e,Function.comp_apply]
    rw [h.left_inv hxp,φ.symm_apply_apply]
end CannonPolygonal

end
end
end
end
end
end
end
end

end OAI
