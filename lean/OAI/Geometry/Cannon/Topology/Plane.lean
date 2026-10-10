import Mathlib

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

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

namespace CannonPlaneLinear
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def complexPlaneL : ℂ ≃L[ℝ] Plane :=
  Complex.equivRealProdCLM.trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜:=ℝ) (ι:=Fin 2)).symm)

lemma preimage_segment (x y : Plane) :
    complexPlaneL ⁻¹' segment ℝ x y=segment ℝ (complexPlaneL.symm x) (complexPlaneL.symm y) := by
  calc
    _=complexPlaneL.symm '' segment ℝ x y := by
      ext z
      constructor
      · intro hz
        exact ⟨complexPlaneL z,hz,complexPlaneL.symm_apply_apply z⟩
      · rintro ⟨w,hw,rfl⟩
        simpa using hw
    _=segment ℝ (complexPlaneL.symm x) (complexPlaneL.symm y) := by
      simpa using image_segment ℝ complexPlaneL.symm.toLinearEquiv.toAffineEquiv.toAffineMap x y

lemma finite_segments_pull (P : Finset (Plane × Plane)) :
    ∃ Q : Finset (ℂ × ℂ), complexPlaneL ⁻¹' (⋃ p∈P,segment ℝ p.1 p.2)=
      ⋃ q∈Q,segment ℝ q.1 q.2 := by
  classical
  refine ⟨P.image (fun p => (complexPlaneL.symm p.1,complexPlaneL.symm p.2)),?_⟩
  simp only [preimage_iUnion,preimage_segment]
  ext z
  simp
end CannonPlaneLinear

noncomputable section
open Set Topology

namespace CannonConnectedSupport
variable {X : Type*} [TopologicalSpace X] [T1Space X]

theorem finite_extras_absorbed {K T : Set X} (hK : IsClosed K) (hT : T.Finite)
    (hconn : IsPreconnected (K∪T)) (hnt : (K∪T).Nontrivial) : T⊆K := by
  intro x hxT
  by_contra hxK
  let S := K∪T
  let _ : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  let z : S := ⟨x,Or.inr hxT⟩
  have he : ({z} : Set S)ᶜ=Subtype.val ⁻¹' (K∪(T\{x})) := by
    ext y
    simp only [mem_compl_iff,mem_singleton_iff,mem_preimage,mem_union,mem_sdiff]
    constructor
    · intro hy
      rcases y.property with hyK|hyT
      · exact Or.inl hyK
      · exact Or.inr ⟨hyT,fun h => hy (Subtype.ext h)⟩
    · intro hy h
      subst y
      rcases hy with hzK|hzT
      · exact hxK hzK
      · exact hzT.2 rfl
  have hc : IsClopen ({z} : Set S) := by
    refine ⟨isClosed_singleton,?_⟩
    rw [←isClosed_compl_iff,he]
    exact (hK.union (hT.sdiff).isClosed).preimage continuous_subtype_val
  have hall := hc.eq_univ (singleton_nonempty z)
  obtain ⟨a,ha,b,hb,hab⟩ := hnt
  have ha' : (⟨a,ha⟩ : S)=z := mem_singleton_iff.mp (hall.symm ▸ mem_univ _)
  have hb' : (⟨b,hb⟩ : S)=z := mem_singleton_iff.mp (hall.symm ▸ mem_univ _)
  exact hab (congrArg Subtype.val (ha'.trans hb'.symm))
end CannonConnectedSupport

noncomputable section
open Set Topology

namespace CannonFaceLabels
variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

lemma complement_component_label_continuous {K : Set X} (hK : IsClosed K) :
    Continuous (ConnectedComponents.mk : (Kᶜ : Set X) → ConnectedComponents (Kᶜ : Set X)) := by
  let _ : LocallyConnectedSpace (Kᶜ : Set X) := hK.isOpen_compl.locallyConnectedSpace
  apply continuous_discrete_rng.mpr
  intro component
  obtain ⟨point, rfl⟩ := ConnectedComponents.surjective_coe component
  simpa only [connectedComponents_preimage_singleton] using
    (isOpen_connectedComponent : IsOpen (connectedComponent point))

lemma complement_components_discrete {K : Set X} (hK : IsClosed K) :
    DiscreteTopology (ConnectedComponents (Kᶜ : Set X)) := by
  let _ : LocallyConnectedSpace (Kᶜ : Set X) := hK.isOpen_compl.locallyConnectedSpace
  infer_instance
end CannonFaceLabels

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
