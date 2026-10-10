import OAI.Analysis.KadisonKastler.SpatialStateHomogeneity

namespace OAI

/-! # Spatial transfer of faithful vector-state bicentralizers -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

def FaithfulVectorBicentralizersScalar (M : VonNeumannAlgebra H) : Prop :=
  ∀ ξ : H, ‖ξ‖=1 → Function.Injective (algebraVectorMap M ξ) →
    ∀ a : Algebra M, stateBicentralizerMember ξ a → ∃ z : ℂ, a=z • 1

variable (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (W : H ≃ₗᵢ[ℂ] K)
  (hW : ∀ (a : Algebra M) (x : H), W (a.val x)=(e a).val (W x))

include hW in
theorem stateBicentralizerMember.spatial_pullback (ξ : K) (a : Algebra M)
    (ha : stateBicentralizerMember ξ (e a)) :
    stateBicentralizerMember (W.symm ξ) a := by
  apply (stateBicentralizerMember_iff_unitary_tests _ _).mpr
  intro u hu η
  let v (n : ℕ) : unitary (Algebra N) := Unitary.map (StarMonoidHom.ofClass e) (u n)
  have hv : Tendsto (fun n => ‖vectorStateCommutator ξ (v n).val‖) atTop (𝓝 0) := by
    change Tendsto (fun n => ‖vectorStateCommutator ξ (e (u n).val)‖) atTop (𝓝 0)
    simpa only [spatial_stateCommutator_norm e W hW] using hu
  have h := (stateBicentralizerMember_iff_unitary_tests _ _).mp ha v hv (W η)
  have he (n : ℕ) : W ((a*(u n).val-(u n).val*a).val η) =
      (e a*(v n).val-(v n).val*e a).val (W η) := by
    rw [hW,map_sub e,map_mul e,map_mul e]
    rfl
  have ht := (W.symm.continuous.tendsto 0).comp h
  change Tendsto (fun n => W.symm ((e a*(v n).val-(v n).val*e a).val (W η)))
    atTop (𝓝 (W.symm 0)) at ht
  simpa only [← he,W.symm_apply_apply,map_zero] using ht

include hW in
theorem FaithfulVectorBicentralizersScalar.spatial_transport
    (hscalar : FaithfulVectorBicentralizersScalar M) : FaithfulVectorBicentralizersScalar N := by
  intro ξ hξ hs a ha
  have hb := stateBicentralizerMember.spatial_pullback e W hW ξ (e.symm a)
    (by simpa only [e.apply_symm_apply] using ha)
  obtain ⟨z,hz⟩ := hscalar (W.symm ξ) ((W.symm.norm_map ξ).trans hξ)
    (spatialVectorTransport_separating e W hW ξ hs) (e.symm a) hb
  refine ⟨z,?_⟩
  have he := congrArg e hz
  rw [e.apply_symm_apply] at he
  have hm : e (z • (1 : Algebra M))=z • e (1 : Algebra M) := e.map_smul' z 1
  rw [map_one] at hm
  exact he.trans hm

end

end KadisonKastler

end OAI
