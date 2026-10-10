import Mathlib
import OAI.Analysis.Commutator.HilbertBiprod
import OAI.Analysis.Commutator.NormalGNSContinuity
import OAI.Analysis.Commutator.NormalOperatorHom

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder NNReal

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma gns_normal (τ : M →ₚ[ℂ] ℂ) (hτ : NormalGNS.BoundedWOTContinuous M τ) :
    BoundedNormal M τ.gnsStarAlgHom := by
  intro C x y
  apply continuous_iff_continuousAt.mpr
  intro a
  let C' : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let f : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} → M :=
    fun b => ⟨b.val.toCLM,b.property.1⟩
  have hf : ∀ b,‖f b‖≤C' := fun b => b.property.2.trans (le_max_left _ _)
  apply NormalGNS.tendsto_gns M τ hτ f (f a) C' hf (hf a)
  intro u v
  have hc := (ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val u v).tendsto a
  simpa only [f,RCLike.star_def,inner_conj_symm,coe_toCLM] using hc.star

lemma subtype_normal : BoundedNormal M M.toStarSubalgebra.subtype := by
  intro C x y
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val y x

lemma diag_normal {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (ψ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hφ : BoundedNormal M φ) (hψ : BoundedNormal M ψ) :
    BoundedNormal M (HilbertBiprod.diagHom φ ψ) := by
  intro C x y
  have hc := (hφ C x.ofLp.1 y.ofLp.1).add (hψ C x.ofLp.2 y.ofLp.2)
  change Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} => inner ℂ x.ofLp.1 (φ ⟨a.val.toCLM,a.property.1⟩ y.ofLp.1) +
    inner ℂ x.ofLp.2 (ψ ⟨a.val.toCLM,a.property.1⟩ y.ofLp.2)) at hc
  simpa only [HilbertBiprod.diagHom_apply,HilbertBiprod.block_apply,WithLp.prod_inner_apply]
    using hc

lemma diagonal_gns_range (τ : M →ₚ[ℂ] ℂ) (hτ : NormalGNS.BoundedWOTContinuous M τ) :
    Set.centralizer (Set.centralizer
      (Set.range (HilbertBiprod.diagHom (A:=M) (H:=H) (G:=τ.GNS) M.toStarSubalgebra.subtype τ.gnsStarAlgHom)))=
      Set.range (HilbertBiprod.diagHom (A:=M) (H:=H) (G:=τ.GNS) M.toStarSubalgebra.subtype τ.gnsStarAlgHom) :=
  range_bicommutant M _ (diag_normal M _ _ (subtype_normal M) (gns_normal M τ hτ))

end Kadison.NormalOperatorHom

end

end
end

end OAI
