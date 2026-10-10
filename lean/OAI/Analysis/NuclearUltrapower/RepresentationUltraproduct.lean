import OAI.Analysis.NuclearUltrapower.TensorGap
import OAI.Analysis.NuclearUltrapower.Schur

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
open scoped TensorProduct

namespace VariableUltra
variable {ι : Type*} {Γ : Type u} [Group Γ]
variable (π : ι → FiniteUnitaryRep.{u,v} Γ)

/-- The bounded coordinate representation, before taking its quotient. -/
def representationSequence : Γ →* unitary (operatorSeq (fun i => π i)) where
  toFun g := isoSequence _ (fun i => (π i).action g)
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change ((Unitary.linearIsometryEquiv.symm ((π i).action 1) : unitary (π i →L[ℂ] π i)) :
      π i →L[ℂ] π i) = 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change ((Unitary.linearIsometryEquiv.symm ((π i).action (g*h)) : unitary (π i →L[ℂ] π i)) :
      π i →L[ℂ] π i) =
      (Unitary.linearIsometryEquiv.symm ((π i).action g) : π i →L[ℂ] π i) *
      (Unitary.linearIsometryEquiv.symm ((π i).action h) : π i →L[ℂ] π i)
    rw [map_mul, map_mul]
    rfl

variable (ω : Ultrafilter ι) {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Any unital representation of the quotient carries the source group tuple. -/
def quotientRepresentation (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Γ →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    ((Unitary.map (starAlgToStarMonoid φ)).toMonoidHom.comp
      ((Unitary.map (starAlgToStarMonoid (mk _ ω))).toMonoidHom.comp (representationSequence π)))

@[simp] theorem quotientRepresentation_apply
    (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) (g : Γ) :
    quotientRepresentation π ω φ g = representedIso (fun i => π i) ω φ
      (fun i => (π i).action g) := rfl

/-- An inequivalent sequence has at most one coordinate of any fixed type. -/
theorem eventually_inequivalent
    (hω : ∀ i : ι, ({i} : Set ι) ∉ (ω : Filter ι))
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (τ : FiniteUnitaryRep.{u,v} Γ) :
    ∀ᶠ i in (ω : Filter ι), ¬ τ.Equivalent (π i) := by
  classical
  by_cases he : ∃ i, τ.Equivalent (π i)
  · obtain ⟨i, hi⟩ := he
    have hiω : ∀ᶠ j in (ω : Filter ι), j ≠ i :=
      show {j | j ≠ i} ∈ (ω : Filter ι) from
        (ω.compl_mem_iff_notMem.mpr (hω i))
    filter_upwards [hiω] with j hj
    intro hjτ
    exact hne hj (hjτ.symm.trans hi)
  · exact Filter.Eventually.of_forall (fun i h => he ⟨i, h⟩)

/-- The ordinary finite-dimensional tensor gap at a nonexceptional coordinate. -/
theorem inequivalent_tensor_gap (P T : FiniteUnitaryRep.{u,v} Γ)
    (hP : P.Irreducible) (hT : T.Irreducible) (hne : ¬ T.Equivalent P)
    (S : Finset Γ) (κ : ℝ) (hgap : HasKazhdanGap.{u,v} S κ) :
    ∀ w : P ⊗[ℂ] StrongDual ℂ T, κ * ‖w‖ ^ 2 ≤ ∑ s ∈ S,
      ‖TensorProduct.congrIsometry (P.action s) (dualUnitary (T.action s)) w - w‖ ^ 2 := by
  let ρ := tensorContragredientRep P.action T.action
  have hρ : ∀ w : P ⊗[ℂ] StrongDual ℂ T, (∀ g : Γ, ρ g w = w) → w = 0 :=
    tensor_no_invariants_of_inequivalent hP hT hne
  have he := hgap (P ⊗[ℂ] StrongDual ℂ T) ρ hρ
  exact he

/-- The varying matrix quotient has no finite-dimensional parts in any
unital representation. This is the hard quotient step of nuclear-finiteness. -/
theorem quotientRepresentation_weakly_mixing
    (hω : ∀ i : ι, ({i} : Set ι) ∉ (ω : Filter ι))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (S : Finset Γ) (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    HasNoFiniteDimensionalSubrep (quotientRepresentation π ω φ) := by
  classical
  intro W hW0 hW hfd
  let : FiniteDimensional ℂ W := hfd
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨τ, hτ, T, hT⟩ := finiteSubspace_exists_irreducible
    (quotientRepresentation π ω φ) W hW
  have hT0 : T.toContinuousLinearMap ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : τ)
    apply hx
    apply T.injective
    change T.toContinuousLinearMap x = T.toContinuousLinearMap 0
    rw [he]
    rfl
  obtain ⟨z, hz0, hz⟩ := exists_invariant_tensor_of_intertwiner
    (quotientRepresentation π ω φ) τ.action T.toContinuousLinearMap hT0 hT
  have hcoord : ∀ᶠ i in (ω : Filter ι), ∀ w : π i ⊗[ℂ] StrongDual ℂ τ,
      κ * ‖w‖ ^ 2 ≤ ∑ s ∈ S,
        ‖TensorProduct.congrIsometry ((π i).action s) (dualUnitary (τ.action s)) w - w‖ ^ 2 := by
    filter_upwards [eventually_inequivalent π ω hω hne τ] with i hi
    exact inequivalent_tensor_gap (π i) τ (hirr i) hτ hi S κ hgap
  have hn : Nonempty (Fin (Module.finrank ℂ (StrongDual ℂ τ))) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := ℂ) (M := StrongDual ℂ τ))
  let := hn
  exact hz0 (quotient_tensor_no_invariants (fun i => π i) ω S
    (stdOrthonormalBasis ℂ (StrongDual ℂ τ)) (fun i => (π i).action)
    (fun s => dualUnitary (τ.action s)) hκ0 hκ hcoord φ z (fun s _ => hz s))
end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
