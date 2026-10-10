import OAI.Analysis.NuclearUltrapower.Predecessors
import OAI.Analysis.NuclearUltrapower.NormUltrapower
import OAI.Analysis.NuclearUltrapower.FullGroupAlgebra
import OAI.Analysis.NuclearUltrapower.FaithfulGNS
import OAI.Analysis.NuclearUltrapower.ModTwo

namespace OAI

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower
universe u v w
section InjectiveInduction
variable {Γ : Type u} {Δ : Type v} [Group Γ] [Group Δ]
  (f : Γ →* Δ) (hf : Function.Injective f) (π : FiniteUnitaryRep.{u,w} Γ)

/-- Induction along an honest subgroup inclusion; the index may be infinite. -/
abbrev InjectiveInducedSpace := lp (fun _ : Δ ⧸ f.range => π) 2

def injectiveInduced : Δ →* (InjectiveInducedSpace f π ≃ₗᵢ[ℂ] InjectiveInducedSpace f π) :=
  inducedUnitary f.range (π.action.comp (MonoidHom.ofInjective hf).symm.toMonoidHom)

/-- On the identity coset the induced representation contains the original one. -/
theorem injectiveInduction_intertwines (g : Γ) (x : π) :
    inductionInclusion f.range (π.action g x) =
      injectiveInduced f hf π (f g) (inductionInclusion f.range x) := by
  have h := inductionInclusion_intertwines f.range
    (π.action.comp (MonoidHom.ofInjective hf).symm.toMonoidHom)
    ((MonoidHom.ofInjective hf) g) x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply, injectiveInduced] using h

/-- The full group algebra sees the initial finite-dimensional constituent,
using an algebraic invariant tensor in the identity coset of the induction. -/
theorem injectiveInduced_invariant_tensor :
    ∃ z : InjectiveInducedSpace f π ⊗[ℂ] π.dual, z ≠ 0 ∧
      ∀ g : Γ, TensorProduct.congrIsometry (injectiveInduced f hf π (f g))
        (π.dual.action g) z = z := by
  let T : π →L[ℂ] InjectiveInducedSpace f π := (inductionInclusion f.range).toContinuousLinearMap
  have hT : T ≠ 0 := by
    intro h
    obtain ⟨x,hx⟩ := exists_ne (0 : π)
    apply hx
    apply (inductionInclusion f.range).injective
    rw [map_zero]
    exact congrArg (fun T : π →L[ℂ] InjectiveInducedSpace f π => T x) h
  obtain ⟨z,hz,hiz⟩ := exists_invariant_tensor_of_intertwiner
    ((injectiveInduced f hf π).comp f) π.action T hT
    (injectiveInduction_intertwines f hf π)
  exact ⟨z,hz,hiz⟩

end InjectiveInduction
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower

/-- A faithful unital representation of a nonzero algebra has nonzero Hilbert space. -/
theorem faithful_hilbert_nontrivial {B E : Type*} [CStarAlgebra B] [Nontrivial B]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hρ : Function.Injective ρ) : Nontrivial E := by
  by_contra h
  have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
  exact (zero_ne_one : (0 : B) ≠ 1) (hρ (Subsingleton.elim _ _))

section Obstruction
variable {Γ Δ B : Type} [Group Γ] [Group Δ] [CStarAlgebra B] [Nontrivial B]
  (f : Γ →* Δ) (hf : Function.Injective f)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)]
  (t : Δ) (ht : ∀ g, f (θ g) * t = t * f g)
  (S : Finset Γ) (hSne : S.Nonempty) (hS : Subgroup.closure (S : Set Γ) = ⊤)
  (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
  (hgap : HasKazhdanGap.{0,0} S κ)
  (π : FiniteUnitaryRep.{0,0} Γ) (hirr : π.Irreducible)
  (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))

include hf hθ ht hSne hS hκ0 hκ hgap hirr haper in
/-- The spectral obstruction for an injective
ascending subgroup in the exact ambient group, without assuming an initial
match or a coordinate representation. -/
theorem fullGroup_no_nuclear_ultrapower (hB : IsNuclear.{0,0} B)
    (ω : Ultrafilter ℕ) (hω : IsFree ω) :
    ¬ ∃ φ : FullGroupModel.Full Δ →⋆ₐ[ℂ] NormUltrapower B ω,
      Function.Injective φ := by
  classical
  rintro ⟨φ,hφ⟩
  let ρ := universalGNS (A := B)
  have hρ : Function.Injective ρ := universalGNS_injective
  let : Nontrivial (UniversalGNS B) := faithful_hilbert_nontrivial ρ hρ
  let ι := FullGroupModel.inclusion Δ
  let φu : FullGroupModel.Full Δ →⋆* NormUltrapower B ω :=
    { φ.toMonoidHom with map_star' := map_star φ }
  let r : Δ →* unitary (NormUltrapower B ω) :=
    (Unitary.map φu).toMonoidHom.comp ι
  obtain ⟨u,hu1,hu,hmul⟩ := exists_unitary_lifts ω r
  have hmul' (g h : Δ) : Tendsto
      (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
        (ω : Filter ℕ) (𝓝 0) := by
    simpa only [norm_sub_rev, norm_zero] using (hmul g h).norm
  let φ' := (normUltraToCStar B ω).comp φ
  have hφ' : Function.Injective φ' := (normUltraToCStar_injective B ω).comp hφ
  let σ := injectiveInduced f hf π
  let ψ := FullGroupModel.modelMap Δ
    (Unitary.linearIsometryEquiv.symm.toMonoidHom.comp σ)
  have hψ (g : Γ) : ψ (ι (f g)) = (σ (f g) : InjectiveInducedSpace f π →L[ℂ] _) := by
    exact FullGroupModel.modelMap_generator Δ _ (f g)
  have hu' (g : Γ) : φ' (ι (f g)) = VariableUltra.mk (fun _ : ℕ => B) ω
      (VariableUltra.unitarySequence (fun _ : ℕ => B) (u (f g))) := by
    have h := congrArg (normUltraToCStar B ω) (hu (f g))
    have hr (d : Δ) : (r d : NormUltrapower B ω) = φ (ι d) := rfl
    rw [hr] at h
    simpa only [normUltraToCStar_mk, boundedSeqToLp_unitary, φ',
      StarAlgHom.comp_apply] using h.symm
  obtain ⟨z,hz0,hz⟩ := injectiveInduced_invariant_tensor f hf π
  let a : ℝ := min (κ/2) (κ^2 / (8 * (S.card : ℝ)))
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have ha : a < κ := (min_le_left _ _).trans_lt (by linarith)
  have ha' : a < κ^2 / (4 * (S.card : ℝ)) := by
    have hk2 : 0 < κ^2 := sq_pos_of_pos hκ0
    exact (min_le_right _ _).trans_lt (by
      apply div_lt_div_of_pos_left hk2 (by positivity)
      linarith)
  have hm := initial_match ρ hρ S ω φ' hφ' (fun g => (ι (f g) : FullGroupModel.Full Δ))
    (fun g => u (f g)) hu' ψ (fun g => σ (f g)) hψ π.dual a ha0
    (ha.le.trans hκ) z hz0 (fun s _ => hz s)
  exact contradiction_of_initial_match ρ f θ hθ t S u ω κ a hB hSne hκ0 hκ hgap hS
    ha ha0 ha' ht (fun n => by simpa only [Finset.coe_singleton] using hω {n}) hu1 hmul'
    π.dual hirr.dual (FiniteUnitaryRep.dual_aperiodic θ haper) hm
end Obstruction
end NuclearUltrapower
end
end

end OAI
