import OAI.Analysis.NuclearUltrapower.InitialMatching
import OAI.Analysis.NuclearUltrapower.DyadicGroup

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ] {E : ℕ → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ℕ) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)

theorem vectors_of_small_energies (κ a : ℝ) (hgap : HasKazhdanGap.{u,v} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ i in (ω : Filter ℕ), bottomEnergy S (fun g => U g i) < a) :
    ∃ x : ∀ i, E i, (∀ i, ‖x i‖ = 1) ∧ ∀ g, AlmostInvariant (ω : Filter ℕ) U x g := by
  have hb0 := bottom_tendsto_zero_of_small ω S U κ a hgap ha h1 hmul hm
  obtain ⟨ξ,hξ,he⟩ := exists_almost_invariant_vectors ω S U hω hb0
  refine ⟨ξ,hξ,fun g => ?_⟩
  apply almostInvariant_of_generators S hS (fun n => (hξ n).le) h1 hmul _ g
  intro s hs
  exact displacement_tendsto_of_energy (ω : Filter ℕ) S U ξ he s hs
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v
section MatchedVectors
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → ℕ → unitary B)
  (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

omit [Nontrivial E] in
theorem matchingTuple_defects
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0)) (g h : Γ) :
    Tendsto (fun n => ‖(matchingTuple ρ (fun g => u g n) (π n) (g*h) :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((matchingTuple ρ (fun g => u g n) (π n) g * matchingTuple ρ (fun g => u g n) (π n) h) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))‖) (ω : Filter ℕ) (𝓝 0) := by
  have hb (n : ℕ) : 0 ≤ ‖(matchingTuple ρ (fun g => u g n) (π n) (g*h) :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((matchingTuple ρ (fun g => u g n) (π n) g * matchingTuple ρ (fun g => u g n) (π n) h) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))‖ := by
    exact norm_nonneg ((matchingTuple ρ (fun g => u g n) (π n) (g*h) :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((matchingTuple ρ (fun g => u g n) (π n) g * matchingTuple ρ (fun g => u g n) (π n) h) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)))
  exact squeeze_zero hb (fun n => matchingTuple_mul_defect ρ (fun g => u g n) (π n) g h) (hmul g h)

omit [Nontrivial E] in
theorem matchingTuple_identity (h1 : ∀ n, u 1 n = 1) :
    Tendsto (fun n => ‖(matchingTuple ρ (fun g => u g n) (π n) 1 :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((1 : TensorHilbert E (π n) ≃ₗᵢ[ℂ] TensorHilbert E (π n)) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))‖) (ω : Filter ℕ) (𝓝 0) := by
  have hz (n : ℕ) : matchingTuple ρ (fun g => u g n) (π n) 1 = 1 :=
    matchingTuple_one ρ (fun g => u g n) (π n) (h1 n)
  apply (tendsto_const_nhds (x := (0 : ℝ))).congr
  intro n
  rw [hz]
  rw [sub_self]
  exact (norm_zero (E := TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))).symm

/-- A sequence of matched representations admits unit vectors invariant under
EVERY fixed group element in the ultralimit; dimensions are still unrestricted. -/
theorem matched_vectors (κ a : ℝ) (hgap : HasKazhdanGap.{u,v} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a (π n)) :
    ∃ ξ : ∀ n, TensorHilbert E (π n), (∀ n, ‖ξ n‖ = 1) ∧
      ∀ g, Tendsto (fun n => ‖matchingTuple ρ (fun g => u g n) (π n) g (ξ n) - ξ n‖)
        (ω : Filter ℕ) (𝓝 0) := by
  let U : Γ → ∀ n, TensorHilbert E (π n) ≃ₗᵢ[ℂ] TensorHilbert E (π n) :=
    fun g n => matchingTuple ρ (fun g => u g n) (π n) g
  have hi := matchingTuple_identity ρ u π ω h1
  have hd := matchingTuple_defects ρ u π ω hmul
  have hb : ∀ᶠ n in (ω : Filter ℕ), bottomEnergy S (fun g => U g n) < a := by
    filter_upwards [hm] with n hn
    obtain ⟨x,hx,he⟩ := hn
    exact (bottomEnergy_le S _ x hx).trans_lt he
  exact vectors_of_small_energies ω S U κ a hgap hS ha hω hi hd hb
end MatchedVectors
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower

section Covariance
variable {E F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Quantitative tensor covariance; the two fixed coordinate maps are isometries. -/
theorem tensor_covariance_bound (U W : E →L[ℂ] E) (V : E →ₗᵢ[ℂ] E)
    (A : F →ₗᵢ[ℂ] F) (J : F →ₗᵢ[ℂ] F') (x : TensorHilbert E F) :
    ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x -
        tensorMapBetween V.toContinuousLinearMap J.toContinuousLinearMap x‖ ≤
      ‖U - V.toContinuousLinearMap * W‖ * ‖x‖ +
        ‖tensorMapBetween W A.toContinuousLinearMap x - x‖ := by
  let T := tensorIsometry V J
  have he : tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap =
      T.toContinuousLinearMap.comp (tensorMapBetween W A.toContinuousLinearMap) := by
    change tensorMapBetween (V.toContinuousLinearMap.comp W)
      (J.toContinuousLinearMap.comp A.toContinuousLinearMap) = _
    exact tensorMapBetween_comp W V.toContinuousLinearMap A.toContinuousLinearMap J.toContinuousLinearMap
  have hd := (tensorMapBetween_sub_norm_le U (V.toContinuousLinearMap * W) (J.comp A))
  have hl := ContinuousLinearMap.le_opNorm
    (tensorMapBetween U (J.comp A).toContinuousLinearMap -
      tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap) x
  have hb := hl.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg x))
  change ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x -
      tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap x‖ ≤ _ at hb
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (tensorMapBetween U (J.comp A).toContinuousLinearMap x)
    (tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap x)
    (T x)
  rw [he, ContinuousLinearMap.comp_apply] at ht
  change ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x - T x‖ ≤
    ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x -
      T (tensorMapBetween W A.toContinuousLinearMap x)‖ +
      ‖T (tensorMapBetween W A.toContinuousLinearMap x) - T x‖ at ht
  rw [← map_sub, T.norm_map] at ht
  rw [he, ContinuousLinearMap.comp_apply] at hb
  exact ht.trans (add_le_add hb le_rfl)
end Covariance

section Products
variable {Γ B E : Type*} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

theorem represented_product_defect (g h k l : Γ) (he : g*h=k*l) :
    ‖ρ (u g) * ρ (u h) - ρ (u k) * ρ (u l)‖ ≤
      ‖(u (g*h) : B) - (u g : B)*(u h : B)‖ +
      ‖(u (k*l) : B) - (u k : B)*(u l : B)‖ := by
  rw [← map_mul, ← map_mul, ← map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le ρ _).trans
  have ht := norm_sub_le_norm_sub_add_norm_sub ((u g : B)*(u h : B))
    (u (g*h) : B) ((u k : B)*(u l : B))
  rw [norm_sub_rev ((u g : B)*(u h : B)) (u (g*h))] at ht
  conv_rhs at ht => rhs; rw [he]
  exact ht
end Products
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v w
namespace FiniteUnitaryRep
variable {Γ : Type u} {Λ : Type w} [Group Γ] [Group Λ]

/-- Pullback along an arbitrary group homomorphism, retaining the Hilbert space. -/
def comap (π : FiniteUnitaryRep.{u,v} Γ) (f : Λ →* Γ) : FiniteUnitaryRep.{w,v} Λ :=
  { π with action := π.action.comp f }

@[simp] theorem comap_action (π : FiniteUnitaryRep.{u,v} Γ) (f : Λ →* Γ) (g : Λ) :
    (π.comap f).action g = π.action (f g) := rfl

theorem Irreducible.comap {π : FiniteUnitaryRep.{u,v} Γ} (hi : π.Irreducible)
    (f : Λ →* Γ) (hf : Function.Surjective f) : (π.comap f).Irreducible := by
  intro W hW
  apply hi W
  intro g x hx
  obtain ⟨h,rfl⟩ := hf g
  exact hW h x hx

theorem Embeds.comap {π τ : FiniteUnitaryRep.{u,v} Γ} (hi : π.Embeds τ)
    (f : Λ →* Γ) : (π.comap f).Embeds (τ.comap f) := by
  obtain ⟨T,hT⟩ := hi
  exact ⟨T,fun g x => hT (f g) x⟩

end FiniteUnitaryRep
section Range
variable {Γ : Type u} [Group Γ] (θ : Monoid.End Γ) (hθ : Function.Injective θ)

def rangeTwist (π : FiniteUnitaryRep.{u,u} Γ) : FiniteUnitaryRep.{u,u} θ.range :=
  π.comap (MonoidHom.ofInjective hθ).symm.toMonoidHom

theorem rangeTwist_irreducible {π : FiniteUnitaryRep.{u,u} Γ}
    (hi : π.Irreducible) : (rangeTwist θ hθ π).Irreducible :=
  hi.comap _ (MonoidHom.ofInjective hθ).symm.surjective

theorem rangeTwist_action (π : FiniteUnitaryRep.{u,u} Γ) (g : Γ) :
    (rangeTwist θ hθ π).action ((MonoidHom.ofInjective hθ) g) = π.action g := by
  change π.action ((MonoidHom.ofInjective hθ).symm ((MonoidHom.ofInjective hθ) g)) = π.action g
  rw [MulEquiv.symm_apply_apply]

theorem frobenius_predecessor [Finite (Γ ⧸ θ.range)]
    {π τ : FiniteUnitaryRep.{u,u} Γ} (hi : π.Irreducible)
    (ht : τ.Embeds (finiteInduced θ.range (rangeTwist θ hθ π))) :
    π.Embeds (τ.pull θ) := by
  obtain ⟨T,hT⟩ := frobenius_all_constituents θ.range (rangeTwist θ hθ π)
    (rangeTwist_irreducible θ hθ hi) ht
  refine ⟨T,fun g x => ?_⟩
  have hh := hT ((MonoidHom.ofInjective hθ) g) x
  rw [rangeTwist_action] at hh
  exact hh

end Range
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Shift
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) (t : Δ)

def rangeTwistInclusion (π : FiniteUnitaryRep.{u,u} Γ) : π →ₗᵢ[ℂ] rangeTwist θ hθ π :=
  LinearIsometry.id

/-- Translation of a tensor vector by the stable-letter coordinate. -/
def shiftVector (π : FiniteUnitaryRep.{u,u} Γ) (b : unitary B) :
    TensorHilbert E π →ₗᵢ[ℂ] TensorHilbert E (rangeTwist θ hθ π) :=
  tensorIsometry (representedUnitary ρ b).toLinearIsometry (rangeTwistInclusion θ hθ π)

theorem shiftVector_action_map (π : FiniteUnitaryRep.{u,u} Γ) (u : Δ → unitary B) (g : Γ) :
    (matchingTuple ρ (fun h : θ.range => u (f h)) (rangeTwist θ hθ π)
      ((MonoidHom.ofInjective hθ) g) : TensorHilbert E (rangeTwist θ hθ π) →L[ℂ] TensorHilbert E (rangeTwist θ hθ π)).comp
      (shiftVector ρ θ hθ π (u t)).toContinuousLinearMap =
    tensorMapBetween (ρ (u (f (θ g))) * ρ (u t))
      ((rangeTwistInclusion θ hθ π).comp (π.action g).toLinearIsometry).toContinuousLinearMap := by
  rw [matchingTuple_toCLM, completedTensorMap_eq_between, shiftVector, tensorIsometry_toCLM]
  rw [← tensorMapBetween_comp]
  have ha : ((rangeTwist θ hθ π).action ((MonoidHom.ofInjective hθ) g) :
      rangeTwist θ hθ π →L[ℂ] rangeTwist θ hθ π).comp
      (rangeTwistInclusion θ hθ π).toContinuousLinearMap =
      ((rangeTwistInclusion θ hθ π).comp (π.action g).toLinearIsometry).toContinuousLinearMap := by
    ext x
    change (rangeTwist θ hθ π).action ((MonoidHom.ofInjective hθ) g) x = π.action g x
    rw [rangeTwist_action]
    rfl
  rw [ha]
  rfl

theorem shiftVector_displacement (ht : ∀ g, f (θ g) * t = t * f g)
    (π : FiniteUnitaryRep.{u,u} Γ) (u : Δ → unitary B) (g : Γ) (ξ : TensorHilbert E π) :
    ‖matchingTuple ρ (fun h : θ.range => u (f h)) (rangeTwist θ hθ π)
      ((MonoidHom.ofInjective hθ) g) (shiftVector ρ θ hθ π (u t) ξ) -
      shiftVector ρ θ hθ π (u t) ξ‖ ≤
    (‖(u (f (θ g)*t) : B) - (u (f (θ g)) : B)*(u t : B)‖ +
      ‖(u (t*f g) : B) - (u t : B)*(u (f g) : B)‖) * ‖ξ‖ +
      ‖matchingTuple ρ (fun g => u (f g)) π g ξ - ξ‖ := by
  have he := congrArg (fun T : TensorHilbert E π →L[ℂ] TensorHilbert E (rangeTwist θ hθ π) => T ξ)
    (shiftVector_action_map ρ f θ hθ t π u g)
  change matchingTuple ρ (fun h : θ.range => u (f h)) (rangeTwist θ hθ π)
      ((MonoidHom.ofInjective hθ) g) (shiftVector ρ θ hθ π (u t) ξ) = _ at he
  rw [he]
  have hb := tensor_covariance_bound (ρ (u (f (θ g))) * ρ (u t)) (ρ (u (f g)))
    (representedUnitary ρ (u t)).toLinearIsometry (π.action g).toLinearIsometry
    (rangeTwistInclusion θ hθ π) ξ
  have hd := represented_product_defect ρ u (f (θ g)) t t (f g) (ht g)
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg ξ)) le_rfl)

end Shift
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section InductionApprox
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

theorem inductionTerm_displacement (g : Γ) (i : Γ ⧸ H) (η : TensorHilbert E α) :
    ‖matchingTuple ρ u (finiteInduced H α) g (inductionTerm H α ρ u i η) -
      inductionTerm H α ρ u (g • i) η‖ ≤
    (‖(u (g*cosetRep H i) : B) - (u g : B)*(u (cosetRep H i) : B)‖ +
      ‖(u (cosetRep H (g • i)*(cosetCocycle H g i : Γ)) : B) -
        (u (cosetRep H (g • i)) : B)*(u (cosetCocycle H g i) : B)‖) * ‖η‖ +
      ‖matchingTuple ρ (fun h : H => u h) α (cosetCocycle H g i) η - η‖ := by
  rw [inductionTerm_action]
  have ht := tensor_covariance_bound
    (ρ (u g) * ρ (u (cosetRep H i))) (ρ (u (cosetCocycle H g i)))
    (representedUnitary ρ (u (cosetRep H (g • i)))).toLinearIsometry
    (α.action (cosetCocycle H g i)).toLinearIsometry (inducedCoordinate H α (g • i)) η
  have hm := represented_product_defect ρ u g (cosetRep H i)
    (cosetRep H (g • i)) (cosetCocycle H g i) (cosetCocycle_factor H g i)
  apply ht.trans
  exact add_le_add (mul_le_mul_of_nonneg_right hm (norm_nonneg η)) le_rfl

theorem inductionSeed_displacement (g : Γ) (η : TensorHilbert E α) :
    ‖matchingTuple ρ u (finiteInduced H α) g (inductionSeed H α ρ u η) -
      inductionSeed H α ρ u η‖ ≤
      ∑ i : Γ ⧸ H, ‖matchingTuple ρ u (finiteInduced H α) g (inductionTerm H α ρ u i η) -
        inductionTerm H α ρ u (g • i) η‖ := by
  classical
  have he : (∑ i : Γ ⧸ H, inductionTerm H α ρ u (g • i) η) = inductionSeed H α ρ u η := by
    exact Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm (Γ ⧸ H)) (fun i => inductionTerm H α ρ u i η)
  change (∑ i : Γ ⧸ H, inductionTerm H α ρ u (g • i) η) = ∑ i : Γ ⧸ H, inductionTerm H α ρ u i η at he
  rw [inductionSeed, map_sum, ← he, ← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

end InductionApprox

section Limits
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : ℕ → FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → ℕ → unitary B)
  (ω : Ultrafilter ℕ) (η : ∀ n, TensorHilbert E (α n))

theorem inductionSeed_almostInvariant
    (hη : ∀ n, ‖η n‖ = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (hinv : ∀ h : H, Tendsto (fun n =>
      ‖matchingTuple ρ (fun h : H => u h n) (α n) h (η n) - η n‖)
        (ω : Filter ℕ) (𝓝 0)) (g : Γ) :
    Tendsto (fun n => ‖matchingTuple ρ (fun g => u g n) (finiteInduced H (α n)) g
      (inductionSeed H (α n) ρ (fun g => u g n) (η n)) -
        inductionSeed H (α n) ρ (fun g => u g n) (η n)‖) (ω : Filter ℕ) (𝓝 0) := by
  have hi (i : Γ ⧸ H) : Tendsto (fun n =>
      ‖matchingTuple ρ (fun g => u g n) (finiteInduced H (α n)) g
        (inductionTerm H (α n) ρ (fun g => u g n) i (η n)) -
        inductionTerm H (α n) ρ (fun g => u g n) (g • i) (η n)‖)
        (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (inductionTerm_displacement H (α n) ρ (fun g => u g n) g i (η n)))
    simp_rw [hη, mul_one]
    simpa only [add_zero] using ((hmul g (cosetRep H i)).add
      (hmul (cosetRep H (g • i)) (cosetCocycle H g i)) |>.add (hinv (cosetCocycle H g i)))
  apply squeeze_zero (fun n => norm_nonneg _) (fun n =>
    inductionSeed_displacement H (α n) ρ (fun g => u g n) g (η n))
  simpa using tendsto_finsetSum Finset.univ (fun i _ => hi i)
end Limits
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
theorem Matches.exists_irreducible {a : ℝ} (π : FiniteUnitaryRep.{u,v} Γ)
    (hm : Matches ρ S u a π) :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π ∧ Matches ρ S u a τ := by
  classical
  suffices hall : ∀ n : ℕ, ∀ π : FiniteUnitaryRep.{u,v} Γ,
      Module.finrank ℂ π = n → Matches ρ S u a π →
      ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π ∧ Matches ρ S u a τ by
    exact hall _ π rfl hm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro π hn hm
    by_cases hi : π.Irreducible
    · exact ⟨π,hi,FiniteUnitaryRep.embeds_refl π,hm⟩
    unfold FiniteUnitaryRep.Irreducible at hi
    push Not at hi
    obtain ⟨W,hW,hWb,hWt⟩ := hi
    let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWb
    let : Nontrivial Wᗮ := Submodule.nontrivial_iff_ne_bot.mpr
      (mt W.orthogonal_eq_bot_iff.mp hWt)
    have hd := W.finrank_add_finrank_orthogonal
    have hp1 : 0 < Module.finrank ℂ W := Module.finrank_pos
    have hp2 : 0 < Module.finrank ℂ Wᗮ := Module.finrank_pos
    have hwlt : Module.finrank ℂ (π.restrict W hW) < n := by
      change Module.finrank ℂ W < n
      omega
    have hplt : Module.finrank ℂ (π.restrict Wᗮ (π.orthogonal_invariant W hW)) < n := by
      change Module.finrank ℂ Wᗮ < n
      omega
    obtain ⟨x,hx⟩ := (matches_iff_homogeneous ρ S u a π).mp hm
    have he := tensor_projection_energy ρ S u π W hW x
    have hn' := tensorProjection_norm_sq (E := E) W x
    have hor :
        tupleEnergy S (matchingTuple ρ u (π.restrict W hW)) (tensorProjection (E := E) W x) <
          a * ‖tensorProjection (E := E) W x‖^2 ∨
        tupleEnergy S (matchingTuple ρ u (π.restrict Wᗮ (π.orthogonal_invariant W hW)))
          (tensorProjection (E := E) Wᗮ x) < a * ‖tensorProjection (E := E) Wᗮ x‖^2 := by
      rw [he, hn', mul_add] at hx
      exact lt_or_lt_of_add_lt_add hx
    rcases hor with hleft | hright
    · have hmW := (matches_iff_homogeneous ρ S u a (π.restrict W hW)).mpr ⟨_,hleft⟩
      obtain ⟨τ,hτ,hU,hmτ⟩ := ih _ hwlt (π.restrict W hW) rfl hmW
      exact ⟨τ,hτ,hU.trans (π.restrict_embeds W hW),hmτ⟩
    · have hmW := (matches_iff_homogeneous ρ S u a
        (π.restrict Wᗮ (π.orthogonal_invariant W hW))).mpr ⟨_,hright⟩
      obtain ⟨τ,hτ,hU,hmτ⟩ := ih _ hplt (π.restrict Wᗮ (π.orthogonal_invariant W hW)) rfl hmW
      exact ⟨τ,hτ,hU.trans (π.restrict_embeds Wᗮ (π.orthogonal_invariant W hW)),hmτ⟩

end NuclearUltrapower
end
end

end OAI
