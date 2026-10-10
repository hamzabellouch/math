import OAI.Analysis.KadisonSimilarity.Representation.DominatedVectorRealization

namespace OAI

/-! The polar isometry of an injective bounded intertwiner. This form allows
different source and target Hilbert spaces, as needed for closed cyclic
graphs in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An injective bounded intertwiner has an isometric polar part, even when
its range is not closed. -/
theorem isometry_of_injective_intertwiner
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (hLi : Function.Injective L)
    (hL : ∀ a, L.comp (σ a) = (ρ a).comp L) :
    ∃ J : H →ₗᵢ[ℂ] K,
      (∀ a, J.toContinuousLinearMap.comp (σ a) = (ρ a).comp J.toContinuousLinearMap) ∧
      Set.range L ⊆ Set.range J := by
  let R : H →L[ℂ] H := L.adjoint.comp L
  have hR : 0 ≤ R :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr L.isPositive_adjoint_comp_self
  let S : H →L[ℂ] H := CFC.sqrt R
  have hS : S.adjoint = S := (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
  have hSS : S.comp S = R := CFC.sqrt_mul_sqrt_self R hR
  have hn (x : H) : ‖S x‖ = ‖L x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hS, hSS]
  have hSk : S.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    change S x = S y at hxy
    apply hLi
    apply sub_eq_zero.mp
    rw [← L.map_sub, ← norm_eq_zero, ← hn, S.map_sub, hxy, sub_self, norm_zero]
  have hd : DenseRange S := by
    have ht : S.range.topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure,
        ContinuousLinearMap.orthogonal_range, hS, hSk, Submodule.bot_orthogonal_eq_top]
    intro x
    change x ∈ S.range.topologicalClosure
    rw [ht]
    trivial
  let J : H →ₗᵢ[ℂ] K := L.toLinearMap.extendOfIsometry (e := S.toLinearMap) hd
    (fun x => (hn x).symm)
  have he (x : H) : J (S x) = L x :=
    LinearMap.extendOfIsometry_eq L.toLinearMap hd (fun x => (hn x).symm) x
  have hLa (a : A) : (σ a).comp L.adjoint = L.adjoint.comp (ρ a) := by
    have h := congrArg ContinuousLinearMap.adjoint (hL (star a))
    simpa only [ContinuousLinearMap.adjoint_comp, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h
  have hRc (a : A) : Commute R (σ a) := by
    change (L.adjoint.comp L).comp (σ a) = (σ a).comp (L.adjoint.comp L)
    rw [ContinuousLinearMap.comp_assoc, hL a,
      ← ContinuousLinearMap.comp_assoc, ← hLa a, ContinuousLinearMap.comp_assoc]
  have hSc (a : A) : S.comp (σ a) = (σ a).comp S :=
    (hRc a).cfcₙ_nnreal NNReal.sqrt
  refine ⟨J, fun a => ?_, ?_⟩
  · ext x
    refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro y
    change J (σ a (S y)) = ρ a (J (S y))
    rw [← show S (σ a y) = σ a (S y) from
      congrArg (fun T : H →L[ℂ] H => T y) (hSc a), he, he]
    exact congrArg (fun T : H →L[ℂ] K => T y) (hL a)
  · rintro _ ⟨x, rfl⟩
    exact ⟨S x, he x⟩

/-- A closed correspondence with injective first coordinate and dense second
coordinate gives an isometric embedding of its second representation into
its first. This is the operator step for a closable cyclic graph. -/
theorem isometry_of_injective_dense_correspondence
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (ν : A →⋆ₐ[ℂ] (Q →L[ℂ] Q))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (X : Q →L[ℂ] H) (Y : Q →L[ℂ] K)
    (hX : Function.Injective X) (hY : DenseRange Y)
    (hXν : ∀ a, X.comp (ν a) = (σ a).comp X)
    (hYν : ∀ a, Y.comp (ν a) = (ρ a).comp Y) :
    ∃ J : K →ₗᵢ[ℂ] H, ∀ a,
      J.toContinuousLinearMap.comp (ρ a) = (σ a).comp J.toContinuousLinearMap := by
  have ht : Y.range.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hY
  have hYi : Function.Injective Y.adjoint := by
    apply LinearMap.ker_eq_bot.mp
    rw [← ContinuousLinearMap.orthogonal_range,
      ← Submodule.orthogonal_closure, ht, Submodule.top_orthogonal_eq_bot]
  have hYa (a : A) : Y.adjoint.comp (ρ a) = (ν a).comp Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint (hYν (star a))
    simpa only [ContinuousLinearMap.adjoint_comp, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h.symm
  obtain ⟨J₁, hJ₁, -⟩ := isometry_of_injective_intertwiner ν σ X hX hXν
  obtain ⟨J₂, hJ₂, -⟩ := isometry_of_injective_intertwiner ρ ν Y.adjoint hYi hYa
  refine ⟨J₁.comp J₂, fun a => ?_⟩
  change (J₁.toContinuousLinearMap.comp J₂.toContinuousLinearMap).comp (ρ a) =
    (σ a).comp (J₁.toContinuousLinearMap.comp J₂.toContinuousLinearMap)
  rw [ContinuousLinearMap.comp_assoc, hJ₂ a,
    ← ContinuousLinearMap.comp_assoc, hJ₁ a, ContinuousLinearMap.comp_assoc]

end KadisonSimilarity

end

end OAI
