import OAI.Analysis.KadisonSimilarity.Derivation.CyclicStandardEmbedding
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! Vector functionals dominated on a cyclic orbit are realized in that
cyclic representation. The square root of the positive intertwiner supplies
the vector, so no Radon--Nikodym theorem is assumed for this bounded case. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pull a vector functional back along a bounded intertwiner by its absolute
value. This is the bounded part of the standard-form construction. -/
theorem vector_realization_of_intertwiner
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K)
    (hL : ∀ a, L.comp (σ a) = (ρ a).comp L) (Ω : H) :
    ∃ η : H, ∀ a, inner ℂ η (σ a η) = inner ℂ (L Ω) (ρ a (L Ω)) := by
  let R : H →L[ℂ] H := L.adjoint.comp L
  have hR : 0 ≤ R :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr L.isPositive_adjoint_comp_self
  have hLa (a : A) : (σ a).comp L.adjoint = L.adjoint.comp (ρ a) := by
    have h := congrArg ContinuousLinearMap.adjoint (hL (star a))
    simpa only [ContinuousLinearMap.adjoint_comp, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h
  have hRc (a : A) : Commute R (σ a) := by
    change (L.adjoint.comp L).comp (σ a) = (σ a).comp (L.adjoint.comp L)
    rw [ContinuousLinearMap.comp_assoc, hL a,
      ← ContinuousLinearMap.comp_assoc, ← hLa a, ContinuousLinearMap.comp_assoc]
  let S : H →L[ℂ] H := CFC.sqrt R
  have hS : S.adjoint = S := (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
  have hSS : S.comp S = R := CFC.sqrt_mul_sqrt_self R hR
  have hSc (a : A) : S.comp (σ a) = (σ a).comp S :=
    (hRc a).cfcₙ_nnreal NNReal.sqrt
  refine ⟨S Ω, fun a => ?_⟩
  calc
    inner ℂ (S Ω) (σ a (S Ω)) = inner ℂ (S Ω) (S (σ a Ω)) := by
      rw [show σ a (S Ω) = S (σ a Ω) from
        (congrArg (fun T : H →L[ℂ] H => T Ω) (hSc a)).symm]
    _ = inner ℂ Ω (S.adjoint (S (σ a Ω))) :=
      (ContinuousLinearMap.adjoint_inner_right S Ω (S (σ a Ω))).symm
    _ = inner ℂ Ω (R (σ a Ω)) := by
      rw [hS, ← ContinuousLinearMap.comp_apply, hSS]
    _ = inner ℂ (L Ω) (L (σ a Ω)) :=
      ContinuousLinearMap.adjoint_inner_right L Ω (L (σ a Ω))
    _ = inner ℂ (L Ω) (ρ a (L Ω)) := by
      rw [show L (σ a Ω) = ρ a (L Ω) from
        congrArg (fun T : H →L[ℂ] K => T Ω) (hL a)]

/-- A norm bound on the dense cyclic orbit constructs the required bounded
intertwiner and hence realizes the dominated vector functional. -/
theorem vector_realization_of_cyclic_domination
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (hΩ : DenseRange (fun a : A => σ a Ω))
    (hbound : ∃ C : ℝ, ∀ a : A, ‖ρ a ξ‖ ≤ C * ‖σ a Ω‖) :
    ∃ η : H, ∀ a, inner ℂ η (σ a η) = inner ℂ ξ (ρ a ξ) := by
  let e : A →ₗ[ℂ] H :=
    { toFun := fun a => σ a Ω
      map_add' a b := by simp
      map_smul' c a := by simp }
  let f : A →ₗ[ℂ] K :=
    { toFun := fun a => ρ a ξ
      map_add' a b := by simp
      map_smul' c a := by simp }
  have hd : DenseRange e := hΩ
  have hn : ∃ C : ℝ, ∀ a : A, ‖f a‖ ≤ C * ‖e a‖ := hbound
  let L : H →L[ℂ] K := f.extendOfNorm e
  have he (a : A) : L (e a) = f a :=
    LinearMap.extendOfNorm_eq hd hn a
  have hL (a : A) : L.comp (σ a) = (ρ a).comp L := by
    ext x
    refine hΩ.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro b
    change L (σ a (e b)) = ρ a (L (e b))
    have hab : σ a (e b) = e (a * b) := by
      change σ a (σ b Ω) = σ (a * b) Ω
      rw [map_mul]
      rfl
    rw [hab, he, he]
    change ρ (a * b) ξ = ρ a (ρ b ξ)
    rw [map_mul]
    rfl
  have hLΩ : L Ω = ξ := by
    have h := he 1
    change L (σ 1 Ω) = ρ 1 ξ at h
    simpa only [map_one, one_apply_eq_self] using h
  obtain ⟨η, hη⟩ := vector_realization_of_intertwiner σ ρ L hL Ω
  exact ⟨η, fun a => by simpa only [hLΩ] using hη a⟩

end KadisonSimilarity

end

end OAI
