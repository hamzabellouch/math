import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution

namespace OAI

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]
variable {P₂ P₁ P₀ Q₃ Q₂ Q₁ : Type u}
variable [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup Q₃] [Module R Q₃]
variable [AddCommGroup Q₂] [Module R Q₂] [AddCommGroup Q₁] [Module R Q₁]

theorem extend_homotopy_up [Module.Projective R P₂]
    (p₂ : P₂ →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] P₀) (hp : p₁.comp p₂ = 0)
    (q₃ : Q₃ →ₗ[R] Q₂) (q₂ : Q₂ →ₗ[R] Q₁)
    (hq : LinearMap.range q₃ = LinearMap.ker q₂)
    (f₂ : P₂ →ₗ[R] Q₂) (f₁ : P₁ →ₗ[R] Q₁)
    (hc : q₂.comp f₂ = f₁.comp p₂)
    (h₁ : P₁ →ₗ[R] Q₂) (h₀ : P₀ →ₗ[R] Q₁)
    (hh : f₁ = q₂.comp h₁ + h₀.comp p₁) :
    ∃ h₂ : P₂ →ₗ[R] Q₃, f₂ = q₃.comp h₂ + h₁.comp p₂ := by
  have hz : q₂.comp (f₂ - h₁.comp p₂) = 0 := by
    ext x
    have hc' : q₂ (f₂ x) = f₁ (p₂ x) := DFunLike.congr_fun hc x
    have hh' : f₁ (p₂ x) = q₂ (h₁ (p₂ x)) + h₀ (p₁ (p₂ x)) :=
      DFunLike.congr_fun hh (p₂ x)
    have hp' : p₁ (p₂ x) = 0 := DFunLike.congr_fun hp x
    change q₂ (f₂ x - h₁ (p₂ x)) = 0
    rw [map_sub, hc', hh', hp', map_zero, add_zero, sub_self]
  obtain ⟨h₂, hh₂⟩ := lift_through_exact q₃ q₂ hq (f₂ - h₁.comp p₂) hz
  exact ⟨h₂, by rw [hh₂, sub_add_cancel]⟩

theorem extend_homotopy_down [Module.Finite R Q₁] [Module.Projective R Q₁]
    (p₂ : P₂ →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] P₀) (hp : HomExactAt p₂ p₁)
    (q₃ : Q₃ →ₗ[R] Q₂) (q₂ : Q₂ →ₗ[R] Q₁) (hq : q₂.comp q₃ = 0)
    (f₂ : P₂ →ₗ[R] Q₂) (f₁ : P₁ →ₗ[R] Q₁)
    (hc : q₂.comp f₂ = f₁.comp p₂)
    (h₂ : P₂ →ₗ[R] Q₃) (h₁ : P₁ →ₗ[R] Q₂)
    (hh : f₂ = q₃.comp h₂ + h₁.comp p₂) :
    ∃ h₀ : P₀ →ₗ[R] Q₁, f₁ = q₂.comp h₁ + h₀.comp p₁ := by
  have hz : (f₁ - q₂.comp h₁).comp p₂ = 0 := by
    ext x
    have hc' : f₁ (p₂ x) = q₂ (f₂ x) := (DFunLike.congr_fun hc x).symm
    have hh' : f₂ x = q₃ (h₂ x) + h₁ (p₂ x) := DFunLike.congr_fun hh x
    have hq' : q₂ (q₃ (h₂ x)) = 0 := DFunLike.congr_fun hq (h₂ x)
    change f₁ (p₂ x) - q₂ (h₁ (p₂ x)) = 0
    rw [hc', hh', map_add, hq', zero_add, sub_self]
  obtain ⟨h₀, hh₀⟩ := hp.projective (f₁ - q₂.comp h₁) hz
  refine ⟨h₀, ?_⟩
  rw [hh₀]
  abel

theorem initial_homotopy_of_factorization
    [Module.Projective R P₁] [Module.Finite R Q₁] [Module.Projective R Q₁]
    (e : P₂ →ₗ[R] P₁) (d : P₁ →ₗ[R] P₀) (hd : HomExactAt e d)
    (e' : Q₃ →ₗ[R] Q₂) (f : P₁ →ₗ[R] Q₂)
    (a : (P₁ ⧸ LinearMap.range e) →ₗ[R] Q₁)
    (b : Q₁ →ₗ[R] (Q₂ ⧸ LinearMap.range e'))
    (hf : (LinearMap.range e').mkQ.comp f =
      b.comp (a.comp (LinearMap.range e).mkQ)) :
    ∃ (h₀ : P₀ →ₗ[R] Q₂) (h₁ : P₁ →ₗ[R] Q₃),
      f = e'.comp h₁ + h₀.comp d := by
  have ha : (a.comp (LinearMap.range e).mkQ).comp e = 0 := by
    ext x
    change a ((LinearMap.range e).mkQ (e x)) = 0
    rw [show (LinearMap.range e).mkQ (e x) = 0 by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]
  obtain ⟨A, hA⟩ := hd.projective (a.comp (LinearMap.range e).mkQ) ha
  obtain ⟨B, hB⟩ := Module.projective_lifting_property (LinearMap.range e').mkQ b
    (Submodule.mkQ_surjective _)
  have hz : (LinearMap.range e').mkQ.comp (f - (B.comp A).comp d) = 0 := by
    ext x
    have hf' : (LinearMap.range e').mkQ (f x) =
        b (a ((LinearMap.range e).mkQ x)) := DFunLike.congr_fun hf x
    have hB' : (LinearMap.range e').mkQ (B (A (d x))) = b (A (d x)) :=
      DFunLike.congr_fun hB (A (d x))
    have hA' : A (d x) = a ((LinearMap.range e).mkQ x) := DFunLike.congr_fun hA x
    change (LinearMap.range e').mkQ (f x - B (A (d x))) = 0
    rw [map_sub, hf', hB', hA', sub_self]
  obtain ⟨h₁, hh₁⟩ := lift_through_exact e' (LinearMap.range e').mkQ
    (Submodule.ker_mkQ _).symm (f - (B.comp A).comp d) hz
  exact ⟨B.comp A, h₁, by rw [hh₁, sub_add_cancel]⟩

theorem factorization_of_initial_homotopy
    (e : P₂ →ₗ[R] P₁) (d : P₁ →ₗ[R] P₀) (hd : d.comp e = 0)
    (e' : Q₃ →ₗ[R] Q₂) (f : P₁ →ₗ[R] Q₂)
    (u : (P₁ ⧸ LinearMap.range e) →ₗ[R] (Q₂ ⧸ LinearMap.range e'))
    (hu : (LinearMap.range e').mkQ.comp f = u.comp (LinearMap.range e).mkQ)
    (h₀ : P₀ →ₗ[R] Q₂) (h₁ : P₁ →ₗ[R] Q₃)
    (hh : f = e'.comp h₁ + h₀.comp d) :
    ∃ (a : (P₁ ⧸ LinearMap.range e) →ₗ[R] P₀)
      (b : P₀ →ₗ[R] (Q₂ ⧸ LinearMap.range e')), b.comp a = u := by
  have he : LinearMap.range e ≤ LinearMap.ker d := by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hd x
  let a : (P₁ ⧸ LinearMap.range e) →ₗ[R] P₀ := (LinearMap.range e).liftQ d he
  refine ⟨a, (LinearMap.range e').mkQ.comp h₀, ?_⟩
  apply LinearMap.ext
  intro t
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) t
  change (LinearMap.range e').mkQ (h₀ (d x)) = u ((LinearMap.range e).mkQ x)
  have hz : (LinearMap.range e').mkQ (e' (h₁ x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨h₁ x, rfl⟩
  calc
    (LinearMap.range e').mkQ (h₀ (d x)) =
        (LinearMap.range e').mkQ (e' (h₁ x) + h₀ (d x)) := by
      rw [map_add, hz, zero_add]
    _ = (LinearMap.range e').mkQ (f x) :=
      congrArg (LinearMap.range e').mkQ (DFunLike.congr_fun hh x).symm
    _ = u ((LinearMap.range e).mkQ x) := DFunLike.congr_fun hu x

end ArExplicit

end OAI
