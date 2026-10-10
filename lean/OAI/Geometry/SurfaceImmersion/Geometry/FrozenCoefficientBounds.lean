import OAI.Geometry.SurfaceImmersion.Geometry.FrozenBoundaryCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

namespace OAI

/-! The metric and first-normal bounds precede every choice of large angular
jet: they are uniform over the entire circle of angular values. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma frozenSize_pos {X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {x : E}
    (hD : gramDet (Y x) (C x) ≠ 0) (hR : R x ≠ 0)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (α : ℝ) : 0 < frozenSize X Y C R e₁ e₂ (x,α) := by
  apply normalSize_positive hD
  · simp [direction,dotProduct_smul,dotProduct_add,hframe.2.2.2.1,hframe.2.2.2.2.2.1]
  · simp [direction,dotProduct_smul,dotProduct_add,hframe.2.2.2.2.1,hframe.2.2.2.2.2.2]
  · apply smul_ne_zero hR
    intro he
    have hh := direction_unit hframe.1 hframe.2.1 hframe.2.2.1 α
    rw [he] at hh
    norm_num at hh

theorem compact_frozen_coefficient_bounds {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) (d : E) :
    ∃ sLo sHi B : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ B ∧ ∀ x ∈ K, ∀ α : ℝ,
      sLo ≤ frozenSize X Y C R e₁ e₂ (x,α) ∧
      frozenSize X Y C R e₁ e₂ (x,α) ≤ sHi ∧
      |frozenFirst Q X Y C R e₁ e₂ d (x,α)| ≤ B := by
  obtain ⟨hfirst,hsize⟩ := frozen_coefficients_smoothOn hU hQ hX hY hC hR h₁ h₂ hD hframe hR0 d
  let Z : Set (E × ℝ) := K ×ˢ Icc (-Real.pi) Real.pi
  have hZ : IsCompact Z := hK.prod isCompact_Icc
  have hZU : Z ⊆ U ×ˢ univ := fun z hz => ⟨hKU hz.1,mem_univ _⟩
  have hs : ContinuousOn (frozenSize X Y C R e₁ e₂) Z := hsize.continuousOn.mono hZU
  have hf : ContinuousOn (frozenFirst Q X Y C R e₁ e₂ d) Z := hfirst.continuousOn.mono hZU
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1,1,0,zero_lt_one,zero_lt_one,le_rfl,?_⟩
    simp [hempty]
  have hZne : Z.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,0),hx,by constructor <;> linarith [Real.pi_pos]⟩
  obtain ⟨z,hz,hmin⟩ := hZ.exists_isMinOn hZne hs
  obtain ⟨S,hS⟩ := hZ.exists_bound_of_continuousOn hs
  obtain ⟨B,hB⟩ := hZ.exists_bound_of_continuousOn hf
  refine ⟨frozenSize X Y C R e₁ e₂ z,max 1 S,max 0 B,
    frozenSize_pos (hD z.1 (hKU hz.1)) (hR0 z.1 (hKU hz.1)) (hframe z.1 (hKU hz.1)) z.2,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),le_max_left _ _,?_⟩
  intro x hx α
  let θ := (α : Real.Angle).toReal
  have hθ : θ ∈ Icc (-Real.pi) Real.pi :=
    ⟨(Real.Angle.toReal_mem_Ioc (α : Real.Angle)).1.le,(Real.Angle.toReal_mem_Ioc (α : Real.Angle)).2⟩
  have hcos : Real.cos θ = Real.cos α := (Real.Angle.cos_toReal _).trans (Real.Angle.cos_coe _)
  have hsin : Real.sin θ = Real.sin α := (Real.Angle.sin_toReal _).trans (Real.Angle.sin_coe _)
  have hsizeEq : frozenSize X Y C R e₁ e₂ (x,θ) = frozenSize X Y C R e₁ e₂ (x,α) := by
    simp only [frozenSize,direction,hcos,hsin]
  have hfirstEq : frozenFirst Q X Y C R e₁ e₂ d (x,θ) =
      frozenFirst Q X Y C R e₁ e₂ d (x,α) := by
    simp only [frozenFirst,frozenError,frozenNormal,direction,hcos,hsin]
  have hxθ : (x,θ) ∈ Z := ⟨hx,hθ⟩
  rw [← hsizeEq,← hfirstEq]
  exact ⟨hmin hxθ,(le_abs_self _).trans ((hS _ hxθ).trans (le_max_right _ _)),
    (hB _ hxθ).trans (le_max_right _ _)⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
