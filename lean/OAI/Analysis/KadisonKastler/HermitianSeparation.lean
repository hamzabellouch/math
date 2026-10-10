import OAI.Analysis.KadisonKastler.HermitianAnnihilatorBall
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient

namespace OAI

/-! # Separating a self-adjoint element from a closed star subalgebra

Hahn–Banach on the Banach-space quotient gives a norm-one functional
annihilating the source. Its Hermitian part still separates a self-adjoint
element. The compact annihilator ball then supplies an extreme separator.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def conjugateFunctional (f : B →L[ℂ] ℂ) : B →L[ℂ] ℂ where
  toFun b := star (f (star b))
  map_add' x y := by simp
  map_smul' c x := by simp
  cont := continuous_star.comp (f.continuous.comp continuous_star)

theorem conjugateFunctional_norm_le (f : B →L[ℂ] ℂ) : ‖conjugateFunctional f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro b
  change ‖star (f (star b))‖ ≤ ‖f‖ * ‖b‖
  rw [norm_star, ← norm_star b]
  exact f.le_opNorm (star b)

theorem exists_hermitian_separator (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (b : B) (hb : IsSelfAdjoint b)
    (hnot : b ∉ Set.range φ) :
    ∃ f ∈ hermitianAnnihilatorBall φ, f b ≠ 0 := by
  let P := φ.range.toSubalgebra.toSubmodule
  have hclosed : IsClosed (P : Set B) :=
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
  let : IsClosed (P : Set B) := hclosed
  let q : B →L[ℂ] (B ⧸ P) := P.mkQ.mkContinuous 1 (fun x => by
    change ‖(Submodule.Quotient.mk x : B ⧸ P)‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le P x)
  have hqb : q b ≠ 0 := by
    intro hz
    apply hnot
    exact (Submodule.Quotient.mk_eq_zero P).mp hz
  obtain ⟨g, hgn, hgb⟩ := exists_dual_vector ℂ (q b) (norm_ne_zero_iff.mpr hqb)
  let f₀ := g.comp q
  have hf₀ : ‖f₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖g (q x)‖ ≤ 1 * ‖x‖
    calc
      _ ≤ ‖g‖ * ‖q x‖ := g.le_opNorm _
      _ ≤ 1 * ‖x‖ := by
        rw [hgn, one_mul, one_mul]
        exact Submodule.Quotient.norm_mk_le P x
  have hann (a : A) : f₀ (φ a) = 0 := by
    have hz : q (φ a) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr ⟨a, rfl⟩
    change g (q (φ a)) = 0
    rw [hz, map_zero]
  let F : B →L[ℂ] ℂ := (1 / 2 : ℂ) • (f₀ + conjugateFunctional f₀)
  have hF : ‖F‖ ≤ 1 := by
    calc
      ‖F‖ = (1 / 2 : ℝ) * ‖f₀ + conjugateFunctional f₀‖ := by
        dsimp only [F]
        rw [norm_smul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (‖f₀‖ + ‖conjugateFunctional f₀‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ 1 := by linarith [conjugateFunctional_norm_le f₀]
  refine ⟨StrongDual.toWeakDual F, ⟨hF, ?_, ?_⟩, ?_⟩
  · intro x
    change (1 / 2 : ℂ) • (f₀ (star x) + star (f₀ (star (star x)))) =
      star ((1 / 2 : ℂ) • (f₀ x + star (f₀ (star x))))
    simp only [star_smul, star_add, star_star]
    norm_num
    ring
  · intro a
    change (1 / 2 : ℂ) • (f₀ (φ a) + star (f₀ (star (φ a)))) = 0
    rw [← map_star φ, hann, hann, star_zero, zero_add, smul_zero]
  · have hval : F b = (‖q b‖ : ℂ) := by
      change (1 / 2 : ℂ) • (f₀ b + star (f₀ (star b))) = _
      rw [hb.star_eq]
      change (1 / 2 : ℂ) • (g (q b) + star (g (q b))) = _
      rw [hgb]
      rw [RCLike.star_def, RCLike.conj_ofReal]
      change (1 / 2 : ℂ) * ((‖q b‖ : ℂ) + (‖q b‖ : ℂ)) = _
      ring
    change F b ≠ 0
    rw [hval]
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hqb)

theorem exists_extreme_hermitian_separator (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (b : B) (hb : IsSelfAdjoint b)
    (hnot : b ∉ Set.range φ) :
    ∃ f ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ,
      ‖f.toStrongDual‖ = 1 ∧ f b ≠ 0 :=
  exists_extreme_hermitian_annihilator φ b (exists_hermitian_separator φ hφ b hb hnot)

end

end KadisonKastler

end OAI
