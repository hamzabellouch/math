import OAI.Geometry.SurfaceImmersion.Primitive.CalibratedJetAngle

namespace OAI

/-! A small collar amplitude controls every angle after any clock change.
The collar and permitted translation size are fixed before prescribing turns. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.CollarVelocity

lemma abs_baseAngle_le (a t : ℝ) : |baseAngle a t| ≤ 2 * Real.arctan |a| := by
  have hab : |a * Real.cos t| ≤ |a| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one t)
  have hl := Real.arctan_strictMono.monotone (neg_le_of_abs_le hab)
  have hu := Real.arctan_strictMono.monotone (le_of_abs_le hab)
  rw [Real.arctan_neg] at hl
  rw [baseAngle,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hl,hu⟩) (by norm_num)

lemma abs_unitAngle_collar_le (a A h t : ℝ) :
    |unitAngle a A 0 h t| ≤ |h| + 2 * Real.arctan |a| := by
  calc
    |unitAngle a A 0 h t| = |h + baseAngle a (2 * Real.pi * t)| := by
      simp [unitAngle,blendedAngle]
    _ ≤ |h| + |baseAngle a (2 * Real.pi * t)| := abs_add_le _ _
    _ ≤ |h| + 2 * Real.arctan |a| := add_le_add_right (abs_baseAngle_le _ _) _

variable {E : Type} [NormedAddCommGroup E]

lemma small_collar_angle_window {C W : Set E} (hW : IsOpen W) (hCW : C ⊆ W)
    {b : E → ℝ} (hb : Continuous b) (hbC : ∀ x ∈ C, b x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ C ⊆ V ∧ V ⊆ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (A s h : E → ℝ) (ρ : E × ℝ → ℝ),
        (∀ x ∈ W, s x = 0) → (∀ x, |h x| < δ) →
        ∀ x ∈ V, ∀ t : ℝ,
        |PositiveDensity.reparametrize ρ
          (fun z => unitAngle (b z.1) (A z.1) (s z.1) (h z.1) z.2) (x,t)| < ε := by
  let V := W ∩ {x | 2 * Real.arctan |b x| < ε/2}
  have hV : IsOpen V := hW.inter (isOpen_lt
    (continuous_const.mul (Real.continuous_arctan.comp hb.abs)) continuous_const)
  have hCV : C ⊆ V := by
    intro x hx
    refine ⟨hCW hx,?_⟩
    simp only [mem_ofPred_eq,hbC x hx,abs_zero,Real.arctan_zero,mul_zero]
    positivity
  refine ⟨V,hV,hCV,inter_subset_left,ε/2,half_pos hε,?_⟩
  intro A s h ρ hs hh x hx t
  change |unitAngle (b x) (A x) (s x) (h x) (PositiveDensity.inverseClock ρ x t)| < ε
  rw [hs x hx.1]
  have hxsmall : 2 * Real.arctan |b x| < ε/2 := hx.2
  exact (abs_unitAngle_collar_le _ _ _ _).trans_lt (by linarith [hh x])

end ClosedSurfaceR4.CollarVelocity

end

end OAI
