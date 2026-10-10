import OAI.Geometry.SurfaceImmersion.Primitive.VelocityAngleInterpolation
import OAI.Geometry.SurfaceImmersion.Whitney.ArcDensityLocal

namespace OAI

/-! Smooth transition paths and their strict convex-hull margin. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def blendedPath (a A s h t : ℝ) : LoopDensity.Plane :=
  ![Real.cos (blendedAngle a A s h (2 * Real.pi * t)),
    Real.sin (blendedAngle a A s h (2 * Real.pi * t))]

lemma blendedPath_periodic (a A s h : ℝ) : Function.Periodic (blendedPath a A s h) 1 := by
  intro t
  simp [blendedPath, blendedAngle, baseAngle, mul_add, Real.cos_add_two_pi]

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma blendedPath_smooth {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : B × ℝ => blendedPath (a z.1) (A z.1) (s z.1) (h z.1) z.2) := by
  have hangle : ContDiff ℝ ∞ (fun z : B × ℝ =>
      blendedAngle (a z.1) (A z.1) (s z.1) (h z.1) (2 * Real.pi * z.2)) := by
    have hb : ContDiff ℝ ∞ (fun z : B × ℝ => baseAngle (a z.1) (2 * Real.pi * z.2)) :=
      baseAngle_smooth.comp ((ha.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
    exact ((hh.comp contDiff_fst).add
      ((contDiff_const.sub (hs.comp contDiff_fst)).mul hb)).add
        ((hs.comp contDiff_fst).mul ((hA.comp contDiff_fst).mul
          (contDiff_const.mul contDiff_snd).cos))
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hangle.cos
  · exact hangle.sin

lemma blendedPath_covers {a A s β : ℝ}
    (hβ : β ∈ Ioo (-((1 - s) * (2 * Real.arctan a) + s * A))
      ((1 - s) * (2 * Real.arctan a) + s * A)) :
    ∃ t ∈ Ioo (0 : ℝ) 1, blendedPath a A s 0 t = ![Real.cos β, Real.sin β] := by
  have hf : Continuous (blendedAngle a A s 0) := by
    unfold blendedAngle baseAngle
    fun_prop
  have hmem : β ∈ Icc (blendedAngle a A s 0 Real.pi) (blendedAngle a A s 0 0) := by
    rw [blendedAngle_pi, blendedAngle_zero]
    simpa only [zero_add, zero_sub] using ⟨hβ.1.le, hβ.2.le⟩
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' Real.pi_pos.le hf.continuousOn hmem
  have hu0 : 0 < u := by
    by_contra hn
    have hz : u = 0 := le_antisymm (le_of_not_gt hn) hu.1
    rw [hz, blendedAngle_zero, zero_add] at heq
    linarith [hβ.2]
  have huπ : u < Real.pi := by
    by_contra hn
    have hz : u = Real.pi := le_antisymm hu.2 (le_of_not_gt hn)
    rw [hz, blendedAngle_pi, zero_sub] at heq
    linarith [hβ.1]
  refine ⟨u / (2 * Real.pi), ⟨div_pos hu0 (by positivity), ?_⟩, ?_⟩
  · apply (div_lt_one (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.pi_pos]
  · have hsimp : 2 * Real.pi * (u / (2 * Real.pi)) = u := by field_simp
    simp only [blendedPath, hsimp, heq]

lemma collar_mean_arc_margin {a : ℝ} (ha : 0 < a) :
    Real.arccos ((1 - a ^ 2 / 2) / (1 + a ^ 2 / 2)) < 2 * Real.arctan a := by
  have hd : 0 < 1 + a ^ 2 := by positivity
  have hd' : 0 < 1 + a ^ 2 / 2 := by positivity
  have hsq : 0 < a ^ 2 := sq_pos_of_pos ha
  have hcos : Real.cos (2 * Real.arctan a) = (1 - a ^ 2) / (1 + a ^ 2) := by
    simpa [baseAngle, arcX] using cos_baseAngle a 0
  have hlt : (1 - a ^ 2) / (1 + a ^ 2) < (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
    apply (div_lt_div_iff₀ hd hd').mpr
    nlinarith
  have hangle0 : 0 ≤ 2 * Real.arctan a := by
    have := Real.arctan_pos.mpr ha
    positivity
  have hangleπ : 2 * Real.arctan a ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two a
    linarith
  have hm1 : (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) ≤ 1 := by
    apply (div_le_one hd').mpr
    linarith
  have hleft : -1 ≤ Real.cos (2 * Real.arctan a) := Real.neg_one_le_cos _
  have hh := Real.arccos_lt_arccos hleft (hcos ▸ hlt) hm1
  rwa [Real.arccos_cos hangle0 hangleπ] at hh

theorem blended_positive_density_near [FiniteDimensional ℝ B]
    {a A s h : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (ha₀ : 0 < a b₀) (hA₀ : 2 * Real.arctan (a b₀) ≤ A b₀)
    (hs₀ : s b₀ ∈ Icc (0 : ℝ) 1) (hh₀ : h b₀ = 0)
    (hc₀ : c b₀ = ![(1 - a b₀ ^ 2 / 2) / (1 + a b₀ ^ 2 / 2), 0]) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) = LoopDensity.augment (c b) := by
  have hd : 0 < 1 + a b₀ ^ 2 / 2 := by positivity
  have hsq : 0 < a b₀ ^ 2 := sq_pos_of_pos ha₀
  have hml : -1 < (1 - a b₀ ^ 2 / 2) / (1 + a b₀ ^ 2 / 2) := by
    apply (lt_div_iff₀ hd).mpr
    linarith
  have hmu : (1 - a b₀ ^ 2 / 2) / (1 + a b₀ ^ 2 / 2) < 1 := by
    apply (div_lt_one hd).mpr
    linarith
  have hamplitude : 2 * Real.arctan (a b₀) ≤
      (1 - s b₀) * (2 * Real.arctan (a b₀)) + s b₀ * A b₀ := by
    nlinarith [mul_nonneg hs₀.1 (sub_nonneg.mpr hA₀)]
  apply LoopDensity.positive_density_near_of_arc_coverage (blendedPath_smooth ha hA hs hh)
    hc hc₀ hml hmu (lt_of_lt_of_le (collar_mean_arc_margin ha₀) hamplitude)
  intro β hβ
  rw [hh₀]
  exact blendedPath_covers hβ

end ClosedSurfaceR4.CollarVelocity

end

end OAI
