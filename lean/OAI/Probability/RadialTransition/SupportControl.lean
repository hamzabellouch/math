import OAI.Probability.RadialTransition.CanonicalCorner

namespace OAI

universe uE uY uI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section MoreSupportGeometry
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem supportsOn_of_local {F : E → ℝ} {D : Set E} {x v : E} {r : ℝ}
    (hF : ConvexOn ℝ D F) (hx : x ∈ D) (hr : 0 < r)
    (hlocal : SupportsOn F (D ∩ Metric.closedBall x r) x v) : SupportsOn F D x v := by
  intro y hy
  let a : ℝ := r / (r + ‖y - x‖ + 1)
  have hd : 0 < r + ‖y - x‖ + 1 := by positivity
  have ha : 0 < a := div_pos hr hd
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith [norm_nonneg (y - x)]
  have hae : a * (r + ‖y - x‖ + 1) = r := div_mul_cancel₀ _ hd.ne'
  have hab : a * ‖y - x‖ ≤ r := by
    nlinarith [mul_nonneg ha.le hr.le]
  let z := (1 - a) • x + a • y
  have hzD : z ∈ D := hF.1 hx hy (sub_nonneg.mpr ha1) ha.le (by ring)
  have hzx : z - x = a • (y - x) := by dsimp [z]; module
  have hzball : z ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact hab
  have hlo := hlocal z ⟨hzD, hzball⟩
  have hhi := hF.2 hx hy (sub_nonneg.mpr ha1) ha.le (show 1 - a + a = 1 by ring)
  change F z ≤ (1 - a) * F x + a * F y at hhi
  rw [hzx, real_inner_smul_right] at hlo
  nlinarith [mul_le_mul_of_nonneg_left (show 0 ≤ (0 : ℝ) from le_rfl) ha.le]

theorem nonempty_of_closedHull_nonempty {G : Set E}
    (h : (closure (convexHull ℝ G)).Nonempty) : G.Nonempty := by
  by_contra hG
  have he : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hG
  simp [he] at h

theorem common_group_of_density_band {Y : Type uY} {I : Type uI}
    (S : Y → Set E) (A : Set Y) (c : I → E) (d : E → ℝ)
    {u R b p : ℝ} (hA : A.Nonempty)
    (hgen : ∀ y ∈ A, S y = closure (convexHull ℝ
      {v | v ∈ S y ∧ ∃ i, v ∈ Metric.closedBall (c i) R}))
    (hne : ∀ y ∈ A, (S y).Nonempty)
    (hband : ∀ y ∈ A, ∀ v ∈ S y, |d v - u| ≤ b)
    (hd : ∀ v w, |d v - d w| ≤ dist v w)
    (hsep : ∀ i j, i ≠ j → p ≤ |d (c i) - d (c j)|)
    (hgap : 2 * (b + R) < p) :
    ∃ i, ∀ y ∈ A, S y ⊆ Metric.closedBall (c i) R := by
  classical
  have hcenter (y : Y) (hy : y ∈ A) (v : E) (hv : v ∈ S y)
      (i : I) (hi : v ∈ Metric.closedBall (c i) R) : |d (c i) - u| ≤ b + R := by
    have hdist : |d (c i) - d v| ≤ R := by
      calc
        _ ≤ dist (c i) v := hd _ _
        _ = dist v (c i) := dist_comm _ _
        _ ≤ R := hi
    calc
      |d (c i) - u| ≤ |d (c i) - d v| + |d v - u| := abs_sub_le _ _ _
      _ ≤ b + R := by linarith [hband y hy v hv]
  obtain ⟨y₀, hy₀⟩ := hA
  have hng : ({v | v ∈ S y₀ ∧ ∃ i, v ∈ Metric.closedBall (c i) R}).Nonempty := by
    apply nonempty_of_closedHull_nonempty
    rw [← hgen y₀ hy₀]
    exact hne y₀ hy₀
  obtain ⟨v₀, hv₀, i₀, hi₀⟩ := hng
  have hc₀ := hcenter y₀ hy₀ v₀ hv₀ i₀ hi₀
  refine ⟨i₀, ?_⟩
  intro y hy
  rw [hgen y hy]
  apply closure_minimal _ Metric.isClosed_closedBall
  apply convexHull_min _ (convex_closedBall (c i₀) R)
  rintro v ⟨hv, i, hi⟩
  have heq : i = i₀ := by
    by_contra hne'
    have hc := hcenter y hy v hv i hi
    have habs : |d (c i) - d (c i₀)| ≤ 2 * (b + R) := by
      calc
        _ ≤ |d (c i) - u| + |u - d (c i₀)| := abs_sub_le _ _ _
        _ = |d (c i) - u| + |d (c i₀) - u| := by rw [abs_sub_comm u]
        _ ≤ 2 * (b + R) := by linarith
    linarith [hsep i i₀ hne']
  simpa [heq] using hi

end MoreSupportGeometry

theorem active_neighborhood_density_band {P Q : Pressure}
    {a β h u βy hy e d η δ C r : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβy : 0 < βy) (hη : 0 < η)
    (hu : ActiveShift Q a β h u) (hs : pressureSupport P βy hy e d)
    (happrox : ∀ z ∈ ({0, η, -η} : Set ℝ),
      |Q β (h + β * a * u + z) - P β (h + β * a * u + z)| ≤ δ)
    (hlip : ∀ z ∈ ({0, η, -η} : Set ℝ),
      |P βy (hy + z) - P β (h + β * a * u + z)| ≤ C * r) :
    |d - u| ≤ η / (2 * β * a) + 2 * δ / η + 2 * C * r / η := by
  have hzero : (0 : ℝ) ∈ ({0, η, -η} : Set ℝ) := by simp
  have hplus : η ∈ ({0, η, -η} : Set ℝ) := by simp
  have hminus : -η ∈ ({0, η, -η} : Set ℝ) := by simp
  have happ0 := happrox 0 hzero
  have hlip0 := hlip 0 hzero
  simp only [add_zero] at happ0 hlip0
  have hsupport (z : ℝ) : z * d ≤ P βy (hy + z) - P βy hy := by
    have hh := hs βy (hy + z) hβy
    simp only [sub_self, mul_zero, add_zero, add_sub_cancel_left] at hh
    nlinarith
  have hup : η * (d - u) ≤ η ^ 2 / (2 * β * a) + 2 * δ + 2 * C * r := by
    have hp := active_parabola ha hβ hu η
    have hq := hsupport η
    have ha := abs_le.mp (happrox η hplus)
    have hl := abs_le.mp (hlip η hplus)
    have ha0 := abs_le.mp happ0
    have hl0 := abs_le.mp hlip0
    linarith
  have hlo : -(η * (d - u)) ≤ η ^ 2 / (2 * β * a) + 2 * δ + 2 * C * r := by
    have hp := active_parabola ha hβ hu (-η)
    have hq := hsupport (-η)
    have ha := abs_le.mp (happrox (-η) hminus)
    have hl := abs_le.mp (hlip (-η) hminus)
    have ha0 := abs_le.mp happ0
    have hl0 := abs_le.mp hlip0
    simp only [neg_sq] at hp
    linarith
  have heq : η * (η / (2 * β * a) + 2 * δ / η + 2 * C * r / η) =
      η ^ 2 / (2 * β * a) + 2 * δ + 2 * C * r := by
    field_simp
  apply abs_le.mpr
  constructor <;> nlinarith

end RadialTransition

end

end OAI
