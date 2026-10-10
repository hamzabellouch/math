import OAI.Probability.RadialTransition.IdealAttraction

namespace OAI

universe uE

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section InnerSupport

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SupportsOn (F : E → ℝ) (D : Set E) (x v : E) : Prop :=
  ∀ y ∈ D, F x + inner ℝ v (y - x) ≤ F y

def supportSet (F : E → ℝ) (D : Set E) (x : E) : Set E :=
  {v | SupportsOn F D x v}

theorem convex_supportSet (F : E → ℝ) (D : Set E) (x : E) :
    Convex ℝ (supportSet F D x) := by
  intro v hv w hw a b ha hb hab y hy
  have hv' := hv y hy
  have hw' := hw y hy
  simp only [inner_add_left, real_inner_smul_left]
  calc
    F x + (a * inner ℝ v (y - x) + b * inner ℝ w (y - x)) =
        a * (F x + inner ℝ v (y - x)) + b * (F x + inner ℝ w (y - x)) := by
      calc
        _ = (a + b) * F x +
            (a * inner ℝ v (y - x) + b * inner ℝ w (y - x)) := by rw [hab, one_mul]
        _ = _ := by ring
    _ ≤ a * F y + b * F y := add_le_add
      (mul_le_mul_of_nonneg_left hv' ha) (mul_le_mul_of_nonneg_left hw' hb)
    _ = F y := by rw [← add_mul, hab, one_mul]

theorem isClosed_supportSet (F : E → ℝ) (D : Set E) (x : E) :
    IsClosed (supportSet F D x) := by
  have heq : supportSet F D x = ⋂ y ∈ D, {v | F x + inner ℝ v (y - x) ≤ F y} := by
    ext v
    simp only [supportSet, SupportsOn, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_biInter fun y _ => isClosed_le
    (continuous_const.add (continuous_id.inner continuous_const)) continuous_const

theorem norm_le_of_unit_inner_le (w : E) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z : E, ‖z‖ = 1 → inner ℝ w z ≤ R) : ‖w‖ ≤ R := by
  by_cases hw : w = 0
  · simpa [hw] using hR
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hz : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 := by
    simp [norm_smul, hn]
  have hi : inner ℝ w ((‖w‖⁻¹ : ℝ) • w) = ‖w‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  simpa only [hi] using h _ hz

theorem support_transfer_bound (P Q : E → ℝ) (D : Set E)
    (x c v : E) {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hball : Metric.closedBall x r ⊆ D)
    (happrox : ∀ y ∈ Metric.closedBall x r, |Q y - P y| ≤ δ)
    (hnear : ∀ y ∈ Metric.closedBall x r,
      ∃ w : E, SupportsOn P D y w ∧ ‖w - c‖ ≤ R)
    (hv : SupportsOn Q D x v) :
    ‖v - c‖ ≤ R + 2 * δ / r := by
  apply norm_le_of_unit_inner_le _ (by positivity)
  intro z hz
  let y := x + r • z
  have hy : y ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [y]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz]
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  obtain ⟨w, hw, hwc⟩ := hnear y hy
  have hqy := hv y (hball hy)
  have hpx := hw x (hball hx)
  have hax := (abs_le.mp (happrox x hx)).1
  have hay := (abs_le.mp (happrox y hy)).2
  have hyx : y - x = r • z := by simp [y]
  have hxy : x - y = -(r • z) := by simp [y]
  rw [hyx, real_inner_smul_right] at hqy
  rw [hxy, inner_neg_right, real_inner_smul_right] at hpx
  have hi : inner ℝ (w - c) z ≤ R := by
    calc
      inner ℝ (w - c) z ≤ ‖w - c‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ R := by simpa only [hz, mul_one] using hwc
  rw [inner_sub_left] at hi ⊢
  have hg : r * (inner ℝ v z - inner ℝ c z) ≤ r * R + 2 * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hi hr.le]
  have hd := div_mul_cancel₀ (2 * δ) (ne_of_gt hr)
  nlinarith [hg, hd]

theorem supportSet_nonempty [FiniteDimensional ℝ E] {F : E → ℝ} {D : Set E}
    (hD : IsOpen D) (hF : ConvexOn ℝ D F) {x : E} (hx : x ∈ D) :
    (supportSet F D x).Nonempty := by
  let S : Set (E × ℝ) := {z | z.1 ∈ D ∧ F z.1 < z.2}
  have hSconv : Convex ℝ S := hF.convex_strict_epigraph
  have hFcont : ContinuousOn F D := ConvexOn.continuousOn hD hF
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hDnhds : D ∈ nhds z.1 := hD.mem_nhds hz.1
    have hc : ContinuousAt (fun w : E × ℝ => F w.1) z :=
      (hFcont.continuousAt hDnhds).comp continuous_fst.continuousAt
    exact inter_mem (continuous_fst.continuousAt.preimage_mem_nhds hDnhds)
      (hc.eventually_lt continuous_snd.continuousAt hz.2)
  have hnot : (x, F x) ∉ S := by simp [S]
  obtain ⟨ell, hsep⟩ := geometric_hahn_banach_point_open hSconv hSopen hnot
  let α : ℝ := ell (0, 1)
  let g : E →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (y : E) (r : ℝ) : ell (y, r) = g y + r * α := by
    have hp : (y, r) = (y, 0) + r • (0, 1) := by ext <;> simp
    rw [hp, map_add, map_smul]
    rfl
  have hα : 0 < α := by
    have hh := hsep (x, F x + 1) (by exact ⟨hx, by dsimp; linarith⟩)
    rw [hsplit, hsplit] at hh
    nlinarith
  have hle (y : E) (hy : y ∈ D) : g x + F x * α ≤ g y + F y * α := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hsep (y, F y + ε / α) (by exact ⟨hy, by dsimp; linarith [div_pos hε hα]⟩)
    rw [hsplit, hsplit] at hh
    have he := div_mul_cancel₀ ε (ne_of_gt hα)
    nlinarith [hh, he]
  let v : E := (InnerProductSpace.toDual ℝ E).symm ((-1 / α) • g)
  refine ⟨v, ?_⟩
  intro y hy
  have heq : α * inner ℝ v (y - x) = g x - g y := by
    dsimp [v]
    rw [InnerProductSpace.toDual_symm_apply, smul_apply, map_sub]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hh := hle y hy
  nlinarith [hh, heq]

end InnerSupport

end RadialTransition

end

end OAI
