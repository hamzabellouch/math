import OAI.Combinatorics.ProgressionColoring.ShortPeriodCut
import OAI.Combinatorics.ProgressionColoring.Dichotomy
import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh
import OAI.Combinatorics.ProgressionColoring.ModelGeometry

namespace OAI

/-!
# The short-period branch of the outer-color dichotomy

A cut crossed by the unreduced real path is close to every sample. The actual
adaptive mesh then makes every sampled interval narrower than the nonzero
step. Two equal labels contradict this, forcing one global real affine lift.
-/

universe uIndex

namespace QuantitativeVanDerWaerden

theorem rho_eq_of_integer_difference {x y : ℝ}
    (h : ∃ z : ℤ, x - y = (z : ℝ)) : rho x = rho y := by
  obtain ⟨z, hz⟩ := h
  have he : x = y + z := by linarith
  rw [he, rho_add_int]

theorem rho_half : rho (1 / 2 : ℝ) = 0 := by
  rw [rho_eq_of_closed_mem (by norm_num) le_rfl,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- The circle distance to the cut is at most the real distance to any lift
of that cut. This includes equality at either endpoint. -/
theorem rho_le_distance_to_cut (x : ℝ) (z : ℤ) :
    rho x ≤ |x - (1 / 2 + z)| := by
  have h := rho_lipschitz_integer x (1 / 2) z
  rw [rho_half, sub_zero, abs_of_nonneg (rho_nonneg x)] at h
  simpa only [sub_add_eq_sub_sub] using h

/-- Once the closed real segment hits a cut, every sample is cut-near.
The congruences connect the real path with the actual centered samples. -/
theorem short_segment_cut_rho {Y : ℕ → ℝ} {A w t : ℝ} {k : ℕ} {z : ℤ}
    (hcongr : ∀ j, j < k → ∃ m : ℤ, Y j - (A + (j : ℝ) * w) = (m : ℝ))
    (ht0 : 0 ≤ t) (htk : t ≤ (k : ℝ))
    (hcut : A + t * w = 1 / 2 + z) :
    ∀ j, j < k → rho (Y j) ≤ (k : ℝ) * |w| := by
  intro j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj.le
  have hdist : |(j : ℝ) - t| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    rho (Y j) = rho (A + (j : ℝ) * w) := rho_eq_of_integer_difference (hcongr j hj)
    _ ≤ |A + (j : ℝ) * w - (1 / 2 + z)| := rho_le_distance_to_cut _ z
    _ = |((j : ℝ) - t) * w| := by rw [← hcut]; congr 1; ring
    _ = |(j : ℝ) - t| * |w| := abs_mul _ _
    _ ≤ (k : ℝ) * |w| := mul_le_mul_of_nonneg_right hdist (abs_nonneg w)

/-- A repeated interval forces every centered sample onto the same real lift.
Only the width at one of the repeated samples is needed. -/
theorem short_period_affine_lift {Y : ℕ → ℝ} {A w H α width : ℝ} {k a b : ℕ}
    (hrep : ∀ j, j < k → -(1 / 2 : ℝ) ≤ Y j ∧ Y j < 1 / 2)
    (hbase : Y 0 = A)
    (hcongr : ∀ j, j < k → ∃ z : ℤ, Y j - (A + (j : ℝ) * w) = (z : ℝ))
    (hH : 0 ≤ H) (hmotion : (k : ℝ) * |w| < 1 / 2)
    (hsep : w ≠ 0 → α ≤ |w|) (hsmall : 2 * H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : |Y a - Y b| ≤ width)
    (hwidth : width ≤ 2 * H * (rho (Y a) + α)) :
    ∀ j, j < k → Y j = A + (j : ℝ) * w := by
  intro j hj
  by_contra hfail
  obtain ⟨hw, t, ht0, htk, z, hcut⟩ :=
    failed_centered_lift_cut hrep hbase hcongr ⟨j, hj, hfail⟩
  have hrho := short_segment_cut_rho hcongr ht0
    (show t ≤ (k : ℝ) by linarith) hcut a hak
  have hnarrow := short_cut_interval_lt_step hH hw (hsep hw) hrho hwidth hsmall
  have hint : ∃ z : ℤ, (Y a - Y b) - ((a : ℝ) - b) * w = (z : ℝ) := by
    obtain ⟨za, hza⟩ := hcongr a hak
    obtain ⟨zb, hzb⟩ := hcongr b hbk
    refine ⟨za - zb, ?_⟩
    push_cast
    linarith
  exact short_step_not_same_interval hab hak hbk hmotion hint (hsame.trans_lt hnarrow)

theorem AdaptiveMesh.short_period_affine_lift (M : AdaptiveMesh)
    {Y : ℕ → ℝ} {A w : ℝ} {k a b : ℕ}
    (hrep : ∀ j, j < k → -(1 / 2 : ℝ) ≤ Y j ∧ Y j < 1 / 2)
    (hbase : Y 0 = A)
    (hcongr : ∀ j, j < k → ∃ z : ℤ, Y j - (A + (j : ℝ) * w) = (z : ℝ))
    (hmotion : (k : ℝ) * |w| < 1 / 2)
    (hsep : w ≠ 0 → M.alpha ≤ |w|)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : M.meshLabel (Y a) = M.meshLabel (Y b)) :
    ∀ j, j < k → Y j = A + (j : ℝ) * w := by
  have hca : centered (Y a) = Y a := centered_eq_of_mem (hrep a hak).1 (hrep a hak).2
  have hcb : centered (Y b) = Y b := centered_eq_of_mem (hrep b hbk).1 (hrep b hbk).2
  have hdist := M.same_label_distance hsame
  rw [hca, hcb] at hdist
  have hcontains := M.meshLabel_contains (Y a)
  rw [hca] at hcontains
  exact QuantitativeVanDerWaerden.short_period_affine_lift hrep hbase hcongr M.H_pos.le
    hmotion hsep hsmall hab hak hbk hdist
    (M.width_bounds_of_closed_mem _ hcontains.1 hcontains.2.le).2

/-- The coordinatewise conclusion gives a single vector affine lift. -/
theorem AdaptiveMesh.short_period_vector_lift (M : AdaptiveMesh)
    {ι : Type uIndex} {Y : ℕ → ι → ℝ} {w : ι → ℝ} {k a b : ℕ}
    (hrep : ∀ i j, j < k → -(1 / 2 : ℝ) ≤ Y j i ∧ Y j i < 1 / 2)
    (hcongr : ∀ i j, j < k →
      ∃ z : ℤ, Y j i - (Y 0 i + (j : ℝ) * w i) = (z : ℝ))
    (hmotion : ∀ i, (k : ℝ) * |w i| < 1 / 2)
    (hsep : ∀ i, w i ≠ 0 → M.alpha ≤ |w i|)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : ∀ i, M.meshLabel (Y a i) = M.meshLabel (Y b i)) :
    ∀ j, j < k → Y j = fun i => Y 0 i + (j : ℝ) * w i := by
  intro j hj
  funext i
  exact M.short_period_affine_lift (hrep i) rfl (hcongr i) (hmotion i)
    (hsep i) hsmall hab hak hbk (hsame i) j hj

/-- Short-period lifting for the actual cyclic representatives and actual
adaptive labels. The only remaining inputs are the numerical short-motion
bounds, a congruent step, and a repeated label. -/
theorem AdaptiveMesh.short_period_cyclic_lift (M : AdaptiveMesh)
    {q D dilation k a b : ℕ} (hq : 0 < q)
    (n d : CyclicGroup q D) (w : Fin D → ℝ)
    (hstep : ∀ i, ∃ z : ℤ, yRep q D dilation d i - w i = (z : ℝ))
    (halpha : M.alpha ≤ 1 / (q : ℝ) ^ D)
    (hmotion : ∀ i, (k : ℝ) * |w i| < 1 / 2)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : ∀ i, M.meshLabel (yRep q D dilation (n + a • d) i) =
      M.meshLabel (yRep q D dilation (n + b • d) i)) :
    ∀ j, j < k → yRep q D dilation (n + j • d) =
      fun i => yRep q D dilation n i + (j : ℝ) * w i := by
  have hcongr : ∀ i j, j < k → ∃ z : ℤ,
      yRep q D dilation (n + j • d) i -
        (yRep q D dilation (n + 0 • d) i + (j : ℝ) * w i) = (z : ℝ) := by
    intro i j _
    obtain ⟨a, ha⟩ := yRep_ap_congr hq dilation n d j i
    obtain ⟨b, hb⟩ := hstep i
    refine ⟨a + (j : ℤ) * b, ?_⟩
    simp only [zero_nsmul, add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    nlinarith [congrArg (fun t : ℝ => (j : ℝ) * t) hb]
  have hsep : ∀ i, w i ≠ 0 → M.alpha ≤ |w i| := by
    intro i hi
    exact halpha.trans (yRep_step_mesh_lower hq d i (hstep i) hi).2
  have h := M.short_period_vector_lift
    (fun i j _ => yRep_mem q D dilation (n + j • d) i)
    hcongr hmotion hsep hsmall hab hak hbk hsame
  simpa only [zero_nsmul, add_zero] using h

end QuantitativeVanDerWaerden

end OAI
