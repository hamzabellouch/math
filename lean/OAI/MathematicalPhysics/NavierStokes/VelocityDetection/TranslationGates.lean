import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfiles
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculusPartialDComm

namespace OAI

noncomputable section
namespace VelocityDetection.TranslationGates
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open SmoothProfiles SpatialCalculus

def window (s : ℝ) : ℝ := step (s + 3) * step (3 - s)

def windowD (s : ℝ) : ℝ :=
  pulse (s + 3) * step (3 - s) - step (s + 3) * pulse (3 - s)

@[fun_prop] theorem contDiff_window : ContDiff ℝ ∞ window := by
  unfold window
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem hasDerivAt_window (s : ℝ) : HasDerivAt window (windowD s) s := by
  have h1 := (differentiable_step (s + 3)).hasDerivAt.comp s ((hasDerivAt_id s).add_const 3)
  have h2 := (differentiable_step (3 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 3)
  change HasDerivAt (fun t : ℝ => step (t + 3) * step (3 - t)) _ s
  dsimp only [windowD, pulse]
  simpa only [comp_def, mul_one, mul_neg_one, mul_neg, sub_eq_add_neg, Pi.mul_def, id_eq]
    using h1.mul h2

theorem deriv_window : deriv window = windowD := funext (fun s => (hasDerivAt_window s).deriv)

@[fun_prop] theorem contDiff_windowD : ContDiff ℝ ∞ windowD := by
  rw [← deriv_window]
  exact (contDiff_infty_iff_deriv.mp contDiff_window).2

theorem window_one {s : ℝ} (hs : |s| ≤ 2) : window s = 1 := by
  have hs' := abs_le.mp hs
  simp [window, Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ s + 3 by linarith),
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 3 - s by linarith)]

theorem windowD_zero_inside {s : ℝ} (hs : |s| ≤ 2) : windowD s = 0 := by
  have hs' := abs_le.mp hs
  simp [windowD, pulse_zero_of_one_le (show (1 : ℝ) ≤ s + 3 by linarith),
    pulse_zero_of_one_le (show (1 : ℝ) ≤ 3 - s by linarith)]

theorem window_zero_outside {s : ℝ} (hs : 3 ≤ |s|) : window s = 0 := by
  rcases le_abs.mp hs with hs | hs
  · simp [window, Real.smoothTransition.zero_of_nonpos (show 3 - s ≤ 0 by linarith)]
  · simp [window, Real.smoothTransition.zero_of_nonpos (show s + 3 ≤ 0 by linarith)]

theorem windowD_zero_outside {s : ℝ} (hs : 3 ≤ |s|) : windowD s = 0 := by
  rcases le_abs.mp hs with hs | hs
  · simp [windowD, Real.smoothTransition.zero_of_nonpos (show 3 - s ≤ 0 by linarith),
      pulse_zero_of_nonpos (show 3 - s ≤ 0 by linarith)]
  · simp [windowD, Real.smoothTransition.zero_of_nonpos (show s + 3 ≤ 0 by linarith),
      pulse_zero_of_nonpos (show s + 3 ≤ 0 by linarith)]

def potential (R : ℝ) (c G X : Coord 2) : ℝ :=
  (window ((X 0 - c 0) / R) * window ((X 1 - c 1) / R)) *
    (G 0 * (X 1 - c 1) - G 1 * (X 0 - c 0))

def field (R : ℝ) (c G : Coord 2) : Coord 2 → Coord 2 :=
  rotatedGradient (potential R c G)

@[fun_prop] theorem contDiff_potential (R : ℝ) (c G : Coord 2) :
    ContDiff ℝ ∞ (potential R c G) := by
  unfold potential
  fun_prop

theorem divergence_field (R : ℝ) (c G X : Coord 2) :
    divergence (fun _ => field R c G) 0 X = 0 :=
  divergence_rotatedGradient (contDiff_infty.mp (contDiff_potential R c G) 2) X

theorem potential_partial_zero (R : ℝ) (c G X : Coord 2) :
    partialD 0 (potential R c G) X =
      (windowD ((X 0 - c 0) / R) / R * window ((X 1 - c 1) / R)) *
        (G 0 * (X 1 - c 1) - G 1 * (X 0 - c 0)) -
      (window ((X 0 - c 0) / R) * window ((X 1 - c 1) / R)) * G 1 := by
  have hW := (hasDerivAt_window ((X 0 - c 0) / R)).comp (X 0)
    (((hasDerivAt_id (X 0)).sub_const (c 0)).div_const R)
  have hL := (hasDerivAt_const (X 0) (G 0 * (X 1 - c 1))).sub
    (((hasDerivAt_id (X 0)).sub_const (c 0)).const_mul (G 1))
  have h := ((hW.mul_const (window ((X 1 - c 1) / R))).mul hL).deriv
  change deriv (fun s => potential R c G (update X 0 s)) (X 0) = _
  simpa [Pi.mul_def, Pi.sub_def, Pi.neg_def, Pi.add_def, potential, comp_def, sub_eq_add_neg, mul_div_assoc, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem potential_partial_one (R : ℝ) (c G X : Coord 2) :
    partialD 1 (potential R c G) X =
      (window ((X 0 - c 0) / R) * (windowD ((X 1 - c 1) / R) / R)) *
        (G 0 * (X 1 - c 1) - G 1 * (X 0 - c 0)) +
      (window ((X 0 - c 0) / R) * window ((X 1 - c 1) / R)) * G 0 := by
  have hW := (hasDerivAt_window ((X 1 - c 1) / R)).comp (X 1)
    (((hasDerivAt_id (X 1)).sub_const (c 1)).div_const R)
  have hL := (((hasDerivAt_id (X 1)).sub_const (c 1)).const_mul (G 0)).sub
    (hasDerivAt_const (X 1) (G 1 * (X 0 - c 0)))
  have h := ((hW.const_mul (window ((X 0 - c 0) / R))).mul hL).deriv
  change deriv (fun s => potential R c G (update X 1 s)) (X 1) = _
  simpa [Pi.mul_def, Pi.sub_def, Pi.neg_def, Pi.add_def, potential, comp_def, sub_eq_add_neg, mul_div_assoc, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem field_eq_velocity {R : ℝ} (hR : 0 < R) (c G X : Coord 2)
    (hX : ∀ i, |X i - c i| ≤ 2 * R) : field R c G X = G := by
  have hb (i : Fin 2) : |(X i - c i) / R| ≤ 2 := by
    rw [abs_div, abs_of_pos hR, div_le_iff₀ hR]
    exact hX i
  ext i
  fin_cases i
  · simp [field, rotatedGradient, potential_partial_one, window_one (hb 0),
      window_one (hb 1), windowD_zero_inside (hb 1)]
  · simp [field, rotatedGradient, potential_partial_zero, window_one (hb 0),
      window_one (hb 1), windowD_zero_inside (hb 0)]

theorem field_zero_outside {R : ℝ} (hR : 0 < R) (c G X : Coord 2)
    (hX : ∃ i, 3 * R ≤ |X i - c i|) : field R c G X = 0 := by
  obtain ⟨i, hi⟩ := hX
  have hb : 3 ≤ |(X i - c i) / R| := by
    rw [abs_div, abs_of_pos hR, le_div_iff₀ hR]
    exact hi
  fin_cases i
  · change 3 ≤ |(X 0 - c 0) / R| at hb
    ext j
    fin_cases j <;>
      simp [field, rotatedGradient, potential_partial_one, potential_partial_zero,
        window_zero_outside hb, windowD_zero_outside hb]
  · change 3 ≤ |(X 1 - c 1) / R| at hb
    ext j
    fin_cases j <;>
      simp [field, rotatedGradient, potential_partial_one, potential_partial_zero,
        window_zero_outside hb, windowD_zero_outside hb]

theorem field_zero_velocity (R : ℝ) (c X : Coord 2) : field R c 0 X = 0 := by
  ext i
  fin_cases i <;> simp [field, rotatedGradient, potential_partial_one, potential_partial_zero]

theorem field_apply_zero (R : ℝ) (c G X : Coord 2) :
    field R c G X 0 =
      (window ((X 0 - c 0) / R) * (windowD ((X 1 - c 1) / R) / R)) *
        (G 0 * (X 1 - c 1) - G 1 * (X 0 - c 0)) +
      (window ((X 0 - c 0) / R) * window ((X 1 - c 1) / R)) * G 0 := by
  simp [field, rotatedGradient, potential_partial_one]

theorem field_apply_one (R : ℝ) (c G X : Coord 2) :
    field R c G X 1 =
      (window ((X 0 - c 0) / R) * window ((X 1 - c 1) / R)) * G 1 -
      (windowD ((X 0 - c 0) / R) / R * window ((X 1 - c 1) / R)) *
        (G 0 * (X 1 - c 1) - G 1 * (X 0 - c 0)) := by
  simp [field, rotatedGradient, potential_partial_zero]

@[fun_prop] theorem contDiff_field (R : ℝ) (c G : Coord 2) :
    ContDiff ℝ ∞ (field R c G) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun X => field R c G X 0)
    simp only [field_apply_zero]
    fun_prop
  · change ContDiff ℝ ∞ (fun X => field R c G X 1)
    simp only [field_apply_one]
    fun_prop

theorem contDiff_movingField (R : ℝ) {c G : ℝ → Coord 2}
    (hc : ContDiff ℝ ∞ c) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => field R (c q.1) (G q.1) q.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => field R (c q.1) (G q.1) q.2 0)
    simp only [field_apply_zero]
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => field R (c q.1) (G q.1) q.2 1)
    simp only [field_apply_one]
    fun_prop

theorem compactSupport_field {R : ℝ} (hR : 0 < R) (c G : Coord 2) :
    HasCompactSupport (field R c G) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (fun j => c j - 3 * R) (fun j => c j + 3 * R)))
  intro X hX
  have hi (i : Fin 2) : |X i - c i| < 3 * R :=
    lt_of_not_ge (fun h => hX (field_zero_outside hR c G X ⟨i, h⟩))
  exact ⟨fun i => by linarith [(abs_lt.mp (hi i)).1],
    fun i => by linarith [(abs_lt.mp (hi i)).2]⟩

theorem finiteCylinderSupport {R : ℝ} (hR : 0 < R) {c G : ℝ → Coord 2}
    (hc : Continuous c) (a b : ℝ) :
    ∃ K : Set (Coord 2), IsCompact K ∧
      ∀ t ∈ Icc a b, ∀ X ∉ K, field R (c t) (G t) X = 0 := by
  let K : Set (Coord 2) := (fun q : ℝ × Coord 2 => c q.1 + q.2) ''
    (Icc a b ×ˢ Icc (fun _ => -3 * R) (fun _ => 3 * R))
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image ((hc.comp continuous_fst).add continuous_snd)
  refine ⟨K, hK, ?_⟩
  intro t ht X hX
  by_contra hnz
  have hi (i : Fin 2) : |X i - c t i| < 3 * R :=
    lt_of_not_ge (fun h => hnz (field_zero_outside hR (c t) (G t) X ⟨i, h⟩))
  apply hX
  refine ⟨(t, X - c t), ⟨ht, ?_⟩, ?_⟩
  · exact ⟨fun i => by dsimp; linarith [(abs_lt.mp (hi i)).1],
      fun i => by dsimp; linarith [(abs_lt.mp (hi i)).2]⟩
  · dsimp
    abel

def array {ι : Type*} (s : Finset ι) (R : ℝ) (c G : ι → Coord 2)
    (X : Coord 2) : Coord 2 := ∑ k ∈ s, field R (c k) (G k) X

theorem otherGate_zero {R : ℝ} (hR : 0 < R) (c d G X : Coord 2)
    (hsep : ∃ i, 16 * R ≤ |c i - d i|)
    (hnear : ∀ i, |X i - c i| ≤ R) : field R d G X = 0 := by
  apply field_zero_outside hR
  obtain ⟨i, hi⟩ := hsep
  refine ⟨i, ?_⟩
  have htri : |c i - d i| ≤ |X i - c i| + |X i - d i| := by
    calc
      |c i - d i| ≤ |c i - X i| + |X i - d i| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm (c i) (X i)]
  linarith [hnear i]

theorem array_plateau {ι : Type*} {s : Finset ι} {R : ℝ} (hR : 0 < R)
    (c G : ι → Coord 2) (hsep : ∀ k ∈ s, ∀ l ∈ s, k ≠ l →
      ∃ i, 16 * R ≤ |c k i - c l i|) {k : ι} (hk : k ∈ s) (X : Coord 2)
    (hnear : ∀ i, |X i - c k i| ≤ R) : array s R c G X = G k := by
  classical
  unfold array
  rw [Finset.sum_eq_single k]
  · exact field_eq_velocity hR (c k) (G k) X (fun i => (hnear i).trans (by linarith))
  · intro l hl hlk
    exact otherGate_zero hR (c k) (c l) (G l) X (hsep k hk l hl hlk.symm) hnear
  · exact fun h => False.elim (h hk)

end VelocityDetection.TranslationGates
end

end OAI
