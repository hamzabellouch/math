import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

namespace Alternating.Memory
open scoped BigOperators Topology

noncomputable def digitSelector (b d : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (8 * ((b : ℝ) * x - 2 * d) + 2) *
    Real.smoothTransition (8 * (2 * d + 1 - (b : ℝ) * x) + 2)

theorem digitSelector_smooth (b d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (digitSelector b d) := by
  unfold digitSelector
  fun_prop

theorem digitSelector_mem (b d : ℕ) (x : ℝ) :
    digitSelector b d x ∈ Set.Icc 0 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

theorem digitSelector_one_near {b d : ℕ} {x : ℝ}
    (hl : 2 * (d : ℝ) - 1 / 8 ≤ (b : ℝ) * x)
    (hr : (b : ℝ) * x ≤ 2 * d + 1 + 1 / 8) : digitSelector b d x = 1 := by
  unfold digitSelector
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem digitSelector_one {b d : ℕ} {x : ℝ}
    (hx : (b : ℝ) * x ∈ Set.Icc (2 * (d : ℝ)) (2 * d + 1)) : digitSelector b d x = 1 :=
  digitSelector_one_near (by linarith [hx.1]) (by linarith [hx.2])

theorem digitSelector_zero_left {b d : ℕ} {x : ℝ}
    (hx : (b : ℝ) * x ≤ 2 * d - 1 / 4) : digitSelector b d x = 0 := by
  unfold digitSelector
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem digitSelector_zero_right {b d : ℕ} {x : ℝ}
    (hx : 2 * d + 1 + 1 / 4 ≤ (b : ℝ) * x) : digitSelector b d x = 0 := by
  unfold digitSelector
  have h : Real.smoothTransition (8 * (2 * (d : ℝ) + 1 - (b : ℝ) * x) + 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [h, mul_zero]

theorem digitSelector_selects {b d e : ℕ} {x : ℝ}
    (hx : (b : ℝ) * x ∈ Set.Icc (2 * (d : ℝ)) (2 * d + 1)) :
    digitSelector b e x = if e = d then 1 else 0 := by
  split_ifs with he
  · subst e
    exact digitSelector_one hx
  · rcases lt_or_gt_of_ne he with h | h
    · apply digitSelector_zero_right
      have h' : (e : ℝ) + 1 ≤ d := by exact_mod_cast h
      linarith [hx.1]
    · apply digitSelector_zero_left
      have h' : (d : ℝ) + 1 ≤ e := by exact_mod_cast h
      linarith [hx.2]

theorem digitSelector_support {b d : ℕ} (hb : 0 < b) :
    tsupport (digitSelector b d) ⊆
      Set.Icc ((2 * (d : ℝ) - 1 / 4) / b) ((2 * d + 1 + 1 / 4) / b) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · rw [div_le_iff₀ hb']
    by_contra h
    exact hx (digitSelector_zero_left (by linarith))
  · rw [le_div_iff₀ hb']
    by_contra h
    exact hx (digitSelector_zero_right (by linarith))

theorem digitSelector_compact {b d : ℕ} (hb : 0 < b) :
    HasCompactSupport (digitSelector b d) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (digitSelector_support hb)

theorem digitSelector_disjoint {b : ℕ} (hb : 0 < b) {d e : ℕ} (hde : d ≠ e) :
    Disjoint (tsupport (digitSelector b d)) (tsupport (digitSelector b e)) := by
  apply Set.disjoint_left.2
  intro x hd he
  have hdx := digitSelector_support hb hd
  have hex := digitSelector_support hb he
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd1 := (div_le_iff₀ hb').1 hdx.1
  have hd2 := (le_div_iff₀ hb').1 hdx.2
  have he1 := (div_le_iff₀ hb').1 hex.1
  have he2 := (le_div_iff₀ hb').1 hex.2
  rcases lt_or_gt_of_ne hde with h | h
  · have h' : (d : ℝ) + 1 ≤ e := by exact_mod_cast h
    linarith
  · have h' : (e : ℝ) + 1 ≤ d := by exact_mod_cast h
    linarith

theorem digitSelector_deriv_compact {b d : ℕ} (hb : 0 < b) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n (digitSelector b d)) := by
  induction n with
  | zero => simpa using (digitSelector_compact (d := d) hb)
  | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv

theorem digitSelector_derivatives_bounded {b d : ℕ} (hb : 0 < b) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |iteratedDeriv n (digitSelector b d) x| ≤ M := by
  have hc := (digitSelector_smooth b d).continuous_iteratedDeriv n
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  obtain ⟨M, hM, hbound⟩ :=
    ((digitSelector_deriv_compact (d := d) hb n).isCompact_range hc).isBounded.exists_pos_norm_le
  exact ⟨M, hM, fun x => by simpa using hbound _ ⟨x, rfl⟩⟩

end Alternating.Memory

end OAI
