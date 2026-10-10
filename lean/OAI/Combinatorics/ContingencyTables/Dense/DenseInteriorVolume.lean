import OAI.Combinatorics.ContingencyTables.Dense.DenseGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Positive volume of the actual dense completion polytope -/

namespace ContingencyTables.DenseAffine

open MeasureTheory
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def normalizedEntry (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (u : I × J → ℝ) (g : Option I × Option J) : ℝ :=
  table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u g.1 g.2 /
    cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g

theorem normalizedEntry_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (x y : I × J → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ∀ p, |x p - y p| ≤ r) (g : Option I × Option J) :
    |normalizedEntry R P d x g - normalizedEntry R P d y g| ≤
      ((d : ℝ) / (d : ℝ) ^ 8) * r := by
  unfold normalizedEntry
  rw [normalized_table_affine, normalized_table_affine]
  have hb := AffinePenalty.affineValue_change
    (entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    x y (1 / (d : ℝ) ^ 8) r
    (by positivity) (dense_normalized_coeff_bound R P d hd hR hP hRmax hPmax g) hxy
  have hc : (Fintype.card (I × J) : ℝ) ≤ d := by exact_mod_cast hfree
  calc
    _ ≤ Fintype.card (I × J) * (1 / (d : ℝ) ^ 8) * r := hb
    _ ≤ (d : ℝ) * (1 / (d : ℝ) ^ 8) * r := by gcongr
    _ = _ := by ring

theorem dense_change_below_interior_slack (d : ℕ) (hd : 14 ≤ d) :
    (d : ℝ) / (d : ℝ) ^ 8 ≤ 1 / (2 * (d : ℝ)) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hnat : 2 * d ^ 2 ≤ d ^ 8 := by
    have hsix : 2 ≤ d ^ 6 := (show 2 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
    calc
      2 * d ^ 2 ≤ d ^ 6 * d ^ 2 := Nat.mul_le_mul_right _ hsix
      _ = d ^ 8 := by ring
  apply (div_le_div_iff₀ (pow_pos hd₀ _) (show 0 < 2 * (d : ℝ) by positivity)).mpr
  have hreal : 2 * (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 8 := by exact_mod_cast hnat
  nlinarith

/-- A full open unit box around the constructed interior point is
feasible. Consequently the feasible polytope has positive Lebesgue volume,
including the zero-dimensional convention. -/
theorem dense_feasible_volume_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j) :
    0 < volume {u : I × J → ℝ | Feasible R P d u} := by
  obtain ⟨u, _, _, hcenter⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  let box : Set (I × J → ℝ) := Set.pi Set.univ (fun p => Set.Ioo (u p - 1) (u p + 1))
  have hbox : box ⊆ {x | Feasible R P d x} := by
    intro x hx i j
    have hxy (p : I × J) : |x p - u p| ≤ 1 := by
      have hp := hx p (Set.mem_univ p)
      apply abs_le.mpr
      constructor <;> linarith [hp.1, hp.2]
    have hc := normalizedEntry_change R P d hd hR hP hRmax hPmax hfree
      x u 1 (by norm_num) hxy (i, j)
    have hbound := dense_change_below_interior_slack d hd
    have hnonneg : 0 ≤ normalizedEntry R P d x (i, j) := by
      have hl := (abs_le.mp hc).1
      have hs := hcenter (i, j)
      change 1 / (2 * (d : ℝ)) ≤ normalizedEntry R P d u (i, j) at hs
      linarith
    have hscale : 0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (i, j) := by
      change 0 < min (R i : ℝ) (P j : ℝ)
      apply lt_min
      · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR _))
      · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP _))
    have h := (le_div_iff₀ hscale).mp hnonneg
    simpa only [zero_mul] using h
  have hv : 0 < volume box := by
    rw [Real.volume_pi_Ioo]
    apply bot_lt_iff_ne_bot.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    linarith
  exact hv.trans_le (measure_mono hbox)

end ContingencyTables.DenseAffine

end OAI
