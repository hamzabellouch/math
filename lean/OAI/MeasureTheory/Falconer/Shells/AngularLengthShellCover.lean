import OAI.MeasureTheory.Falconer.Angular.AngularLengthPartition

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem angularLengthShell_cover {x : Fin 4 → Plane} {a h : ℕ}
    (hc : x ∈ angularLengthComparable)
    (hupper : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hfar : 16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3))) :
    ∃ b ∈ Finset.Icc (a+9) (h+5), x ∈ angularLengthShell b := by
  let d := max (dist (x 0) (x 1)) (dist (x 2) (x 3))
  have hd : 0 < d := (by positivity : 0 < 16*(2:ℝ)^(-(h:ℝ))).trans hfar
  obtain ⟨n,hnlo,hnhi⟩ := exists_displacement_depth hd
  have hpow (k : ℝ) : (2:ℝ)^(k-(n:ℝ)-10) = (2:ℝ)^k*(2:ℝ)^(-((n:ℝ)+10)) := by
    rw [show k-(n:ℝ)-10 = k+(-((n:ℝ)+10)) by ring,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  have haexp : (2:ℝ)^(-(n:ℝ)-1) < (2:ℝ)^(1-(a:ℝ)) := by
    have he : (2:ℝ)^(1-(a:ℝ)) = 2*(2:ℝ)^(-(a:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_one]
    rw [he]
    exact hnlo.trans_le hupper
  have hhexp : (2:ℝ)^(4-(h:ℝ)) < (2:ℝ)^(-(n:ℝ)) := by
    have he : (2:ℝ)^(4-(h:ℝ)) = 16*(2:ℝ)^(-(h:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    exact hfar.trans_le hnhi
  have haR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp haexp
  have hhR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hhexp
  have haZ : (a:ℤ)-2 < n := by exact_mod_cast (show (a:ℝ)-2 < (n:ℝ) by linarith)
  have hhZ : n < (h:ℤ)-4 := by exact_mod_cast (show (n:ℝ) < (h:ℝ)-4 by linarith)
  have hb0 : 0 ≤ n+10 := by omega
  let b := (n+10).toNat
  have hbZ : (b:ℤ) = n+10 := Int.toNat_of_nonneg hb0
  have hbR : (b:ℝ) = (n:ℝ)+10 := by exact_mod_cast hbZ
  refine ⟨b,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hc,?_,?_⟩
  · have he : (2:ℝ)^(-(n:ℝ)-1) = 512*(2:ℝ)^(-(b:ℝ)) := by
      rw [hbR,show -(n:ℝ)-1 = 9-(n:ℝ)-10 by ring,hpow]
      norm_num
    rw [← he]
    exact hnlo
  · have he : (2:ℝ)^(-(n:ℝ)) = 1024*(2:ℝ)^(-(b:ℝ)) := by
      rw [hbR,show -(n:ℝ) = 10-(n:ℝ)-10 by ring,hpow]
      norm_num
    rw [← he]
    exact hnhi

theorem parent_cell_displacement_bound (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (a : ℕ) (A B : CellPath)
    (hA : A.length = a) (hB : B.length = a) (x : Fin 4 → Plane)
    (hx₀ : x 0 ∈ (Q₁.descendant A).carrier) (hx₁ : x 1 ∈ (Q₁.descendant A).carrier)
    (hx₂ : x 2 ∈ (Q₂.descendant B).carrier) (hx₃ : x 3 ∈ (Q₂.descendant B).carrier) :
    max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
  have h1 := (Q₁.descendant A).dist_le
    (Q₁.descendant_side_pos (by rw [hQ₁]; norm_num) A).le hx₀ hx₁
  have h2 := (Q₂.descendant B).dist_le
    (Q₂.descendant_side_pos (by rw [hQ₂]; norm_num) B).le hx₂ hx₃
  rw [Q₁.descendant_side,hA,hQ₁] at h1
  rw [Q₂.descendant_side,hB,hQ₂] at h2
  simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
    one_div] at *
  exact max_le h1 h2

theorem angular_far_max_displacement (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (h : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col) (x : Fin 4 → Plane)
    (hx₀ : x 0 ∈ (Q₁.descendant row.1).carrier) (hx₁ : x 1 ∈ (Q₁.descendant col.1).carrier)
    (hx₂ : x 2 ∈ (Q₂.descendant row.2).carrier) (hx₃ : x 3 ∈ (Q₂.descendant col.2).carrier) :
    16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) := by
  have hh := angular_far_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar
    (x 0) (x 1) (x 2) (x 3) hx₀ hx₁ hx₂ hx₃
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
    ← div_eq_mul_inv,lt_max_iff] using hh

end PlanarFalconer

end OAI
