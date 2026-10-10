import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RectangleAffine

namespace OAI

/-! A positive-determinant affine change of planar coordinates which places
halting state bands below nonhalting bands and swaps reciprocal factors. -/

noncomputable section

namespace ForcedComputation.PlanarConjugacy

open ShearFlows Set

/-- The determinant of the linear part is `ε * c`. -/
def map (a b ε c : ℚ) (x : Plane) : Plane :=
  letI := ShearFlows.neZeroTwo
  ![(a : ℝ) + (ε : ℝ) * x 1, (b : ℝ) - (c : ℝ) * x 0]

def box (a b ε c : ℚ) (R : RationalBox 2) : RationalBox 2 :=
  letI := ShearFlows.neZeroTwo
  ⟨![a + ε * R.lower 1, b - c * R.upper 0],
    ![a + ε * R.upper 1, b - c * R.lower 0]⟩

theorem box_positive {a b ε c : ℚ} (hε : 0 < ε) (hc : 0 < c)
    {R : RationalBox 2} (hR : R.positive) : (box a b ε c R).positive := by
  intro j
  fin_cases j <;> dsimp [box]
  · exact add_lt_add_right (mul_lt_mul_of_pos_left (hR 1) hε) a
  · exact sub_lt_sub_left (mul_lt_mul_of_pos_left (hR 0) hc) b

theorem box_center (a b ε c : ℚ) (R : RationalBox 2) :
    (box a b ε c R).center = map a b ε c R.center := by
  funext j
  fin_cases j <;> simp [box, map, RationalBox.center] <;> ring_nf

theorem box_halfWidth (a b ε c : ℚ) (R : RationalBox 2) :
    (box a b ε c R).halfWidth =
      ![(ε : ℝ) * R.halfWidth 1, (c : ℝ) * R.halfWidth 0] := by
  funext j
  fin_cases j <;> simp [box, RationalBox.halfWidth] <;> ring_nf

theorem mem_box_of_mem {a b ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 ≤ c)
    {R : RationalBox 2} {x : Plane} (hx : x ∈ R.carrier) :
    map a b ε c x ∈ (box a b ε c R).carrier := by
  have hε' : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  intro j
  fin_cases j <;> dsimp [map, box] <;> push_cast
  · constructor <;> nlinarith [(hx 1).1, (hx 1).2]
  · constructor <;> nlinarith [(hx 0).1, (hx 0).2]

theorem map_injective {a b ε c : ℚ} (hε : 0 < ε) (hc : 0 < c) :
    Function.Injective (map a b ε c) := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  intro x y hxy
  have h₀ := congrFun hxy 0
  have h₁ := congrFun hxy 1
  simp only [map, Matrix.cons_val_zero, Matrix.cons_val_one] at h₀ h₁
  funext j
  fin_cases j
  · change x 0 = y 0
    apply mul_left_cancel₀ hc'.ne'
    linarith
  · change x 1 = y 1
    apply mul_left_cancel₀ hε'.ne'
    linarith

theorem box_image {a b ε c : ℚ} (hε : 0 < ε) (hc : 0 < c)
    (R : RationalBox 2) :
    map a b ε c '' R.carrier = (box a b ε c R).carrier := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_box_of_mem hε.le hc.le hx
  · have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    intro y hy
    let x : Plane := ![((b : ℝ) - y 1) / (c : ℝ),
      (y 0 - (a : ℝ)) / (ε : ℝ)]
    refine ⟨x, ?_, ?_⟩
    · have hy₀ := hy 0
      have hy₁ := hy 1
      simp only [box, Matrix.cons_val_zero, Matrix.cons_val_one,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul] at hy₀ hy₁
      intro j
      fin_cases j <;> dsimp [x]
      · constructor
        · apply (le_div_iff₀ hc').mpr
          nlinarith [hy₁.2]
        · apply (div_le_iff₀ hc').mpr
          nlinarith [hy₁.1]
      · constructor
        · apply (le_div_iff₀ hε').mpr
          nlinarith [hy₀.1]
        · apply (div_le_iff₀ hε').mpr
          nlinarith [hy₀.2]
    · funext j
      fin_cases j <;> dsimp [map, x] <;> field_simp [hε'.ne', hc'.ne'] <;> ring_nf

theorem norm_lower_bound {a b ε c : ℚ} (hε : 0 < ε) (hc : 0 < c) (x y : Plane) :
    min (ε : ℝ) (c : ℝ) * ‖x - y‖ ≤ ‖map a b ε c x - map a b ε c y‖ := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  let m : ℝ := min (ε : ℝ) (c : ℝ)
  have hm : 0 < m := lt_min hε' hc'
  have h₀ : (ε : ℝ) * |x 1 - y 1| ≤ ‖map a b ε c x - map a b ε c y‖ := by
    have h := norm_le_pi_norm (map a b ε c x - map a b ε c y) 0
    have he : (map a b ε c x - map a b ε c y) 0 = (ε : ℝ) * (x 1 - y 1) := by
      simp only [map, Pi.sub_apply, Matrix.cons_val_zero]
      ring_nf
    simpa only [he, Real.norm_eq_abs, abs_mul, abs_of_pos hε'] using h
  have h₁ : (c : ℝ) * |x 0 - y 0| ≤ ‖map a b ε c x - map a b ε c y‖ := by
    have h := norm_le_pi_norm (map a b ε c x - map a b ε c y) 1
    have he : (map a b ε c x - map a b ε c y) 1 = -(c : ℝ) * (x 0 - y 0) := by
      change ((b : ℝ) - (c : ℝ) * x 0) - ((b : ℝ) - (c : ℝ) * y 0) = _
      ring_nf
    simpa only [he, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hc'] using h
  have hnorm : ‖x - y‖ ≤ ‖map a b ε c x - map a b ε c y‖ / m := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) hm.le)).mpr
    intro j
    rw [le_div_iff₀ hm]
    fin_cases j
    · change |x 0 - y 0| * m ≤ _
      dsimp only [m]
      have hb := (mul_le_mul_of_nonneg_right (min_le_right (ε : ℝ) (c : ℝ))
        (abs_nonneg (x 0 - y 0))).trans h₁
      linarith
    · change |x 1 - y 1| * m ≤ _
      dsimp only [m]
      have hb := (mul_le_mul_of_nonneg_right (min_le_left (ε : ℝ) (c : ℝ))
        (abs_nonneg (x 1 - y 1))).trans h₀
      linarith
  simpa only [m, mul_comm] using (le_div_iff₀ hm).mp hnorm

theorem separated_image {a b ε c : ℚ} (hε : 0 < ε) (hc : 0 < c)
    {S T : Set Plane} (hST : PositivelySeparated S T) :
    PositivelySeparated (map a b ε c '' S) (map a b ε c '' T) := by
  obtain ⟨δ, hδ, hd⟩ := hST
  have hm : 0 < min (ε : ℝ) (c : ℝ) := lt_min (by exact_mod_cast hε) (by exact_mod_cast hc)
  refine ⟨min (ε : ℝ) (c : ℝ) * δ, mul_pos hm hδ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (mul_le_mul_of_nonneg_left (hd x hx y hy) hm.le).trans (norm_lower_bound hε hc x y)

def instruction (a b ε c : ℚ) (r : Instruction) : Instruction :=
  ⟨box a b ε c r.source, box a b ε c r.target, r.factor⁻¹⟩

theorem instruction_factor_pos {a b ε c : ℚ} {r : Instruction}
    (hr : 0 < r.factor) : 0 < (instruction a b ε c r).factor :=
  inv_pos.mpr hr

theorem instruction_conjugacy (a b ε c : ℚ) (r : Instruction) (hr : r.factor ≠ 0)
    (x : Plane) :
    (instruction a b ε c r).affine (map a b ε c x) = map a b ε c (r.affine x) := by
  have hr' : (r.factor : ℝ) ≠ 0 := by exact_mod_cast hr
  have hsource := box_center a b ε c r.source
  have htarget := box_center a b ε c r.target
  funext j
  fin_cases j <;>
    simp only [Instruction.affine, instruction, hsource, htarget, map,
      Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_inv]
  · field_simp
    ring_nf
  · field_simp
    ring_nf

theorem instruction_image_eq {a b ε c : ℚ} (hε : 0 < ε) (hc : 0 < c)
    {r : Instruction} (hr : r.factor ≠ 0)
    (himage : r.affine '' r.source.carrier = r.target.carrier) :
    (instruction a b ε c r).affine '' (instruction a b ε c r).source.carrier =
      (instruction a b ε c r).target.carrier := by
  change (instruction a b ε c r).affine '' (box a b ε c r.source).carrier =
    (box a b ε c r.target).carrier
  rw [← box_image hε hc r.source, ← box_image hε hc r.target, image_image]
  have hcomp : (instruction a b ε c r).affine ∘ map a b ε c =
      map a b ε c ∘ r.affine := by
    funext x
    exact instruction_conjugacy a b ε c r hr x
  simp only [Function.comp_def] at hcomp
  rw [hcomp, ← image_image, himage]

end ForcedComputation.PlanarConjugacy

end

end OAI
