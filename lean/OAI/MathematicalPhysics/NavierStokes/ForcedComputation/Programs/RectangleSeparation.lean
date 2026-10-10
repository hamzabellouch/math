import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.GappedSeparation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InstructionRectangles

namespace OAI

noncomputable section

namespace ForcedComputation.Radix

open ShearFlows Set

def pairOfPlane (x : Plane) : ℝ × ℝ :=
  letI := ShearFlows.neZeroTwo
  (x 0, x 1)

theorem plane_pair (x : Plane) : planeOfPair (pairOfPlane x) = x := by
  funext j
  fin_cases j <;> rfl

theorem planeOfPair_injective : Function.Injective planeOfPair := by
  intro x y h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

theorem sourceBox_pair_mem (B l a : ℚ) (p : ℝ × ℝ) :
    planeOfPair p ∈ (sourceBox B l a).carrier ↔ p ∈ rectangle B l a := by
  constructor
  · intro h
    constructor
    · simpa only [sourceBox, planeOfPair, RationalBox.carrier, cylinder, mem_Icc,
        Matrix.cons_val_zero, Rat.cast_div, Rat.cast_add, Rat.cast_one] using h 0
    · simpa only [sourceBox, planeOfPair, RationalBox.carrier, cylinder, mem_Icc,
        Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_div, Rat.cast_add, Rat.cast_one] using h 1
  · intro h j
    fin_cases j
    · dsimp [sourceBox, planeOfPair]
      simpa only [cylinder, Set.mem_Icc, Rat.cast_div, Rat.cast_add, Rat.cast_one] using h.1
    · dsimp [sourceBox, planeOfPair]
      simpa only [cylinder, Set.mem_Icc, Rat.cast_div, Rat.cast_add, Rat.cast_one] using h.2

def targetRegion (B l b : ℝ) (m : HeadMove) : Set (ℝ × ℝ) :=
  HeadMove.casesOn m
    (Icc 0 1 ×ˢ (push B l '' cylinder B b))
    (cylinder B l ×ˢ cylinder B b)
    ((push B b '' cylinder B l) ×ˢ Icc 0 1)

theorem targetBox_pair_mem {B : ℚ} (hB : 0 < B) (l a b : ℚ)
    (m : HeadMove) (p : ℝ × ℝ) :
    planeOfPair p ∈ (targetBox B l b m).carrier ↔ p ∈ targetRegion B l b m := by
  have hp : (0 : ℝ) < B := by exact_mod_cast hB
  have himage : normalizedMove B l a b m '' rectangle B l a = targetRegion B l b m := by
    cases m
    · exact leftMove_image hp _ _ _
    · exact stayMove_image hp _ _ _
    · exact rightMove_image hp _ _ _
  rw [← himage]
  constructor
  · intro h
    rw [← radixInstruction_image hB l a b m] at h
    obtain ⟨x, hx, he⟩ := h
    refine ⟨pairOfPlane x, (sourceBox_pair_mem B l a _).mp ?_, ?_⟩
    · simpa only [plane_pair] using hx
    · apply planeOfPair_injective
      rw [← radixInstruction_action hB, plane_pair]
      exact he
  · rintro ⟨x, hx, rfl⟩
    rw [← radixInstruction_action hB]
    rw [← radixInstruction_image hB l a b m]
    exact mem_image_of_mem _ ((sourceBox_pair_mem B l a x).mpr hx)

def CoordinateGap (δ : ℝ) (R S : RationalBox 2) : Prop :=
  ∀ x ∈ R.carrier, ∀ y ∈ S.carrier, ∃ j : Fin 2, δ ≤ |x j - y j|

theorem CoordinateGap.positiveSeparated {δ : ℝ} {R S : RationalBox 2}
    (hδ : 0 < δ) (h : CoordinateGap δ R S) : PositivelySeparated R.carrier S.carrier := by
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  obtain ⟨j, hj⟩ := h x hx y hy
  exact hj.trans (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) j)

theorem CoordinateGap.scaled {δ : ℝ} {R S : RationalBox 2}
    (h : CoordinateGap δ R S) {κ : ℚ} (hκ : 0 < κ) (offset : Fin 2 → ℚ) :
    CoordinateGap ((κ : ℝ) * δ) (scaledBox κ offset R) (scaledBox κ offset S) := by
  intro x hx y hy
  rw [← scaledBox_image hκ offset R] at hx
  rw [← scaledBox_image hκ offset S] at hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨j, hj⟩ := h u hu v hv
  refine ⟨j, ?_⟩
  have hp : (0 : ℝ) < κ := by exact_mod_cast hκ
  have he : embedPlane κ offset u j - embedPlane κ offset v j = (κ : ℝ) * (u j - v j) := by
    dsimp [embedPlane]
    ring
  rw [he, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_left hj hp.le

theorem sourceBox_gap {N : ℕ} (l a l' a' : Fin N) (hne : (l, a) ≠ (l', a')) :
    CoordinateGap (1 / (rationalBase N : ℝ))
      (sourceBox (rationalBase N) (rationalDigit l) (rationalDigit a))
      (sourceBox (rationalBase N) (rationalDigit l') (rationalDigit a')) := by
  intro x hx y hy
  have hx' := (sourceBox_pair_mem _ _ _ (pairOfPlane x)).mp (by simpa only [plane_pair] using hx)
  have hy' := (sourceBox_pair_mem _ _ _ (pairOfPlane y)).mp (by simpa only [plane_pair] using hy)
  have hp : (0 : ℝ) < rationalBase N := lt_of_lt_of_le zero_lt_one (rationalBase_ge_one N)
  by_cases hl : l = l'
  · have ha : a ≠ a' := by intro h; exact hne (by simp [hl, h])
    exact ⟨1, cylinder_separated hp (rationalDigit_gap ha) _ hx'.2 _ hy'.2⟩
  · exact ⟨0, cylinder_separated hp (rationalDigit_gap hl) _ hx'.1 _ hy'.1⟩

theorem targetBox_gap {N : ℕ} (l b l' b' : Fin N) (m : HeadMove)
    (hne : (l, b) ≠ (l', b')) :
    CoordinateGap (1 / (rationalBase N : ℝ) ^ 2)
      (targetBox (rationalBase N) (rationalDigit l) (rationalDigit b) m)
      (targetBox (rationalBase N) (rationalDigit l') (rationalDigit b') m) := by
  intro x hx y hy
  have hp : (0 : ℚ) < rationalBase N := by dsimp [rationalBase]; positivity
  have hpr : (0 : ℝ) < rationalBase N := by exact_mod_cast hp
  have hx' := (targetBox_pair_mem hp _ 0 _ m (pairOfPlane x)).mp (by simpa only [plane_pair] using hx)
  have hy' := (targetBox_pair_mem hp _ 0 _ m (pairOfPlane y)).mp (by simpa only [plane_pair] using hy)
  cases m with
  | left =>
    exact ⟨1, twoSymbol_separated l l' b b' hne _ hx'.2 _ hy'.2⟩
  | right =>
    have hne' : (b, l) ≠ (b', l') := by
      intro he
      exact hne (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))
    exact ⟨0, twoSymbol_separated b b' l l' hne' _ hx'.1 _ hy'.1⟩
  | stay =>
    have hrecip : 1 / (rationalBase N : ℝ) ^ 2 ≤ 1 / (rationalBase N : ℝ) :=
      one_div_le_one_div_of_le hpr (by nlinarith [rationalBase_ge_one N])
    by_cases hl : l = l'
    · have hb : b ≠ b' := by intro h; exact hne (by simp [hl, h])
      exact ⟨1, hrecip.trans (cylinder_separated hpr (rationalDigit_gap hb) _ hx'.2 _ hy'.2)⟩
    · exact ⟨0, hrecip.trans (cylinder_separated hpr (rationalDigit_gap hl) _ hx'.1 _ hy'.1)⟩

end ForcedComputation.Radix

end

end OAI
