import OAI.GroupTheory.Thompson.StandardPL
import OAI.GroupTheory.Thompson.UniformPartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Resolving a finite dyadic PL subdivision on a uniform grid

All original knots lie on a sufficiently fine dyadic grid. Such a knot
cannot lie strictly between consecutive grid points. The source piece
containing a cell's midpoint therefore contains the whole closed cell.
-/

noncomputable section

namespace ThompsonNonamenability

open BasicPartition

/-- A point on the closed depth-`n` dyadic grid, including both endpoints. -/
def uniformDyadicPoint (n : ℕ) (j : Fin (2 ^ n + 1)) : UnitInterval :=
  ⟨(j.val : ℝ) / (2 : ℝ) ^ n, by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) n))
    · apply (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
      exact_mod_cast Nat.le_of_lt_succ j.isLt⟩

@[simp] theorem coe_uniformDyadicPoint (n : ℕ) (j : Fin (2 ^ n + 1)) :
    (uniformDyadicPoint n j : ℝ) = (j.val : ℝ) / (2 : ℝ) ^ n := rfl

@[simp] theorem uniformDyadicPoint_castSucc_coe (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformDyadicPoint n k.castSucc : ℝ) = (uniformCell n k).left := rfl

@[simp] theorem uniformDyadicPoint_succ_coe (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformDyadicPoint n k.succ : ℝ) = (uniformCell n k).right := by
  change (((k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) =
    ((k.val : ℝ) + 1) / (2 : ℝ) ^ n
  simp only [Nat.cast_add, Nat.cast_one]

theorem uniformDyadicPoint_strictMono (n : ℕ) : StrictMono (uniformDyadicPoint n) := by
  intro i j hij
  change (i.val : ℝ) / (2 : ℝ) ^ n < (j.val : ℝ) / (2 : ℝ) ^ n
  apply (div_lt_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  have hij' : i.val < j.val := hij
  exact_mod_cast hij'

@[simp] theorem uniformDyadicPoint_zero (n : ℕ) :
    uniformDyadicPoint n 0 = unitIntervalZero := by
  apply Subtype.ext
  simp

@[simp] theorem uniformDyadicPoint_last (n : ℕ) :
    uniformDyadicPoint n (Fin.last (2 ^ n)) = unitIntervalOne := by
  apply Subtype.ext
  simp [Fin.val_last]

theorem uniformDyadicPoint_dyadic (n : ℕ) (j : Fin (2 ^ n + 1)) :
    IsDyadic (uniformDyadicPoint n j : ℝ) := by
  exact ⟨(j.val : ℤ), n, by simp⟩

/-- There is no grid point strictly between consecutive grid points. -/
theorem grid_point_not_inside_uniform_cell (n : ℕ) (k : Fin (2 ^ n)) (j : ℤ) :
    ¬ ((uniformCell n k).left < (j : ℝ) / (2 : ℝ) ^ n ∧
      (j : ℝ) / (2 : ℝ) ^ n < (uniformCell n k).right) := by
  intro h
  have hd : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  change (k.val : ℝ) / (2 : ℝ) ^ n < (j : ℝ) / (2 : ℝ) ^ n ∧
    (j : ℝ) / (2 : ℝ) ^ n < ((k.val : ℝ) + 1) / (2 : ℝ) ^ n at h
  have hleft : (k.val : ℤ) < j := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp h.1
  have hright : j < (k.val : ℤ) + 1 := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp h.2
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hleft)) hright

namespace DyadicPLWitness

/-- A single grid depth resolves every knot of the original subdivision.
At all larger depths each closed grid cell lies in one original piece. -/
theorem eventually_uniform_refines {f : IntervalHomeomorph} (w : DyadicPLWitness f) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : Fin (2 ^ n),
      ∃ i : Fin w.pieceCount,
        w.knots i.castSucc ≤ uniformDyadicPoint n k.castSucc ∧
        uniformDyadicPoint n k.succ ≤ w.knots i.succ := by
  classical
  obtain ⟨N, hN⟩ := dyadic_common_denominator_finset
    (Finset.univ : Finset (Fin (w.pieceCount + 1)))
    (fun j => (w.knots j : ℝ)) (fun j _ => w.dyadic j)
  refine ⟨N, ?_⟩
  intro n hn k
  let I := uniformCell n k
  have hlen : I.left < I.right := I.left_lt_right
  let m : UnitInterval := ⟨(I.left + I.right) / 2, by
    constructor <;> linarith [I.left_nonneg, I.right_le_one]⟩
  have hml : I.left < (m : ℝ) := by dsimp [m]; linarith
  have hmr : (m : ℝ) < I.right := by dsimp [m]; linarith
  obtain ⟨i, hil, hir⟩ := w.cover m
  have hilR : (w.knots i.castSucc : ℝ) ≤ (m : ℝ) := hil
  have hirR : (m : ℝ) ≤ (w.knots i.succ : ℝ) := hir
  have hno (j : Fin (w.pieceCount + 1)) :
      ¬ (I.left < (w.knots j : ℝ) ∧ (w.knots j : ℝ) < I.right) := by
    obtain ⟨a, ha⟩ := dyadic_denominator_mono (hN j (Finset.mem_univ j)) hn
    rw [ha]
    exact grid_point_not_inside_uniform_cell n k a
  refine ⟨i, ?_, ?_⟩
  · change (w.knots i.castSucc : ℝ) ≤ (uniformDyadicPoint n k.castSucc : ℝ)
    rw [uniformDyadicPoint_castSucc_coe]
    change (w.knots i.castSucc : ℝ) ≤ I.left
    apply le_of_not_gt
    intro h
    exact hno i.castSucc ⟨h, lt_of_le_of_lt hilR hmr⟩
  · change (uniformDyadicPoint n k.succ : ℝ) ≤ (w.knots i.succ : ℝ)
    rw [uniformDyadicPoint_succ_coe]
    change I.right ≤ (w.knots i.succ : ℝ)
    apply le_of_not_gt
    intro h
    exact hno i.succ ⟨lt_of_lt_of_le hml hirR, h⟩

end DyadicPLWitness

/-- A genuine affine formula on every closed cell of one uniform subdivision. -/
structure UniformDyadicPLWitness (f : IntervalHomeomorph) (n : ℕ) where
  exponent : Fin (2 ^ n) → ℤ
  affine : ∀ (k : Fin (2 ^ n)) (x : UnitInterval),
    (uniformCell n k).left ≤ (x : ℝ) → (x : ℝ) ≤ (uniformCell n k).right →
    (f x : ℝ) = (f (uniformDyadicPoint n k.castSucc) : ℝ) +
      (2 : ℝ) ^ exponent k * ((x : ℝ) - (uniformCell n k).left)

namespace DyadicPLWitness

/-- Restricting an original affine piece to a contained grid cell preserves
its exact exponent; the translation is rebased at the new left endpoint. -/
def uniformOfRefines {f : IntervalHomeomorph} (w : DyadicPLWitness f) (n : ℕ)
    (hr : ∀ k : Fin (2 ^ n), ∃ i : Fin w.pieceCount,
      w.knots i.castSucc ≤ uniformDyadicPoint n k.castSucc ∧
      uniformDyadicPoint n k.succ ≤ w.knots i.succ) : UniformDyadicPLWitness f n where
  exponent k := w.exponent (Classical.choose (hr k))
  affine := by
    intro k x hleft hright
    let i := Classical.choose (hr k)
    have hi := Classical.choose_spec (hr k)
    have hxl : w.knots i.castSucc ≤ x := by
      apply hi.1.trans
      change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (x : ℝ)
      simpa only [uniformDyadicPoint_castSucc_coe] using hleft
    have hxr : x ≤ w.knots i.succ := by
      apply le_trans _ hi.2
      change (x : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ)
      simpa only [uniformDyadicPoint_succ_coe] using hright
    have hcell : uniformDyadicPoint n k.castSucc ≤ uniformDyadicPoint n k.succ := by
      apply (uniformDyadicPoint_strictMono n).monotone
      exact (Fin.castSucc_lt_succ_iff.mpr le_rfl).le
    have hx := w.affine i x hxl hxr
    have hb := w.affine i (uniformDyadicPoint n k.castSucc) hi.1 (hcell.trans hi.2)
    rw [hx, hb, uniformDyadicPoint_castSucc_coe]
    ring

theorem eventually_uniform_affine {f : IntervalHomeomorph} (w : DyadicPLWitness f) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nonempty (UniformDyadicPLWitness f n) := by
  obtain ⟨N, hN⟩ := w.eventually_uniform_refines
  exact ⟨N, fun n hn => ⟨w.uniformOfRefines n (hN n hn)⟩⟩

end DyadicPLWitness

namespace UniformDyadicPLWitness

/-- Uniform affine data is an ordinary finite dyadic PL subdivision. -/
def toDyadicPLWitness {f : IntervalHomeomorph} {n : ℕ}
    (w : UniformDyadicPLWitness f n) : DyadicPLWitness f where
  pieceCount := 2 ^ n
  positive := pow_pos (by decide) n
  knots := uniformDyadicPoint n
  strictMono_knots := uniformDyadicPoint_strictMono n
  first := uniformDyadicPoint_zero n
  last := uniformDyadicPoint_last n
  dyadic := uniformDyadicPoint_dyadic n
  cover := by
    intro x
    obtain ⟨I, hI, hx⟩ := uniformCells_cover n (x : ℝ) x.property
    obtain ⟨k, rfl⟩ := mem_uniformCells.mp hI
    refine ⟨k, ?_, ?_⟩
    · change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (x : ℝ)
      simpa only [uniformDyadicPoint_castSucc_coe] using hx.1
    · change (x : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ)
      simpa only [uniformDyadicPoint_succ_coe] using hx.2
  exponent := w.exponent
  affine := by
    intro k x hleft hright
    change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (x : ℝ) at hleft
    change (x : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ) at hright
    rw [uniformDyadicPoint_castSucc_coe] at hleft
    rw [uniformDyadicPoint_succ_coe] at hright
    simpa only [uniformDyadicPoint_castSucc_coe] using w.affine k x hleft hright

end UniformDyadicPLWitness

theorem hasDyadicPLPieces_iff_uniform {f : IntervalHomeomorph} :
    HasDyadicPLPieces f ↔ ∃ n : ℕ, Nonempty (UniformDyadicPLWitness f n) := by
  constructor
  · rintro ⟨w⟩
    obtain ⟨N, hN⟩ := w.eventually_uniform_affine
    exact ⟨N, hN N le_rfl⟩
  · rintro ⟨n, ⟨w⟩⟩
    exact ⟨w.toDyadicPLWitness⟩

end ThompsonNonamenability

end

end OAI
