import OAI.GroupTheory.Thompson.IntervalHomeomorph
import OAI.GroupTheory.Thompson.DyadicArithmetic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The ordinary finite-piece dyadic PL condition

A witness is a finite subdivision of the actual real interval, together with
an affine equality on each closed piece. Knots may be redundant. The witness
is existential in `HasDyadicPLPieces`, so its choice is not part of a group
element's identity.
-/

namespace ThompsonNonamenability

namespace DyadicPLWitness

theorem knot_le_next {f : IntervalHomeomorph} (w : DyadicPLWitness f)
    (i : Fin w.pieceCount) : w.knots i.castSucc ≤ w.knots i.succ :=
  (w.strictMono_knots (Fin.castSucc_lt_succ_iff.mpr le_rfl)).le

theorem image_knots_dyadic {f : IntervalHomeomorph} (w : DyadicPLWitness f)
    (hf : StrictMono f) (i : Fin (w.pieceCount + 1)) :
    IsDyadic (f (w.knots i) : ℝ) := by
  refine Fin.induction ?_ ?_ i
  · simpa only [w.first, IntervalHomeomorph.map_zero hf, coe_unitIntervalZero]
      using isDyadic_zero
  · intro j hj
    rw [w.affine j (w.knots j.succ) (w.knot_le_next j) le_rfl]
    exact hj.add ((isDyadic_zpow (w.exponent j)).mul
      ((w.dyadic j.succ).sub (w.dyadic j.castSucc)))

theorem map_dyadic {f : IntervalHomeomorph} (w : DyadicPLWitness f)
    (hf : StrictMono f) {x : UnitInterval} (hx : IsDyadic (x : ℝ)) :
    IsDyadic (f x : ℝ) := by
  obtain ⟨i, hleft, hright⟩ := w.cover x
  rw [w.affine i x hleft hright]
  exact (w.image_knots_dyadic hf i.castSucc).add
    ((isDyadic_zpow (w.exponent i)).mul (hx.sub (w.dyadic i.castSucc)))

def identity : DyadicPLWitness (1 : IntervalHomeomorph) where
  pieceCount := 1
  positive := Nat.zero_lt_succ 0
  knots := Fin.cases unitIntervalZero (fun _ => unitIntervalOne)
  strictMono_knots := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [unitIntervalZero, unitIntervalOne]
    change (0 : ℝ) < 1
    exact zero_lt_one
  first := rfl
  last := rfl
  dyadic := by
    intro i
    fin_cases i
    · exact isDyadic_zero
    · exact isDyadic_one
  cover := by
    intro x
    exact ⟨0, x.property⟩
  exponent := fun _ => 0
  affine := by
    intro i x hleft hright
    simp only [IntervalHomeomorph.one_apply, zpow_zero, one_mul]
    ring

def inverse {f : IntervalHomeomorph} (w : DyadicPLWitness f) (hf : StrictMono f) :
    DyadicPLWitness f⁻¹ where
  pieceCount := w.pieceCount
  positive := w.positive
  knots := fun i => f (w.knots i)
  strictMono_knots := hf.comp w.strictMono_knots
  first := by rw [w.first, IntervalHomeomorph.map_zero hf]
  last := by rw [w.last, IntervalHomeomorph.map_one hf]
  dyadic := w.image_knots_dyadic hf
  cover := by
    intro x
    obtain ⟨i, hleft, hright⟩ := w.cover (f⁻¹ x)
    refine ⟨i, ?_, ?_⟩
    · simpa only [IntervalHomeomorph.apply_inv_apply] using hf.monotone hleft
    · simpa only [IntervalHomeomorph.apply_inv_apply] using hf.monotone hright
  exponent := fun i => -w.exponent i
  affine := by
    intro i x hleft hright
    have hleft' : w.knots i.castSucc ≤ f⁻¹ x := by
      apply hf.le_iff_le.mp
      simpa only [IntervalHomeomorph.apply_inv_apply] using hleft
    have hright' : f⁻¹ x ≤ w.knots i.succ := by
      apply hf.le_iff_le.mp
      simpa only [IntervalHomeomorph.apply_inv_apply] using hright
    have h := w.affine i (f⁻¹ x) hleft' hright'
    simp only [IntervalHomeomorph.apply_inv_apply] at h
    simp only [IntervalHomeomorph.inv_apply_apply, zpow_neg]
    have hpow : (2 : ℝ) ^ w.exponent i ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [h]
    field_simp [hpow]
    ring

end DyadicPLWitness

theorem hasDyadicPLPieces_one : HasDyadicPLPieces (1 : IntervalHomeomorph) :=
  ⟨DyadicPLWitness.identity⟩

theorem HasDyadicPLPieces.inv {f : IntervalHomeomorph}
    (h : HasDyadicPLPieces f) (hf : StrictMono f) : HasDyadicPLPieces f⁻¹ := by
  obtain ⟨w⟩ := h
  exact ⟨w.inverse hf⟩

theorem HasDyadicPLPieces.map_dyadic {f : IntervalHomeomorph}
    (h : HasDyadicPLPieces f) (hf : StrictMono f)
    {x : UnitInterval} (hx : IsDyadic (x : ℝ)) : IsDyadic (f x : ℝ) := by
  obtain ⟨w⟩ := h
  exact w.map_dyadic hf hx

namespace F

def toIntervalHomeomorph (g : F) : IntervalHomeomorph := g.val

instance : CoeFun F (fun _ => UnitInterval → UnitInterval) :=
  ⟨fun g => g.toIntervalHomeomorph⟩

def toHomeomorph (g : F) : UnitInterval ≃ₜ UnitInterval :=
  g.toIntervalHomeomorph.toHomeomorph

theorem strictMono (g : F) : StrictMono g := g.property.1

theorem hasDyadicPLPieces (g : F) : HasDyadicPLPieces g.toIntervalHomeomorph :=
  g.property.2

noncomputable def witness (g : F) : DyadicPLWitness g.toIntervalHomeomorph :=
  Classical.choice g.hasDyadicPLPieces

theorem map_dyadic (g : F) {x : UnitInterval} (hx : IsDyadic (x : ℝ)) :
    IsDyadic (g x : ℝ) :=
  g.hasDyadicPLPieces.map_dyadic g.strictMono hx

@[simp] theorem map_zero (g : F) : g unitIntervalZero = unitIntervalZero :=
  IntervalHomeomorph.map_zero g.strictMono

@[simp] theorem map_one (g : F) : g unitIntervalOne = unitIntervalOne :=
  IntervalHomeomorph.map_one g.strictMono

@[ext] theorem ext {g h : F} (heq : ∀ x, g x = h x) : g = h := by
  apply Subtype.ext
  exact IntervalHomeomorph.ext heq

end F

end ThompsonNonamenability

end OAI
