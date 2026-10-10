import OAI.NumberTheory.Ostmann.Construction.WordTransferPeriods

namespace OAI

/-! # Exact polynomial support of one original arithmetic transfer node -/

namespace Ostmann

open scoped Classical

noncomputable def HistoryFormula.integerValue {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) : ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator / F.cleared.denominator

theorem HistoryFormula.smallDivisionTest_of_value {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.value (fun i => (x i : ℚ)) = y) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔ IsUnit (y : ZMod m) := by
  have he := F.cleared.integer_value_cleared x y hy
  simp only [smallDivisionTest, he, dvd_mul_right, true_and,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

theorem HistoryFormula.smallDivisionTest_iff {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔
      ∃ y : ℤ, F.value (fun i => (x i : ℚ)) = y ∧ IsUnit (y : ZMod m) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (F.integralAt_iff x).mpr h.1
    exact ⟨y, hy, (F.smallDivisionTest_of_value x y hy m).mp h⟩
  · rintro ⟨y, hy, hu⟩
    exact (F.smallDivisionTest_of_value x y hy m).mpr hu

structure WordTransferGuard (σ : Type*) where
  pivot : HistoryFormula σ
  rightProduct : HistoryFormula σ
  root : ℤ
  left : ℤ
  right : ℤ
  childBound : ℕ
  pivotBound : ℕ

noncomputable def WordTransferGuard.ValidAt {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ) : Prop :=
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.pivot.cleared.numerator)
    g.pivot.cleared.denominator g.right.natAbs ∧
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.rightProduct.cleared.numerator)
    g.rightProduct.cleared.denominator g.root.natAbs ∧
  1 ≤ g.pivot.realValue x ∧ g.pivot.realValue x ≤ g.pivotBound ∧
  (2 * g.pivotBound * g.childBound : ℕ) < g.rightProduct.realValue x ∧
  g.left.natAbs ≤ g.childBound ∧ g.right.natAbs ≤ g.childBound

noncomputable def wordTransferGuard {σ : Type*} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (env : σ → HistoryFormula σ) : WordTransferGuard σ where
  pivot := (wordTransferStep d s v w hs).formula.bind env
  rightProduct := HistoryFormula.listProduct (d.right.map env)
  root := s
  left := v
  right := w
  childBound := d.childBound
  pivotBound := d.pivotBound

/-- All original node conditions are represented: both coprimality tests,
integrality, positive bounded pivot, child-frequency bounds and strict gap. -/
theorem wordTransferGuard_iff {σ : Type*} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (s v w : ℤ) (hs : s ≠ 0)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (wordTransferGuard d s v w hs env).ValidAt a ↔
      ∃ P, ValidTransferNode (wordTransferSystem σ)
        ((WordTransferTemplate.node d l r).state x) s v w P := by
  let step := wordTransferStep d s v w hs
  let f := step.formula.bind env
  let g := HistoryFormula.listProduct (d.right.map env)
  let R := (d.right.map x).prod
  let L := (d.left.map x).prod
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  have hright : g.value (fun j => (a j : ℚ)) = (R : ℤ) := by
    have hh := BranchingWordHistory.wordFormula_value d.right env (fun j => (a j : ℚ))
      (fun i => (x i : ℤ)) (by intro i; simpa only [Int.cast_natCast] using henv i)
    have hc : (d.right.map (fun i => (x i : ℤ))).prod = (R : ℤ) := hcast d.right
    exact hh.trans (congrArg (fun z : ℤ => (z : ℚ)) hc)
  have hrightR : g.realValue a = (R : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hright, Rat.cast_intCast, Int.cast_natCast]
  have hf : f.value (fun j => (a j : ℚ)) = ((v * (R : ℤ) - w * (L : ℤ) : ℤ) : ℚ) / s := by
    rw [HistoryFormula.value_bind]
    have he : (fun i => (env i).value (fun j => (a j : ℚ))) = fun i => ((x i : ℤ) : ℚ) := by
      funext i; simpa only [Int.cast_natCast] using henv i
    rw [he, HistoryPivotStep.formula_value, wordTransferStep_numerator]
    rfl
  have hroot : IsUnit ((R : ℤ) : ZMod s.natAbs) ↔ IsCoprime s (R : ℤ) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]
  change (smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a f.cleared.numerator) f.cleared.denominator w.natAbs ∧
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a g.cleared.numerator) g.cleared.denominator s.natAbs ∧
    1 ≤ f.realValue a ∧ f.realValue a ≤ d.pivotBound ∧
    (2 * d.pivotBound * d.childBound : ℕ) < g.realValue a ∧
    v.natAbs ≤ d.childBound ∧ w.natAbs ≤ d.childBound) ↔ _
  rw [f.smallDivisionTest_iff, g.smallDivisionTest_of_value a (R : ℤ) hright,
    hrightR, hroot]
  constructor
  · rintro ⟨⟨Y, hY, hunit⟩, hcop, hlo, hhi, hgap, hv, hw⟩
    have hreal : f.realValue a = (Y : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hY, Rat.cast_intCast]
    rw [hreal] at hlo hhi
    have hY0 : 0 ≤ Y := by exact_mod_cast (show (0 : ℝ) ≤ Y by linarith)
    let P := Y.toNat
    have hPY : (P : ℤ) = Y := Int.toNat_of_nonneg hY0
    have hrel : v * (R : ℤ) - w * (L : ℤ) = s * P := by
      have he := (div_eq_iff (Int.cast_ne_zero.mpr hs)).mp (hf.symm.trans hY)
      have hi : v * (R : ℤ) - w * (L : ℤ) = Y * s := by exact_mod_cast he
      rw [hi, hPY, mul_comm]
    refine ⟨P, ⟨hs, hcop, hrel, ?_, ?_, hv, hw, ?_, ?_⟩⟩
    · have : (1 : ℤ) ≤ P := by rw [hPY]; exact_mod_cast hlo
      omega
    · have : (P : ℤ) ≤ d.pivotBound := by rw [hPY]; exact_mod_cast hhi
      exact_mod_cast this
    · exact_mod_cast hgap
    · have hu : IsUnit (P : ZMod w.natAbs) := by
        simpa only [← hPY, Int.cast_natCast] using hunit
      exact (ZMod.isUnit_iff_coprime P w.natAbs).mp hu
  · rintro ⟨P, hp⟩
    have hvalue : f.value (fun j => (a j : ℚ)) = (P : ℤ) := by
      have he : v * (R : ℤ) - w * (L : ℤ) = s * P := hp.relation
      rw [hf, he]
      push_cast
      exact mul_div_cancel_left₀ (P : ℚ) (Int.cast_ne_zero.mpr hs)
    have hreal : f.realValue a = (P : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hvalue, Rat.cast_intCast, Int.cast_natCast]
    refine ⟨⟨(P : ℤ), hvalue, ?_⟩, hp.root_unit, ?_, ?_, ?_, hp.left_bound, hp.right_bound⟩
    · simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime P w.natAbs).mpr hp.pivot_unit
    · rw [hreal]; exact_mod_cast hp.pivot_pos
    · rw [hreal]; exact_mod_cast hp.pivot_bound
    · exact_mod_cast hp.range_gap

end Ostmann

end OAI
