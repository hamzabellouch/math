import OAI.LinearAlgebra.MatrixMultiplication.Numerical.AllFieldCertificatesReplaySemantics
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.AllFieldCertificatesReplayStatic

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.AllFieldCertificates.Replay

theorem Op.before_refs (op : Op) (n : ℕ) (h : op.before n = true) :
    ∀ j ∈ op.refs, j < n := by
  cases op <;> simp_all [Op.before, Op.refs]

theorem checkedProgramValues_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    (p : Program) (ops : ℕ → Op) (bs : ℕ → Ball) (count : ℕ)
    (hget : ∀ i < count, p[i]? = some (ops i))
    (hc : RangeChecked two ops bs 0 count) :
    ∀ i < count, (bs i).Encloses (p.eval[i]?.getD 0) := by
  apply checkedValues_sound htwo ops bs _ count
  · intro i hi
    obtain ⟨w, hw⟩ := hc i (Nat.zero_le i) hi
    simp only [checkAt, Bool.and_eq_true] at hw
    exact p.eval_get i (ops i) (hget i hi) ((ops i).before_refs i hw.1.2)
  · intro i hi
    exact hc i (Nat.zero_le i) hi

def programOfLookup (ops : ℕ → Op) (count : ℕ) : Program :=
  Array.ofFn (fun i : Fin count => ops i)

theorem programOfLookup_get (ops : ℕ → Op) (count i : ℕ) (hi : i < count) :
    (programOfLookup ops count)[i]? = some (ops i) := by
  have hh : i < (programOfLookup ops count).size := by simpa [programOfLookup] using hi
  rw [Array.getElem?_eq_getElem hh]
  simp [programOfLookup]

theorem checkedLookupValues_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    (ops : ℕ → Op) (bs : ℕ → Ball) (count : ℕ)
    (hc : RangeChecked two ops bs 0 count) :
    ∀ i < count, (bs i).Encloses ((programOfLookup ops count).eval[i]?.getD 0) :=
  checkedProgramValues_sound htwo _ ops bs count (fun i hi => programOfLookup_get ops count i hi) hc

theorem checkedLookup_positive {two : Ball} (htwo : two.Encloses (Real.log 2))
    (ops : ℕ → Op) (bs : ℕ → Ball) (count : ℕ)
    (hc : RangeChecked two ops bs 0 count) (i : ℕ) (hi : i < count)
    (hpos : 0 < (bs i).lower) : 0 < (programOfLookup ops count).eval[i]?.getD 0 := by
  have h := (Ball.bounds (checkedLookupValues_sound htwo ops bs count hc i hi)).1
  have hp : (0 : ℝ) < (bs i).lower := by exact_mod_cast hpos
  exact hp.trans_le h

theorem checkedLookup_upper {two : Ball} (htwo : two.Encloses (Real.log 2))
    (ops : ℕ → Op) (bs : ℕ → Ball) (count : ℕ)
    (hc : RangeChecked two ops bs 0 count) (i : ℕ) (hi : i < count) (bound : ℚ)
    (hu : (bs i).upper < bound) : (programOfLookup ops count).eval[i]?.getD 0 < (bound : ℝ) := by
  have h := (Ball.bounds (checkedLookupValues_sound htwo ops bs count hc i hi)).2
  have hb : ((bs i).upper : ℝ) < (bound : ℝ) := Rat.cast_lt.mpr hu
  exact h.trans_lt hb

end MatrixMultiplication.AllFieldCertificates.Replay

end OAI
