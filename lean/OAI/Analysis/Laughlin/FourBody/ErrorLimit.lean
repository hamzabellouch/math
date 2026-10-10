import OAI.Analysis.Laughlin.FourBody.CoefficientLimit
import OAI.Analysis.Laughlin.Operators.Certificate

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def sourceAlpha (t : ℕ) (e : ℕ × ℕ × ℤ) : ℝ :=
  (e.2.2 : ℝ)/(10^7) * Real.sqrt ((2 : ℝ)^((e.1 : ℤ)-t) *
    ((t.factorial : ℝ)*((e.1+e.2.1-t).factorial : ℝ) /
      ((e.1.factorial : ℝ)*(e.2.1.factorial : ℝ))))

noncomputable def fourErrorEntry (Q D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℝ :=
  let i := e.1+e.2.1-t
  let k := f.1+f.2.1-t
  let T := e.1+e.2.1+k
  if D ≤ T then sourceAlpha t e * sourceAlpha t f *
    fourBodyCoefficient Q r D T e.1 e.2.1 k * fourBodyCoefficient Q s D T f.1 f.2.1 i else 0

noncomputable def fourErrorLimitEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℝ :=
  let i := e.1+e.2.1-t
  let k := f.1+f.2.1-t
  let T := e.1+e.2.1+k
  if D ≤ T then sourceAlpha t e * sourceAlpha t f *
    fourBodyLimitCoefficient r D T e.1 e.2.1 k * fourBodyLimitCoefficient s D T f.1 f.2.1 i else 0

theorem fourErrorEntry_tendsto (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    Tendsto (fun Q => fourErrorEntry Q D r s t e f) atTop (𝓝 (fourErrorLimitEntry D r s t e f)) := by
  unfold fourErrorEntry fourErrorLimitEntry
  dsimp only
  by_cases hD : D ≤ e.1+e.2.1+(f.1+f.2.1-t)
  · simp only [ite_eq_left hD]
    exact (tendsto_const_nhds.mul
      (source_fourBody_coefficient_tendsto r D _ e.1 e.2.1 _ hr hD rfl)).mul
      (source_fourBody_coefficient_tendsto s D _ f.1 f.2.1 _ hs hD (by omega))
  · simp only [ite_eq_right hD]; exact tendsto_const_nhds

theorem physical_list_sum_tendsto {I : Type*} (l : List I) (f : ℕ → I → ℝ) (g : I → ℝ)
    (h : ∀ i ∈ l, Tendsto (fun Q => f Q i) atTop (𝓝 (g i))) :
    Tendsto (fun Q => (l.map (f Q)).sum) atTop (𝓝 ((l.map g).sum)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

noncomputable def fourErrorRow (Q D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℝ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => fourErrorEntry Q D r s row.1 e f)).sum)).sum
noncomputable def fourErrorLimitRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℝ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => fourErrorLimitEntry D r s row.1 e f)).sum)).sum

noncomputable def physicalFourError (Q D r s : ℕ) : ℝ :=
  -(Certificate.rows.map (fourErrorRow Q D r s)).sum
noncomputable def limitFourError (D r s : ℕ) : ℝ :=
  -(Certificate.rows.map (fourErrorLimitRow D r s)).sum

theorem physicalFourError_tendsto (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D) :
    Tendsto (fun Q => physicalFourError Q D r s) atTop (𝓝 (limitFourError D r s)) := by
  apply Filter.Tendsto.neg
  apply physical_list_sum_tendsto
  intro row hrow
  apply physical_list_sum_tendsto
  intro e he
  apply physical_list_sum_tendsto
  intro f hf
  exact fourErrorEntry_tendsto D r s row.1 e f hr hs
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)

end Laughlin.Spin

end OAI
