import OAI.Analysis.Laughlin.FourBody.ErrorLimit
import OAI.Analysis.Laughlin.FourBody.RadicalCancellation

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sourceAlpha_factor (t : ℕ) (e : ℕ × ℕ × ℤ) :
    sourceAlpha t e = (e.2.2 : ℝ)/(10^7) * alphaRadical t e.1 e.2.1 := rfl

theorem fourErrorLimitEntry_certificate (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s)
    (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    fourErrorLimitEntry D r s t e f =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yEntry D r s t e f : ℝ) := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp only at he hf ⊢
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  by_cases hD : D ≤ T
  · have heq : fourErrorLimitEntry D r s t (p,j,a) (q,l,b) =
        sourceAlpha t (p,j,a) * sourceAlpha t (q,l,b) *
          fourBodyLimitCoefficient r D T p j k * fourBodyLimitCoefficient s D T q l i := by
      simp only [fourErrorLimitEntry]; exact ite_eq_left hD
    rw [heq,sourceAlpha_factor,sourceAlpha_factor,
      source_fourBody_radical_coefficient r D T p j k hr hD rfl,
      source_fourBody_radical_coefficient s D T q l i hs hD hT']
    dsimp only
    calc
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k * fourBodyRadical s D T q l i) := by ring
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)*sourceYFactor D r s t p j q l) := by
        rw [source_Y_radical_cancellation D r s t p j q l hor hos he hf]
      _ = _ := by
        simp only [Certificate.yEntry]
        rw [ite_eq_left hD]
        push_cast
        dsimp [sourceYFactor,i,k,T]
        ring
  · simp only [fourErrorLimitEntry,Certificate.yEntry]
    rw [ite_eq_right hD,ite_eq_right hD]
    simp

theorem real_list_sum_scale {I : Type*} (l : List I) (c : ℝ) (f : I → ℝ) :
    (l.map (fun i => c*f i)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem fourErrorLimitRow_certificate (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
    fourErrorLimitRow D r s row =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ) := by
  unfold fourErrorLimitRow
  have he : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      fourErrorLimitEntry D r s row.1 e f =
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ) := by
    intro e he f hf
    exact fourErrorLimitEntry_certificate D r s row.1 e f hr hs hor hos
      (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left; intro e he'
      apply congrArg List.sum
      apply List.map_congr_left; intro f hf'
      exact he e he' f hf'
    _ = _ := by
      simp_rw [real_list_sum_scale]
      unfold Certificate.yRow
      push_cast
      simp only [List.map_map,Function.comp_def]
      push_cast
      simp only [List.map_map,Function.comp_def]

theorem source_fourBody_error_certificate_identity (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    limitFourError D r s = Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
      (Certificate.Y D r s : ℝ) := by
  unfold limitFourError
  have he : Certificate.rows.map (fourErrorLimitRow D r s) = Certificate.rows.map (fun row =>
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ)) := by
    apply List.map_congr_left; intro row hrow
    exact fourErrorLimitRow_certificate D r s hr hs hor hos row hrow
  rw [he,real_list_sum_scale]
  unfold Certificate.Y
  push_cast
  simp only [List.map_map,Function.comp_def]
  ring

end Laughlin.Spin

end OAI
