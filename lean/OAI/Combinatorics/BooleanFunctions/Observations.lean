import OAI.Combinatorics.BooleanFunctions.Projection
import OAI.Combinatorics.BooleanFunctions.FiniteCLT

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

variable {γ β κ : Type*} [Fintype γ] [Fintype β] [Fintype κ]
  [DecidableEq γ] [DecidableEq κ]

def cubeSum (x : Cube γ) : ℝ := ∑ i, sign (x i)
def score (F : Cube γ → β) : Cube γ → ℝ := conditionalAverage F cubeSum
def variance (F : Cube γ → β) : ℝ := average (fun x => (score F x)^2)

omit [Fintype β] [Fintype κ] in
theorem cubeSum_zero : average (cubeSum (γ := γ)) = 0 := by
  unfold cubeSum
  rw [average_sum]
  have hz : average sign = 0 := by norm_num [average,sign,Fintype.sum_bool]
  have hi (i : γ) : average (fun x : Cube γ => sign (x i)) = 0 := by
    calc _ = average sign := by
           convert average_pi_eval i sign using 1
           congr 1
           exact Subsingleton.elim _ _
      _ = 0 := hz
  simp only [hi,Finset.sum_const_zero]

omit [Fintype κ] in
theorem score_zero (F : Cube γ → β) : average (score F) = 0 := by
  rw [score,average_conditionalAverage]
  exact cubeSum_zero

omit [Fintype β] [DecidableEq γ] [DecidableEq κ] in
theorem cubeSum_block (x : Cube (κ × γ)) :
    cubeSum x = ∑ j, cubeSum (fun i => x (j,i)) := by
  exact Fintype.sum_prod_type _

def grouped (F : Cube γ → β) (x : Cube (κ × γ)) : κ → β :=
  fun j => F (fun i => x (j,i))

omit [DecidableEq γ] [DecidableEq κ] in
theorem grouped_degree (F : Cube γ → β) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) (b : κ → β) :
    fourierDegree (cell (grouped F) b) ≤ Fintype.card κ*D := by
  have h := fourierDegree_comp_tuple_le (fun j x => F (fun i => x (j,i))) (fun _ : κ => D)
      (fun j a => fourierDegree_block_cell_le F D hF j a) (cell id b)
  have he : (fun x : Cube (κ × γ) => cell id b (fun j => F (fun i => x (j,i)))) =
      cell (grouped F) b := by
    funext x
    unfold cell grouped
    rfl
  rw [he] at h
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using h

theorem grouped_score (F : Cube γ → β) :
    score (grouped (κ := κ) F) = fun x => ∑ j, score F (fun i => x (j,i)) := by
  let e := blockCurry κ γ Bool
  let G : (κ → Cube γ) → (κ → β) := fun x j => F (x j)
  let R : (κ → Cube γ) → ℝ := fun x => ∑ j, cubeSum (x j)
  have he : cubeSum (γ := κ × γ) = R ∘ e := by funext x; exact cubeSum_block x
  have hp := Projection.conditional_tuple_sum (ι := κ) F cubeSum
  have hc := Projection.conditional_equiv e G R
  have hscore : conditionalAverage (G ∘ e) (cubeSum (γ := κ × γ)) =
      (fun x => ∑ j, conditionalAverage F cubeSum (x j)) ∘ e := by
    rw [he,hc]
    exact congrArg (fun p => p ∘ e) hp
  convert hscore using 1
  · unfold score
    congr 1
  · unfold score
    funext x
    apply Finset.sum_congr rfl
    intro j _
    congr 1


omit [Fintype β] [Fintype κ] [DecidableEq κ] in
theorem variance_nonneg (F : Cube γ → β) : 0 ≤ variance F :=
  average_nonneg (fun _ => sq_nonneg _)

def standardValue (F : Cube γ → β) (b : β) : ℝ :=
  (Real.sqrt (variance F))⁻¹*conditionalValue F cubeSum b

def standard (F : Cube γ → β) (x : Cube γ) : ℝ := standardValue F (F x)

omit [Fintype κ] [DecidableEq κ] in
theorem standard_zero (F : Cube γ → β) : average (standard F) = 0 := by
  change average (fun x => (Real.sqrt (variance F))⁻¹*score F x) = 0
  rw [average_const_mul,score_zero,mul_zero]

omit [Fintype β] [Fintype κ] [DecidableEq κ] in
theorem standard_sq (F : Cube γ → β) (hv : 0 < variance F) :
    average (fun x => (standard F x)^2) = 1 := by
  change average (fun x => ((Real.sqrt (variance F))⁻¹*score F x)^2) = 1
  simp only [mul_pow,average_const_mul,inv_pow]
  rw [Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

end Observations
end SquareRootDegree

end

end OAI
