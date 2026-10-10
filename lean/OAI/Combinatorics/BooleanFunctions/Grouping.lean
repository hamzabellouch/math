import OAI.Combinatorics.BooleanFunctions.CellDegree
import OAI.Combinatorics.BooleanFunctions.Producer

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
open Switching FiniteCLT UniformFinite GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

variable {α δ ι : Type*} [Fintype α] [Fintype δ] [Fintype ι]

def eventCongr (e : α ≃ δ) : EventSpace α ι ≃ EventSpace δ ι :=
  Equiv.prodCongr e (Equiv.piCongrRight (fun _ : ι => e))

theorem deficit_equiv (e : α ≃ δ) (T : δ → ℝ) (b : ℝ)
    (a : EventSpace δ ι → ℝ) :
    SoftEvent.deficit (T ∘ e) b (a ∘ eventCongr e) = SoftEvent.deficit T b a := by
  unfold SoftEvent.deficit
  convert average_equiv (eventCongr (ι := ι) e)
    (fun x => a x*(1-(T x.1+∑ j, T (x.2 j)-b)^2)) using 1
  congr 1

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

def groupScale (F : Cube γ → β) (n : ℕ) : ℝ := Real.sqrt n * Real.sqrt (variance F)
def groupStandard (F : Cube γ → β) (n : ℕ) : Cube (Fin n × γ) → ℝ :=
  normalizedSum (standard F) n ∘ blockCurry (Fin n) γ Bool

omit [Fintype α] [Fintype δ] [Fintype ι] [Fintype β] in
theorem groupScale_sq (F : Cube γ → β) (n : ℕ) :
    (groupScale F n)^2 = n*variance F := by
  rw [groupScale,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt (variance_nonneg F)]

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem grouped_score_scaled (F : Cube γ → β) (hv : 0 < variance F) {n : ℕ} (hn : 0 < n) :
    score (grouped (κ := Fin n) F) = fun x => groupScale F n * groupStandard F n x := by
  rw [grouped_score]
  funext x
  simp only [groupScale,groupStandard,normalizedSum,Function.comp_apply,blockCurry,Equiv.coe_fn_mk,
    standard,standardValue,← Finset.mul_sum]
  have hv' := (Real.sqrt_pos.mpr hv).ne'
  have hn' := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  unfold score conditionalAverage
  field_simp

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem groupStandard_zero (F : Cube γ → β) (n : ℕ) : average (groupStandard F n) = 0 := by
  rw [groupStandard]
  change average (fun x => normalizedSum (standard F) n (blockCurry (Fin n) γ Bool x)) = 0
  rw [average_equiv]
  exact average_normalizedSum (standard F) (standard_zero F) n

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem groupStandard_sq (F : Cube γ → β) (hv : 0 < variance F) {n : ℕ} (hn : 0 < n) :
    average (fun x => (groupStandard F n x)^2) = 1 := by
  unfold groupStandard
  rw [show (fun x => (normalizedSum (standard F) n ∘ blockCurry (Fin n) γ Bool) x ^ 2) =
    (fun x => (normalizedSum (standard F) n x)^2) ∘ blockCurry (Fin n) γ Bool from rfl]
  change average (fun x => (normalizedSum (standard F) n (blockCurry (Fin n) γ Bool x))^2) = 1
  exact (average_equiv (blockCurry (Fin n) γ Bool)
    (fun x => (normalizedSum (standard F) n x)^2)).trans
    (average_normalizedSum_sq (standard F) (standard_zero F) (standard_sq F hv) hn)

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem exists_amplification (F : Cube γ → β) (hv : 0 < variance F) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : (Fin n → β) → Leaves, ∃ L : Leaves → (Fin n → β) → Bool,
      (n:ℝ)*variance F*(Fintype.card Leaves+1+eta) <
        variance (switched (grouped (κ := Fin n) F) S L) := by
  let : MeasurableSpace (Cube γ) := ⊤
  obtain ⟨n,hn,b,S,L,hg⟩ := Producer.exists_table_gain F (standardValue F)
    (standard_zero F) (standard_sq F hv)
  refine ⟨n,hn,S,L,?_⟩
  let G := grouped (κ := Fin n) F
  let T := groupStandard F n
  let A := TableRounding.tableEvent S L
  have hd : eta < SoftEvent.deficit T b
      (fun x => if A (oldLabels G x) then 1 else 0) := by
    have he := deficit_equiv (blockCurry (Fin n) γ Bool)
      (normalizedSum (standard F) n) b
      (fun x => if A ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0)
    have hA : (fun x : EventSpace (Cube (Fin n × γ)) Leaves => if A (oldLabels G x) then (1:ℝ) else 0) =
        (fun x => if A ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0) ∘
          eventCongr (blockCurry (Fin n) γ Bool) := rfl
    change eta < SoftEvent.deficit (normalizedSum (standard F) n ∘ blockCurry (Fin n) γ Bool) b _
    rw [hA,he]
    exact hg
  have hr := retained_gain G A T (normalizedSum (standardValue F) n) (fun _ => rfl) b eta
    (groupStandard_zero F n) (groupStandard_sq F hv hn) hd
  have hs := switched_variance_scaled G S L T (groupScale F n) (grouped_score_scaled F hv hn)
  rw [groupScale_sq] at hs
  rw [hs]
  have hnV : 0 < (n:ℝ)*variance F := mul_pos (Nat.cast_pos.mpr hn) hv
  exact mul_lt_mul_of_pos_left hr hnV

end Observations
end SquareRootDegree

end

end OAI
