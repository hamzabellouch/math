import OAI.Dynamics.StandardMap.ArrayHalf

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal
namespace StandardMapEntropy
lemma sub_add_cancel_sigma {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite ν]
    (h : ν≤μ) : μ-ν+ν=μ := by
  have hr : ∀n:ℕ,(μ-ν+ν).restrict (spanningSets ν n)=μ.restrict (spanningSets ν n) := by
    intro n
    rw [Measure.restrict_add,Measure.restrict_sub_eq_restrict_sub_restrict (measurableSet_spanningSets ν n)]
    have : IsFiniteMeasure (ν.restrict (spanningSets ν n)) := isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top ν n).ne
    exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl h)
  have hh := Measure.restrict_iUnion_congr.mpr hr
  rwa [iUnion_spanningSets,Measure.restrict_univ,Measure.restrict_univ] at hh
lemma map_iterate_succ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map (f^[n])).map f=μ.map (f^[n+1]) := by
  rw [Measure.map_map hf (hf.iterate n)]
  congr 1
  exact funext (fun x => (Function.iterate_succ_apply' f n x).symm)
lemma map_iterate_succ' {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map f).map (f^[n])=μ.map (f^[n+1]) := by
  rw [Measure.map_map (hf.iterate n) hf]
  congr 1
lemma renewal_partial {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) (n : ℕ) :
    μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := congrArg (fun m : Measure X => m.map (f^[n])) hb
    rw [Measure.map_add _ _ (hf.iterate n),map_iterate_succ' μ f hf n,map_iterate_succ' ν f hf n] at hh
    rw [Finset.sum_range_succ]
    calc
      μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := ih
      _=μ.map (f^[n+1])+(∑j∈Finset.range n,ν.map (f^[j+1])+ν.map (f^[n+1])) := by rw [hh]; ac_rfl
lemma renewal_sum_le {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) : (Measure.sum (fun j : ℕ => ν.map (f^[j+1])))≤μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.sum_apply _ hs]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have hh : (∑j∈Finset.range n,ν.map (f^[j+1]))≤μ := by
    rw [renewal_partial μ ν f hf hb n]
    exact Measure.le_add_left le_rfl
  simpa only [Measure.finsetSum_apply] using hh s
lemma renewal_sum_balance {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → X) (hf : Measurable f) :
    Measure.sum (fun j : ℕ => ν.map (f^[j+1]))=
      (Measure.sum (fun j : ℕ => ν.map (f^[j+1]))).map f+ν.map f := by
  rw [Measure.map_sum hf.aemeasurable]
  ext s hs
  simp_rw [Measure.add_apply,Measure.sum_apply _ hs,map_iterate_succ ν f hf]
  rw [add_comm]
  exact tsum_eq_zero_add' ENNReal.summable
lemma renewal_remainder_invariant {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ]
    (f : X → X) (hf : Measurable f) (hb : μ=μ.map f+ν.map f) :
    let σ:=Measure.sum (fun j : ℕ => ν.map (f^[j+1])); (μ-σ).map f=μ-σ := by
  dsimp only
  let σ:=Measure.sum (fun j : ℕ => ν.map (f^[j+1]))
  have hσ : σ≤μ := renewal_sum_le μ ν f hf hb
  have : SigmaFinite σ := Measure.sigmaFinite_of_le μ hσ
  have he : μ-σ+σ=μ := sub_add_cancel_sigma μ σ hσ
  have hs : σ=σ.map f+ν.map f := renewal_sum_balance ν f hf
  apply (Measure.add_left_inj σ _ _).mp
  calc
    (μ-σ).map f+σ=(μ-σ).map f+σ.map f+ν.map f := by calc
      (μ-σ).map f+σ=(μ-σ).map f+(σ.map f+ν.map f) := congrArg ((μ-σ).map f+·) hs
      _=_ := (add_assoc _ _ _).symm
    _=(μ-σ+σ).map f+ν.map f := by rw [Measure.map_add _ _ hf]
    _=μ := by rw [he]; exact hb.symm
    _=μ-σ+σ := he.symm
end StandardMapEntropy

end OAI
