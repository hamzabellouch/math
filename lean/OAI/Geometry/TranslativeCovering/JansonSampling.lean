import OAI.Geometry.TranslativeCovering.FiniteJanson

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set

universe u_1 u_2 u_3

namespace FiniteJanson

variable {Ω : Type u_1} {V : Type u_2} [MeasurableSpace Ω] [Fintype V]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : V → Ω → Bool}

noncomputable def successProb (P : Measure Ω) (X : V → Ω → Bool) (v : V) : ℝ :=
  P.real {ω | X v ω = true}

omit [Fintype V] in
theorem successProb_mem (v : V) :
    0 ≤ successProb P X v ∧ successProb P X v ≤ 1 :=
  ⟨measureReal_nonneg, by
    exact (measureReal_mono (μ := P) (subset_univ _)).trans_eq probReal_univ⟩

theorem joint_atom (hX : ∀ v, Measurable (X v)) (hind : iIndepFun X P)
    (x : V → Bool) :
    P.real {ω | (fun v => X v ω) = x} = atom (successProb P X) x := by
  have he : {ω | (fun v => X v ω) = x} =
      ⋂ v ∈ (Finset.univ : Finset V), X v ⁻¹' {x v} := by
    ext ω
    simp [funext_iff]
  rw [he, measureReal_def, hind.measure_inter_preimage_eq_mul _
    (fun v _ => measurableSet_singleton (x v)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro v _
  change P.real (X v ⁻¹' {x v}) = if x v then successProb P X v else 1 - successProb P X v
  cases hx : x v
  · have hc : X v ⁻¹' {false} = {ω | X v ω = true}ᶜ := by
      ext ω
      cases X v ω <;> simp
    rw [hc]
    exact probReal_compl_eq_one_sub ((hX v) (measurableSet_singleton true))
  · rfl

theorem joint_event (hX : ∀ v, Measurable (X v)) (hind : iIndepFun X P)
    (A : Set (V → Bool)) :
    P.real {ω | (fun v => X v ω) ∈ A} = prob (successProb P X) A := by
  classical
  let J : Ω → (V → Bool) := fun ω v => X v ω
  have hJ : Measurable J := Measurable.of_eval hX
  change P.real (J ⁻¹' A) = _
  calc
    P.real (J ⁻¹' A) =
        ∑ x ∈ Finset.univ.filter (fun x => x ∈ A), P.real (J ⁻¹' {x}) := by
      rw [sum_measureReal_preimage_singleton _ (fun x _ =>
        hJ (measurableSet_singleton x))]
      simp
    _ = prob (successProb P X) A := by
      rw [Finset.sum_filter]
      unfold prob
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · exact joint_atom hX hind x
      · rfl

theorem janson_of_iIndepFun {ι : Type u_3} [Fintype ι]
    (hX : ∀ v, Measurable (X v)) (hind : iIndepFun X P)
    (H : ι → Finset V) (s : Finset ι) (hH : ∀ i ∈ s, (H i).Nonempty)
    (hm : 0 < mean (successProb P X) H s) :
    mean (successProb P X) H s ≤ depSum (successProb P X) H s ∧
    P.real {ω | ∀ i ∈ s, ¬ ∀ v ∈ H i, X v ω = true} ≤
      Real.exp (-(mean (successProb P X) H s)^2 /
        (2 * depSum (successProb P X) H s)) := by
  have hj := janson (fun v => successProb_mem (P := P) (X := X) v) H s hH hm
  refine ⟨hj.1, ?_⟩
  have he := joint_event hX hind (avoids H s)
  change P.real {ω | (fun v => X v ω) ∈ avoids H s} ≤ _
  rw [he]
  exact hj.2

end FiniteJanson

end OAI
