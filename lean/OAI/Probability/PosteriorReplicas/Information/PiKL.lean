import OAI.Probability.PosteriorReplicas.Information.KLTools
import OAI.Probability.PosteriorReplicas.Kernels.KernelPi

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma probability_measure_eq_of_subsingleton {X : Type*} [MeasurableSpace X] [Subsingleton X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s hs
  by_cases h : s.Nonempty
  · have he : s = univ := by
      obtain ⟨x,hx⟩ := h
      apply eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y x] using hx
    simp [he]
  · simp [Set.not_nonempty_iff_eq_empty.mp h]

def coordinateMarginal {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) (i : Fin n) : Measure Y := q.map (fun u => u i)

instance coordinateMarginal_probability {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) [IsProbabilityMeasure q] (i : Fin n) :
    IsProbabilityMeasure (coordinateMarginal q i) :=
  inferInstanceAs (IsProbabilityMeasure (q.map (fun u => u i)))

def marginalProduct {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) : Measure (Fin n → Y) := Measure.pi (coordinateMarginal q)

instance marginalProduct_probability {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) [IsProbabilityMeasure q] : IsProbabilityMeasure (marginalProduct q) := by
  unfold marginalProduct
  infer_instance

lemma piFinSucc_fst {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin (n+1) → Y)) :
    (q.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0)).fst =
      coordinateMarginal q 0 := by
  rw [Measure.fst, Measure.map_map measurable_fst (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).measurable]
  rfl

lemma piFinSucc_tail_marginal {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin (n+1) → Y)) (i : Fin n) :
    coordinateMarginal (q.map (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n+1) => Y) 0)).snd i = coordinateMarginal q i.succ := by
  unfold coordinateMarginal Measure.snd
  rw [Measure.map_map measurable_snd (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).measurable,
    Measure.map_map (measurable_pi_apply i) (measurable_snd.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).measurable)]
  rfl

lemma klDiv_pi_decomposition {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {n : ℕ} (q : Measure (Fin n → Y)) [IsProbabilityMeasure q]
    (ρ : Fin n → Measure Y) [∀ i, IsProbabilityMeasure (ρ i)] :
    klDiv q (Measure.pi ρ) = klDiv q (marginalProduct q) + ∑ i, klDiv (coordinateMarginal q i) (ρ i) := by
  induction n with
  | zero =>
    have h1 := probability_measure_eq_of_subsingleton q (Measure.pi ρ)
    have h2 := probability_measure_eq_of_subsingleton q (marginalProduct q)
    simp only [← h1, ← h2, klDiv_self, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0
    let r := q.map e
    have : IsProbabilityMeasure r := inferInstance
    have hρ : (Measure.pi ρ).map e = (ρ 0).prod (Measure.pi (fun i : Fin n => ρ i.succ)) :=
      (measurePreserving_piFinSuccAbove ρ 0).map_eq
    have ho : (marginalProduct q).map e = r.fst.prod (marginalProduct r.snd) := by
      rw [marginalProduct, (measurePreserving_piFinSuccAbove (coordinateMarginal q) 0).map_eq]
      congr 1
      · exact (piFinSucc_fst q).symm
      · unfold marginalProduct
        congr 1
        funext i
        exact (piFinSucc_tail_marginal q i).symm
    have hD : klDiv q (Measure.pi ρ) =
        klDiv r.fst (ρ 0) + klDiv r.snd (Measure.pi (fun i : Fin n => ρ i.succ)) +
          klDiv r (r.fst.prod r.snd) := by
      rw [← klDiv_map_equiv _ _ e, hρ]
      exact klDiv_prod_decomposition r (ρ 0) _
    have hC : klDiv q (marginalProduct q) =
        klDiv r.snd (marginalProduct r.snd) + klDiv r (r.fst.prod r.snd) := by
      rw [← klDiv_map_equiv _ _ e, ho, klDiv_prod_decomposition r r.fst _, klDiv_self, zero_add]
    rw [hD, hC, ih r.snd (fun i : Fin n => ρ i.succ), Fin.sum_univ_succ]
    have hf : r.fst = coordinateMarginal q 0 := piFinSucc_fst q
    have ht : ∀ i : Fin n, coordinateMarginal r.snd i = coordinateMarginal q i.succ :=
      piFinSucc_tail_marginal q
    simp_rw [hf, ht]
    ac_rfl

end PosteriorReplicas
end

end OAI
