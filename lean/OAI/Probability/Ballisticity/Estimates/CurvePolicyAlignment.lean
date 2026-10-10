import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyPMF
import OAI.Probability.Ballisticity.Estimates.CurvePolicyLateral

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicyPMF_zero {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (hd : signedHeight e dummy = H) (ω : Environment d) (u : Lattice d)
    (hu : signedHeight e u ≠ H) :
    curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω u = 0 := by
  rw [curvePolicyPMF_apply]
  apply measure_mono_null (show {u} ⊆ {u | ¬signedHeight e u = H} by simpa)
  exact ae_iff.mp (curvePolicy_supported e f x b B H E δ α dummy hd ω)

lemma curvePolicy_alignment {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (hd : signedHeight e dummy = H) (ω : Environment d) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) (w : List (Lattice d)) :
    finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n w = finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x n w := by
  induction n generalizing i x w with
  | zero => rfl
  | succ n ih =>
    cases w with
    | nil => simp only [finitePolicyPMF_nil_succ]
    | cons u w =>
      rw [finitePolicyPMF_cons,finitePolicyPMF_cons]
      have he : alignedCurvePolicy e f b B H E hδ hα dummy i ω x =
          curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω := by
        simp only [alignedCurvePolicy,alignHeight_eq_self e _ x hx]
      rw [he]
      by_cases hu : signedHeight e u = H
      · rw [ih (i+1) (x+u) (by rw [signedHeight_add,hx,hu]; push_cast; ring)]
      · rw [curvePolicyPMF_zero e f x b B H E hδ hα dummy hd ω u hu]
        simp

theorem curvePolicy_iid_annealed {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy = H) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) (w : List (Lattice d)) :
    (∫⁻ ω, finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n w ∂environmentLaw ν) =
      finitePolicyPMF (fun _ (_ : Unit) _ => curvePolicy_average ν
        (realPosition (step e)) f b B hH E hδ hα dummy) () i x n w := by
  simp_rw [curvePolicy_alignment e f b B H E hδ hα dummy hd _ i x hx]
  exact alignedCurvePolicy_annealed ν e f b B hH E hδ hα dummy i x n w

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def iidListPMF {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (p : PMF G) (n : ℕ) : PMF (List G) :=
  ((Measure.pi fun _ : Fin n => p.toMeasure).toPMF).map List.ofFn

lemma iidListPMF_ofFn {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (p : PMF G) (n : ℕ) (f : Fin n → G) :
    iidListPMF p n (List.ofFn f) = ∏ i, p (f i) := by
  rw [iidListPMF,PMF.map_apply]
  simp only [List.ofFn_injective.eq_iff]
  rw [tsum_ite_eq' f]
  change Measure.pi (fun _ : Fin n => p.toMeasure) {f} = _
  rw [Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i _
  exact p.toMeasure_apply_singleton (f i) (measurableSet_singleton _)

lemma iidListPMF_length {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (p : PMF G) (n : ℕ) (w : List G) (hw : w.length ≠ n) :
    iidListPMF p n w = 0 := by
  rw [iidListPMF,PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro f
  have hf : w ≠ List.ofFn f := fun h => hw (by rw [h,List.length_ofFn])
  simp only [ite_eq_right hf]

lemma finitePolicyPMF_const_ofFn {G : Type*} [Add G] (p : PMF G)
    (n i : ℕ) (x : G) (f : Fin n → G) :
    finitePolicyPMF (fun _ (_ : Unit) _ => p) () i x n (List.ofFn f) = ∏ j, p (f j) := by
  induction n generalizing i x with
  | zero => simp [List.ofFn_zero,finitePolicyPMF]
  | succ n ih =>
    rw [List.ofFn_succ,finitePolicyPMF_cons,ih,Fin.prod_univ_succ]

lemma iidListPMF_eq_const {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] [Add G] (p : PMF G) (n i : ℕ) (x : G) :
    iidListPMF p n = finitePolicyPMF (fun _ (_ : Unit) _ => p) () i x n := by
  ext w
  by_cases hw : w.length=n
  · subst n
    rw [← List.ofFn_get w]
    simp only [List.length_ofFn]
    rw [iidListPMF_ofFn,finitePolicyPMF_const_ofFn]
  · rw [iidListPMF_length p n w hw,finitePolicyPMF_length _ _ _ _ _ w hw]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finitePolicyPMF_annealed_event {d : ℕ} {G : Type*} [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (p : PMF G) (havg : ∀ i x u, (∫⁻ ω, Q i ω x u ∂environmentLaw ν) = p u)
    (i : ℕ) (x : G) (n : ℕ) (B : Set (List G)) :
    (∫⁻ ω, (finitePolicyPMF Q ω i x n).toMeasure B ∂environmentLaw ν) = (iidListPMF p n).toMeasure B := by
  simp only [PMF.toMeasure_apply _ B.to_countable.measurableSet]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro w
    simp only [Set.indicator_apply]
    split_ifs with h
    · rw [finitePolicyPMF_annealed ν Q S hS hQ p havg,iidListPMF_eq_const p n i x]
    · simp
  · intro w
    simp only [Set.indicator_apply]
    split_ifs
    · exact (finitePolicyPMF_measurable_atom Q
        (fun j x u => (hQ j x u).mono (rowSigma_le _) le_rfl) i x n w).aemeasurable
    · exact aemeasurable_const

end DirectionalTransience

end

end

end OAI
