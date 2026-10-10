import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyMaximal

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finitePolicyPMF_prefix_event {Ω G : Type*} [AddMonoid G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) {j N : ℕ} (hj : j ≤ N)
    (B : G → Prop) :
    (finitePolicyPMF Q ω i x N).toMeasure {w | B (x+(w.take j).sum)} =
      (finitePolicyPMF Q ω i x j).toMeasure {w | B (x+w.sum)} := by
  have he := congrArg (fun p : PMF (List G) => p.toMeasure {w | B (x+w.sum)})
    (finitePolicyPMF_take Q ω i x j (N-j))
  rw [Nat.add_sub_of_le hj,PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _)
    (Set.to_countable _ |>.measurableSet)] at he
  exact he

lemma finitePolicyPMF_fresh_failure {d : ℕ} {G : Type*} [AddMonoid G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (Bad : Environment d → G → Prop) (i n : ℕ) (x : G)
    (hB : ∀ y, @MeasurableSet _ (rowSigma (S (i+n))) {ω | Bad ω y})
    (p : ℝ≥0∞) (havg : ∀ y, environmentLaw ν {ω | Bad ω y} = p) :
    (∫⁻ ω, (finitePolicyPMF Q ω i x n).toMeasure {w | Bad ω (x+w.sum)} ∂environmentLaw ν) = p := by
  simp_rw [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
  have he (ω : Environment d) (w : List G) :
      ({w | Bad ω (x+w.sum)}.indicator (finitePolicyPMF Q ω i x n)) w =
        finitePolicyPMF Q ω i x n w * (if Bad ω (x+w.sum) then 1 else 0) := by
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
    split_ifs <;> simp
  simp_rw [he]
  apply finitePolicyPMF_fresh_test ν Q S hS hQ (fun ω y => if Bad ω y then 1 else 0) i n x
    (fun y => Measurable.ite (hB y) measurable_const measurable_const) p
  intro y
  have hm := (rowSigma_le _) _ (hB y)
  change (∫⁻ ω, ({ω | Bad ω y}.indicator (fun _ => (1:ℝ≥0∞))) ω ∂environmentLaw ν) = p
  rw [lintegral_indicator hm]
  simpa only [lintegral_one,Measure.restrict_apply_univ] using havg y

lemma finitePolicyPMF_failure_union {d : ℕ} {G : Type*} [AddMonoid G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (Bad : ℕ → Environment d → G → Prop)
    (hB : ∀ j y, @MeasurableSet _ (rowSigma (S j)) {ω | Bad j ω y})
    (p : ℝ≥0∞) (havg : ∀ j y, environmentLaw ν {ω | Bad j ω y} = p)
    (i N : ℕ) (x : G) :
    (∫⁻ ω, (finitePolicyPMF Q ω i x N).toMeasure
      {w | ∃ j < N, Bad (i+j) ω (x+(w.take j).sum)} ∂environmentLaw ν) ≤ (N:ℝ≥0∞)*p := by
  have hpt (ω : Environment d) :
      (finitePolicyPMF Q ω i x N).toMeasure {w | ∃ j < N, Bad (i+j) ω (x+(w.take j).sum)} ≤
        ∑ j ∈ Finset.range N, (finitePolicyPMF Q ω i x j).toMeasure {w | Bad (i+j) ω (x+w.sum)} := by
    rw [show {w : List G | ∃ j < N, Bad (i+j) ω (x+(w.take j).sum)} =
      ⋃ j ∈ Finset.range N, {w | Bad (i+j) ω (x+(w.take j).sum)} by ext w; simp]
    apply (measure_biUnion_finset_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    exact (finitePolicyPMF_prefix_event Q ω i x (Finset.mem_range.mp hj).le (Bad (i+j) ω)).le
  apply (lintegral_mono hpt).trans
  rw [lintegral_finsetSum]
  · simp_rw [finitePolicyPMF_fresh_failure ν Q S hS hQ _ i _ x (hB _) p (havg _)]
    simp
  · intro j hj
    simp only [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
    apply Measurable.tsum
    intro w
    exact Measurable.ite ((rowSigma_le _) _ (hB _ _))
      (finitePolicyPMF_measurable_atom Q (fun j x u => (hQ j x u).mono (rowSigma_le _) le_rfl) i x j w)
      measurable_const

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveFailure_rows {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (δ : ℝ≥0∞) (j : ℕ) (y : Lattice d) :
    @MeasurableSet _ (rowSigma (blockRows e H j))
      {ω | curveIncrement (realPosition (step e)) f (alignHeight e ((j:ℤ)*H) y) b B H ω Set.univ < δ} := by
  have hm := (Measure.measurable_coe MeasurableSet.univ).comp
    (curveIncrement_rows (realPosition (step e)) f (alignHeight e ((j:ℤ)*H) y) b B hH)
  rw [strip_align_blockRows] at hm
  exact measurableSet_lt hm measurable_const

lemma curveFailure_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (b : ℕ → ℝ) (B : ℝ)
    {H : ℕ} (hH : 0 < H) (δ : ℝ≥0∞) :
    environmentLaw ν {ω | curveIncrement ℓ f x b B H ω Set.univ < δ} =
      environmentLaw ν {ω | curveIncrement ℓ f 0 b B H ω Set.univ < δ} := by
  have hm : MeasurableSet {ω | curveIncrement ℓ f 0 b B H ω Set.univ < δ} :=
    measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
      ((curveIncrement_rows ℓ f 0 b B hH).mono (rowSigma_le _) le_rfl)) measurable_const
  have hshift : Measurable (fun ω : Environment d => fun y => ω (x+y)) := by fun_prop
  have he := congrArg (fun μ : Measure (Environment d) => μ {ω | curveIncrement ℓ f 0 b B H ω Set.univ < δ})
    (environment_translation ν x)
  rw [Measure.map_apply hshift hm] at he
  convert he using 1
  congr 1
  ext ω
  simp only [Set.mem_preimage,Set.mem_ofPred_eq]
  exact (congrArg (fun D : Measure (Lattice d) => D Set.univ < δ) (curveIncrement_translation ℓ f x b B H ω)).to_iff

local instance CurvePolicyFailureMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance CurvePolicyFailureSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma alignedCurvePolicy_failure_union {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (i N : ℕ) (x : Lattice d) :
    (∫⁻ ω, (finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x N).toMeasure
      {w | ∃ j < N, curveIncrement (realPosition (step e)) f
        (alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum)) b B H ω Set.univ < δ} ∂environmentLaw ν) ≤
      (N:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} := by
  apply finitePolicyPMF_failure_union ν _ (blockRows e H) (blockRows_pairwise e H)
    (alignedCurvePolicy_rows e f b B hH E hδ hα dummy) _
    (curveFailure_rows e f b B hH δ)
  intro j y
  exact curveFailure_translation ν (realPosition (step e)) f _ b B hH δ

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
local instance CurveActualFailureMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance CurveActualFailureSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_actual_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (i N : ℕ) (x : Lattice d)
    (hx : signedHeight e x=(i:ℤ)*H) :
    (∫⁻ ω, (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x N).toMeasure {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w}
      ∂environmentLaw ν) ≤
      (N:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} := by
  have he (ω : Environment d) :
      (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
        ω i x N).toMeasure {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w} =
      (finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x N).toMeasure
        {w | ∃ j < N, curveIncrement (realPosition (step e)) f
          (alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum)) b B H ω Set.univ < δ} := by
    simp only [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
    apply tsum_congr; intro w
    have hal := curvePolicy_alignment e f b B H E hδ hα dummy hd ω i x hx N w
    by_cases hw : finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
        ω i x N w = 0
    · simp [Set.indicator_apply,← hal,hw]
    · have hlen : w.length=N := by
        by_contra h; exact hw (finitePolicyPMF_length _ ω i x N w h)
      have hheight := curvePolicy_word_height e f b B H E hδ hα dummy hd ω i x N w hw
      have halt (j : ℕ) (hj : j < N) :
          alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum) = x+(w.take j).sum := by
        apply alignHeight_eq_self
        rw [signedHeight_add,hx,signedHeight_sum_of_constant e H (w.take j)
          (fun u hu => hheight u (List.mem_of_mem_take hu)),List.length_take,hlen,min_eq_left hj.le]
        ring
      have hpred : (¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w) ↔
          ∃ j < N, curveIncrement (realPosition (step e)) f (alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum)) b B H ω Set.univ < δ := by
        rw [policySafe_iff]
        simp only [not_forall,not_le,hlen]
        constructor <;> rintro ⟨j,hj,h⟩ <;> refine ⟨j,hj,?_⟩
        · simpa only [halt j hj] using h
        · simpa only [halt j hj] using h
      simp only [Set.indicator_apply,Set.mem_ofPred_eq,hpred,hal]
  simp_rw [he]
  exact alignedCurvePolicy_failure_union ν e f b B hH E hδ hα dummy i N x

end DirectionalTransience

end

end

end OAI
