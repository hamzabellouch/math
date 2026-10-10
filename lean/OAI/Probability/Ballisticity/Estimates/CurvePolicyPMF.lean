import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicy
import OAI.Probability.Ballisticity.Geometry.AlignedSlabs
import OAI.Probability.Ballisticity.Coupling.FreshPolicyIndependence

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def curvePolicyPMF {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (ω : Environment d) : PMF (Lattice d) :=
  let := curvePolicy_probability ℓ f x b B H E hδ hα dummy ω
  (curvePolicy ℓ f x b B H E δ α dummy ω).toPMF

lemma curvePolicyPMF_apply {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy u : Lattice d) (ω : Environment d) :
    curvePolicyPMF ℓ f x b B H E hδ hα dummy ω u = curvePolicy ℓ f x b B H E δ α dummy ω {u} := rfl

lemma curvePolicy_average_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) :
    IsProbabilityMeasure ((environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy)) := by
  have hm := (curvePolicy_rows ℓ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl
  have (ω : Environment d) := curvePolicy_probability ℓ f 0 b B H E hδ hα dummy ω
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp

noncomputable def curvePolicy_average {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) : PMF (Lattice d) :=
  let := curvePolicy_average_probability ν ℓ f b B hH E hδ hα dummy
  ((environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy)).toPMF

lemma curvePolicyPMF_average {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy u : Lattice d) :
    (∫⁻ ω, curvePolicyPMF ℓ f x b B H E hδ hα dummy ω u ∂environmentLaw ν) =
      curvePolicy_average ν ℓ f b B hH E hδ hα dummy u := by
  simp only [curvePolicyPMF_apply]
  rw [curvePolicy_annealed_translation ν ℓ f x b B hH E δ α dummy]
  symm
  change ((environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy)) {u} = _
  exact Measure.bind_apply (measurableSet_singleton u)
    ((curvePolicy_rows ℓ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl).aemeasurable

noncomputable def alignedCurvePolicy {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) (H : ℕ) (E : Set (Lattice d)) {δ α : ℝ≥0∞}
    (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (i : ℕ) (ω : Environment d) (x : Lattice d) : PMF (Lattice d) :=
  curvePolicyPMF (realPosition (step e)) f (alignHeight e ((i:ℤ)*H) x) b B H E hδ hα dummy ω

lemma alignedCurvePolicy_rows {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d)) {δ α : ℝ≥0∞}
    (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (i : ℕ) (x u : Lattice d) :
    @Measurable _ _ (rowSigma (blockRows e H i)) _
      (fun ω => alignedCurvePolicy e f b B H E hδ hα dummy i ω x u) := by
  have hm := (Measure.measurable_coe (measurableSet_singleton u)).comp
    (curvePolicy_rows (realPosition (step e)) f (alignHeight e ((i:ℤ)*H) x) b B hH E δ α dummy)
  rwa [strip_align_blockRows] at hm

theorem alignedCurvePolicy_annealed {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (i : ℕ) (x : Lattice d) (n : ℕ) (w : List (Lattice d)) :
    (∫⁻ ω, finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x n w ∂environmentLaw ν) =
      finitePolicyPMF (fun _ (_ : Unit) _ => curvePolicy_average ν
        (realPosition (step e)) f b B hH E hδ hα dummy) () i x n w := by
  apply finitePolicyPMF_annealed ν _ (blockRows e H) (blockRows_pairwise e H)
    (alignedCurvePolicy_rows e f b B hH E hδ hα dummy)
  intro j y u
  exact curvePolicyPMF_average ν (realPosition (step e)) f _ b B hH E hδ hα dummy u

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def policySafe {G : Type*} [Add G] (Good : G → Prop) : G → List G → Prop
  | _, [] => True
  | x, u::w => Good x ∧ policySafe Good (x+u) w

lemma curveIncrement_singleton {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) (u : Lattice d) :
    curveIncrement ℓ f x b B H ω {u} = curveEndpoint ℓ f x b B H ω {x+u} := by
  rw [curveIncrement,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton u)]
  congr 1
  ext y
  simp only [Set.mem_preimage,Set.mem_singleton_iff]
  constructor
  · intro h; rw [sub_eq_iff_eq_add] at h; simpa only [add_comm] using h
  · intro h; rw [h]; abel

lemma curvePolicyPMF_atom_domination {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (u : Lattice d)
    (hf : δ ≤ curveIncrement ℓ f x b B H ω Set.univ) :
    curvePolicyPMF ℓ f x b B H E hδ hα dummy ω u ≤
      (α*δ)⁻¹ * curveEndpoint ℓ f x b B H ω {x+u} := by
  have h := Measure.le_iff'.mp (curvePolicy_domination ℓ f x b B H E hδ hα hα1 dummy ω hf)
    {u}
  simpa only [curvePolicyPMF_apply,Measure.smul_apply,smul_eq_mul,curveIncrement_singleton] using h

lemma curvePolicy_word_density {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (w : List (Lattice d))
    (hs : policySafe (fun y => δ ≤ curveIncrement ℓ f y b B H ω Set.univ) x w) :
    finitePolicyPMF (fun _ ω x => curvePolicyPMF ℓ f x b B H E hδ hα dummy ω) ω i x w.length w ≤
      ((α*δ)⁻¹)^w.length * quenchedKernel (ω,x) (curveWordEvent ℓ f b B H x w) := by
  induction w generalizing i x with
  | nil => simp [finitePolicyPMF,curveWordEvent]
  | cons u w ih =>
    rw [List.length_cons,finitePolicyPMF_cons,curveWordEvent_cons_mass]
    have h₁ := curvePolicyPMF_atom_domination ℓ f x b B H E hδ hα hα1 dummy ω u hs.1
    have h₂ := ih (i+1) (x+u) hs.2
    apply (mul_le_mul' h₁ h₂).trans_eq
    rw [pow_succ]
    ring

local instance {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_event_density {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (n : ℕ)
    (S : Set (List (Lattice d))) (hlen : ∀ w ∈ S, w.length=n)
    (hs : ∀ w ∈ S, policySafe (fun y => δ ≤ curveIncrement ℓ f y b B H ω Set.univ) x w) :
    (finitePolicyPMF (fun _ ω x => curvePolicyPMF ℓ f x b B H E hδ hα dummy ω) ω i x n).toMeasure S ≤
      ((α*δ)⁻¹)^n * quenchedKernel (ω,x) (⋃ w ∈ S, curveWordEvent ℓ f b B H x w) := by
  let A (w : List (Lattice d)) : Set (Path d) := if w ∈ S then curveWordEvent ℓ f b B H x w else ∅
  have ha : ∀ w, MeasurableSet (A w) := by
    intro w; dsimp [A]; split_ifs; exact measurableSet_curveWordEvent ℓ f b B H x w; exact MeasurableSet.empty
  have haDis : Pairwise (fun w v => Disjoint (A w) (A v)) := by
    intro w v hwv
    dsimp [A]
    split_ifs with hw hv hv
    · exact curveWordEvent_disjoint ℓ f b B H x w v ((hlen w hw).trans (hlen v hv).symm) hwv
    all_goals simp
  have he : (⋃ w ∈ S, curveWordEvent ℓ f b B H x w) = ⋃ w, A w := by
    ext X
    simp only [Set.mem_iUnion,A,Set.mem_ite_empty_right]
    constructor <;> rintro ⟨w,hw,hX⟩ <;> exact ⟨w,hw,hX⟩
  rw [he,measure_iUnion haDis ha,← ENNReal.tsum_mul_left,PMF.toMeasure_apply _ S.to_countable.measurableSet]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw,A,ite_eq_left hw]
    simpa only [hlen w hw] using curvePolicy_word_density ℓ f b B H E hδ hα hα1 dummy ω i x w (hs w hw)
  · simp [A,hw]

end DirectionalTransience

end

end

end OAI
