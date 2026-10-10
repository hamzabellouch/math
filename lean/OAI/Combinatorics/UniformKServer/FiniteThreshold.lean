import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteProbability

namespace OAI

                                      
section
namespace UniformKServer.FiniteThreshold
noncomputable section
open MeasureTheory FiniteProbability
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

def collapse {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : A → Ω) (hf : ∀ ω, MeasurableSet (f ⁻¹' {ω})) : Law Ω where
  weight ω := μ.real (f ⁻¹' {ω})
  nonneg _ := measureReal_nonneg
  total := by
    have h := sum_measureReal_preimage_singleton (μ := μ) Finset.univ (fun ω _ => hf ω)
    simpa using h

def unitInterval : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance unitInterval_probability : IsProbabilityMeasure unitInterval where
  measure_univ := by simp [unitInterval,Real.volume_Ioc]

def normalized (u : ℝ) : ℝ := if u ∈ Set.Ioc (0:ℝ) 1 then u else 1

theorem normalized_mem (u : ℝ) : normalized u ∈ Set.Ioc (0:ℝ) 1 := by
  unfold normalized
  split_ifs with hu
  · exact hu
  · exact ⟨zero_lt_one,le_rfl⟩

theorem normalized_measurable : Measurable normalized :=
  Measurable.ite measurableSet_Ioc measurable_id measurable_const

variable {X : Type*} [Fintype X]

def threshold (p : X → ℝ) (u : ℝ) : X → Bool := fun x => decide (u ≤ p x)

abbrev Signature (p : X → ℝ) := {ω : X → Bool // ∃ u ∈ Set.Ioc (0:ℝ) 1, ω = threshold p u}

def sample (p : X → ℝ) (u : ℝ) : Signature p :=
  ⟨threshold p (normalized u),normalized u,normalized_mem u,rfl⟩

theorem sample_measurable (p : X → ℝ) (ω : Signature p) :
    MeasurableSet (sample p ⁻¹' {ω}) := by
  have heq : sample p ⁻¹' {ω} = ⋂ x : X, {u : ℝ | threshold p (normalized u) x = ω.val x} := by
    ext u
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · intro h x
      exact congrFun (congrArg Subtype.val h) x
    · intro h
      exact Subtype.ext (funext h)
  rw [heq]
  apply MeasurableSet.iInter
  intro x
  cases hω : ω.val x
  · simp only [threshold,decide_eq_false_iff_not]
    exact (measurableSet_le normalized_measurable (measurable_const : Measurable (fun _ : ℝ => p x))).compl
  · simpa only [threshold,decide_eq_true_eq] using
      (measurableSet_le normalized_measurable measurable_const)

def experiment (p : X → ℝ) : Law (Signature p) :=
  collapse unitInterval (sample p) (sample_measurable p)
theorem collapse_event {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : A → Ω) (hf : ∀ ω, MeasurableSet (f ⁻¹' {ω})) (P : Ω → Prop) :
    (collapse μ f hf).expect (fun ω => if P ω then 1 else 0) = μ.real (f ⁻¹' {ω | P ω}) := by
  classical
  unfold Law.expect collapse
  simp only [mul_ite,mul_one,mul_zero,←Finset.sum_filter]
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ.filter P) (fun ω _ => hf ω)
  simpa using h

theorem threshold_event (p : X → ℝ) (P : Signature p → Prop) :
    (experiment p).expect (fun ω => if P ω then 1 else 0) =
      unitInterval.real {u | P (sample p u)} := by
  exact collapse_event unitInterval (sample p) (sample_measurable p) P

theorem threshold_bool_event (p : X → ℝ) (P : Signature p → Bool) :
    (experiment p).expect (fun ω => if P ω then 1 else 0) =
      unitInterval.real {u | P (sample p u) = true} := by
  have h := threshold_event p (fun ω => P ω = true)
  convert h using 1
  apply (experiment p).expect_congr
  intro ω
  by_cases hω : P ω = true <;> simp [hω]

theorem interval_threshold (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) :
    unitInterval.real {u | normalized u ≤ a} = a := by
  rw [unitInterval,measureReal_restrict_apply (measurableSet_le normalized_measurable measurable_const)]
  have hset : {u | normalized u ≤ a} ∩ Set.Ioc (0:ℝ) 1 = Set.Ioc 0 a := by
    ext u
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_Ioc]
    constructor
    · rintro ⟨hu,hu0,hu1⟩
      rw [normalized,ite_eq_left ⟨hu0,hu1⟩] at hu
      exact ⟨hu0,hu⟩
    · rintro ⟨hu0,hua⟩
      have hu1 := hua.trans ha.2
      exact ⟨by rw [normalized,ite_eq_left ⟨hu0,hu1⟩]; exact hua,hu0,hu1⟩
  rw [hset,Real.volume_real_Ioc,sub_zero,max_eq_left ha.1]
/-- Finite collapse of one shared uniform threshold. These laws realize the
same nested coverage events as a single truncated-exponential radius. -/
theorem threshold_coordinate (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0:ℝ) 1) (x : X) :
    (experiment p).expect (fun ω => if ω.val x then 1 else 0) = p x := by
  rw [threshold_bool_event p (fun ω => ω.val x)]
  simpa only [sample,threshold,decide_eq_true_eq] using interval_threshold (p x) (hp x)

theorem threshold_hit (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0:ℝ) 1) (x y : X) :
    (experiment p).expect (fun ω => if ω.val x || ω.val y then 1 else 0) = max (p x) (p y) := by
  rw [threshold_bool_event p (fun ω => ω.val x || ω.val y)]
  have hset : {u | ((sample p u).val x || (sample p u).val y) = true} =
      {u | normalized u ≤ max (p x) (p y)} := by
    ext u
    simp only [Set.mem_ofPred_eq,sample,threshold,Bool.or_eq_true,decide_eq_true_eq,le_max_iff]
  rw [hset]
  exact interval_threshold _ ⟨(hp x).1.trans (le_max_left _ _),max_le (hp x).2 (hp y).2⟩

theorem threshold_separation (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0:ℝ) 1) (x y : X) :
    (experiment p).expect (fun ω => if ω.val x != ω.val y then 1 else 0) = |p x-p y| := by
  have hid (ω : Signature p) : (if ω.val x != ω.val y then (1:ℝ) else 0) =
      2*(if ω.val x || ω.val y then 1 else 0)-(if ω.val x then 1 else 0)-(if ω.val y then 1 else 0) := by
    cases ω.val x <;> cases ω.val y <;> norm_num
  rw [(experiment p).expect_congr _ _ hid,(experiment p).expect_sub,(experiment p).expect_sub,
    (experiment p).expect_mul,threshold_hit p hp x y,threshold_coordinate p hp x,threshold_coordinate p hp y]
  rcases le_total (p x) (p y) with h|h
  · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring
end
end UniformKServer.FiniteThreshold

end


end OAI
