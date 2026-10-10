import OAI.NumberTheory.Jacobsthal.Analysis.ContinuousQRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def baseCutoff (b : ℝ) : ℝ := max 1 (min 2 b)
noncomputable def survivorBaseline (b : ℝ) : ℝ := (baseCutoff b)⁻¹

theorem baseCutoff_bounds (b : ℝ) : 1 ≤ baseCutoff b ∧ baseCutoff b ≤ 2 :=
  upperCutoff_bounds .even 0 b

theorem baseCutoff_on {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) : baseCutoff b=b := by
  rw [baseCutoff,min_eq_right hb2,max_eq_right hb1]

theorem cutoff_le_base (i : Side) (r b : ℝ) : upperCutoff i r b ≤ baseCutoff b := by
  cases i with
  | even => exact le_rfl
  | odd => exact max_le_max le_rfl (min_le_left _ _)

theorem survivorBaseline_continuous : Continuous survivorBaseline :=
  (continuous_const.max (continuous_const.min continuous_id)).inv₀ (fun b =>
    ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (baseCutoff_bounds b).1))

theorem baseline_profile_continuous : JointContinuous (fun _ _ b => survivorBaseline b) :=
  fun _ => survivorBaseline_continuous.comp continuous_snd

theorem gate_survivorBaseline (i : Side) (r b : ℝ) :
    gate (fun _ _ t => survivorBaseline t) i r b=1-(upperCutoff i r b)⁻¹ := by
  let a := upperCutoff i r b
  have ha : 1 ≤ a := (upperCutoff_bounds i r b).1
  have hne : ∀ x ∈ uIcc (1:ℝ) a,x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le ha] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (uIcc (1:ℝ) a) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hne x hx))
  have hd : ∀ x ∈ uIcc (1:ℝ) a,HasDerivAt (fun t : ℝ => -t⁻¹) ((x^2)⁻¹) x := by
    intro x hx
    simpa only [neg_neg] using! (hasDerivAt_inv (hne x hx)).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))
  calc
    gate (fun _ _ t => survivorBaseline t) i r b=∫ x in (1:ℝ)..a,(x^2)⁻¹ := by
      unfold gate
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ha] at hx
      dsimp only
      have hx2 : x ≤ 2 := hx.2.trans (upperCutoff_bounds i r b).2
      rw [survivorBaseline,baseCutoff_on hx.1 hx2,max_eq_right hx.1]
      ring
    _ = 1-a⁻¹ := by rw [h]; simp only [inv_one]; ring

noncomputable def omissionForce : Profile
  | .even,_,_ => 0
  | .odd,r,b => (upperCutoff .odd r b)⁻¹-survivorBaseline b

theorem omissionForce_continuous : JointContinuous omissionForce := by
  intro i
  cases i with
  | even => exact continuous_const
  | odd =>
    have hc := (upperCutoff_continuous .odd).inv₀ (fun p => ne_of_gt
      ((by norm_num : (0:ℝ)<1).trans_le (upperCutoff_bounds .odd p.1 p.2).1))
    exact hc.sub (survivorBaseline_continuous.comp continuous_snd)

theorem omissionForce_nonnegative (i : Side) (r b : ℝ) : 0 ≤ omissionForce i r b := by
  cases i with
  | even => exact le_rfl
  | odd =>
    apply sub_nonneg.mpr
    have h := one_div_le_one_div_of_le
      ((by norm_num : (0:ℝ)<1).trans_le (upperCutoff_bounds .odd r b).1) (cutoff_le_base .odd r b)
    simpa only [one_div,survivorBaseline] using h

end ErdosContinuousOmission

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def omissionDefect : Profile
  | .even,r,b => survivorBaseline b-boundaryReference .even r b
  | .odd,r,b => boundaryReference .odd r b-survivorBaseline b

theorem omissionDefect_continuous : JointContinuous omissionDefect := by
  intro i
  cases i with
  | even => exact (baseline_profile_continuous .even).sub (boundaryReference_continuous .even)
  | odd => exact (boundaryReference_continuous .odd).sub (baseline_profile_continuous .odd)

theorem gate_sub {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (i : Side) (r b : ℝ) :
    gate (fun j s t => H j s t-G j s t) i r b=gate H i r b-gate G i r b := by
  simp only [gate,sub_div]
  exact intervalIntegral.integral_sub
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _) ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)

theorem gate_defect_even (r b : ℝ) :
    gate omissionDefect .even r b=gate boundaryReference .even r b-gate (fun _ _ t => survivorBaseline t) .even r b := by
  change gate (fun j s t => boundaryReference j s t-survivorBaseline t) .even r b=_
  exact gate_sub boundaryReference_continuous baseline_profile_continuous .even r b

theorem gate_defect_odd (r b : ℝ) :
    gate omissionDefect .odd r b=gate (fun _ _ t => survivorBaseline t) .odd r b-gate boundaryReference .odd r b := by
  change gate (fun j s t => survivorBaseline t-boundaryReference j s t) .odd r b=_
  exact gate_sub baseline_profile_continuous boundaryReference_continuous .odd r b

theorem actual_defect_forcing (i : Side) (r b : ℝ) :
    omissionDefect i r b=omissionForce i r b+gate omissionDefect i r b := by
  cases i with
  | even =>
    change survivorBaseline b-boundaryReference .even r b=0+gate omissionDefect .even r b
    rw [gate_defect_even,gate_survivorBaseline,boundaryReference_recurrence .even r b]
    change survivorBaseline b-(1-gate boundaryReference .even r b)=0+(gate boundaryReference .even r b-(1-survivorBaseline b))
    ring
  | odd =>
    change boundaryReference .odd r b-survivorBaseline b=
      (upperCutoff .odd r b)⁻¹-survivorBaseline b+gate omissionDefect .odd r b
    rw [gate_defect_odd,gate_survivorBaseline,boundaryReference_recurrence .odd r b]
    ring

theorem actual_finite_omission_expansion (N : ℕ) (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) :
    omissionDefect i r b=∑ n ∈ Finset.range N,gateIterate n omissionForce i r b := by
  have h := finite_forcing_expansion omissionDefect_continuous omissionForce_continuous actual_defect_forcing N i r b
  rw [gateIterate_zero_of_index omissionDefect hN i hr,add_zero] at h
  exact h

theorem omissionDefect_nonnegative (i : Side) (r b : ℝ) : 0 ≤ omissionDefect i r b := by
  rw [actual_finite_omission_expansion (referenceDepth r) (referenceDepth_bounds r).1 i (referenceDepth_bounds r).2]
  apply Finset.sum_nonneg
  intro n _
  exact gateIterate_nonnegative omissionForce_nonnegative n i r b

theorem actual_reference_order {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (r : ℝ) :
    boundaryReference .even r b ≤ b⁻¹ ∧ b⁻¹ ≤ boundaryReference .odd r b := by
  have he := omissionDefect_nonnegative .even r b
  have ho := omissionDefect_nonnegative .odd r b
  simp only [omissionDefect,survivorBaseline,baseCutoff_on hb1 hb2] at he ho
  exact ⟨by linarith,by linarith⟩

theorem partial_omission_le_defect (N : ℕ) (i : Side) (r b : ℝ) :
    (∑ n ∈ Finset.range N,gateIterate n omissionForce i r b) ≤ omissionDefect i r b := by
  have h := finite_forcing_expansion omissionDefect_continuous omissionForce_continuous actual_defect_forcing N i r b
  have hn := gateIterate_nonnegative omissionDefect_nonnegative N i r b
  linarith

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omission_terms_vanish (i : Side) (r b : ℝ) :
    ∀ n : ℕ,referenceDepth r ≤ n → gateIterate n omissionForce i r b=0 := by
  intro n hn
  apply gateIterate_zero_of_index omissionForce ((referenceDepth_bounds r).1.trans hn) i
  have hh : (referenceDepth r:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  exact (referenceDepth_bounds r).2.trans (by linarith)

theorem actual_omission_hasSum (i : Side) (r b : ℝ) :
    HasSum (fun n : ℕ => gateIterate n omissionForce i r b) (omissionDefect i r b) := by
  rw [actual_finite_omission_expansion (referenceDepth r) (referenceDepth_bounds r).1 i (referenceDepth_bounds r).2]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply omission_terms_vanish i r b n
  exact le_of_not_gt (by simpa only [Finset.mem_range] using hn)

theorem actual_omission_tsum (i : Side) (r b : ℝ) :
    (∑' n : ℕ,gateIterate n omissionForce i r b)=omissionDefect i r b :=
  (actual_omission_hasSum i r b).tsum_eq

theorem actual_omission_summable (i : Side) (r b : ℝ) :
    Summable (fun n : ℕ => gateIterate n omissionForce i r b) :=
  (actual_omission_hasSum i r b).summable

end ErdosContinuousOmission

end

end Erdos970

end OAI
