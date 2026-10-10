import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UsedPrimeReciprocal
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResiduesAdd

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def retainedKernel (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) (x : S.Residues) : ℝ :=
  if G ((S.splitResidues w x).1) then
    S.chronologicalKernel w cut x * listIndicator w 𝔏 x else 0

lemma retainedKernel_avg_le (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) :
    |avg (retainedKernel w cut 𝔏 G)| ≤ assignedKernelIntegral w cut 𝔏 G := by
  rw [avg_equiv (S.splitResidues w),avg_prod]
  have he : (fun a : S.FixedResidues w =>
      avg (fun bc : S.FreeCoreResidues w × S.FreeCenterResidues w =>
        retainedKernel w cut 𝔏 G ((S.splitResidues w).symm (a,bc)))) =
      fun a => if G a then avg (fun bc : S.FreeCoreResidues w × S.FreeCenterResidues w =>
        S.kernel w cut ((S.splitResidues w).symm (a,bc)) *
        listIndicator w 𝔏 ((S.splitResidues w).symm (a,bc))) else 0 := by
    funext a
    by_cases hG : G a
    · simp only [retainedKernel,Equiv.apply_symm_apply,hG,ite_true,chronologicalKernel_eq]
    · simp only [retainedKernel,Equiv.apply_symm_apply,hG,ite_false,avg_const]
  rw [he]
  apply (abs_avg_le _).trans
  apply avg_mono
  intro a
  by_cases ha : G a <;> simp only [ha,ite_true,ite_false,abs_zero,le_refl]

def retainedRecordSet (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) :
    Finset (AssignedRecord S ℓ) := univ.filter (fun R => ∃ a, G a ∧ recordGroup w hh 𝔏 R a)

lemma retained_record_partition (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (G : S.FixedResidues w → Prop) :
    (∑ R ∈ retainedRecordSet w hh 𝔏 G,
      assignedKernelIntegral w cut 𝔏 (fun a => G a ∧ recordGroup w hh 𝔏 R a)) =
    assignedKernelIntegral w cut 𝔏 G := by
  unfold assignedKernelIntegral avg
  rw [← mul_sum,sum_comm]
  apply congrArg (fun z : ℝ => (Fintype.card (S.FixedResidues w) : ℝ)⁻¹*z)
  apply sum_congr rfl
  intro a ha
  by_cases hG : G a
  · have hr : recordAt w hh 𝔏 a ∈ retainedRecordSet w hh 𝔏 G :=
      mem_filter.mpr ⟨mem_univ _,⟨a,hG,rfl⟩⟩
    simp only [hG,true_and,ite_true,recordGroup]
    simp [hr]
  · simp only [hG,false_and,ite_false,sum_const_zero]

theorem retained_origin_reduction (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (G : S.FixedResidues w → Prop) (hlarge : ∀ p : S.Index, 2*(ℓ+1) ≤ (p : ℕ)) :
    |avg (retainedKernel w cut 𝔏 G)| ≤
      ∑ R ∈ retainedRecordSet w hh 𝔏 G,
        traceIntegrationMajorant w hh 𝔏 R T (restorationError w 𝔏) := by
  apply (retainedKernel_avg_le w cut 𝔏 G).trans
  rw [← retained_record_partition w hh cut 𝔏 G]
  apply sum_le_sum
  intro R hR
  exact (assignedKernelIntegral_mono w cut 𝔏 _ _ (fun a ha => ha.2)).trans
    (trace_integration_finite w hh cut 𝔏 R hlarge)

theorem retained_origin_tendsto (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) (z : ℝ → ℤ) :
    Tendsto (fun X : ℝ => (∑ n ∈ range ⌊X⌋₊,
      retainedKernel w cut 𝔏 G (S.integerResidues ((n : ℤ)+z X)))/X) atTop
      (𝓝 (avg (retainedKernel w cut 𝔏 G))) := S.real_origin_tendsto _ z

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
