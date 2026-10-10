import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Shells.TransportedAngularField

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric MeasureTheory PlanarFalconer
open scoped ContDiff
variable {d : ℕ}

lemma tensorCapND_compact {δ : ℝ} (hδ : 0 < δ) (a : Fin d → ℤ) :
    HasCompactSupport (tensorCapND δ a) := by
  apply (isCompact_closedBall (capGridPointND δ a) ((d+1:ℝ)*δ)).of_isClosed_subset
    isClosed_closure
  exact fun w hw => tensorCapND_tsupport_dist hδ a hw

lemma bufferedMaskND_compact {δ : ℝ} (hδ : 0 < δ)
    (K : Set (EuclideanSpace ℝ (Fin d))) : HasCompactSupport (bufferedMaskND δ K) := by
  have h : HasCompactSupport (∑ a ∈ maskCapSelectionND δ K, tensorCapND δ a) :=
    HasCompactSupport.finset_sum (fun a _ => tensorCapND_compact hδ a)
  have he : (∑ a ∈ maskCapSelectionND δ K, tensorCapND δ a) = bufferedMaskND δ K := by
    funext w
    simp only [Finset.sum_apply,bufferedMaskND,selectedCapND]
  rw [he] at h
  exact h

lemma evenBufferedMaskND_compact {δ : ℝ} (hδ : 0 < δ)
    (K : Set (EuclideanSpace ℝ (Fin d))) : HasCompactSupport (evenBufferedMaskND δ K) := by
  have h := bufferedMaskND_compact hδ K
  have hn : HasCompactSupport (fun w => bufferedMaskND δ K (-w)) :=
    h.comp_homeomorph (Homeomorph.neg _)
  exact (h.add hn).mul_left

namespace TreeND

lemma actualDescriptorSmooth_compact (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d)
    (b : PolicyDescriptor) : HasCompactSupport (actualDescriptorSmooth ρ m N sig C J i P b).1 := by
  exact (evenBufferedMaskND_compact (sourceMaskRadiusND_pos _ _ _ _)
    (descriptorGood ρ m N sig C J i P b)).comp_left (by simp : Complex.ofReal 0=0)

lemma actualEndpointAngular_global_bound
    (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x w, ‖(actualEndpointAngular L ρ m N sig C J i b x).1 w‖ ≤ B := by
  classical
  let D := sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig
  let f := fun P : CellPath d => normalizedAngularWordND D L
    (actualDescriptorSmooth ρ m N sig C J i P b)
  have hf : ∀ P, ∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖(f P).1 w‖ ≤ B := by
    intro P
    have hc : HasCompactSupport (f P).1 :=
      (actualDescriptorSmooth_compact ρ m N sig C J i P b).of_isClosed_subset
        isClosed_closure (normalizedAngularWordND_support _ _ _)
    obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous (smoothFunctionND_contDiff (f P)).continuous
    exact ⟨max 0 B,le_max_left _ _,fun w => (hB w).trans (le_max_right _ _)⟩
  choose B hB hbound using hf
  refine ⟨∑ P ∈ dyadicPaths (descriptorAnchor b), B P,
    Finset.sum_nonneg (fun P _ => hB P),?_⟩
  intro x w
  by_cases hx : ∃ P ∈ dyadicPaths (descriptorAnchor b), x ∈ treeCell P
  · obtain ⟨P,hP,hx⟩ := hx
    have he : actualEndpointSmooth ρ m N sig C J i b x=
        actualDescriptorSmooth ρ m N sig C J i P b := by
      apply Subtype.ext
      exact congrArg (fun g => fun u => (g u:ℂ)) (actualEndpointMask_of_mem ρ m N sig C J i b hP hx)
    unfold actualEndpointAngular
    rw [he]
    exact (hbound P w).trans (Finset.single_le_sum (fun Q _ => hB Q) hP)
  · have he : actualEndpointSmooth ρ m N sig C J i b x=0 := by
      apply Subtype.ext
      have hzero := actualEndpointMask_of_absent ρ m N sig C J i b
        (by simpa only [not_exists,not_and] using hx)
      funext u
      change (actualEndpointMask ρ m N sig C J i b x u:ℂ)=0
      rw [hzero]
      simp
    simp only [actualEndpointAngular,he,normalizedAngularWordND,map_zero,smul_zero]
    change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    exact Finset.sum_nonneg (fun P _ => hB P)

lemma actualAngularProduct_global_bound {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor)
    (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x w, ‖(actualAngularProduct S b L ρ m N sig C J i x).1 w‖ ≤ B := by
  classical
  choose B hB hb using (fun a => actualEndpointAngular_global_bound (L a) ρ m N sig C J i (b a))
  refine ⟨∏ a ∈ S, B a,Finset.prod_nonneg (fun a _ => hB a),?_⟩
  intro x w
  change ‖∏ a ∈ S, (actualEndpointAngular (L a) ρ m N sig C J i (b a) x).1 w‖ ≤ _
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hb a x w)

namespace PositiveDistanceState
variable {n : ℕ} (e : PositiveDistanceState (n+1))
lemma prefixInverse_global_bound (p : PrefixAssignment n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x w, ‖e.prefixInverseLeft p x w‖ ≤ B ∧
      ‖e.prefixInverseRight p x w‖ ≤ B := by
  obtain ⟨B,hB,hleft⟩ := actualAngularProduct_global_bound e.prefixDescriptors id (prefixLeftWords p)
    e.ρ e.mass e.N e.sig e.C e.J e.i
  obtain ⟨C,hC,hright⟩ := actualAngularProduct_global_bound e.prefixDescriptors id (prefixRightWords p)
    e.ρ e.mass e.N e.sig e.C e.J e.i
  refine ⟨max B C,hB.trans (le_max_left _ _),?_⟩
  intro x w
  rw [e.prefixInverseLeft_eq,e.prefixInverseRight_eq]
  exact ⟨(hleft x w).trans (le_max_left _ _),(hright x w).trans (le_max_right _ _)⟩
end PositiveDistanceState

end TreeND
end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
