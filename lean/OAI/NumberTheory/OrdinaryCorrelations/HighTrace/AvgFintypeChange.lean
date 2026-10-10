import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DataInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AmplitudeGeOne

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ t : ℕ}

private lemma avg_fintype_change {α : Type*} (i j : Fintype α) (f : α → ℝ) :
    @avg α i f = @avg α j f := by cases Subsingleton.elim i j; rfl

private lemma avg_mono_instances {α : Type*} (i j : Fintype α) (f g : α → ℝ)
    (hf : ∀ a, f a ≤ g a) : @avg α i f ≤ @avg α j g := by
  rw [avg_fintype_change i j]
  exact @avg_mono α j f g hf

lemma avg_merge_eq (w : ClosedLine h ℓ) (F : S.Residues → ℝ) :
    avg (fun a : S.FixedResidues w => avg (fun z : S.FreeResidues w => F (mergeResidues w a z))) =
      avg F := by
  calc
    _ = avg (fun az : S.FixedResidues w × S.FreeResidues w =>
        F (mergeResidues w az.1 az.2)) := (avg_prod _).symm
    _ = _ := by
      convert (avg_equiv (S.binarySplit w) F).symm using 1
      exact avg_fintype_change _ _ _

theorem residualWitnessIntegral_le_list_integrals (w : ClosedLine h ℓ)
    {T : ℝ} (cut : S.Cutoffs T) (G : S.FixedResidues w → Prop) (ht : 0 < t) :
    residualWitnessIntegral (D:=D) (L:=L) w cut G t ≤
      ∑ l ∈ boundedLists (AttachedSpec w D L) t,
        ∑ F : PrivateFamily w D L t,
          avg (fun r : S.Residues => |S.kernel w cut r| * listIndicator w (l++List.ofFn F.witness) r) := by
  let J (l : List (AttachedSpec w D L)) (F : PrivateFamily w D L t) (r : S.Residues) :=
    |S.kernel w cut r| * listIndicator w (l++List.ofFn F.witness) r
  calc
    _ ≤ avg (fun a : S.FixedResidues w => avg (fun z : S.FreeResidues w =>
        ∑ l ∈ boundedLists (AttachedSpec w D L) t,
          ∑ F : PrivateFamily w D L t, J l F (mergeResidues w a z))) := by
      apply avg_mono
      intro a
      by_cases ha : G a
      · simp only [ha,ite_true]
        apply avg_mono_instances
        intro z
        have hh := mul_le_mul_of_nonneg_left (witnessCount_le_joint_lists (D:=D) (L:=L) w a z ht)
          (abs_nonneg (S.kernel w cut (mergeResidues w a z)))
        simpa only [mul_sum,J] using hh
      · simp only [ha,ite_false]
        apply avg_nonneg
        intro z
        exact sum_nonneg (fun l hl => sum_nonneg (fun F hF =>
          mul_nonneg (abs_nonneg _) (listIndicator_nonneg w _ _)))
    _ = _ := by
      simp_rw [avg_sum']
      apply sum_congr rfl
      intro l hl
      apply sum_congr rfl
      intro F hF
      exact avg_merge_eq w (J l F)

def JointlyRealizable (w : ClosedLine h ℓ) (l : List (AttachedSpec w D L)) : Prop :=
  ∃ r : S.Residues, ∀ s ∈ l, ∀ p : S.Index, s.spec.ResidueTest p s.vertex (r p)

noncomputable def crudeListWeight (w : ClosedLine h ℓ) (l : List (AttachedSpec w D L)) : ℝ :=
  if JointlyRealizable w l then
    A^(ℓ*⌈C₀*Real.log B⌉₊) * 2^(fullUsedIndices w l).card *
      ∏ p ∈ fullUsedIndices w l, (p:ℝ)⁻¹
  else 0

lemma crudeListWeight_nonneg (w : ClosedLine h ℓ) (l : List (AttachedSpec w D L)) :
    0 ≤ crudeListWeight w l := by
  unfold crudeListWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (pow_nonneg A_pos.le _) (by positivity))
      (prod_nonneg (fun p hp => by positivity))
  · exact le_rfl

lemma list_integral_le_crudeListWeight (w : ClosedLine h ℓ)
    (hl : ∀ i, w.label i ∈ D.members) {T : ℝ} (cut : S.Cutoffs T)
    (l : List (AttachedSpec w D L)) :
    avg (fun r : S.Residues => |S.kernel w cut r| * listIndicator w l r) ≤ crudeListWeight w l := by
  by_cases hj : JointlyRealizable w l
  · rw [crudeListWeight,ite_eq_left hj]
    simpa only [mul_one] using crude_unpartitioned_majorant w hl cut l (fun _ => 1)
      (fun _ => ⟨zero_le_one,le_rfl⟩)
  · rw [crudeListWeight,ite_eq_right hj]
    have hzero (r : S.Residues) : listIndicator w l r=0 := by
      apply ite_eq_right
      intro hg
      exact hj ⟨r,hg⟩
    simp only [hzero,mul_zero,avg_const,le_refl]

theorem residualWitnessIntegral_le_crude_list_sum (w : ClosedLine h ℓ)
    (hl : ∀ i, w.label i ∈ D.members) {T : ℝ} (cut : S.Cutoffs T)
    (G : S.FixedResidues w → Prop) (ht : 0 < t) :
    residualWitnessIntegral (D:=D) (L:=L) w cut G t ≤
      ∑ l ∈ boundedLists (AttachedSpec w D L) t,
        ∑ F : PrivateFamily w D L t, crudeListWeight w (l++List.ofFn F.witness) := by
  apply (residualWitnessIntegral_le_list_integrals w cut G ht).trans
  apply sum_le_sum
  intro l hl'
  apply sum_le_sum
  intro F hF
  exact list_integral_le_crudeListWeight w hl cut _

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
