import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshGeometry

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem source_label_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1) (p d : ℕ→ℕ)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b) :
    ∃ (u : (n : ℕ)→Fin (n+1)→ℝ)
      (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) (s : ℕ→ℕ),
      (∀ n,u n∈Icc (fun _=>1) (fun _=>2)) ∧ StrictMono s ∧
      Tendsto (fun n => sourceGibbsArrayLaw (s n) k 0 (fun j=>p j.val)
        (fun j=>d j.val) (fun _=>0) (u (s n)) (stepCumulative w) 0) atTop (𝓝 ν) ∧
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G g=0) ∧
      (∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
        (ν : Measure _) (ν : Measure _)) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hc (n : ℕ) := source_perturbation_contact_exists n k (0 : ℝ →ᵇ ℝ)
    (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (fun _=>le_rfl) monotone_const
    (stepCumulative w) hz hz0 hz1 0
  choose u hu hm using hc
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence (fun n => sourceGibbsArrayLaw n k
    (0 : ℝ →ᵇ ℝ) (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (u n) (stepCumulative w) 0)
  refine ⟨u,ν,s,hu,hs,hlim,?_,?_,?_,?_⟩
  · exact source_contact_limit_joint_gg k 0 p d (stepCumulative w) hz hz0 hz1
      (fun _=>0) (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u hu hm
      (H:=0) (T:=0) le_rfl (fun _=>le_rfl) (fun _=>le_rfl) hs hlim hcover
  · exact source_contact_limit_exchangeable k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
      (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  · apply source_array_limit_label_law k 0 p d w hw hw1
      (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u (fun n j=>?_) (fun _=>0)
      (fun b hb=>hcover 0 b (by omega)) hs hlim
    have h := (hu n).1 j
    linarith
  · exact source_contact_limit_spin_geometry k 0 p d (stepCumulative w) hz hz0 hz1
      (fun _=>0) (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u hu hm
      (H:=0) (T:=0) le_rfl (fun _=>le_rfl) (fun _=>le_rfl) hcover hs hlim

lemma indexedCommonDepth_ultrametric (n : ℕ) (a b c : IndexedLeaf n) :
    min (indexedCommonDepth n a b) (indexedCommonDepth n a c)≤ indexedCommonDepth n b c := by
  let l := min (indexedCommonDepth n a b) (indexedCommonDepth n a c)
  apply (indexedLeafSharedVertex_eq_iff n b c l).mp
  exact ((indexedLeafSharedVertex_eq_iff n a b l).mpr (min_le_left _ _)).symm.trans
    ((indexedLeafSharedVertex_eq_iff n a c l).mpr (min_le_right _ _))

def CompactLabelGeometry (k : ℕ) (Q : CompactArray CompactJointOverlap) : Prop :=
  (∀ i j, (Q i j).2.val=(Q j i).2.val) ∧
  (∀ i, (Q i i).2.val=(k:ℝ)/(k+1:ℕ)) ∧
  ∀ i j l, min (Q i j).2.val (Q i l).2.val ≤ (Q j l).2.val

lemma sourceJointArray_label_geometry {N k : ℕ} (x : ℕ→NormalizedSpin N×IndexedLeaf k) :
    CompactLabelGeometry k (sourceJointArray x) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    simp only [sourceJointArray,sourceJointOverlap,indexedCommonDepth_comm k (x j).2 (x i).2]
  · intro i
    simp only [sourceJointArray,sourceJointOverlap,indexedCommonDepth_self,Fin.val_last]
  · intro i j l
    change min (((indexedCommonDepth k (x j).2 (x i).2).val:ℝ)/(k+1:ℕ))
      (((indexedCommonDepth k (x l).2 (x i).2).val:ℝ)/(k+1:ℕ))≤
      ((indexedCommonDepth k (x l).2 (x j).2).val:ℝ)/(k+1:ℕ)
    have h := indexedCommonDepth_ultrametric k (x i).2 (x j).2 (x l).2
    rw [indexedCommonDepth_comm k (x i).2 (x j).2,
      indexedCommonDepth_comm k (x i).2 (x l).2,indexedCommonDepth_comm k (x j).2 (x l).2] at h
    rcases le_total (indexedCommonDepth k (x j).2 (x i).2) (indexedCommonDepth k (x l).2 (x i).2) with he|he
    · rw [min_eq_left he] at h
      exact (min_le_left _ _).trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))
    · rw [min_eq_right he] at h
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

lemma compactLabelGeometry_closed (k : ℕ) : IsClosed {Q | CompactLabelGeometry k Q} := by
  unfold CompactLabelGeometry
  simp only [ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
        isClosed_le (by fun_prop) (by fun_prop)))

lemma sourceGibbsArray_limit_label_geometry (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactLabelGeometry k Q := by
  have hc := compactLabelGeometry_closed k
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc (fun n=>sourceGibbsArray_closed_full
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) hc
    (fun x => sourceJointArray_label_geometry x))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy

end

end OAI
