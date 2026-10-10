import Mathlib
import OAI.Probability.Perceptron.Interpolation.CompactArrayMap
import OAI.Probability.Perceptron.Variational.LabelValue
import OAI.Probability.Perceptron.Variational.LabelReference

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def CompactLabelNodes (k : ℕ) (Q : CompactArray CompactJointOverlap) : Prop :=
  ∀ i j, (Q i j).2∈Set.range (sourceLabelLevel k)

lemma compactLabelNodes_closed (k : ℕ) : IsClosed {Q | CompactLabelNodes k Q} := by
  unfold CompactLabelNodes
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (Set.finite_range (sourceLabelLevel k)).isClosed.preimage (by fun_prop)

lemma sourceGibbsArray_limit_label_nodes (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactLabelNodes k Q := by
  have hc := compactLabelNodes_closed k
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc (fun n=>sourceGibbsArray_closed_full
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) hc
    (fun x i j => ⟨indexedCommonDepth k (x j).2 (x i).2,rfl⟩))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

def timeSpin (x : Time) : CompactOverlap := ⟨x.val,by linarith [x.prop.1],x.prop.2⟩
lemma timeSpin_continuous : Continuous timeSpin := by unfold timeSpin; fun_prop

def labelProfileSpin {k : ℕ} (q : Fin (k+1)→Time) (x : Time) : CompactOverlap :=
  ⟨min 1 (max 0 (labelProfileInterpolant (fun i => (q i:ℝ)) x)),
    le_min (by norm_num) ((by norm_num : (-1:ℝ)≤0).trans (le_max_left _ _)),min_le_left _ _⟩
lemma labelProfileSpin_continuous {k : ℕ} (q : Fin (k+1)→Time) : Continuous (labelProfileSpin q) := by
  unfold labelProfileSpin
  fun_prop
lemma labelProfileSpin_node {k : ℕ} (q : Fin (k+1)→Time) (l : Fin (k+1)) :
    labelProfileSpin q (sourceLabelLevel k l)=timeSpin (q l) := by
  apply Subtype.ext
  change min 1 (max 0 (labelProfileInterpolant (fun i => (q i:ℝ)) (sourceLabelLevel k l)))=(q l:ℝ)
  rw [labelProfileInterpolant_node,max_eq_right (q l).prop.1,min_eq_right (q l).prop.2]

def labelProfileMap {k : ℕ} (q : Fin (k+1)→Time) (x : CompactJointOverlap) : CompactJointOverlap :=
  (labelProfileSpin q x.2,x.2)
lemma labelProfileMap_continuous {k : ℕ} (q : Fin (k+1)→Time) : Continuous (labelProfileMap q) :=
  ((labelProfileSpin_continuous q).comp continuous_snd).prodMk continuous_snd

lemma sourceLabelLevel_le {k : ℕ} (i j : Fin (k+1)) :
    sourceLabelLevel k i ≤ sourceLabelLevel k j ↔ i≤j := by
  change (i.val:ℝ)/(k+1:ℕ)≤(j.val:ℝ)/(k+1:ℕ) ↔ i≤j
  rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(k+1:ℕ))]
  exact_mod_cast (Iff.rfl : i.val≤j.val ↔ i≤j)

lemma labelProfileMap_geometry {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    (h1 : q (Fin.last k)=1) {Q : CompactArray CompactJointOverlap}
    (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q) :
    CompactSpinGeometry (compactMapArray (labelProfileMap q) Q) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    have h : (Q i j).2=(Q j i).2 := Subtype.ext (hQ.1 i j)
    change (labelProfileSpin q (Q i j).2).val=(labelProfileSpin q (Q j i).2).val
    rw [h]
  · intro i
    have h : (Q i i).2=sourceLabelLevel k (Fin.last k) := Subtype.ext (hQ.2.1 i)
    change (labelProfileSpin q (Q i i).2).val=1
    rw [h,labelProfileSpin_node,h1]
    rfl
  · intro i j l
    obtain ⟨a,ha⟩ := hN i j
    obtain ⟨b,hb⟩ := hN i l
    obtain ⟨c,hc⟩ := hN j l
    have hs := hQ.2.2 i j l
    rw [←ha,←hb,←hc] at hs
    change min (labelProfileSpin q (Q i j).2).val (labelProfileSpin q (Q i l).2).val≤
      (labelProfileSpin q (Q j l).2).val
    rw [←ha,←hb,←hc,labelProfileSpin_node,labelProfileSpin_node,labelProfileSpin_node]
    change min (q a:ℝ) (q b:ℝ)≤(q c:ℝ)
    rcases le_total a b with hab|hab
    · have hab' : (sourceLabelLevel k a).val ≤ (sourceLabelLevel k b).val :=
        (sourceLabelLevel_le a b).mpr hab
      have hac : a≤c := (sourceLabelLevel_le a c).mp (by
        change (sourceLabelLevel k a).val≤(sourceLabelLevel k c).val
        simpa only [min_eq_left hab'] using hs)
      exact (min_le_left _ _).trans (hq hac)
    · have hba' : (sourceLabelLevel k b).val ≤ (sourceLabelLevel k a).val :=
        (sourceLabelLevel_le b a).mpr hab
      have hbc : b≤c := (sourceLabelLevel_le b c).mp (by
        change (sourceLabelLevel k b).val≤(sourceLabelLevel k c).val
        simpa only [min_eq_right hba'] using hs)
      exact (min_le_right _ _).trans (hq hbc)

lemma labelProfileMap_kernel {k : ℕ} (q : Fin (k+1)→Time) (h1 : q (Fin.last k)=1)
    (f : ℝ →ᵇ ℝ) (r : ℕ) {Q : CompactArray CompactJointOverlap}
    (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q) :
    freshReplicaArrayKernel f r (compactMapArray (labelProfileMap q) Q)=
      labelFreshArrayKernel (fun i => (q i:ℝ)) f r Q := by
  change freshReplicaMatrixKernel f r (fun i j => (labelProfileSpin q (Q i j).2).val)=
    freshReplicaMatrixKernel f r (fun i j => if i=j then 1 else
      labelProfileInterpolant (fun l => (q l:ℝ)) (Q i j).2)
  congr 1
  funext i j
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    have h : (Q i i).2=sourceLabelLevel k (Fin.last k) := Subtype.ext (hQ.2.1 i)
    rw [h,labelProfileSpin_node,h1]
    rfl
  · rw [ite_eq_right hij]
    obtain ⟨a,ha⟩ := hN i j
    rw [←ha,labelProfileSpin_node,labelProfileInterpolant_node]
    rfl

lemma compactSpinGeometry_closed : IsClosed {Q : CompactArray CompactJointOverlap | CompactSpinGeometry Q} := by
  unfold CompactSpinGeometry
  simp only [ofPred_and,ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
        isClosed_le (by fun_prop) (by fun_prop)))

theorem labelProfile_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1)
    (q : Fin (k+1)→Time) (hq : Monotone q) (h1 : q (Fin.last k)=1) (g : Jet3) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (FreshPartitionRange g.f)),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ F : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, F (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*F (timeSpin (q l))) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
        ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _)) ∧
      (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
        labelProfileValue k (stepCumulative w) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g := by
  let p := fun n => (Nat.unpair n).1
  let d := fun n => (Nat.unpair n).2
  have hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b := by
    intro a b _
    exact ⟨Nat.pair a b,by simp [p,d]⟩
  obtain ⟨u,ρ,s,hu,hs,hlim,hGG,hex,hpair,hgeo⟩ := source_label_reference_exists k w hw hw1 p d hcover
  have hL := sourceGibbsArray_limit_label_geometry k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  have hN := sourceGibbsArray_limit_label_nodes k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  let ν := compactMapLaw (labelProfileMap q) (labelProfileMap_continuous q) ρ
  obtain ⟨η,hη,hm,hl⟩ := sourceLabelFreshLog_tendsto k (fun i => (q i:ℝ)) (q 0).prop.1
    (fun i j hij => hq hij) (q (Fin.last k)).prop.2 0 g.f
    (fun _ j=>p j.val) (fun _ j=>d j.val) (fun _ _=>0) (fun _ _=>le_rfl)
    (fun _=>monotone_const) u (stepCumulative w) (fun _=>0) s hlim
  refine ⟨ν,η,compactMapLaw_gg _ _ ρ hGG,?_,?_,?_,?_⟩
  · change ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)).map
      (compactMapArray (labelProfileMap q)), CompactSpinGeometry Q
    apply (ae_map_iff (compactMapArray_continuous (labelProfileMap_continuous q)).measurable.aemeasurable
      compactSpinGeometry_closed.measurableSet).mpr
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact labelProfileMap_geometry q hq h1 hLQ hNQ
  · intro F
    change (∫ Q : CompactArray CompactJointOverlap, F (Q 0 1).1
      ∂(compactMapLaw (labelProfileMap q) (labelProfileMap_continuous q) ρ : Measure _))=_
    rw [compactMapLaw_integral (labelProfileMap q) (labelProfileMap_continuous q) ρ
      (fun Q => F (Q 0 1).1) (by fun_prop)]
    have he : (∫ Q, F (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=
        ∫ Q, F (labelProfileSpin q (Q 1 0).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)) := by
      apply integral_congr_ae
      filter_upwards [hL] with Q hLQ
      rw [show (Q 0 1).2=(Q 1 0).2 from Subtype.ext (hLQ.1 0 1)]
    change (∫ Q, F (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=_
    have hmap : (∫ x, F (labelProfileSpin q x) ∂((ρ : Measure (CompactArray CompactJointOverlap)).map
        (fun Q => (Q 1 0).2)))=∫ Q, F (labelProfileSpin q (Q 1 0).2)
          ∂(ρ : Measure (CompactArray CompactJointOverlap)) :=
      integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 1 0).2)
        from by fun_prop).aemeasurable
        (show Measurable (fun x : Time => F (labelProfileSpin q x)) from
          F.measurable.comp (labelProfileSpin_continuous q).measurable).aestronglyMeasurable
    rw [he,←hmap,hpair,sourceLabelLaw_integral k w (fun l => (hw l).le) (fun x => F (labelProfileSpin q x))
      (F.measurable.comp (labelProfileSpin_continuous q).measurable)]
    simp_rw [labelProfileSpin_node]
  · intro r
    rw [hm r]
    change _ = ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q
      ∂(compactMapLaw (labelProfileMap q) (labelProfileMap_continuous q) ρ : Measure _)
    rw [compactMapLaw_integral (labelProfileMap q) (labelProfileMap_continuous q) ρ
      (fun Q => freshReplicaArrayKernel (expBCF 1 g.f) r Q)
      (freshReplicaArrayKernel (expBCF 1 g.f) r).measurable]
    apply integral_congr_ae
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact (labelProfileMap_kernel q h1 (expBCF 1 g.f) r hLQ hNQ).symm
  · have hv := fun n => sourceLabelFreshLog_value (s n) k 0
      (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (fun _=>le_rfl) monotone_const
      (u (s n)) (stepCumulative w) (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
      (stepCumulative_lt_one w hw hw1) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g 0
    simp_rw [hv] at hl
    exact (tendsto_nhds_unique tendsto_const_nhds hl).symm

end SphericalPerceptronFreeEnergy
end

end OAI
