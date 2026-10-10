import Mathlib
import OAI.Probability.Perceptron.Variational.LabelProfileReference

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def labelProfileDiagonal (x : CompactJointOverlap) : CompactJointOverlap :=
  (⟨1,by norm_num,le_rfl⟩,x.2)
lemma labelProfileDiagonal_continuous : Continuous labelProfileDiagonal := by
  unfold labelProfileDiagonal
  fun_prop

lemma labelProfileSpin_ultra {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    {Q : CompactArray CompactJointOverlap} (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q)
    (i j l : ℕ) : min (labelProfileSpin q (Q i j).2).val (labelProfileSpin q (Q i l).2).val≤
      (labelProfileSpin q (Q j l).2).val := by
  obtain ⟨a,ha⟩ := hN i j
  obtain ⟨b,hb⟩ := hN i l
  obtain ⟨c,hc⟩ := hN j l
  have hs := hQ.2.2 i j l
  rw [←ha,←hb,←hc] at hs
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

lemma labelProfileDiagonalMap_geometry {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    {Q : CompactArray CompactJointOverlap} (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q) :
    CompactSpinGeometry (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q) := by
  have hsym (i j : ℕ) : (Q i j).2=(Q j i).2 := Subtype.ext (hQ.1 i j)
  refine ⟨?_,?_,?_⟩
  · intro i j
    by_cases hij : i=j
    · subst j; rfl
    · simp only [compactDiagonalMapArray,ite_eq_right hij,ite_eq_right (Ne.symm hij),labelProfileMap,hsym i j]
  · intro i
    simp only [compactDiagonalMapArray,↓reduceIte,labelProfileDiagonal]
  · intro i j l
    by_cases hjl : j=l
    · subst l
      simp only [compactDiagonalMapArray,↓reduceIte,labelProfileDiagonal,min_self]
      split_ifs <;> first | exact le_rfl | exact (labelProfileSpin q (Q i j).2).prop.2
    · by_cases hij : i=j
      · subst j
        simp only [compactDiagonalMapArray,↓reduceIte,ite_eq_right hjl,labelProfileDiagonal,labelProfileMap]
        exact min_le_right _ _
      · by_cases hil : i=l
        · subst l
          simp only [compactDiagonalMapArray,↓reduceIte,ite_eq_right hij,ite_eq_right hjl,labelProfileDiagonal,labelProfileMap]
          rw [hsym i j]
          exact min_le_left _ _
        · simp only [compactDiagonalMapArray,ite_eq_right hij,ite_eq_right hil,ite_eq_right hjl,labelProfileMap]
          exact labelProfileSpin_ultra q hq hQ hN i j l

lemma labelProfileDiagonalMap_kernel {k : ℕ} (q : Fin (k+1)→Time)
    (f : ℝ →ᵇ ℝ) (r : ℕ) {Q : CompactArray CompactJointOverlap} (hN : CompactLabelNodes k Q) :
    freshReplicaArrayKernel f r (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q)=
      labelFreshArrayKernel (fun i => (q i:ℝ)) f r Q := by
  change freshReplicaMatrixKernel f r (fun i j =>
      ((if (i:ℕ)=j then labelProfileDiagonal (Q i j) else labelProfileMap q (Q i j)).1:ℝ))=
    freshReplicaMatrixKernel f r (fun i j => if i=j then 1 else
      labelProfileInterpolant (fun l => (q l:ℝ)) (Q i j).2)
  congr 1
  funext i j
  by_cases hij : i=j
  · subst j
    simp only [↓reduceIte,labelProfileDiagonal]
  · have hv : (i:ℕ)≠j := fun h => hij (Fin.ext h)
    rw [ite_eq_right hv,ite_eq_right hij]
    obtain ⟨a,ha⟩ := hN i j
    change (labelProfileSpin q (Q i j).2).val=_
    rw [←ha,labelProfileSpin_node,labelProfileInterpolant_node]
    rfl

theorem labelProfile_reference_full_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1)
    (q : Fin (k+1)→Time) (hq : Monotone q) (g : Jet3) :
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
  let ν := compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
  obtain ⟨η,hη,hm,hl⟩ := sourceLabelFreshLog_tendsto k (fun i => (q i:ℝ)) (q 0).prop.1
    (fun i j hij => hq hij) (q (Fin.last k)).prop.2 0 g.f
    (fun _ j=>p j.val) (fun _ j=>d j.val) (fun _ _=>0) (fun _ _=>le_rfl)
    (fun _=>monotone_const) u (stepCumulative w) (fun _=>0) s hlim
  refine ⟨ν,η,compactDiagonalMapLaw_gg _ _ _ _ ρ hGG,?_,?_,?_,?_⟩
  · change ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)).map
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal), CompactSpinGeometry Q
    apply (ae_map_iff (compactDiagonalMapArray_continuous (labelProfileMap_continuous q) labelProfileDiagonal_continuous).measurable.aemeasurable
      compactSpinGeometry_closed.measurableSet).mpr
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact labelProfileDiagonalMap_geometry q hq hLQ hNQ
  · intro F
    change (∫ Q : CompactArray CompactJointOverlap, F (Q 0 1).1
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _))=_
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
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
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _)
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => freshReplicaArrayKernel (expBCF 1 g.f) r Q)
      (freshReplicaArrayKernel (expBCF 1 g.f) r).measurable]
    apply integral_congr_ae
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact (labelProfileDiagonalMap_kernel q (expBCF 1 g.f) r hNQ).symm
  · have hv := fun n => sourceLabelFreshLog_value (s n) k 0
      (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (fun _=>le_rfl) monotone_const
      (u (s n)) (stepCumulative w) (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
      (stepCumulative_lt_one w hw hw1) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g 0
    simp_rw [hv] at hl
    exact (tendsto_nhds_unique tendsto_const_nhds hl).symm

end SphericalPerceptronFreeEnergy
end

end OAI
