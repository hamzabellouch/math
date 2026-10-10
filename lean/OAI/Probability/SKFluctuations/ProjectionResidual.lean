import Mathlib
import OAI.Probability.SKFluctuations.ActualPathScore

namespace OAI

/-! Projection Residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

theorem finite_even_jensen {S : Type*} [Fintype S]
    (w Y : S → ℝ) (hw : ∀ s, 0 ≤ w s) (h1 : ∑ s, w s = 1) (c : ℝ) (k : ℕ) :
    |(∑ s, w s*Y s)-c|^(2*k+2) ≤ ∑ s, w s*|Y s-c|^(2*k+2) := by
  have hev : Even (2*k+2) := ⟨k+1,by omega⟩
  have hh := (hev.convexOn_pow (𝕜 := ℝ)).map_sum_le
    (p := fun s => Y s-c) (fun s _ => hw s) h1 (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,h1,
    one_mul,hev.pow_abs] using hh

theorem finite_centered_even_le {S : Type*} [Fintype S]
    (w Y : S → ℝ) (hw : ∀ s, 0 ≤ w s) (h1 : ∑ s, w s = 1) (c : ℝ) (k : ℕ) :
    (∑ s, w s*|Y s-(∑ t, w t*Y t)|^(2*k+2)) ≤
      (2:ℝ)^(2*k+2)*(∑ s, w s*|Y s-c|^(2*k+2)) := by
  let M := ∑ s, w s*Y s
  have hj := finite_even_jensen w Y hw h1 c k
  have hp (s : S) : |Y s-M|^(2*k+2) ≤
      (2:ℝ)^(2*k+1)*(|Y s-c|^(2*k+2)+|M-c|^(2*k+2)) := by
    have htri : |Y s-M| ≤ |Y s-c|+|M-c| := by
      have hh := abs_add_le (Y s-c) (c-M)
      simpa only [sub_add_sub_cancel,abs_sub_comm c M] using hh
    exact (pow_le_pow_left₀ (abs_nonneg _) htri _).trans (by
      simpa only [show 2*k+2-1 = 2*k+1 by omega] using
        add_pow_le (abs_nonneg (Y s-c)) (abs_nonneg (M-c)) (2*k+2))
  calc
    _ ≤ ∑ s, w s*((2:ℝ)^(2*k+1)*(|Y s-c|^(2*k+2)+|M-c|^(2*k+2))) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hp s) (hw s))
    _ = (2:ℝ)^(2*k+1)*((∑ s, w s*|Y s-c|^(2*k+2))+|M-c|^(2*k+2)) := by
      simp_rw [mul_add,mul_left_comm (w _),Finset.sum_add_distrib,← Finset.mul_sum,
        ← Finset.sum_mul,h1,one_mul]
    _ ≤ (2:ℝ)^(2*k+1)*((∑ s, w s*|Y s-c|^(2*k+2))+(∑ s, w s*|Y s-c|^(2*k+2))) := by gcongr
    _ = _ := by rw [show 2*k+2 = (2*k+1)+1 by omega,pow_succ]; ring

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem hierarchyCenteredEvenMoment_le {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (k : ℕ) (x : ι → ℝ) :
    hierarchyCenteredEvenMoment w φ Y steps k x ≤
      (2:ℝ)^(2*k+2)*gaussianHierarchyMean w φ (fun s => |Y s-c|^(2*k+2)) steps x := by
  simpa only [hierarchyCenteredEvenMoment,gaussianHierarchyMean_atoms hw φ steps ha,
    mul_comm (hierarchyAtom w φ steps _ _)] using
    finite_centered_even_le (fun s => hierarchyAtom w φ steps s x) Y
      (fun s => hierarchyAtom_nonneg hw φ steps ha s x) (hierarchyAtom_sum hw φ steps ha x) c k

 

theorem integral_segmentLaw_centeredEven_le {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (c : ℝ) (k : ℕ) (x : ι → ℝ) :
    (∫ p, hierarchyCenteredEvenMoment w φ Y tail k
      (forwardEnd pre.length (hierarchyIncrements pre) x p) ∂segmentLaw w φ tail pre x) ≤
      (2:ℝ)^(2*k+2)*gaussianHierarchyMean w φ (fun s => |Y s-c|^(2*k+2)) (pre++tail) x := by
  have := segmentLaw_isProbability hw φ tail pre ha x
  obtain ⟨b,hb⟩ := orderedSteps_append_right pre tail ha
  have hend : Measurable (forwardEnd pre.length (hierarchyIncrements pre) x) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp (measurable_const.prodMk measurable_id)
  have hR := (hierarchyCenteredEvenMoment_smooth_zero hw φ Y tail hb k).integrable_comp_measurable hend
    (μ := segmentLaw w φ tail pre x)
  have hB := (gaussianHierarchyMean_smooth hw φ (fun s => |Y s-c|^(2*k+2)) tail hb 0).integrable_comp_measurable hend
    (μ := segmentLaw w φ tail pre x)
  calc
    _ ≤ ∫ p, (2:ℝ)^(2*k+2)*gaussianHierarchyMean w φ (fun s => |Y s-c|^(2*k+2)) tail
        (forwardEnd pre.length (hierarchyIncrements pre) x p) ∂segmentLaw w φ tail pre x :=
      integral_mono hR (hB.const_mul _) (fun p => hierarchyCenteredEvenMoment_le hw φ Y tail hb c k _)
    _ = _ := by rw [integral_const_mul,integral_segmentLaw_mean hw φ _ tail pre ha]

theorem integral_segmentLaw_centeredEven_le_initial {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (k : ℕ) (x : ι → ℝ) :
    (∫ p, hierarchyCenteredEvenMoment w φ Y tail k
      (forwardEnd pre.length (hierarchyIncrements pre) x p) ∂segmentLaw w φ tail pre x) ≤
      (2:ℝ)^(2*k+2)*hierarchyCenteredEvenMoment w φ Y (pre++tail) k x := by
  have hh := integral_segmentLaw_centeredEven_le hw φ Y tail pre ha
    (gaussianHierarchyMean w φ Y (pre++tail) x) k x
  simpa only [hierarchyCenteredEvenMoment,gaussianHierarchyMean_atoms hw φ (pre++tail) ha,
    mul_comm (hierarchyAtom w φ (pre++tail) _ _)] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

noncomputable def segmentResponseCost (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (tail : List (GaussianStep ι)) :
    (pre : List (GaussianStep ι)) → (Fin pre.length → ι → ℝ) →
      (ι → ℝ) → (Fin pre.length → (ι → ℝ)) → ℝ
  | [], _, _, _ => 0
  | (_m,q)::rest, v, x, p =>
      gaussianHierarchyResponse w φ A (scaleDriver q (v 0)) (rest++tail) (x+scaleDriver q (p 0)) +
      segmentResponseCost w φ A tail rest (Fin.tail v) (x+scaleDriver q (p 0)) (Fin.tail p)

theorem segmentResponseCost_continuous {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → ι → ℝ) :
    Continuous (fun xp : (ι → ℝ) × (Fin pre.length → (ι → ℝ)) =>
      segmentResponseCost w φ A tail pre v xp.1 xp.2) := by
  induction pre generalizing a with
  | nil => exact continuous_const
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    have hx : Continuous (fun xp : (ι → ℝ) × (Fin (((m,q)::rest).length) → (ι → ℝ)) =>
        xp.1+scaleDriver q (xp.2 0)) :=
      continuous_fst.add ((scaleDriver q).continuous.comp ((continuous_apply 0).comp continuous_snd))
    exact ((gaussianHierarchyResponse_smooth hw φ A (scaleDriver q (v 0))
      (rest++tail) ha.2.2.2 0).continuous.comp hx).add
      ((ih ha.2.2.2 (Fin.tail v)).comp (hx.prodMk
        (continuous_pi (fun i => (continuous_apply i.succ).comp continuous_snd))))

theorem segmentResponseCost_bound {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x p, |segmentResponseCost w φ A tail pre v x p| ≤ B := by
  induction pre generalizing a with
  | nil => exact ⟨0,le_rfl,fun _ _ => by simp [segmentResponseCost]⟩
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    obtain ⟨B,hB,hb⟩ := (gaussianHierarchyResponse_smooth hw φ A (scaleDriver q (v 0))
      (rest++tail) ha.2.2.2 0).bound
    obtain ⟨C,hC,hc⟩ := ih ha.2.2.2 (Fin.tail v)
    exact ⟨B+C,add_nonneg hB hC, fun x p => (abs_add_le _ _).trans (add_le_add (hb _) (hc _ _))⟩

theorem segmentResponseCost_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → ι → ℝ) (x : ι → ℝ) :
    Integrable (segmentResponseCost w φ A tail pre v x) (segmentLaw w φ tail pre x) := by
  have := segmentLaw_isProbability hw φ tail pre ha x
  obtain ⟨B,_,hB⟩ := segmentResponseCost_bound hw φ A tail pre ha v
  exact memLp_one_iff_integrable.mp (MemLp.of_bound
    (((segmentResponseCost_continuous hw φ A tail pre ha v).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable) B
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hB x p)))

theorem segmentMean_mul_score_integrable {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) :
    Integrable (fun p => gaussianHierarchyMean w φ A tail
      (forwardEnd pre.length (hierarchyIncrements pre) x p)*segmentPathScore w φ tail pre v x p)
      (segmentLaw w φ tail pre x) := by
  obtain ⟨b,hb⟩ := orderedSteps_append_right pre tail ha
  have hA := gaussianHierarchyMean_smooth hw φ A tail hb 0
  obtain ⟨B,_,hB⟩ := hA.bound
  exact (segmentPathScore_hasSubgaussianMGF hw φ tail pre ha v x).integrable.bdd_mul
    ((hA.continuous.measurable.comp ((measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hB _))

theorem integrable_integral_segmentLaw_cons {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail rest : List (GaussianStep ι))
    {a m : ℝ} (q : ι → ℝ≥0) (ha : OrderedSteps a (((m,q)::rest)++tail)) (x : ι → ℝ)
    {f : (Fin (((m,q)::rest).length) → (ι → ℝ)) → ℝ}
    (hf : Integrable f (segmentLaw w φ tail ((m,q)::rest) x)) :
    Integrable (fun z => ∫ p, f (Fin.cons z p) ∂segmentLaw w φ tail rest (x+scaleDriver q z))
      ((standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)) := by
  let inc := hierarchyIncrements ((m,q)::rest)
  let T := segmentTransitions w φ tail ((m,q)::rest)
  have hi := hierarchyIncrements_measurable ((m,q)::rest)
  have ht := segmentTransitions_measurable hw φ tail ((m,q)::rest) ha
  have h1 := segmentTransitions_normalized hw φ tail ((m,q)::rest) ha
  let := forwardKernel_isMarkov rest.length (fun _ => standardDrivers ι)
    (fun i => hi i.succ) (fun i => ht i.succ) (fun i => h1 i.succ)
  have : IsMarkovKernel (forwardTailKernel (fun _ => standardDrivers ι) inc T hi x) := by
    dsimp only [forwardTailKernel,inc,T]; infer_instance
  have : IsProbabilityMeasure ((standardDrivers ι).withDensity (T 0 x)) := by
    refine ⟨?_⟩
    simpa only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using h1 0 x
  change Integrable f (forwardLaw (rest.length+1) (fun _ => standardDrivers ι) inc T x) at hf
  rw [forwardLaw_cons _ hi ht h1 x] at hf
  have hh := hf.comp_measurable measurable_finCons
  have hh' : Integrable (fun zp : (ι → ℝ) × (Fin rest.length → (ι → ℝ)) => f (Fin.cons zp.1 zp.2))
      (((Kernel.const Unit ((standardDrivers ι).withDensity (T 0 x))) ⊗ₖ
        (forwardTailKernel (fun _ => standardDrivers ι) inc T hi x).prodMkLeft Unit) ()) := hh
  have hh'' := hh'.integral_compProd
  simp only [Kernel.const_apply,Kernel.prodMkLeft_apply,forwardTailKernel,Kernel.comap_apply,
    inc,T,hierarchyIncrements,segmentTransitions,Fin.cons_zero,Fin.cons_succ] at hh''
  simpa only [forwardKernel_apply _ _ (hierarchyIncrements_measurable rest)
    (segmentTransitions_measurable hw φ tail rest ha.2.2.2),segmentLaw] using hh''

 

theorem integral_segmentMean_mul_score {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) :
    (∫ p, gaussianHierarchyMean w φ A tail
      (forwardEnd pre.length (hierarchyIncrements pre) x p)*segmentPathScore w φ tail pre v x p
      ∂segmentLaw w φ tail pre x) =
    ∫ p, segmentResponseCost w φ A tail pre v x p ∂segmentLaw w φ tail pre x := by
  induction pre generalizing a x with
  | nil => simp [segmentPathScore,forwardScore,segmentResponseCost]
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    let μ := (standardDrivers (Fin (n+1))).withDensity
      (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)
    have hμ : μ = tiltedLaw (standardDrivers (Fin (n+1))) m
        (fun z => gaussianHierarchy w φ (rest++tail) (x+scaleDriver q z)) :=
      scaledTransitionLaw_eq hw φ (rest++tail) ha.2.2.2 ha.2.2.1.ne' q x
    have : IsProbabilityMeasure μ := by
      refine ⟨?_⟩
      simpa only [μ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using
        hierarchyTransitions_normalized hw φ ((m,q)::(rest++tail)) ha 0 x
    let R := fun z => gaussianHierarchyResponse w φ A (scaleDriver q (v 0)) (rest++tail)
      (x+scaleDriver q z)
    let H := fun z => ∫ p, segmentResponseCost w φ A tail rest (Fin.tail v)
      (x+scaleDriver q z) p ∂segmentLaw w φ tail rest (x+scaleDriver q z)
    let MS := fun z => gaussianHierarchyMean w φ A (rest++tail) (x+scaleDriver q z)*
      hierarchyAffineScore w φ (scaleDriver q) (rest++tail) x m (v 0) z
    have hR : Integrable R μ :=
      (gaussianHierarchyResponse_smooth hw φ A (scaleDriver q (v 0)) (rest++tail) ha.2.2.2 0).integrable_comp_measurable (measurable_const.add (scaleDriver q).measurable)
    have hMS : Integrable MS μ := by
      have hz := (segmentScores_hasSubgaussianMGF hw φ tail ((m,q)::rest) ha v 0 x).integrable
      have hM := gaussianHierarchyMean_smooth hw φ A (rest++tail) ha.2.2.2 0
      obtain ⟨B,_,hB⟩ := hM.bound
      exact hz.bdd_mul ((hM.continuous.measurable.comp
        (measurable_const.add (scaleDriver q).measurable)).aestronglyMeasurable)
        (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hB (x+scaleDriver q z)))
    have hcost := segmentResponseCost_integrable hw φ A tail ((m,q)::rest) ha v x
    have hecost (z : Fin (n+1) → ℝ) :
        (∫ p, segmentResponseCost w φ A tail ((m,q)::rest) v x (Fin.cons z p)
          ∂segmentLaw w φ tail rest (x+scaleDriver q z)) = R z+H z := by
      have := segmentLaw_isProbability hw φ tail rest ha.2.2.2 (x+scaleDriver q z)
      simp only [segmentResponseCost,Fin.cons_zero,Fin.tail_cons]
      rw [integral_add (integrable_const _) (segmentResponseCost_integrable hw φ A tail rest
        ha.2.2.2 (Fin.tail v) (x+scaleDriver q z)),integral_const]
      simp only [probReal_univ,one_smul,R,H]
    have hRH : Integrable (fun z => R z+H z) μ := by
      have hh := integrable_integral_segmentLaw_cons hw φ tail rest q ha x hcost
      exact hh.congr (ae_of_all _ hecost)
    have hH : Integrable H μ := by
      have hh := hRH.sub hR
      change Integrable (fun z => (R z+H z)-R z) μ at hh
      simpa only [add_sub_cancel_left] using hh
    have hlhs := segmentMean_mul_score_integrable hw φ A tail ((m,q)::rest) ha v x
    rw [integral_segmentLaw_cons hw φ tail rest q ha x hlhs,
      integral_segmentLaw_cons hw φ tail rest q ha x hcost]
    have heleft (z : Fin (n+1) → ℝ) :
        (∫ p, gaussianHierarchyMean w φ A tail
          (forwardEnd (((m,q)::rest).length) (hierarchyIncrements ((m,q)::rest)) x (Fin.cons z p))*
          segmentPathScore w φ tail ((m,q)::rest) v x (Fin.cons z p)
          ∂segmentLaw w φ tail rest (x+scaleDriver q z)) = MS z+H z := by
      have := segmentLaw_isProbability hw φ tail rest ha.2.2.2 (x+scaleDriver q z)
      obtain ⟨b,hb⟩ := orderedSteps_append_right rest tail ha.2.2.2
      have hA := (gaussianHierarchyMean_smooth hw φ A tail hb 0).integrable_comp_measurable
        (f := forwardEnd rest.length (hierarchyIncrements rest) (x+scaleDriver q z))
        ((measurable_forwardEnd _ (hierarchyIncrements_measurable rest)).comp
          (measurable_const.prodMk measurable_id))
        (μ := segmentLaw w φ tail rest (x+scaleDriver q z))
      have hAS := segmentMean_mul_score_integrable hw φ A tail rest ha.2.2.2 (Fin.tail v)
        (x+scaleDriver q z)
      simp only [List.length_cons,forwardEnd,hierarchyIncrements,segmentPathScore,forwardScore,
        segmentScores,Fin.cons_zero,Fin.cons_succ,Fin.tail_cons,mul_add]
      change (∫ p, gaussianHierarchyMean w φ A tail
        (forwardEnd rest.length (hierarchyIncrements rest) (x+scaleDriver q z) p)*
        hierarchyAffineScore w φ (scaleDriver q) (rest++tail) x m (v 0) z +
        gaussianHierarchyMean w φ A tail
          (forwardEnd rest.length (hierarchyIncrements rest) (x+scaleDriver q z) p)*
          segmentPathScore w φ tail rest (Fin.tail v) (x+scaleDriver q z) p
          ∂segmentLaw w φ tail rest (x+scaleDriver q z)) = MS z+H z
      rw [integral_add (hA.mul_const _) hAS,integral_mul_const,
        integral_segmentLaw_mean hw φ A tail rest ha.2.2.2 (x+scaleDriver q z),
        ih ha.2.2.2 (Fin.tail v) (x+scaleDriver q z)]
    simp_rw [heleft,hecost]
    rw [integral_add hMS hH,integral_add hR hH]
    congr 1
    obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ (rest++tail) ha.2.2.2
    have hshift : LipschitzWith _ (fun z => gaussianHierarchy w φ (rest++tail) (x+scaleDriver q z)) :=
      hF.comp ((isometry_add_left x).lipschitzWith.comp (scaleDriver q).lipschitzWith)
    have hexp : Integrable (fun z => Real.exp (m*gaussianHierarchy w φ (rest++tail)
        (x+scaleDriver q z))) (standardDrivers (Fin (n+1))) :=
      (ExpNormBounded.exp_lipschitz hshift m).integrable (fun _ => 1)
    change (∫ z, MS z ∂μ) = ∫ z, R z ∂μ
    rw [hμ,integral_tiltedLaw hshift.continuous.measurable hexp,
      integral_tiltedLaw hshift.continuous.measurable hexp]
    exact tiltedMean_hierarchyAffineScore hw φ (scaleDriver q) (rest++tail) ha.2.2.2 x m A (v 0)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem gaussianHierarchyResponse_smul_direction {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x u : ι → ℝ) (d : ℝ) :
    gaussianHierarchyResponse w φ A (d • u) steps x =
      d*gaussianHierarchyResponse w φ A u steps x := by
  simp only [gaussianHierarchyResponse_eq_lineDeriv hw φ A steps ha,lineDeriv_smul,smul_eq_mul]

theorem hierarchyCenteredEvenMoment_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (k : ℕ) (x : ι → ℝ) :
    0 ≤ hierarchyCenteredEvenMoment w φ Y steps k x :=
  Finset.sum_nonneg (fun s _ => mul_nonneg (hierarchyAtom_nonneg hw φ steps ha s x)
    (pow_nonneg (abs_nonneg _) _))

theorem integral_segmentResponseCost_tail_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail rest : List (GaussianStep ι))
    {a m : ℝ} (q : ι → ℝ≥0) (ha : OrderedSteps a (((m,q)::rest)++tail))
    (v : Fin (((m,q)::rest).length) → ι → ℝ) (x : ι → ℝ) :
    Integrable (fun z => ∫ p, segmentResponseCost w φ A tail rest (Fin.tail v)
      (x+scaleDriver q z) p ∂segmentLaw w φ tail rest (x+scaleDriver q z))
      ((standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)) := by
  let μ := (standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)
  have : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simpa only [μ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using
      hierarchyTransitions_normalized hw φ ((m,q)::(rest++tail)) ha 0 x
  have hR : Integrable (fun z => gaussianHierarchyResponse w φ A (scaleDriver q (v 0))
      (rest++tail) (x+scaleDriver q z)) μ :=
    (gaussianHierarchyResponse_smooth hw φ A (scaleDriver q (v 0)) (rest++tail) ha.2.2.2 0).integrable_comp_measurable (measurable_const.add (scaleDriver q).measurable)
  have hI := integrable_integral_segmentLaw_cons hw φ tail rest q ha x
    (segmentResponseCost_integrable hw φ A tail ((m,q)::rest) ha v x)
  have hh := hI.sub hR
  refine hh.congr (ae_of_all _ (fun z => ?_))
  have := segmentLaw_isProbability hw φ tail rest ha.2.2.2 (x+scaleDriver q z)
  simp only [Pi.sub_apply,segmentResponseCost,Fin.cons_zero,Fin.tail_cons]
  rw [integral_add (integrable_const _) (segmentResponseCost_integrable hw φ A tail rest
    ha.2.2.2 (Fin.tail v) (x+scaleDriver q z)),integral_const]
  simp

theorem integral_segmentResponseCost_cons {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail rest : List (GaussianStep ι))
    {a m : ℝ} (q : ι → ℝ≥0) (ha : OrderedSteps a (((m,q)::rest)++tail))
    (v : Fin (((m,q)::rest).length) → ι → ℝ) (x : ι → ℝ) :
    (∫ p, segmentResponseCost w φ A tail ((m,q)::rest) v x p ∂segmentLaw w φ tail ((m,q)::rest) x) =
      (∫ z, gaussianHierarchyResponse w φ A (scaleDriver q (v 0)) (rest++tail) (x+scaleDriver q z)
        ∂(standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)) +
      ∫ z, ∫ p, segmentResponseCost w φ A tail rest (Fin.tail v) (x+scaleDriver q z) p
        ∂segmentLaw w φ tail rest (x+scaleDriver q z)
        ∂(standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x) := by
  let μ := (standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)
  have : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simpa only [μ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using
      hierarchyTransitions_normalized hw φ ((m,q)::(rest++tail)) ha 0 x
  have hR : Integrable (fun z => gaussianHierarchyResponse w φ A (scaleDriver q (v 0))
      (rest++tail) (x+scaleDriver q z)) μ :=
    (gaussianHierarchyResponse_smooth hw φ A (scaleDriver q (v 0)) (rest++tail) ha.2.2.2 0).integrable_comp_measurable (measurable_const.add (scaleDriver q).measurable)
  rw [integral_segmentLaw_cons hw φ tail rest q ha x
    (segmentResponseCost_integrable hw φ A tail ((m,q)::rest) ha v x)]
  have he (z : ι → ℝ) :
      (∫ p, segmentResponseCost w φ A tail ((m,q)::rest) v x (Fin.cons z p)
        ∂segmentLaw w φ tail rest (x+scaleDriver q z)) =
      gaussianHierarchyResponse w φ A (scaleDriver q (v 0)) (rest++tail) (x+scaleDriver q z) +
      ∫ p, segmentResponseCost w φ A tail rest (Fin.tail v) (x+scaleDriver q z) p
        ∂segmentLaw w φ tail rest (x+scaleDriver q z) := by
    have := segmentLaw_isProbability hw φ tail rest ha.2.2.2 (x+scaleDriver q z)
    simp only [segmentResponseCost,Fin.cons_zero,Fin.tail_cons]
    rw [integral_add (integrable_const _) (segmentResponseCost_integrable hw φ A tail rest
      ha.2.2.2 (Fin.tail v) (x+scaleDriver q z)),integral_const]
    simp
  simp_rw [he]
  exact integral_add hR (integral_segmentResponseCost_tail_integrable hw φ A tail rest q ha v x)

noncomputable def segmentCenteredEvenMoment (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (Y : S → ℝ) (tail pre : List (GaussianStep ι)) (k : ℕ) (x : ι → ℝ) : ℝ :=
  ∫ p, hierarchyCenteredEvenMoment w φ Y tail k
    (forwardEnd pre.length (hierarchyIncrements pre) x p) ∂segmentLaw w φ tail pre x

theorem segmentCenteredEvenMoment_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (k : ℕ) (x : ι → ℝ) :
    Integrable (fun p => hierarchyCenteredEvenMoment w φ Y tail k
      (forwardEnd pre.length (hierarchyIncrements pre) x p)) (segmentLaw w φ tail pre x) := by
  have := segmentLaw_isProbability hw φ tail pre ha x
  obtain ⟨b,hb⟩ := orderedSteps_append_right pre tail ha
  exact (hierarchyCenteredEvenMoment_smooth_zero hw φ Y tail hb k).integrable_comp_measurable
    ((measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
      (measurable_const.prodMk measurable_id))

theorem segmentCenteredEvenMoment_cons {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (tail rest : List (GaussianStep ι))
    {a m : ℝ} (q : ι → ℝ≥0) (ha : OrderedSteps a (((m,q)::rest)++tail)) (k : ℕ) (x : ι → ℝ) :
    segmentCenteredEvenMoment w φ Y tail ((m,q)::rest) k x =
      ∫ z, segmentCenteredEvenMoment w φ Y tail rest k (x+scaleDriver q z)
        ∂(standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x) := by
  rw [segmentCenteredEvenMoment,integral_segmentLaw_cons hw φ tail rest q ha x
    (segmentCenteredEvenMoment_integrable hw φ Y tail ((m,q)::rest) ha k x)]
  simp only [List.length_cons,forwardEnd,hierarchyIncrements,Fin.cons_zero,Fin.cons_succ,
    Fin.tail_cons,segmentCenteredEvenMoment]

theorem segmentCenteredEvenMoment_tail_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (tail rest : List (GaussianStep ι))
    {a m : ℝ} (q : ι → ℝ≥0) (ha : OrderedSteps a (((m,q)::rest)++tail)) (k : ℕ) (x : ι → ℝ) :
    Integrable (fun z => segmentCenteredEvenMoment w φ Y tail rest k (x+scaleDriver q z))
      ((standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)) := by
  have hh := integrable_integral_segmentLaw_cons hw φ tail rest q ha x
    (segmentCenteredEvenMoment_integrable hw φ Y tail ((m,q)::rest) ha k x)
  simpa only [List.length_cons,forwardEnd,hierarchyIncrements,Fin.cons_zero,Fin.cons_succ,
    Fin.tail_cons,segmentCenteredEvenMoment] using hh

 

theorem segmentResponseCost_odd_coercivity {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (u : ι → ℝ)
    (v : Fin pre.length → ι → ℝ) (d : Fin pre.length → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdir : ∀ i, hierarchyIncrements pre i (v i) = d i • u) (c : ℝ) (k : ℕ) (x : ι → ℝ) :
    a*(∑ i, d i)*segmentCenteredEvenMoment w φ (fun s => φ s u) tail pre k x ≤
      ((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k)) *
        ∫ p, segmentResponseCost w φ (fun s => (φ s u-c)^(2*k+1)) tail pre v x p
          ∂segmentLaw w φ tail pre x := by
  induction pre generalizing a x with
  | nil => simp [segmentResponseCost]
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    let Y := fun s => φ s u
    let A := fun s => (Y s-c)^(2*k+1)
    let C := (2:ℝ)^(2*k+2)*(2:ℝ)^(2*k)
    let μ := (standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::(rest++tail)) 0 x)
    let R := fun z => gaussianHierarchyResponse w φ A (scaleDriver q (v 0)) (rest++tail)
      (x+scaleDriver q z)
    let H := fun z => ∫ p, segmentResponseCost w φ A tail rest (Fin.tail v) (x+scaleDriver q z) p
      ∂segmentLaw w φ tail rest (x+scaleDriver q z)
    let E := fun z => segmentCenteredEvenMoment w φ Y tail rest k (x+scaleDriver q z)
    have hrest : OrderedSteps a (rest++tail) := ha.2.2.2.lower ha.nonneg ha.2.1
    have : IsProbabilityMeasure μ := by
      refine ⟨?_⟩
      simpa only [μ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using
        hierarchyTransitions_normalized hw φ ((m,q)::(rest++tail)) ha 0 x
    have hR : Integrable R μ :=
      (gaussianHierarchyResponse_smooth hw φ A (scaleDriver q (v 0)) (rest++tail) hrest 0).integrable_comp_measurable
        (measurable_const.add (scaleDriver q).measurable)
    have hH : Integrable H μ := integral_segmentResponseCost_tail_integrable hw φ A tail rest q ha v x
    have hE : Integrable E μ := segmentCenteredEvenMoment_tail_integrable hw φ Y tail rest q ha k x
    have hdir0 : scaleDriver q (v 0) = d 0 • u := by simpa only [hierarchyIncrements,Fin.cons_zero] using hdir 0
    have hhead (z : ι → ℝ) : a*d 0*E z ≤ C*R z := by
      have hJ := integral_segmentLaw_centeredEven_le_initial hw φ Y tail rest hrest k (x+scaleDriver q z)
      have hco := gaussianHierarchyResponse_odd_coercivity hw φ u c k (rest++tail) hrest (x+scaleDriver q z)
      change a*hierarchyCenteredEvenMoment w φ Y (rest++tail) k (x+scaleDriver q z) ≤ _ at hco
      calc
        _ ≤ a*d 0*((2:ℝ)^(2*k+2)*hierarchyCenteredEvenMoment w φ Y (rest++tail) k (x+scaleDriver q z)) :=
          mul_le_mul_of_nonneg_left hJ (mul_nonneg ha.nonneg (hd 0))
        _ = (d 0*(2:ℝ)^(2*k+2))*(a*hierarchyCenteredEvenMoment w φ Y (rest++tail) k (x+scaleDriver q z)) := by ring
        _ ≤ (d 0*(2:ℝ)^(2*k+2))*((2:ℝ)^(2*k)*gaussianHierarchyResponse w φ A u (rest++tail) (x+scaleDriver q z)) :=
          mul_le_mul_of_nonneg_left hco (mul_nonneg (hd 0) (by positivity))
        _ = C*R z := by
          dsimp only [R,C]
          rw [hdir0,gaussianHierarchyResponse_smul_direction hw φ A (rest++tail) hrest]
          ring
    have htail (z : ι → ℝ) : a*(∑ i : Fin rest.length, d i.succ)*E z ≤ C*H z :=
      ih hrest (Fin.tail v) (Fin.tail d) (fun i => hd i.succ)
        (fun i => by simpa only [hierarchyIncrements,Fin.cons_succ,Fin.tail] using hdir i.succ) (x+scaleDriver q z)
    have hh := integral_mono (hE.const_mul (a*d 0)) (hR.const_mul C) hhead
    have ht := integral_mono (hE.const_mul (a*(∑ i : Fin rest.length, d i.succ))) (hH.const_mul C) htail
    simp only [integral_const_mul] at hh ht
    have he : segmentCenteredEvenMoment w φ Y tail ((m,q)::rest) k x = ∫ z, E z ∂μ :=
      segmentCenteredEvenMoment_cons hw φ Y tail rest q ha k x
    have hc : (∫ p, segmentResponseCost w φ A tail ((m,q)::rest) v x p ∂segmentLaw w φ tail ((m,q)::rest) x) =
        (∫ z, R z ∂μ)+(∫ z, H z ∂μ) := integral_segmentResponseCost_cons hw φ A tail rest q ha v x
    change a*(∑ i : Fin (rest.length+1), d i)*segmentCenteredEvenMoment w φ Y tail ((m,q)::rest) k x ≤
      C*(∫ p, segmentResponseCost w φ A tail ((m,q)::rest) v x p ∂segmentLaw w φ tail ((m,q)::rest) x)
    rw [Fin.sum_univ_succ,he,hc]
    nlinarith [add_le_add hh ht]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

theorem hierarchy_projection_segment {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (u : Fin (n+1) → ℝ)
    (v : Fin pre.length → Fin (n+1) → ℝ) (d : Fin pre.length → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdir : ∀ i, hierarchyIncrements pre i (v i) = d i • u)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (x : Fin (n+1) → ℝ) :
    a*(∑ i, d i)*segmentCenteredEvenMoment w φ (fun s => φ s u) tail pre k x ≤
      ((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k)) *
        (ε*gaussianHierarchyMean w φ (fun s => |φ s u-c|^(2*k+2)) (pre++tail) x +
          (ε⁻¹)^(2*k+1)*subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1)) := by
  let Y := fun s => φ s u
  let A := fun s => (Y s-c)^(2*k+1)
  let B := fun s => |Y s-c|^(2*k+2)
  let μ := segmentLaw w φ tail pre x
  let Z := segmentPathScore w φ tail pre v x
  let e := forwardEnd pre.length (hierarchyIncrements pre) x
  have := segmentLaw_isProbability hw φ tail pre ha x
  obtain ⟨b,hb⟩ := orderedSteps_append_right pre tail ha
  have he : Measurable e := (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
    (measurable_const.prodMk measurable_id)
  have hB := (gaussianHierarchyMean_smooth hw φ B tail hb 0).integrable_comp_measurable he (μ := μ)
  have hZ := subgaussian_integrable_abs_natPow
    (segmentPathScore_hasSubgaussianMGF hw φ tail pre ha v x) (2*k+2)
  have hAZ := segmentMean_mul_score_integrable hw φ A tail pre ha v x
  have hYoung : (∫ p, gaussianHierarchyMean w φ A tail (e p)*Z p ∂μ) ≤
      ε*(∫ p, gaussianHierarchyMean w φ B tail (e p) ∂μ)+
      (ε⁻¹)^(2*k+1)*(∫ p, |Z p|^(2*k+2) ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hB.const_mul ε) (hZ.const_mul _)]
    apply integral_mono hAZ ((hB.const_mul ε).add (hZ.const_mul _))
    intro p
    have hh := weighted_odd_score_young (fun s => hierarchyAtom w φ tail s (e p)) Y
      (fun s => hierarchyAtom_nonneg hw φ tail hb s (e p)) (hierarchyAtom_sum hw φ tail hb (e p))
      c (Z p) hε (2*k+1)
    simpa only [A,B,e,Z,Pi.add_apply,gaussianHierarchyMean_atoms hw φ tail hb,
      mul_comm (hierarchyAtom w φ tail _ _),show 2*k+1+1 = 2*k+2 by omega] using hh
  have hco := segmentResponseCost_odd_coercivity hw φ tail pre ha u v d hd hdir c k x
  rw [← integral_segmentMean_mul_score hw φ A tail pre ha v x] at hco
  have hmoment : (∫ p, |Z p|^(2*k+2) ∂μ) ≤
      subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1) := by
    simpa only [show 2*(k+1) = 2*k+2 by omega] using
      segmentPathScore_even_moment hw φ tail pre ha v x k
  calc
    _ ≤ ((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))*(∫ p, gaussianHierarchyMean w φ A tail (e p)*Z p ∂μ) := hco
    _ ≤ ((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))*(ε*(∫ p, gaussianHierarchyMean w φ B tail (e p) ∂μ)+
        (ε⁻¹)^(2*k+1)*(∫ p, |Z p|^(2*k+2) ∂μ)) := mul_le_mul_of_nonneg_left hYoung (by positivity)
    _ ≤ ((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))*(ε*(∫ p, gaussianHierarchyMean w φ B tail (e p) ∂μ)+
        (ε⁻¹)^(2*k+1)*(subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1))) := by
      gcongr
    _ = _ := by
      rw [show (∫ p, gaussianHierarchyMean w φ B tail (e p) ∂μ) =
        gaussianHierarchyMean w φ B (pre++tail) x from integral_segmentLaw_mean hw φ B tail pre ha x]
      simp only [B,Y,mul_assoc]

 
theorem hierarchy_projection_segment_centered {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (u : Fin (n+1) → ℝ)
    (v : Fin pre.length → Fin (n+1) → ℝ) (d : Fin pre.length → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdir : ∀ i, hierarchyIncrements pre i (v i) = d i • u)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (x : Fin (n+1) → ℝ) :
    a*(∑ i, d i)*segmentCenteredEvenMoment w φ (fun s => φ s u) tail pre k x ≤
      ((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k)) *
        (ε*hierarchyCenteredEvenMoment w φ (fun s => φ s u) (pre++tail) k x +
          (ε⁻¹)^(2*k+1)*subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1)) := by
  have hh := hierarchy_projection_segment hw φ tail pre ha u v d hd hdir
    (gaussianHierarchyMean w φ (fun s => φ s u) (pre++tail) x) hε k x
  simpa only [hierarchyCenteredEvenMoment,gaussianHierarchyMean_atoms hw φ (pre++tail) ha,
    mul_comm (hierarchyAtom w φ (pre++tail) _ _)] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

lemma quantitative_half_contraction {t C x y z : ℝ} (ht : 0 < t) (hC : 0 < C)
    (p : ℕ) (h : t*y ≤ C*((2*C/t)⁻¹*x+(2*C/t)^p*z)) :
    y ≤ x/2+(2*C/t)^(p+1)*z/2 := by
  let q : ℝ := 2*C/t
  have hq : 0 < q := by dsimp [q]; positivity
  have hqt : q*t = 2*C := by dsimp [q]; field_simp
  have hh : C*(2*y) ≤ C*(x+q^(p+1)*z) := calc
    _ = q*(t*y) := by calc
      _ = (2*C)*y := by ring
      _ = _ := by rw [← hqt]; ring
    _ ≤ q*(C*(q⁻¹*x+q^p*z)) := mul_le_mul_of_nonneg_left h hq.le
    _ = _ := by rw [pow_succ]; field_simp
  have := (mul_le_mul_iff_right₀ hC).mp hh
  dsimp [q] at this
  linarith

 
theorem hierarchy_projection_segment_half {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (ha0 : 0 < a) (u : Fin (n+1) → ℝ)
    (v : Fin pre.length → Fin (n+1) → ℝ) (d : Fin pre.length → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hD : 0 < ∑ i, d i) (hdir : ∀ i, hierarchyIncrements pre i (v i) = d i • u)
    (k : ℕ) (x : Fin (n+1) → ℝ) :
    segmentCenteredEvenMoment w φ (fun s => φ s u) tail pre k x ≤
      hierarchyCenteredEvenMoment w φ (fun s => φ s u) (pre++tail) k x / 2 +
      (2*((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))/(a*(∑ i, d i)))^(2*k+2) *
        (subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1))/2 := by
  have hC : 0 < (2:ℝ)^(2*k+2)*(2:ℝ)^(2*k) := by positivity
  have ht : 0 < a*(∑ i, d i) := mul_pos ha0 hD
  have hε : 0 < (2*((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))/(a*(∑ i, d i)))⁻¹ := by positivity
  have hh := hierarchy_projection_segment_centered hw φ tail pre ha u v d hd hdir hε k x
  have hhalf := quantitative_half_contraction
    (x := hierarchyCenteredEvenMoment w φ (fun s => φ s u) (pre++tail) k x)
    (y := segmentCenteredEvenMoment w φ (fun s => φ s u) tail pre k x)
    (z := subgaussianMomentConstant k*(∑ i, ∑ j, (v i j)^2)^(k+1))
    ht hC (2*k+1) (by simpa only [inv_inv,mul_assoc] using hh)
  simpa only [show 2*k+1+1 = 2*k+2 by omega] using hhalf

 
def hierarchyClocks : (steps : List (GaussianStep ι)) → Fin steps.length → ι → ℝ≥0
  | [] => fun i => Fin.elim0 i
  | (_,q)::rest => Fin.cons q (hierarchyClocks rest)

omit [Fintype ι] in
theorem hierarchyIncrements_eq_scaleDriver (steps : List (GaussianStep ι))
    (i : Fin steps.length) : hierarchyIncrements steps i = scaleDriver (hierarchyClocks steps i) := by
  induction steps with
  | nil => exact Fin.elim0 i
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j

omit [Fintype ι] in
 

theorem alignedClock_direction {q : ι → ℝ≥0} {d : ℝ} (hd : 0 ≤ d)
    (u : ι → ℝ) (hq : ∀ j, u j ≠ 0 → (q j : ℝ) = d) :
    scaleDriver q (fun j => Real.sqrt d * u j) = d • u := by
  ext j
  by_cases hu : u j = 0
  · simp [hu]
  · simp only [scaleDriver_apply,Pi.smul_apply,smul_eq_mul,hq j hu]
    rw [← mul_assoc,Real.mul_self_sqrt hd]

theorem alignedClock_variance {d : ℝ} (hd : 0 ≤ d) (u : ι → ℝ) :
    (∑ j, (Real.sqrt d * u j)^2) = d * ∑ j, (u j)^2 := by
  simp_rw [mul_pow,Real.sq_sqrt hd]
  exact (Finset.mul_sum _ _ _).symm

omit [Fintype ι] in
theorem alignedSegment_direction (pre : List (GaussianStep ι)) (d : Fin pre.length → ℝ)
    (hd : ∀ i, 0 ≤ d i) (u : ι → ℝ)
    (hclock : ∀ i j, u j ≠ 0 → (hierarchyClocks pre i j : ℝ) = d i) :
    ∀ i, hierarchyIncrements pre i (fun j => Real.sqrt (d i)*u j) = d i • u := by
  intro i
  rw [hierarchyIncrements_eq_scaleDriver]
  exact alignedClock_direction (hd i) u (hclock i)

theorem alignedSegment_variance (pre : List (GaussianStep ι)) (d : Fin pre.length → ℝ)
    (hd : ∀ i, 0 ≤ d i) (u : ι → ℝ) :
    (∑ i, ∑ j, (Real.sqrt (d i)*u j)^2) = (∑ i, d i)*(∑ j, (u j)^2) := by
  simp_rw [alignedClock_variance (hd _) u]
  exact (Finset.sum_mul _ _ _).symm

end SKFluctuations.Hierarchy

end

end OAI
