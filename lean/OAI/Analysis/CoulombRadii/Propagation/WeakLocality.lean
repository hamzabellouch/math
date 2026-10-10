import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.WeakReactionMax

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Manifold
namespace NeutralAtom

lemma coordinateLaplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Position → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : Position) :
    coordinateLaplacian (fun y => ∑ i ∈ s, f i y) x=∑ i ∈ s, coordinateLaplacian (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordinateLaplacian]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [coordinateLaplacian_add_at ((hf i).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt
      ((ContDiff.sum (s:=s) (fun j _ => hf j)).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt,ih]

theorem WeakLaplacianGE.of_local {f q : Position → ℝ} {U : Set Position}
    (hf : LocallyIntegrable f volume) (hq : LocallyIntegrable q volume)
    (hlocal : ∀ x ∈ U, ∃ V : Set Position, x ∈ V ∧ IsOpen V ∧ WeakLaplacianGE f V q) :
    WeakLaplacianGE f U q := by
  classical
  intro φ hφ hc ht hp
  choose V hmem hopen hweak using (fun x : tsupport φ => hlocal x.val (ht x.property))
  have hcover : tsupport φ ⊆ ⋃ x : tsupport φ, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩
  obtain ⟨s,hs⟩ := hc.elim_finite_subcover V hopen hcover
  let W : s → Set Position := fun i => V i.val
  have hW : tsupport φ ⊆ ⋃ i : s, W i := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨P,hP⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I:=𝓘(ℝ,Position))
    (isClosed_tsupport φ) W (fun i => hopen i.val) hW
  let ψ : s → Position → ℝ := fun i x => P i x*φ x
  have hψc (i : s) : ContDiff ℝ ∞ (ψ i) := by
    exact (contMDiff_iff_contDiff.mp (P i).contMDiff).mul hφ
  have hψs (i : s) : HasCompactSupport (ψ i) := hc.mul_left
  have hψt (i : s) : tsupport (ψ i) ⊆ W i :=
    (tsupport_mul_subset_left).trans (hP i)
  have hsum : (fun x => ∑ i : s, ψ i x)=φ := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have H := P.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at H
      simp only [ψ,←Finset.sum_mul,H,one_mul]
    · simp [ψ,image_eq_zero_of_notMem_tsupport hx]
  have hiq (i : s) : Integrable (fun x => q x*ψ i x) := by
    simpa only [smul_eq_mul] using hq.integrable_smul_right_of_hasCompactSupport
      (hψc i).continuous (hψs i)
  have hif (i : s) : Integrable (fun x => f x*coordinateLaplacian (ψ i) x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport
      (contDiff_coordinateLaplacian (hψc i)).continuous (hasCompactSupport_coordinateLaplacian (hψs i))
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    hweak i.val (ψ i) (hψc i) (hψs i) (hψt i)
      (fun x => mul_nonneg (P.nonneg i x) (hp x)))
  rw [←integral_finsetSum _ (fun i _ => hiq i),←integral_finsetSum _ (fun i _ => hif i)] at H
  have hsume x : (∑ i : s, ψ i x)=φ x := congrFun hsum x
  simpa only [←Finset.mul_sum,←coordinateLaplacian_finset_sum Finset.univ ψ hψc,hsum,hsume] using H

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma locallyIntegrable_of_ball_bounds {q : Position → ℝ} (hm : Measurable q)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |q x| ≤ C) :
    LocallyIntegrable q volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:Position)
  obtain ⟨C,hC⟩ := hb R
  have hfin : volume K < ⊤ := hK.measure_lt_top
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hfin⟩
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simpa only [Real.norm_eq_abs] using hC x (hR hx)

lemma cutoffReaction_offset_locallyIntegrable {a Z : ℝ} (ha : 0<a)
    {f : Position → ℝ} (hf : Continuous f) :
    LocallyIntegrable (cutoffReaction a (fun x => Z*coulombKernel x+f x)) volume := by
  apply locallyIntegrable_of_ball_bounds
  · exact (tfReaction_continuous.measurable.comp ((measurable_const.mul
      measurable_coulombKernel).add hf.measurable)).indicator
      (isClosed_le continuous_const continuous_norm).measurableSet
  · exact cutoffReaction_offset_ball_bound ha hf

lemma WeakLaplacianGE.mono_source_on {f q r : Position → ℝ} {U : Set Position}
    (hw : WeakLaplacianGE f U q) (hq : LocallyIntegrable q volume)
    (hr : LocallyIntegrable r volume) (hle : ∀ᵐ x, x ∈ U → r x≤q x) :
    WeakLaplacianGE f U r := by
  intro φ hφ hc ht hp
  apply le_trans _ (hw φ hφ hc ht hp)
  have hi (g : Position → ℝ) (hg : LocallyIntegrable g volume) :
      Integrable (fun x => g x*φ x) := by
    simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  apply integral_mono_ae (hi r hr) (hi q hq)
  filter_upwards [hle] with x hx
  by_cases h : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hx (ht h)) (hp x)
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem WeakNuclearSubsolution.max_cutoffTF {f g b : Position → ℝ} {a Z : ℝ}
    {U : Set Position} (ha : 0<a) (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hb : Measurable b)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x| ≤ C)
    (hwf : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+f y) x))
    (hwg : WeakNuclearSubsolution (fun x => Z*coulombKernel x+g x) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+g y) x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+max (f x) (g x)) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+max (f y) (g y)) x) := by
  have hbi := locallyIntegrable_of_ball_bounds hb hbb
  apply WeakNuclearSubsolution.max_reaction (F := fun x t => if a≤‖x‖ then tfReaction t else 0)
    hU hf hg
  · exact hbi.add (cutoffReaction_offset_locallyIntegrable ha hf)
  · exact hbi.add (cutoffReaction_offset_locallyIntegrable ha hg)
  · intro R
    obtain ⟨C,hC⟩ := hbb R
    obtain ⟨D,hD⟩ := cutoffReaction_offset_ball_bound (Z:=Z) ha hf R
    exact ⟨C+D,fun x hx => (abs_add_le _ _).trans (add_le_add (hC x hx) (hD x hx))⟩
  · intro R
    obtain ⟨C,hC⟩ := hbb R
    obtain ⟨D,hD⟩ := cutoffReaction_offset_ball_bound (Z:=Z) ha hg R
    exact ⟨C+D,fun x hx => (abs_add_le _ _).trans (add_le_add (hC x hx) (hD x hx))⟩
  · exact hwf
  · exact hwg

theorem WeakNuclearSubsolution.finset_max_cutoffTF {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Position → ℝ) {b : Position → ℝ}
    {a Z : ℝ} {U : Set Position} (ha : 0<a) (hU : IsOpen U)
    (hf : ∀ i∈s, Continuous (f i)) (hb : Measurable b)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x| ≤ C)
    (hw : ∀ i∈s, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f i x) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+f i y) x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+s.sup' hs (fun i => f i x)) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+s.sup' hs (fun i => f i y)) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    by_cases hne : s.Nonempty
    · have hf' : ∀ j∈s, Continuous (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have h := WeakNuclearSubsolution.max_cutoffTF ha hU (hf i (Finset.mem_insert_self _ _))
        (Continuous.finset_sup'_apply hne hf') hb hbb
        (hw i (Finset.mem_insert_self _ _))
        (ih hne hf' (fun j hj => hw j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sup'_insert hne] using h
    · have he := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      simpa using hw i (Finset.mem_insert_self _ _)

end NeutralAtom

end

end OAI
