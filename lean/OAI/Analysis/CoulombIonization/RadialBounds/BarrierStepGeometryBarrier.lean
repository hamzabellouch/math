import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.BarrierInitialDeterministicBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialLipschitzBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

def barrierGap (B : ℝ) : ℝ := B/(16*(11/10:ℝ)^5)

lemma barrierGap_pos {B : ℝ} (hB : 0 < B) : 0 < barrierGap B := by
  unfold barrierGap
  positivity

lemma outerBarrier_dyadic_difference (B R : ℝ) {x : TFSpace} (hx : ‖x‖ ≠ 0) :
    outerBarrier B (R/2) x-outerBarrier B R x = B*R/(16*‖x‖^5) := by
  unfold outerBarrier
  field_simp
  ring

lemma outerBarrier_dyadic_gap {B R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    {x : TFSpace} (hx : R ≤ ‖x‖) (hx' : ‖x‖ ≤ (11/10)*R) :
    barrierGap B/R^4 ≤ outerBarrier B (R/2) x-outerBarrier B R x := by
  have hd := hR.trans_le hx
  rw [outerBarrier_dyadic_difference B R hd.ne']
  calc
    barrierGap B/R^4 = B*R/(16*((11/10)*R)^5) := by
      unfold barrierGap
      field_simp
    _ ≤ B*R/(16*‖x‖^5) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx' 5) (by norm_num))

lemma shifted_old_above_new_barrier {B R lam : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hlam : lam < barrierGap B) {u : TFSpace → ℝ} {x : TFSpace}
    (hx : R ≤ ‖x‖) (hx' : ‖x‖ ≤ (11/10)*R)
    (hu : outerBarrier B (R/2) x ≤ u x) :
    outerBarrier B R x < u x-lam/R^4 := by
  have hg := outerBarrier_dyadic_gap hB hR hx hx'
  have hl := div_lt_div_of_pos_right hlam (pow_pos hR 4)
  linarith

lemma cap_dominated_by_shift {C M R lam d : ℝ} (hC : 0 ≤ C) (hM : 0 < M)
    (hR : 0 < R) (hshift : C/M^4 < lam) (hd : M*R < d) : C/d^4 < lam/R^4 := by
  have hMR : 0 < M*R := mul_pos hM hR
  calc
    C/d^4 ≤ C/(M*R)^4 := div_le_div_of_nonneg_left hC (pow_pos hMR 4)
      (pow_le_pow_left₀ hMR.le hd.le 4)
    _ = (C/M^4)/R^4 := by rw [mul_pow,div_mul_eq_div_div]
    _ < lam/R^4 := div_lt_div_of_pos_right hshift (pow_pos hR 4)

def shiftedCandidates (good : Prop) [Decidable good] (a h : TFSpace → ℝ)
    (R lam1 lam2 : ℝ) (x : TFSpace) : ℝ :=
  if good then max (a x-lam1/R^4) (h x-lam2/R^4) else a x-lam1/R^4

def outwardOffset (good : Prop) [Decidable good] (a h : TFSpace → ℝ)
    (Z B R M lam1 lam2 : ℝ) : TFSpace → ℝ :=
  cutMaximum ((26/25)*R) (2*M*R) (shiftedCandidates good a h R lam1 lam2)
    (outerOffset Z B R)

lemma shiftedCandidates_old_le (good : Prop) [Decidable good] (a h : TFSpace → ℝ)
    (R lam1 lam2 : ℝ) (x : TFSpace) :
    a x-lam1/R^4 ≤ shiftedCandidates good a h R lam1 lam2 x := by
  unfold shiftedCandidates
  split_ifs
  · exact le_max_left _ _
  · exact le_refl _

lemma shiftedCandidates_continuous (good : Prop) [Decidable good]
    {a h : TFSpace → ℝ} (ha : Continuous a) (hh : Continuous h) (R lam1 lam2 : ℝ) :
    Continuous (shiftedCandidates good a h R lam1 lam2) := by
  unfold shiftedCandidates
  split_ifs
  · exact (ha.sub continuous_const).max (hh.sub continuous_const)
  · exact ha.sub continuous_const

lemma outward_lower_overlap (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    {Z B R lam1 lam2 : ℝ} (hB : 0 ≤ B) (hR : 0 < R) (hshift : lam1 < barrierGap B)
    (hu : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    {x : TFSpace} (hx : R ≤ ‖x‖) (hx' : ‖x‖ < (27/25)*R) :
    outerOffset Z B R x ≤ shiftedCandidates good a h R lam1 lam2 x := by
  have hgap := shifted_old_above_new_barrier (u := fun y => nuclearField Z y+a y) hB hR hshift hx (by linarith)
    (hu x (by linarith : R/2 ≤ ‖x‖))
  rw [←nuclear_outerOffset_eq (Z := Z) hx] at hgap
  have hc := shiftedCandidates_old_le good a h R lam1 lam2 x
  linarith

lemma outward_upper_overlap (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    {Z B C R M lam1 lam2 : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hR : 0 < R) (hM : 2 < M) (hshifts : lam2 ≤ lam1) (hshift : C/M^4 < lam2)
    (hu : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hh : good → ∀ x, M*R < ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : M*R < ‖x‖) (hx' : ‖x‖ < 2*M*R) :
    shiftedCandidates good a h R lam1 lam2 x ≤ outerOffset Z B R x := by
  have hxR : R ≤ ‖x‖ := by nlinarith
  have hs := cap_dominated_by_shift hC (by linarith : 0 < M) hR hshift hx
  have hb := (outerBarrier_bounds hB hR hxR).1
  have hb0 : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
  rw [←nuclear_outerOffset_eq (Z := Z) hxR] at hb
  have ha := hu x (by linarith)
  have hl := div_le_div_of_nonneg_right hshifts (pow_nonneg hR.le 4)
  unfold shiftedCandidates
  split_ifs with hg
  · apply max_le
    · linarith
    · have hh' := hh hg x hx hx'; linarith
  · linarith

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma DeterministicLocalLipschitz.ite {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v)
    (q : Ω → Prop) [DecidablePred q] :
    DeterministicLocalLipschitz (fun sample x => if q sample then u sample x else v sample x) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Max.max Ku Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  by_cases hq : q sample
  · simpa only [ite_eq_left hq] using ((hLu sample).mono inter_subset_left).weaken (le_max_left _ _)
  · simpa only [ite_eq_right hq] using ((hLv sample).mono inter_subset_right).weaken (le_max_right _ _)

lemma DeterministicLocalBound.ite {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v)
    (q : Ω → Prop) [DecidablePred q] :
    DeterministicLocalBound (fun sample x => if q sample then u sample x else v sample x) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨max C D,fun sample x hx => ?_⟩
  dsimp only
  split_ifs
  · exact (hC sample x hx).trans (le_max_left _ _)
  · exact (hD sample x hx).trans (le_max_right _ _)

lemma DeterministicLocalBound.max {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) :
    DeterministicLocalBound (fun sample x => max (u sample x) (v sample x)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨Max.max C D,fun sample x hx => ?_⟩
  rcases le_total (u sample x) (v sample x) with h|h
  · simpa only [max_eq_right h] using (hD sample x hx).trans (le_max_right C D)
  · simpa only [max_eq_left h] using (hC sample x hx).trans (le_max_left C D)

lemma shiftedCandidates_deterministicLip {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalLipschitz a)
    (hh : DeterministicLocalLipschitz h) (R lam1 lam2 : ℝ) :
    DeterministicLocalLipschitz (fun sample => shiftedCandidates (good sample) (a sample) (h sample) R lam1 lam2) := by
  have h1 := ha.sub (deterministicLip_spatial (LocallyLipschitz.const (lam1/R^4)))
  have h2 := hh.sub (deterministicLip_spatial (LocallyLipschitz.const (lam2/R^4)))
  exact (h1.max h2).ite h1 good

lemma shiftedCandidates_deterministicBound {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalBound a)
    (hh : DeterministicLocalBound h) (R lam1 lam2 : ℝ) :
    DeterministicLocalBound (fun sample => shiftedCandidates (good sample) (a sample) (h sample) R lam1 lam2) := by
  have h1 : DeterministicLocalBound (fun sample x => a sample x-lam1/R^4) := by
    simpa only [sub_eq_add_neg] using
      ha.add (continuous_deterministicBound (u := fun _ => -(lam1/R^4)) continuous_const)
  have h2 : DeterministicLocalBound (fun sample x => h sample x-lam2/R^4) := by
    simpa only [sub_eq_add_neg] using
      hh.add (continuous_deterministicBound (u := fun _ => -(lam2/R^4)) continuous_const)
  exact (h1.max h2).ite h1 good

lemma shiftedCandidates_measurable {Ω : Type*} [MeasurableSpace Ω]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {a h : Ω → TFSpace → ℝ} (ha : Measurable (Function.uncurry a))
    (hh : Measurable (Function.uncurry h)) (R lam1 lam2 : ℝ) :
    Measurable (fun z : Ω × TFSpace => shiftedCandidates (good z.1) (a z.1) (h z.1) R lam1 lam2 z.2) :=
  Measurable.ite (measurable_fst hg) ((ha.sub measurable_const).max (hh.sub measurable_const))
    (ha.sub measurable_const)

lemma outwardOffset_measurable {Ω : Type*} [MeasurableSpace Ω]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {a h : Ω → TFSpace → ℝ} (ha : Measurable (Function.uncurry a))
    (hh : Measurable (Function.uncurry h)) (Z B M lam1 lam2 : ℝ) {R : ℝ} (hR : 0 < R) :
    Measurable (fun z : Ω × TFSpace => outwardOffset (good z.1) (a z.1) (h z.1) Z B R M lam1 lam2 z.2) := by
  have hc := shiftedCandidates_measurable good hg ha hh R lam1 lam2
  have hb : Measurable (fun z : Ω × TFSpace => outerOffset Z B R z.2) :=
    (outerOffset_continuous Z B hR).measurable.comp measurable_snd
  exact Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)
    hc (Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)
      (hc.max hb) hb)

lemma outwardOffset_deterministicBound {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalBound a)
    (hh : DeterministicLocalBound h) (Z B M lam1 lam2 : ℝ) {R : ℝ} (hR : 0 < R) :
    DeterministicLocalBound (fun sample => outwardOffset (good sample) (a sample) (h sample) Z B R M lam1 lam2) :=
  cutMaximum_deterministicBound (shiftedCandidates_deterministicBound good ha hh R lam1 lam2)
    (continuous_deterministicBound (outerOffset_continuous Z B hR)) _ _

end CoulombBarrier

end

end OAI
