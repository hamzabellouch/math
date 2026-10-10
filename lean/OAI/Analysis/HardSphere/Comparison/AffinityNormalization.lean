import Mathlib
import OAI.Analysis.HardSphere.Comparison.Affinity

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {α : Type*} [MeasurableSpace α]
lemma measureAffinity_eq_dominated (P Q ξ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure ξ]
    (hP : P≪ξ) (hQ : Q≪ξ) :
    measureAffinity P Q=affinity ξ (fun x ↦ (P.rnDeriv ξ x).toReal)
      (fun x ↦ (Q.rnDeriv ξ x).toReal) := by
  have hsum : P+Q≪ξ := by
    intro s hs
    simp only [Measure.add_apply,hP hs,hQ hs,add_zero]
  have hp : P≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  unfold measureAffinity affinity
  rw [←integral_toReal_rnDeriv_mul hsum]
  apply integral_congr_ae
  filter_upwards [real_rnDeriv_chain (ξ:=ξ) hp,real_rnDeriv_chain (ξ:=ξ) hq] with x hx hy
  rw [←hx,←hy,Real.sqrt_mul ENNReal.toReal_nonneg,Real.sqrt_mul ENNReal.toReal_nonneg]
  have hsq := Real.sq_sqrt (show 0≤((P+Q).rnDeriv ξ x).toReal from ENNReal.toReal_nonneg)
  nth_rw 1 [←hsq]
  ring

lemma affinity_finset_sum {ι : Type*} (s : Finset ι) (μ : Measure α)
    (p q : ι→α→ℝ) (hp : ∀i∈s,Integrable (p i) μ) (hq : ∀i∈s,Integrable (q i) μ)
    (hp0 : ∀i x,0≤p i x) (hq0 : ∀i x,0≤q i x) :
    (∑i∈s,affinity μ (p i) (q i))≤
      affinity μ (fun x ↦ ∑i∈s,p i x) (fun x ↦ ∑i∈s,q i x) := by
  unfold affinity
  rw [←integral_finsetSum s (fun i hi ↦ affinity_integrable (hp i hi) (hq i hi)
    (Eventually.of_forall (hp0 i)) (Eventually.of_forall (hq0 i)))]
  apply integral_mono
  · exact integrable_finsetSum _ (fun i hi ↦ affinity_integrable (hp i hi) (hq i hi)
      (Eventually.of_forall (hp0 i)) (Eventually.of_forall (hq0 i)))
  · exact affinity_integrable (integrable_finsetSum _ hp) (integrable_finsetSum _ hq)
      (Eventually.of_forall (fun x ↦ Finset.sum_nonneg (fun i _ ↦ hp0 i x)))
      (Eventually.of_forall (fun x ↦ Finset.sum_nonneg (fun i _ ↦ hq0 i x)))
  · intro x
    exact Real.sum_sqrt_mul_sqrt_le s (fun i ↦ hp0 i x) (fun i ↦ hq0 i x)

lemma rnDeriv_real_mono (P Q ξ : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    [IsFiniteMeasure ξ] (h : P≤Q) :
    (fun x ↦ (P.rnDeriv ξ x).toReal)≤ᵐ[ξ](fun x ↦ (Q.rnDeriv ξ x).toReal) := by
  have he := Measure.sub_add_cancel_of_le h
  have hh := Measure.rnDeriv_add (Q-P) P ξ
  rw [he] at hh
  filter_upwards [hh,Measure.rnDeriv_lt_top P ξ,Measure.rnDeriv_lt_top (Q-P) ξ] with x hx hp hq
  rw [hx,Pi.add_apply,ENNReal.toReal_add hq.ne hp.ne]
  exact le_add_of_nonneg_left ENNReal.toReal_nonneg

lemma measureAffinity_mono (P Q P' Q' : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure P'] [IsFiniteMeasure Q']
    (hP : P≤P') (hQ : Q≤Q') : measureAffinity P Q ≤ measureAffinity P' Q' := by
  have hP' : P'≪P'+Q' := Measure.AbsolutelyContinuous.rfl.add_right Q'
  have hQ' : Q'≪P'+Q' := Measure.AbsolutelyContinuous.rfl.add_right' P'
  have hp := (Measure.absolutelyContinuous_of_le hP).trans hP'
  have hq := (Measure.absolutelyContinuous_of_le hQ).trans hQ'
  rw [measureAffinity_eq_dominated P Q (P'+Q') hp hq]
  unfold measureAffinity affinity
  apply integral_mono_ae
  · exact affinity_integrable Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
  · exact affinity_integrable Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
  · filter_upwards [rnDeriv_real_mono P P' (P'+Q') hP,rnDeriv_real_mono Q Q' (P'+Q') hQ] with x hx hy
    exact mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma rnDeriv_real_finset_sum {ι : Type*} (s : Finset ι) (P : ι→Measure α)
    (ξ : Measure α) [∀i,IsFiniteMeasure (P i)] [IsFiniteMeasure ξ] :
    (fun x ↦ ((∑i∈s,P i).rnDeriv ξ x).toReal)=ᵐ[ξ]
      (fun x ↦ ∑i∈s,((P i).rnDeriv ξ x).toReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Measure.rnDeriv_zero ξ] with x hx
    simp [hx]
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Measure.rnDeriv_add (P i) (∑j∈s,P j) ξ,hs,
      Measure.rnDeriv_lt_top (P i) ξ,Measure.rnDeriv_lt_top (∑j∈s,P j) ξ] with x hx hy ha hb
    rw [hx,Pi.add_apply,ENNReal.toReal_add ha.ne hb.ne,hy]

lemma measureAffinity_finset_sum {ι : Type*} (s : Finset ι) (P Q : ι→Measure α)
    [∀i,IsFiniteMeasure (P i)] [∀i,IsFiniteMeasure (Q i)] :
    (∑i∈s,measureAffinity (P i) (Q i)) ≤ measureAffinity (∑i∈s,P i) (∑i∈s,Q i) := by
  let ξ := (∑i∈s,P i)+(∑i∈s,Q i)
  have hsP : (∑i∈s,P i)≪ξ := Measure.AbsolutelyContinuous.rfl.add_right _
  have hsQ : (∑i∈s,Q i)≪ξ := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hp : ∀i∈s,P i≪ξ := fun i hi ↦
    (Measure.absolutelyContinuous_of_le (Finset.single_le_sum (fun _ _ ↦ bot_le) hi)).trans hsP
  have hq : ∀i∈s,Q i≪ξ := fun i hi ↦
    (Measure.absolutelyContinuous_of_le (Finset.single_le_sum (fun _ _ ↦ bot_le) hi)).trans hsQ
  calc
    _ = ∑i∈s,affinity ξ (fun x ↦ ((P i).rnDeriv ξ x).toReal)
        (fun x ↦ ((Q i).rnDeriv ξ x).toReal) := Finset.sum_congr rfl
      (fun i hi ↦ measureAffinity_eq_dominated _ _ _ (hp i hi) (hq i hi))
    _ ≤ affinity ξ (fun x ↦ ∑i∈s,((P i).rnDeriv ξ x).toReal)
        (fun x ↦ ∑i∈s,((Q i).rnDeriv ξ x).toReal) :=
      affinity_finset_sum s ξ _ _ (fun _ _ ↦ Measure.integrable_toReal_rnDeriv)
        (fun _ _ ↦ Measure.integrable_toReal_rnDeriv)
        (fun _ _ ↦ ENNReal.toReal_nonneg) (fun _ _ ↦ ENNReal.toReal_nonneg)
    _ = _ := by
      rw [measureAffinity_eq_dominated _ _ ξ hsP hsQ]
      unfold affinity
      apply integral_congr_ae
      filter_upwards [rnDeriv_real_finset_sum s P ξ,rnDeriv_real_finset_sum s Q ξ] with x hx hy
      rw [hx,hy]

lemma measureAffinity_smul (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (c : ℝ) (hc : 0≤c) :
    measureAffinity (ENNReal.ofReal c • P) (ENNReal.ofReal c • Q)=c*measureAffinity P Q := by
  let := P.smul_finite (c:=ENNReal.ofReal c) ENNReal.ofReal_ne_top
  let := Q.smul_finite (c:=ENNReal.ofReal c) ENNReal.ofReal_ne_top
  have hp : P≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [measureAffinity_eq_dominated _ _ (P+Q) (hp.smul_left _) (hq.smul_left _)]
  unfold measureAffinity affinity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_smul_left_of_ne_top P (P+Q) ENNReal.ofReal_ne_top,
    Measure.rnDeriv_smul_left_of_ne_top Q (P+Q) ENNReal.ofReal_ne_top] with x hx hy
  rw [hx,hy,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,
    Real.sqrt_mul hc,Real.sqrt_mul hc]
  have hs := Real.sq_sqrt hc
  calc
    _ = (Real.sqrt c)^2*(Real.sqrt ((P.rnDeriv (P+Q) x).toReal)*
        Real.sqrt ((Q.rnDeriv (P+Q) x).toReal)) := by ring
    _ = _ := by rw [hs]

lemma affinity_tag_normalization {ι : Type*} (s : Finset ι)
    (P Q : Measure α) (Pg Qg : ι→Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [∀i,IsFiniteMeasure (Pg i)]
    [∀i,IsFiniteMeasure (Qg i)] (D : ℝ) (hD : 0<D)
    (hp : ∑i∈s,Pg i ≤ ENNReal.ofReal D • P)
    (hq : ∑i∈s,Qg i ≤ ENNReal.ofReal D • Q) :
    D⁻¹*(∑i∈s,measureAffinity (Pg i) (Qg i)) ≤ measureAffinity P Q := by
  let := P.smul_finite (c:=ENNReal.ofReal D) ENNReal.ofReal_ne_top
  let := Q.smul_finite (c:=ENNReal.ofReal D) ENNReal.ofReal_ne_top
  have h := (measureAffinity_finset_sum s Pg Qg).trans (measureAffinity_mono _ _ _ _ hp hq)
  rw [measureAffinity_smul P Q D hD.le] at h
  exact (inv_mul_le_iff₀ hD).2 h

end HardSphere.Comparison

end

end OAI
