import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfMaximal
import OAI.NumberTheory.PrimePackets.InverseEntropy

namespace OAI

/-! # Uniform control of visits to decreasing exceptional sets

The finite Hopf inequality bounds the probability of ever having an
excessive occupation average. Applied to decreasing null-intersection
sets, it gives almost-sure uniform control over every time interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma visitCount_mono {Y : Type*} (T : Y → Y) {A B : Set Y}
    (hAB : A ⊆ B) (n : ℕ) (x : Y) : visitCount T A n x ≤ visitCount T B n x := by
  classical
  unfold visitCount
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,hAB (Finset.mem_filter.mp hj).2⟩

def excessiveOccupation {Y : Type*} (T : Y → Y) (A : Set Y) (δ : ℝ) : Set Y :=
  {x | ∃ n : ℕ, δ*n < (visitCount T A n x : ℝ)}

lemma excessiveOccupation_mono {Y : Type*} (T : Y → Y) (δ : ℝ)
    {A B : Set Y} (hAB : A ⊆ B) : excessiveOccupation T A δ ⊆ excessiveOccupation T B δ := by
  classical
  rintro x ⟨n,hn⟩
  refine ⟨n,hn.trans_le ?_⟩
  exact_mod_cast Finset.card_le_card (show
    (Finset.range n).filter (fun j => T^[j] x ∈ A) ⊆
      (Finset.range n).filter (fun j => T^[j] x ∈ B) from by
        intro j hj
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,hAB (Finset.mem_filter.mp hj).2⟩)

lemma measurableSet_excessiveOccupation {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {A : Set Y} (hA : MeasurableSet A) (δ : ℝ) :
    MeasurableSet (excessiveOccupation T A δ) := by
  have he : excessiveOccupation T A δ =
      ⋃ n : ℕ, {x | δ*n < (visitCount T A n x : ℝ)} := by ext x; simp [excessiveOccupation]
  rw [he]
  exact MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (measurable_visitCount hT hA n)

theorem excessiveOccupation_measure_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {A : Set Y} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal δ * μ (excessiveOccupation T A δ) ≤ μ A := by
  let u : Y → ℝ := A.indicator (fun _ => 1)
  let f : Y → ℝ := fun x => u x-δ
  have hui : Integrable u μ := (integrable_const (1:ℝ)).indicator hA
  have hum : Measurable u := measurable_const.indicator hA
  have hfi : Integrable f μ := hui.sub (integrable_const δ)
  have hfm : Measurable f := hum.sub measurable_const
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hEm n : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfm n)
  have hmono : Monotone E := fun i j hij x hx =>
    hx.trans_le (positiveRunningSum_mono T f x hij)
  have hEn n : ENNReal.ofReal δ * μ (E n) ≤ μ A := by
    have h0 := finite_hopf_maximal hT hfi hfm n
    change 0 ≤ ∫ x in E n, u x-δ ∂μ at h0
    rw [integral_sub hui.integrableOn (integrable_const δ),setIntegral_const,smul_eq_mul] at h0
    have hle : (∫ x in E n, u x ∂μ) ≤ μ.real A := by
      rw [←integral_indicator_one hA]
      exact setIntegral_le_integral hui (ae_of_all _ fun x => by
        by_cases hx : x ∈ A <;> simp [u,hx])
    have hb : δ*μ.real (E n) ≤ μ.real A := by linarith
    have H := ENNReal.ofReal_le_ofReal hb
    simpa only [ENNReal.ofReal_mul hδ.le,measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ (E n)),ENNReal.ofReal_toReal (measure_ne_top μ A)] using H
  have hsub : excessiveOccupation T A δ ⊆ ⋃ n, E n := by
    rintro x ⟨n,hn⟩
    apply mem_iUnion.mpr
    refine ⟨n,lt_of_lt_of_le ?_ (birkhoffSum_le_positiveRunningSum T f n x)⟩
    change 0 < ∑ j ∈ Finset.range n, (u (T^[j] x)-δ)
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hv := visitCount_cast T A n x
    change (visitCount T A n x : ℝ) = ∑ j ∈ Finset.range n, u (T^[j] x) at hv
    linarith
  calc
    _ ≤ ENNReal.ofReal δ * μ (⋃ n, E n) := mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ μ A := by
      rw [hmono.measure_iUnion,ENNReal.mul_iSup]
      exact iSup_le hEn

theorem ae_uniform_small_occupation_of_decreasing {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (A : ℕ → Set Y) (hA : ∀ m, MeasurableSet (A m)) (hmono : Antitone A)
    (hz : μ (⋂ m, A m)=0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ, ∃ m, ∀ n : ℕ, (visitCount T (A m) n x : ℝ) ≤ δ*n := by
  let E : ℕ → Set Y := fun m => excessiveOccupation T (A m) δ
  have hI : ENNReal.ofReal δ * μ (⋂ m, E m) ≤ 0 := by
    have ht := tendsto_measure_iInter_atTop (fun m => (hA m).nullMeasurableSet) hmono
      ⟨0,measure_ne_top μ _⟩
    rw [hz] at ht
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun m => (mul_le_mul' le_rfl (measure_mono (iInter_subset E m))).trans
      (excessiveOccupation_measure_bound μ hT (hA m) hδ)
  have hzero : μ (⋂ m, E m)=0 := by
    exact (mul_eq_zero.mp (le_antisymm hI bot_le)).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  have hgood : ∀ᵐ x ∂μ, x ∉ ⋂ m, E m := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using hzero
  filter_upwards [hgood] with x hx
  obtain ⟨m,hm⟩ := not_forall.mp (fun h => hx (mem_iInter.mpr h))
  refine ⟨m,?_⟩
  intro n
  exact not_lt.mp (fun hn => hm ⟨n,hn⟩)

end DukePrimeDegree

end

end OAI
