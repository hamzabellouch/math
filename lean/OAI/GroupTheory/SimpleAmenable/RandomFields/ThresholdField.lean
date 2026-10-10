import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FieldHS

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ThresholdField
open Classical MeasureTheory Set

noncomputable def thresholdField {ι : Type*} (x : ι → ℝ) : ι → Bool :=
  fun z => if 0<x z then true else false

theorem thresholdField_measurable {ι : Type*} : Measurable (@thresholdField ι) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply z))
    measurable_const measurable_const

theorem thresholdField_reindex {ι : Type*} (e : ι ≃ ι) (x : ι → ℝ) :
    thresholdField (fieldReindex e x)=(fun z => thresholdField x (e.symm z)) := rfl

def signalSuccess {ι : Type*} (a : ι → ℝ) (b : ι → Bool) : Prop :=
  ∀z,(2≤a z → b z=true) ∧ (a z≤-2 → b z=false)

theorem signalSuccess_measurable {ι : Type*} [Countable ι] (a : ι → ℝ) :
    MeasurableSet {b : ι → Bool | signalSuccess a b} := by
  unfold signalSuccess
  measurability

theorem signalSuccess_of_noise {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (B : Matrix ι ι ℝ) (x : ι → ℝ) (hx : ∀z,x z∈Icc (-1:ℝ) 1)
    (hB : ∀z,|∑w∈J,B z w*x w|<1/2) :
    signalSuccess a (thresholdField (finiteCoefficientField J a B x)) := by
  intro z
  have hn := abs_lt.mp (hB z)
  have hxz := hx z
  rcases hxz with ⟨hxlo,hxhi⟩
  constructor
  · intro ha
    have hh : 0<finiteCoefficientField J a B x z := by
      unfold finiteCoefficientField
      linarith
    simp only [thresholdField,ite_eq_left hh]
  · intro ha
    have hh : ¬0<finiteCoefficientField J a B x z := by
      unfold finiteCoefficientField
      linarith
    simp only [thresholdField,ite_eq_right hh]

end ThresholdField

section SourceFieldClose
open Classical Matrix MeasureTheory

theorem sourceSmoothFieldLaw_close {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L ρ η κ : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (q : ℝ) (hθc : ∀x,L≤‖x‖ → θ x=q)
    (hρ : 0<ρ) (hκ : 0<κ) (n : ℕ) :
    let T := sourceCommonSites (v:=v) hD g hL n
    let B : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n z.val w.val)
    let C : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n
      (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val))
    ObservableClose (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n)
      ((sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map (fieldReindex (flagSitePermutation hD g)))
      (smoothNoiseTransportError B C (fun z : T => flagSignalDifference hD g θ (sourceDyadicN n) z.val)) := by
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos (sourceDyadicN_pos n) hL)
  let T := sourceCommonSites (v:=v) hD g hL n
  let e := flagSitePermutation (v:=v) hD g
  have hout (z : FlagSite a m D v) (hz : z∉T) : z∉J :=
    fun hh => hz (Finset.mem_union_left _ hh)
  have hinv (z : FlagSite a m D v) (hz : z∉T) : e.symm z∉J := by
    intro hh
    apply hz
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.symm z,hh,e.apply_symm_apply z⟩)
  have hmean (z : FlagSite a m D v) (hz : z∉J) : flagMeanSignal θ (sourceDyadicN n) z=q :=
    flagMeanSignal_outside θ (sourceDyadicN_pos n) hθc z (by simpa only [J,mem_flagBoxFinset] using hz)
  have hrow (z : FlagSite a m D v) (hz : z∉J) (w : FlagSite a m D v) :
      sourceFlagMatrix χ ρ η κ n z w=0 :=
    sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n z w (Or.inl hz)
  have hpsd := sourceFlagMatrix_posSemidef (a:=a) (m:=m) (D:=D) (v:=v) (η:=η) χ hρ hκ n
  rw [sourceSmoothFieldLaw_transported hD g θ χ hL hχc,
    sourceSmoothFieldLaw_as_common hD g θ χ hL hχc]
  convert! finiteCoefficientField_close T (flagMeanSignal θ (sourceDyadicN n))
    (fun z => flagMeanSignal θ (sourceDyadicN n) (e.symm z))
    (Matrix.of (sourceFlagMatrix χ ρ η κ n))
    ((Matrix.of (sourceFlagMatrix χ ρ η κ n)).submatrix e.symm e.symm) q
    (fun z hz => hmean z (hout z hz))
    (fun z hz => hmean (e.symm z) (hinv z hz))
    (fun z hz w => hrow z (hout z hz) w)
    (fun z hz w => hrow (e.symm z) (hinv z hz) (e.symm w))
    hpsd (hpsd.submatrix e.symm) using 1

end SourceFieldClose

section SourceBitField
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def sourceBitFieldLaw {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    Measure (FlagSite a m D v → Bool) :=
  (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map thresholdField

instance sourceBitFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceBitFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceBitFieldLaw
  infer_instance

theorem sourceBitFieldLaw_success {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Icc (0:ℝ) 1)
    {L ρ η κ : ℝ} (hL : 0<L) (hχc : ∀x,L≤‖x‖ → χ x=0)
    (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ) :
    Tendsto (fun n => (sourceBitFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n).real
      {b | ¬signalSuccess (flagMeanSignal θ (sourceDyadicN n)) b}) atTop (nhds 0) := by
  let μ := independentSmoothNoiseLaw (FlagSite a m D v)
  have ht := sourceFlagMatrix_concentration (v:=v) hD χ hχ hL hχc hρ hη hκ
    (show (0:ℝ)<1/2 by norm_num) μ (fun i x => x i)
    (independentSmoothNoiseLaw_independent _) (fun i => (measurable_pi_apply i).aemeasurable)
    (independentSmoothNoiseLaw_bounded _) (independentSmoothNoiseLaw_centered _)
  apply squeeze_zero (fun n => measureReal_nonneg) _ ht
  intro n
  unfold sourceBitFieldLaw sourceSmoothFieldLaw
  have hs : MeasurableSet {b : FlagSite a m D v → Bool | ¬signalSuccess (flagMeanSignal θ (sourceDyadicN n)) b} :=
    (signalSuccess_measurable _).compl
  rw [map_measureReal_apply thresholdField_measurable hs,
    map_measureReal_apply (finiteCoefficientField_measurable _ _ _)
      (thresholdField_measurable hs)]
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  have hb : ∀ᵐx ∂μ,∀z,x z∈Icc (-1:ℝ) 1 := ae_all_iff.mpr (independentSmoothNoiseLaw_bounded _)
  filter_upwards [hb] with x hx
  intro hbad
  by_contra hnone
  apply hbad
  apply signalSuccess_of_noise _ _ _ _ hx
  intro z
  have hh : ¬(1/2:ℝ)≤|∑y∈sourceActiveSites (v:=v) hD hL n,sourceFlagMatrix χ ρ η κ n z y*x y| :=
    fun hz => hnone ⟨z,hz⟩
  exact lt_of_not_ge hh

noncomputable def extendFiniteBits {ι : Type*} (J : Finset ι) (b : J → Bool) : ι → Bool :=
  fun z => if hz : z∈J then b ⟨z,hz⟩ else false

theorem finiteBitWindow_finite {ι : Type*} (J : Finset ι) :
    Set.Finite {b : ι → Bool | ∀z,z∉J → b z=false} := by
  apply (Set.finite_range (extendFiniteBits J)).subset
  intro b hb
  refine ⟨fun z => b z.val,?_⟩
  funext z
  by_cases hz : z∈J
  · simp only [extendFiniteBits,dite_eq_left hz]
  · simp only [extendFiniteBits,dite_eq_right hz,hb z hz]

theorem sourceBitFieldLaw_finite_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (hθc : ∀x,L≤‖x‖ → θ x=-3)
    (ρ η κ : ℝ) (n : ℕ) :
    ∃S : Finset (FlagSite a m D v → Bool),
      ∀ᵐb ∂sourceBitFieldLaw (v:=v) hD θ χ hL ρ η κ n,b∈S := by
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos (sourceDyadicN_pos n) hL)
  refine ⟨(finiteBitWindow_finite J).toFinset,?_⟩
  have hw : MeasurableSet {b : FlagSite a m D v → Bool | ∀z,z∉J → b z=false} := by measurability
  simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  unfold sourceBitFieldLaw sourceSmoothFieldLaw
  rw [ae_map_iff thresholdField_measurable.aemeasurable hw]
  have hw' : MeasurableSet {x : FlagSite a m D v → ℝ | ∀z,z∉J → thresholdField x z=false} :=
    thresholdField_measurable hw
  rw [ae_map_iff (finiteCoefficientField_measurable _ _ _).aemeasurable hw']
  have hb : ∀ᵐx ∂independentSmoothNoiseLaw (FlagSite a m D v),∀z,x z∈Icc (-1:ℝ) 1 :=
    ae_all_iff.mpr (independentSmoothNoiseLaw_bounded _)
  filter_upwards [hb] with x hx
  intro z hz
  have ha : flagMeanSignal θ (sourceDyadicN n) z=-3 :=
    flagMeanSignal_outside θ (sourceDyadicN_pos n) hθc z (by simpa only [J,mem_flagBoxFinset] using hz)
  have hB (w : FlagSite a m D v) := sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n z w (Or.inl hz)
  have hh : ¬0<finiteCoefficientField J (flagMeanSignal θ (sourceDyadicN n))
      (Matrix.of (sourceFlagMatrix χ ρ η κ n)) x z := by
    simp only [finiteCoefficientField,ha,Matrix.of_apply,hB,zero_mul,Finset.sum_const_zero,add_zero]
    linarith [(hx z).2]
  exact ite_eq_right hh

end SourceBitField

end SimpleAmenable
end
end

end OAI
