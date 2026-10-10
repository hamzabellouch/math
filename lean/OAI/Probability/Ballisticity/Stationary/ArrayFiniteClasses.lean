import Mathlib
import OAI.Probability.Ballisticity.Walk.ArrayGrowthEvent
import OAI.Probability.Ballisticity.Stationary.ArrayClassProbability
import OAI.Probability.Ballisticity.Stationary.ArrayMassSurvival
import OAI.Probability.Ballisticity.Estimates.EventRate
import OAI.Probability.Ballisticity.Estimates.FiniteClasses

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience
namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma finite_current_classes (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event → CurrentFiniteClasses e (arrayCurrentData e 0 Y) := by
  let μ := (L.law : Measure (ActualEpisodeArray e))
  let A := G.event ∩ {Y | ¬CurrentFiniteClasses e (arrayCurrentData e 0 Y)}
  have hA : MeasurableSet A := G.measurable_event.inter
    (((currentFiniteClasses_measurable e).preimage (arrayCurrentData_measurable e 0)).compl)
  obtain ⟨lam,hlam,hmean⟩ := upperNoDrop_inverse_moment e ν hue htrans
  have hprob (n : ℕ) (hn : 0<n) : μ.real A≤ max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2) := by
    let B : ℕ → Set (ActualEpisodeArray e) := fun k => G.event ∩
      {Y | ∃ a, CurrentClassSelection e n (1/((k:ℝ)+1)) (arrayCurrentData e 0 Y) a}
    have hB (k : ℕ) : MeasurableSet (B k) := G.measurable_event.inter
      ((current_selection_event_measurable e n _).preimage (arrayCurrentData_measurable e 0))
    have he : ∀ᵐ Y ∂μ, Y∈A → ∀ᶠ k in atTop, Y∈B k := by
      filter_upwards [G.no_dust] with Y hY hy
      have hp (a : ℕ) : 0<((arrayCurrentData e 0 Y).2 (a,0):ℝ) := by
        have hn : ((arrayCurrentData e 0 Y).2 (a,0):ℝ)≠0 := hY hy.1 0 a
        exact lt_of_le_of_ne ((arrayCurrentData e 0 Y).2 (a,0)).property.1 hn.symm
      have hh := infinite_current_selection_eventually e (arrayCurrentData e 0 Y) hy.2 hp n
      filter_upwards [hh] with k hk
      exact ⟨hy.1,hk⟩
    have hb (k : ℕ) : μ (B k)≤ENNReal.ofReal (max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2)) := by
      rw [←ENNReal.ofReal_toReal (measure_ne_top μ (B k))]
      exact ENNReal.ofReal_le_ofReal (L.class_selection_probability htrans G hlam hmean n hn _ (by positivity))
    have hh := (measure_le_liminf_of_ae_eventually μ A hA B hB he).trans
      (liminf_le_liminf (Eventually.of_forall hb))
    rw [liminf_const] at hh
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (le_max_right _ _)
      (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hlam.le) G.positive_ζ.le) (by norm_num))) hh
  have ht : Tendsto (fun n : ℕ => max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2)) atTop (𝓝 (0:ℝ)) := by
    have hi : Tendsto (fun n : ℕ => (n:ℝ)*lam*G.ζ/2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num) (((tendsto_natCast_atTop_atTop).atTop_mul_const hlam).atTop_mul_const G.positive_ζ)
    exact hi.const_div_atTop _
  have hz : μ.real A=0 := le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht
    ((eventually_gt_atTop 0).mono fun n hn => hprob n hn)) measureReal_nonneg
  have hmzero : μ A=0 := ((ENNReal.toReal_eq_zero_iff (μ A)).mp hz).resolve_right (measure_ne_top μ A)
  have hnot : ∀ᵐ Y ∂μ, Y∉A := ae_iff.mpr (by simpa using hmzero)
  exact hnot.mono (by intro Y hY hE; by_contra hf; exact hY ⟨hE,hf⟩)

lemma finite_classes_all_times (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y) := by
  have hh := stationary_ae_integer_family (L.law : Measure (ActualEpisodeArray e)) L.preserving
    (fun i Y => Y∈G.event → CurrentFiniteClasses e (arrayCurrentData e i Y))
    (fun i => G.measurable_event.imp ((currentFiniteClasses_measurable e).preimage
      (arrayCurrentData_measurable e i)))
    (fun i => G.invariant.mono fun Y hY => by rw [hY]; rfl)
    (L.finite_current_classes hue htrans G)
  filter_upwards [hh] with Y hY hy i
  exact hY i hy

end StationaryArrayLaw
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical BigOperators Topology
namespace DirectionalTransience

def ArrayRelated {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (p q : StationaryCompact.Label) : Prop := ∃ z : HorizontalSpace e,
      Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e))

lemma arrayRelated_measurable {d : ℕ} (e : Direction d) (p q : StationaryCompact.Label) :
    MeasurableSet {Y : ActualEpisodeArray e | ArrayRelated e Y p q} := by
  simp only [ArrayRelated,Set.ofPred_exists]
  exact MeasurableSet.iUnion fun z => measurableSet_eq_fun (by fun_prop) measurable_const

lemma array_offset_self {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p : StationaryCompact.Label) :
    Y.2.1 (p,p)=(0:HorizontalSpace e) := by
  exact (h (fun _ => p)).self 0

lemma array_offset_add {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p q r : StationaryCompact.Label)
    (z w : HorizontalSpace e) (hz : Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)))
    (hw : Y.2.1 (q,r)=(w:OnePoint (HorizontalSpace e))) :
    Y.2.1 (p,r)=((z+w:HorizontalSpace e):OnePoint (HorizontalSpace e)) := by
  let E := Denumerable.eqv StationaryCompact.Label
  have hs := (h E.symm).add (E p) (E q) (E r) z w
  simpa only [selectedOffsets,Equiv.symm_apply_apply] using hs
    (by simpa [selectedOffsets] using hz) (by simpa [selectedOffsets] using hw)

lemma arrayRelated_refl {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p : StationaryCompact.Label) : ArrayRelated e Y p p :=
  ⟨0,array_offset_self e Y h p⟩
lemma arrayRelated_symm {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) {p q : StationaryCompact.Label}
    (hpq : ArrayRelated e Y p q) : ArrayRelated e Y q p := by
  obtain ⟨z,hz⟩ := hpq
  exact ⟨-z,array_offset_symm e Y h p q z hz⟩
lemma arrayRelated_trans {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) {p q r : StationaryCompact.Label}
    (hpq : ArrayRelated e Y p q) (hqr : ArrayRelated e Y q r) : ArrayRelated e Y p r := by
  obtain ⟨z,hz⟩ := hpq
  obtain ⟨w,hw⟩ := hqr
  exact ⟨z+w,array_offset_add e Y h p q r z w hz hw⟩

lemma arrayRelated_current {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (i : ℤ) (a b : ℕ) :
    ReferenceClasses.related (arrayCurrentData e i Y).1 a b ↔ ArrayRelated e Y (i,a) (i,b) := by
  have ho : ReferenceClasses.Consistent (currentOffsets e i Y) := h (fun a => (i,a))
  simp only [arrayCurrentData,typedCurrentArrayWindow,dite_eq_left ho,ReferenceClasses.related,
    ArrayRelated,currentOffsets]

lemma array_positive_coordinate_represented {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hs : ∀ p j z, Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0))
    (p : StationaryCompact.Label) (j : ℤ) (z : HorizontalSpace e)
    (hp : 0<(Y.2.2.1 (j,p,z):ℝ)) :
    ∃ b, Y.2.1 (p,(j,b))=(z:OnePoint (HorizontalSpace e)) := by
  by_contra h
  have hn : ∀ b, Y.2.1 (p,(j,b))≠(z:OnePoint (HorizontalSpace e)) := by simpa using h
  have he (n : ℕ) : arraySamplingError e p j z (2^n) Y=-(Y.2.2.1 (j,p,z):ℝ) := by
    simp [arraySamplingError,arrayOffsetTest,arrayProfileTest,finiteOffsetTest,hn]
  have hlim := hs p j z
  simp_rw [he] at hlim
  have hz := tendsto_nhds_unique hlim tendsto_const_nhds
  linarith

lemma array_next_full {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (κ : ℝ≥0) (hκ : 0<κ) (he : ArrayElliptic e κ Y) (hc : ArrayContinuation e Y)
    (hm : ∀ i, 0<(Y.1 i).1 ∧ (Y.1 i).1<⊤)
    (i : ℤ) (a : ℕ) (ha : 0<(Y.2.2.1 (i,(i,a),0):ℝ)) (z : HorizontalSpace e) :
    0<(Y.2.2.1 (i+1,(i,a),z):ℝ) := by
  let H := (Y.1 i).1.toNat
  have hH : arrayWindowHeight e i 1 Y=(H:ℕ∞) := by
    simp only [arrayWindowHeight,Finset.sum_range_one,Nat.cast_zero,add_zero]
    exact (ENat.natCast_toNat (hm i).2.ne).symm
  have hpH : 0<H := by
    have : (0:ℕ∞)<(H:ℕ∞) := (hm i).1.trans_eq (ENat.natCast_toNat (hm i).2.ne).symm
    exact_mod_cast this
  have hpK := upperHorizontalKernel_pos e H hpH (arrayUpperRows e i 1 a Y)
    (fun p u => hκ.trans_le (he i 1 a p.1 p.2 u)) 0 z
  have hL : 0<arrayKernelImage e i 1 a H {z} Y :=
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr ha).ne' hpK.ne')
      (ENNReal.le_tsum (f := fun offset => arrayProfileMass e i (i,a) offset Y *
        upperHorizontalKernel e H (arrayUpperRows e i 1 a Y) offset {z}) 0)
  have hR := hL.trans_le (hc i 1 a H z hH)
  have : arrayProfileMass e (i+1) (i,a) z Y≠0 := by
    intro hz
    simp only [arrayDiscountedProfile,Nat.cast_one,hz,mul_zero,lt_self_iff_false] at hR
  exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr this)

lemma array_forward_survives {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hs : ∀ p j z, Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0))
    (κ : ℝ≥0) (hκ : 0<κ) (he : ArrayElliptic e κ Y) (hc : ArrayContinuation e Y)
    (hm : ∀ i, 0<(Y.1 i).1 ∧ (Y.1 i).1<⊤)
    (hd : ∀ i a, ¬arrayDust e i a Y) (i : ℤ) (a : ℕ) :
    ∃ b, ArrayRelated e Y (i,a) (i+1,b) := by
  have ha : 0<(Y.2.2.1 (i,(i,a),0):ℝ) :=
    lt_of_le_of_ne (Y.2.2.1 (i,(i,a),0)).property.1 (show (Y.2.2.1 (i,(i,a),0):ℝ)≠0 from hd i a).symm
  obtain ⟨b,hb⟩ := array_positive_coordinate_represented e Y hs (i,a) (i+1) 0
    (array_next_full e Y κ hκ he hc hm i a ha 0)
  exact ⟨b,0,hb⟩

end DirectionalTransience

end

end OAI
