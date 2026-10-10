import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonWordWidth

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma commonTrueRecord_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) :
    CommonTrueRecord ℓ P n m ↔ CommonTrueRecord ℓ P.swap m n := by
  constructor <;> rintro ⟨h1,h2,he⟩ <;> exact ⟨h2,h1,he.symm⟩

lemma firstCommonTrueRecord_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) :
    FirstCommonTrueRecord ℓ P n m ↔ FirstCommonTrueRecord ℓ P.swap m n := by
  constructor
  · rintro ⟨hn,hm,hc,hmin⟩
    refine ⟨hm,hn,(commonTrueRecord_swap ℓ P n m).mp hc,?_⟩
    intro j k hj hjm hk hkn hc'
    exact hmin k j hk hkn hj hjm ((commonTrueRecord_swap ℓ P k j).mpr hc')
  · rintro ⟨hm,hn,hc,hmin⟩
    refine ⟨hn,hm,(commonTrueRecord_swap ℓ P n m).mpr hc,?_⟩
    intro j k hj hjn hk hkm hc'
    exact hmin k j hk hkm hj hjn ((commonTrueRecord_swap ℓ P j k).mp hc')

lemma firstPairWordEvent_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (wv : List (Direction d) × List (Direction d)) :
    P ∈ FirstPairWordEvent ℓ wv ↔ P.swap ∈ FirstPairWordEvent ℓ wv.swap := by
  constructor
  · rintro ⟨⟨hD1,hD2⟩,⟨hw,hv⟩,hc⟩
    exact ⟨⟨hD2,hD1⟩,⟨hv,hw⟩,(firstCommonTrueRecord_swap ℓ P _ _).mp hc⟩
  · rintro ⟨⟨hD2,hD1⟩,⟨hv,hw⟩,hc⟩
    exact ⟨⟨hD1,hD2⟩,⟨hw,hv⟩,(firstCommonTrueRecord_swap ℓ P _ _).mpr hc⟩

lemma firstPairWord_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    firstPairWord ℓ P.swap = (firstPairWord ℓ P).swap := by
  classical
  by_cases h : ∃ wv, P ∈ FirstPairWordEvent ℓ wv
  · have hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P) := by
      simpa only [firstPairWord,dite_eq_left h] using h.choose_spec
    have hw : (firstPairWord ℓ P).swap ≠ ([],[]) := by
      intro he
      have hlen := congrArg (fun p : List (Direction d) × List (Direction d) => p.2.length) he
      exact Nat.ne_of_gt hP.2.2.1 hlen
    exact (firstPairWord_eq_iff ℓ P.swap _ hw).mpr ((firstPairWordEvent_swap ℓ P _).mp hP)
  · have h' : ¬ ∃ wv, P.swap ∈ FirstPairWordEvent ℓ wv := by
      rintro ⟨wv,hwv⟩
      exact h ⟨wv.swap,(firstPairWordEvent_swap ℓ P _).mpr hwv⟩
    rw [show firstPairWord ℓ P.swap = ([],[]) by simp only [firstPairWord,dite_eq_right h'],
      show firstPairWord ℓ P = ([],[]) by simp only [firstPairWord,dite_eq_right h]]
    rfl

lemma independent_commonWordRadius_snd_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => wordRadius (firstPairWord ℓ P).2) (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hs : MeasurePreserving Prod.swap (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) := Measure.measurePreserving_swap
  have hi : Integrable ((fun P : Path d × Path d => wordRadius (firstPairWord ℓ P).1) ∘ Prod.swap)
      (independentConditionedPairLaw ν ℓ) := hs.integrable_comp_of_integrable
        (independent_commonWordRadius_fst_integrable ν hue ℓ hℓ htrans height hproj hstep)
  have heq : ((fun P : Path d × Path d => wordRadius (firstPairWord ℓ P).1) ∘ Prod.swap) =
      (fun P => wordRadius (firstPairWord ℓ P).2) := by
    funext P
    dsimp only [Function.comp_def]
    rw [firstPairWord_swap]
    rfl
  rwa [heq] at hi

noncomputable def commonWordIncrement {d : ℕ} (e : Direction d)
    (wv : List (Direction d) × List (Direction d)) : ℝ :=
  wordCoordinate e wv.1-wordCoordinate e wv.2

lemma commonWordIncrement_abs_le {d : ℕ} (e : Direction d)
    (wv : List (Direction d) × List (Direction d)) :
    |commonWordIncrement e wv| ≤ wordRadius wv.1+wordRadius wv.2 :=
  (abs_sub _ _).trans (add_le_add (wordCoordinate_abs_le_radius e _) (wordCoordinate_abs_le_radius e _))

lemma independent_commonWordIncrement_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) :
    Integrable (fun P => commonWordIncrement e (firstPairWord ℓ P)) (independentConditionedPairLaw ν ℓ) := by
  apply ((independent_commonWordRadius_fst_integrable ν hue ℓ hℓ htrans height hproj hstep).add
    (independent_commonWordRadius_snd_integrable ν hue ℓ hℓ htrans height hproj hstep)).mono'
    (((measurable_of_countable (commonWordIncrement e)).comp (measurable_firstPairWord ℓ)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun P => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.add_apply] using commonWordIncrement_abs_le e (firstPairWord ℓ P)

lemma independent_commonWordIncrement_symmetric {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (e : Direction d) :
    IdentDistrib (fun P => commonWordIncrement e (firstPairWord ℓ P))
      (fun P => -commonWordIncrement e (firstPairWord ℓ P))
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) := by
  have hm : Measurable (fun P => commonWordIncrement e (firstPairWord ℓ P)) :=
    (measurable_of_countable (commonWordIncrement e)).comp (measurable_firstPairWord ℓ)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hp : MeasurePreserving Prod.swap (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) := Measure.measurePreserving_swap
  have hi : IdentDistrib (fun P => commonWordIncrement e (firstPairWord ℓ P.swap))
      (fun P => commonWordIncrement e (firstPairWord ℓ P))
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) := by
    refine ⟨(hm.comp measurable_swap).aemeasurable,hm.aemeasurable,?_⟩
    rw [show (fun P => commonWordIncrement e (firstPairWord ℓ P.swap)) =
      (fun P => commonWordIncrement e (firstPairWord ℓ P)) ∘ Prod.swap from rfl,
      ← Measure.map_map hm measurable_swap,hp.map_eq]
  convert hi.symm using 1
  ext P
  simp only [firstPairWord_swap,commonWordIncrement,Prod.fst_swap,Prod.snd_swap,neg_sub]

lemma signedCoordinate_step_self {d : ℕ} (e : Direction d) :
    signedCoordinate e (step e) = 1 := by
  simp only [signedCoordinate,step,ite_true,Int.cast_ite,Int.cast_one,Int.cast_neg]
  cases e.2 <;> norm_num

lemma signedCoordinate_step_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) :
    signedCoordinate e (step f) = 0 := by
  simp [signedCoordinate,step,hef]

lemma admissible_transverse_commonWords {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) :
    AdmissibleCommonWords (realPosition (step e)) 0 0 [f,e] [e] := by
  have hzero : dot (realPosition (0 : Lattice d)) (realPosition (step e)) = 0 := by
    simp [dot,realPosition]
  have he := signed_direction_unit e
  have hf : dot (realPosition (step f)) (realPosition (step e)) = 0 := by
    rw [dot_signed_direction,signedCoordinate_step_other e f hef]
  have hfe : dot (realPosition (step f+step e)) (realPosition (step e)) = 1 := by
    rw [dot_realPosition_add,hf,he]; ring
  refine ⟨by simp,by simp,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_cons,List.length_nil,wordPath,zero_add] using hfe.trans he.symm
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by simp only [List.length_cons,List.length_nil] at hj; omega
    rcases hj' with rfl | rfl <;>
      simp only [List.length_cons,List.length_nil,wordPath,zero_add,hzero,hf,hfe] <;> norm_num
  · intro j hj
    have hj' : j = 0 := by simp only [List.length_cons,List.length_nil] at hj; omega
    subst j
    simp only [List.length_cons,List.length_nil,wordPath,zero_add,hzero,he]
    norm_num
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      simp only [List.length_cons,List.length_nil] at hj; omega
    rcases hj' with rfl | rfl | rfl <;>
      simp only [wordPath,zero_add,hzero,hf,hfe] <;> norm_num
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by simp only [List.length_cons,List.length_nil] at hj; omega
    rcases hj' with rfl | rfl <;> simp only [wordPath,zero_add,hzero,he] <;> norm_num
  · intro j k _ _ hk hkl _ _ _
    simp only [List.length_cons,List.length_nil] at hkl
    omega

lemma annealed_wordCylinder_positive {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (w : List (Direction d)) :
    0 < annealedLaw ν (wordCylinder 0 w) := by
  obtain ⟨κ,hκ,hrows⟩ := environment_uniform_elliptic ν hue
  exact (ENNReal.pow_pos (by exact_mod_cast hκ : (0 : ℝ≥0∞) < κ) w.length).trans_le
    (annealed_wordCylinder_lower ν κ hrows w)

lemma independent_commonWordIncrement_nonzero {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    0 < independentConditionedPairLaw ν (realPosition (step e))
      {P | commonWordIncrement f (firstPairWord (realPosition (step e)) P) ≠ 0} := by
  let ℓ := realPosition (step e)
  have had := admissible_transverse_commonWords e f hef
  have hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0 := ne_of_gt
    (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hm : 0 < independentConditionedPairLaw ν ℓ (FirstPairWordEvent ℓ ([f,e],[e])) := by
    rw [independent_conditioned_pair_word_mass ν ℓ hp _ had]
    exact ENNReal.mul_pos (ne_of_gt (annealed_wordCylinder_positive ν hue _))
      (ne_of_gt (annealed_wordCylinder_positive ν hue _))
  apply hm.trans_le (measure_mono _)
  intro P hP
  have heq : firstPairWord ℓ P = ([f,e],[e]) :=
    (firstPairWord_eq_iff ℓ P _ (by simp)).mpr hP
  change commonWordIncrement f (firstPairWord ℓ P) ≠ 0
  rw [heq]
  simp only [commonWordIncrement,wordCoordinate,List.length_cons,List.length_nil,
    wordPath,zero_add,signedCoordinate_add,signedCoordinate_step_self,
    signedCoordinate_step_other f e (Ne.symm hef)]
  norm_num

noncomputable def truncatedVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : ℝ := ∫ x, min ((S x)^2) (r^2) ∂μ
noncomputable def fluctuationScale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : ℝ := r^2 / truncatedVariance μ S r

lemma integrable_truncated_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (r : ℝ) :
    Integrable (fun x => min ((S x)^2) (r^2)) μ := by
  apply (integrable_const (r^2)).mono' ((hS.pow_const 2).min measurable_const).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_right _ _

lemma truncatedVariance_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : 0 ≤ truncatedVariance μ S r :=
  integral_nonneg fun _ => le_min (sq_nonneg _) (sq_nonneg _)

lemma truncatedVariance_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    0 < truncatedVariance μ S r := by
  apply (integral_pos_iff_support_of_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))
    (integrable_truncated_square μ S hS r)).mpr
  apply hne.trans_le (measure_mono _)
  intro x hx
  exact ne_of_gt (lt_min (sq_pos_of_ne_zero hx) (sq_pos_of_pos hr))

lemma truncatedVariance_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : truncatedVariance μ S r ≤ truncatedVariance μ S s := by
  apply integral_mono (integrable_truncated_square μ S hS r) (integrable_truncated_square μ S hS s)
  intro x
  exact min_le_min_left _ (pow_le_pow_left₀ hr hrs 2)

lemma truncatedVariance_le_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (r : ℝ) :
    truncatedVariance μ S r ≤ r^2 := by
  simpa only [truncatedVariance,integral_const,probReal_univ,one_smul] using
    integral_mono (integrable_truncated_square μ S hS r) (integrable_const (r^2))
      (fun x => min_le_right ((S x)^2) (r^2))

lemma min_sq_le_mul_abs {s r : ℝ} (hr : 0 ≤ r) : min (s^2) (r^2) ≤ r*|s| := by
  by_cases hs : |s| ≤ r
  · apply (min_le_left _ _).trans
    nlinarith [sq_abs s,abs_nonneg s]
  · apply (min_le_right _ _).trans
    nlinarith [lt_of_not_ge hs]

lemma truncatedVariance_le_firstMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) {r : ℝ} (hr : 0 ≤ r) :
    truncatedVariance μ S r ≤ r*(∫ x, |S x| ∂μ) := by
  rw [truncatedVariance,← integral_const_mul]
  apply integral_mono (integrable_truncated_square μ S hS r) (hI.abs.const_mul r)
  exact fun _ => min_sq_le_mul_abs hr

lemma truncatedVariance_abs_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (r s : ℝ) :
    |truncatedVariance μ S r-truncatedVariance μ S s| ≤ |r^2-s^2| := by
  rw [truncatedVariance,truncatedVariance,← integral_sub
    (integrable_truncated_square μ S hS r) (integrable_truncated_square μ S hS s)]
  have hh := norm_integral_le_of_norm_le_const (C := |r^2-s^2|) (μ := μ) (f := fun x => min ((S x)^2) (r^2)-min ((S x)^2) (s^2))
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_min_sub_min_le_max ((S x)^2) (r^2) ((S x)^2) (s^2)).trans
        (max_le (by simp) le_rfl))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

lemma continuous_truncatedVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S) :
    Continuous (truncatedVariance μ S) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hc : ContinuousAt (fun r : ℝ => r^2) s := continuousAt_id.pow 2
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ,hδ,fun r hr => ?_⟩
  exact (truncatedVariance_abs_sub_le μ S hS r s).trans_lt (hbound hr)

lemma min_sq_cross {a r s : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hrs : r ≤ s) :
    min a (s^2)*r^2 ≤ min a (r^2)*s^2 := by
  have hs2 : r^2 ≤ s^2 := pow_le_pow_left₀ hr hrs 2
  by_cases har : a ≤ r^2
  · rw [min_eq_left har,min_eq_left (har.trans hs2)]
    exact mul_le_mul_of_nonneg_left hs2 ha
  · by_cases has : a ≤ s^2
    · rw [min_eq_right (le_of_not_ge har),min_eq_left has]
      nlinarith [sq_nonneg r]
    · rw [min_eq_right (le_of_not_ge har),min_eq_right (le_of_not_ge has)]
      exact le_of_eq (mul_comm _ _)

lemma fluctuationScale_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    fluctuationScale μ S r ≤ fluctuationScale μ S s := by
  rw [fluctuationScale,fluctuationScale,div_le_div_iff₀
    (truncatedVariance_pos μ S hS hne hr) (truncatedVariance_pos μ S hS hne (hr.trans_le hrs))]
  have hi := integral_mono ((integrable_truncated_square μ S hS s).mul_const (r^2))
    ((integrable_truncated_square μ S hS r).mul_const (s^2))
    (fun x => min_sq_cross (sq_nonneg (S x)) hr.le hrs)
  rw [integral_mul_const,integral_mul_const] at hi
  simpa only [truncatedVariance,mul_comm] using hi

lemma integral_abs_pos_of_nonzero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    0 < ∫ x, |S x| ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => abs_nonneg _) hI.abs).mpr
  simpa only [Function.support,ne_eq,abs_eq_zero] using hne

lemma fluctuationScale_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    r/(∫ x, |S x| ∂μ) ≤ fluctuationScale μ S r := by
  have hM := integral_abs_pos_of_nonzero μ S hI hne
  rw [fluctuationScale,div_le_div_iff₀ hM (truncatedVariance_pos μ S hS hne hr)]
  calc
    r * truncatedVariance μ S r ≤ r*(r * ∫ x, |S x| ∂μ) :=
      mul_le_mul_of_nonneg_left (truncatedVariance_le_firstMoment μ S hS hI hr.le) hr.le
    _ = r^2*(∫ x, |S x| ∂μ) := by ring

lemma fluctuationScale_scaling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (hc1 : c ≤ 1) :
    c^2*fluctuationScale μ S r ≤ fluctuationScale μ S (c*r) := by
  have hcr := mul_pos hc hr
  have hle : c*r ≤ r := by nlinarith
  unfold fluctuationScale
  rw [← mul_div_assoc,mul_pow]
  exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (truncatedVariance_pos μ S hS hne hcr) (truncatedVariance_mono μ S hS hcr.le hle)

lemma fluctuationScale_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    Tendsto (fluctuationScale μ S) atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (tendsto_id.atTop_div_const (integral_abs_pos_of_nonzero μ S hI hne))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact fluctuationScale_lower μ S hS hI hne hr

lemma continuousOn_fluctuationScale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) : ContinuousOn (fluctuationScale μ S) (Set.Ioi 0) := by
  exact (continuous_pow 2).continuousOn.div (continuous_truncatedVariance μ S hS).continuousOn
    (fun r hr => ne_of_gt (truncatedVariance_pos μ S hS hne hr))

lemma exists_bounded_nonzero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (hne : 0 < μ {x | S x ≠ 0}) :
    ∃ N : ℕ, 0 < μ {x | S x ≠ 0 ∧ |S x| ≤ N} := by
  by_contra! hh
  have hz : ∀ N : ℕ, μ {x | S x ≠ 0 ∧ |S x| ≤ N} = 0 :=
    fun N => le_antisymm (hh N) (zero_le)
  have hsub : {x | S x ≠ 0} ⊆ ⋃ N : ℕ, {x | S x ≠ 0 ∧ |S x| ≤ N} := by
    intro x hx
    obtain ⟨N,hN⟩ := exists_nat_ge |S x|
    exact Set.mem_iUnion.mpr ⟨N,hx,hN⟩
  have hle := measure_mono (μ := μ) hsub
  rw [measure_iUnion_null_iff.mpr hz] at hle
  exact not_le_of_gt hne hle

lemma fluctuationScale_eventually_strictMono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) :
    ∃ R : ℝ, 0 < R ∧ StrictMonoOn (fluctuationScale μ S) (Set.Ici R) := by
  obtain ⟨N,hN⟩ := exists_bounded_nonzero μ S hne
  refine ⟨N+1,by positivity,?_⟩
  intro r hr s _ hrs
  change (N:ℝ)+1 ≤ r at hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : (0:ℝ) < N+1) hr
  have hs0 : 0 < s := hr0.trans hrs
  rw [fluctuationScale,fluctuationScale,div_lt_div_iff₀
    (truncatedVariance_pos μ S hS hne hr0) (truncatedVariance_pos μ S hS hne hs0)]
  let D : Ω → ℝ := fun x => min ((S x)^2) (r^2)*s^2-min ((S x)^2) (s^2)*r^2
  have hID : Integrable D μ := ((integrable_truncated_square μ S hS r).mul_const (s^2)).sub
    ((integrable_truncated_square μ S hS s).mul_const (r^2))
  have hDpos : 0 < ∫ x, D x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg
      (fun x => sub_nonneg.mpr (min_sq_cross (sq_nonneg _) hr0.le hrs.le)) hID).mpr
    apply hN.trans_le (measure_mono _)
    intro x hx
    have hxr : (S x)^2 ≤ r^2 := by
      have : |S x| ≤ r := hx.2.trans (by linarith)
      nlinarith [sq_abs (S x),abs_nonneg (S x)]
    have hrs2 : r^2 < s^2 := by nlinarith
    have hxs := hxr.trans hrs2.le
    change D x ≠ 0
    dsimp [D]
    rw [min_eq_left hxr,min_eq_left hxs]
    have := mul_pos (sq_pos_of_ne_zero hx.1) (sub_pos.mpr hrs2)
    nlinarith
  dsimp [D] at hDpos
  rw [integral_sub ((integrable_truncated_square μ S hS r).mul_const (s^2))
    ((integrable_truncated_square μ S hS s).mul_const (r^2)),
    integral_mul_const,integral_mul_const] at hDpos
  simpa only [truncatedVariance,mul_comm] using sub_pos.mp hDpos

def realPartialSum (X : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, X k

def partialSumMax (X : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => max (partialSumMax X n) |realPartialSum X (n+1)|

lemma realPartialSum_zero (X : ℕ → ℝ) : realPartialSum X 0 = 0 := by simp [realPartialSum]
lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

lemma partialSumMax_nonneg (X : ℕ → ℝ) (n : ℕ) : 0 ≤ partialSumMax X n := by
  induction n with
  | zero => rfl
  | succ n _ => exact (abs_nonneg _).trans (le_max_right _ _)

lemma abs_partialSum_le_max (X : ℕ → ℝ) (n : ℕ) : |realPartialSum X n| ≤ partialSumMax X n := by
  cases n with
  | zero => simp [realPartialSum,partialSumMax]
  | succ n => exact le_max_right _ _

lemma partialSumMax_mono (X : ℕ → ℝ) : Monotone (partialSumMax X) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

lemma partialSumMax_bound (X : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hX : ∀ k, |X k| ≤ z) (n : ℕ) :
    partialSumMax X n ≤ n*z := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    apply max_le
    · simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ih.trans (le_add_of_nonneg_right hz)
    · rw [realPartialSum_succ]
      calc
        |realPartialSum X n+X n| ≤ |realPartialSum X n|+|X n| := abs_add_le _ _
        _ ≤ n*z+z := add_le_add ((abs_partialSum_le_max X n).trans ih) (hX n)
        _ = (n+1:ℕ)*z := by push_cast; ring

noncomputable def absSlope (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

lemma abs_absSlope (t : ℝ) : |absSlope t| = 1 := by
  unfold absSlope
  split <;> simp

end DirectionalTransience
end
end

end OAI
