import OAI.Probability.DirectionalWalk.Widths

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def euclideanSite {d : ℕ} (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

lemma euclideanSite_add {d : ℕ} (x y : Site d) :
    euclideanSite (x+y) = euclideanSite x + euclideanSite y := by
  ext i
  simp [euclideanSite]

lemma euclideanSite_zero {d : ℕ} : euclideanSite (0 : Site d) = 0 := by
  ext i
  simp [euclideanSite]

lemma euclideanSite_sub {d : ℕ} (x y : Site d) :
    euclideanSite (x-y) = euclideanSite x - euclideanSite y := by
  ext i
  simp [euclideanSite]

noncomputable def slabRadius {d : ℕ} (γ : Word d) : ℝ :=
  (Finset.range (γ.1+1)).sup' ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => ‖euclideanSite (wordPath γ j - wordPath γ 0)‖)

lemma norm_wordPath_le_radius {d : ℕ} (γ : Word d) {j : ℕ} (hj : j ≤ γ.1) :
    ‖euclideanSite (wordPath γ j - wordPath γ 0)‖ ≤ slabRadius γ :=
  Finset.le_sup' (fun k => ‖euclideanSite (wordPath γ k - wordPath γ 0)‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma slabRadius_nonneg {d : ℕ} (γ : Word d) : 0 ≤ slabRadius γ := by
  exact (norm_nonneg _).trans (norm_wordPath_le_radius γ (j := 0) (Nat.zero_le _))

lemma slabs_identDistrib {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (k : ℕ) :
    IdentDistrib (fun X => slabs v X k) id (conditioned μ v) (slabLaw μ v) := by
  refine ⟨((measurable_pi_apply k).comp (measurable_slabs v)).aemeasurable,
    measurable_id.aemeasurable,?_⟩
  rw [Measure.map_id]
  exact slabs_marginal μ hell v hv hp k

lemma slabObservable_strongLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (f : Word d → ℝ)
    (hf : Integrable f (slabLaw μ v)) :
    ∀ᵐ X ∂conditioned μ v,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f (slabs v X i)) / n)
        atTop (𝓝 (∫ γ, f γ ∂slabLaw μ v)) := by
  have hind := (slabs_iid μ hell v hv hp).comp (fun _ => f)
    (fun _ => measurable_of_countable _)
  have hid (k : ℕ) := (slabs_identDistrib μ hell v hv hp k).comp
    (measurable_of_countable f)
  have hfi : Integrable (fun X => f (slabs v X 0)) (conditioned μ v) :=
    (hid 0).integrable_iff.mpr hf
  have heq : (∫ X, f (slabs v X 0) ∂conditioned μ v) = ∫ γ, f γ ∂slabLaw μ v :=
    (hid 0).integral_eq
  simpa only [Function.comp_apply, id_eq,heq] using strong_law_ae_real
    (fun k X => f (slabs v X k)) hfi (fun i j hij => hind.indepFun hij)
    (fun k => (hid k).trans (hid 0).symm)

lemma slabWidth_strongLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂conditioned μ v,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, slabWidth v (slabs v X i)) / n)
        atTop (𝓝 (∫ γ, slabWidth v γ ∂slabLaw μ v)) :=
  slabObservable_strongLaw μ hell v hv hp _ (integrable_slabWidth μ hell v hv hvnorm hp)

lemma slab_initial_average_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (f : Word d → ℝ)
    (hf : Integrable f (slabLaw μ v)) (hf0 : ∀ γ, 0 ≤ f γ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (conditioned μ v).real {X | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, f (slabs v X j)} ≤
      (∫ γ, f γ ∂slabLaw μ v) / a := by
  let := conditioned_probability μ v hp
  have hid := (slabs_identDistrib μ hell v hv hp 0).comp (measurable_of_countable f)
  have hfi : Integrable (fun X => f (firstWord v X)) (conditioned μ v) :=
    hid.integrable_iff.mpr hf
  have hfe : (∫ X, f (firstWord v X) ∂conditioned μ v) = ∫ γ, f γ ∂slabLaw μ v :=
    hid.integral_eq
  have hh := stationary_initial_average_bound (conditioned μ v) (cutSuffix v)
    (cutSuffix_measurePreserving μ hell v hv hp) (fun X => f (firstWord v X))
    ((measurable_of_countable f).comp (measurable_firstWord v)) hfi (fun X => hf0 _) a ha n
  simpa only [initialAverageBad,slabs,hfe] using hh

noncomputable def slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (slabs v X i).1

lemma slabTime_zero {d : ℕ} (v : Fin d → ℝ) (X : Path d) : slabTime v X 0 = 0 := by
  simp [slabTime]

lemma slabTime_succ {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) :
    slabTime v X (k+1) = slabTime v X k + (slabs v X k).1 := by
  exact Finset.sum_range_succ _ _

lemma iterated_cutSuffix {d : ℕ} (v : Fin d → ℝ) (X : Path d) (h0 : X 0 = 0)
    (k n : ℕ) : (cutSuffix v)^[k] X n = X (slabTime v X k + n) - X (slabTime v X k) := by
  induction k generalizing n with
  | zero => simp [slabTime_zero,h0]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((cutSuffix v)^[k] X) (firstCutTime v ((cutSuffix v)^[k] X) + n) +
      -((cutSuffix v)^[k] X (firstCutTime v ((cutSuffix v)^[k] X))) = _
    rw [ih,ih,slabTime_succ]
    change X (slabTime v X k + ((slabs v X k).1+n)) - X (slabTime v X k) +
      -(X (slabTime v X k + (slabs v X k).1) - X (slabTime v X k)) = _
    rw [← Nat.add_assoc]
    abel

lemma slab_word_path {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ)
    {j : ℕ} (hj : j ≤ (slabs v X k).1) :
    wordPath (slabs v X k) j = (cutSuffix v)^[k] X j :=
  wordPath_prefixWord _ _ hj

def GoodSlabPath {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Prop :=
  X 0 = 0 ∧ ∀ k, RegenerationWord v (slabs v X k)

lemma ae_goodSlabPath {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂conditioned μ v, GoodSlabPath v X := by
  have h0 := (cond_absolutelyContinuous (s := nonBacktracking v) (μ := annealed μ 0)).ae_le
    (ae_start_and_nearestNeighbour μ 0)
  have hs : ∀ᵐ X ∂conditioned μ v, ∀ k, RegenerationWord v (slabs v X k) := by
    rw [ae_all_iff]
    intro k
    exact ((cutSuffix_measurePreserving μ hell v hv hp).iterate k).quasiMeasurePreserving.ae
      (ae_conditioned_firstWord μ hell v hv hp)
  filter_upwards [h0,hs] with X hX hW
  exact ⟨hX.1,hW⟩

lemma slabTime_strictMono {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X) :
    StrictMono (slabTime v X) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [slabTime_succ]
  exact Nat.lt_add_of_pos_right (hX.2 k).1

lemma slab_location {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (n : ℕ) : ∃ k, slabTime v X k ≤ n ∧ n < slabTime v X (k+1) := by
  have hex : ∃ k, n < slabTime v X (k+1) :=
    ⟨n,(Nat.lt_succ_self n).trans_le ((slabTime_strictMono v X hX).id_le (n+1))⟩
  refine ⟨Nat.find hex,?_,Nat.find_spec hex⟩
  by_cases hz : Nat.find hex = 0
  · rw [hz,slabTime_zero]
    exact Nat.zero_le _
  · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hh := Nat.find_min hex (show j < Nat.find hex by omega)
    rw [hj]
    exact not_lt.mp hh

noncomputable def slabHeightSum {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, slabWidth v (slabs v X i)

noncomputable def slabRadiusSum {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, slabRadius (slabs v X i)

lemma height_at_slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (h0 : X 0 = 0)
    (k : ℕ) : height v (X (slabTime v X k)) = slabHeightSum v X k := by
  induction k with
  | zero => simp [slabTime_zero,slabHeightSum,h0,height_zero]
  | succ k ih =>
    have hh := iterated_cutSuffix v X h0 k (slabs v X k).1
    rw [← slab_word_path v X k le_rfl,← slabTime_succ] at hh
    have hh' := congrArg (height v) hh
    rw [height_sub,ih] at hh'
    change slabWidth v (slabs v X k) = height v (X (slabTime v X (k+1))) - _ at hh'
    rw [slabHeightSum,Finset.sum_range_succ]
    change height v (X (slabTime v X (k+1))) = slabHeightSum v X k + _
    linarith

lemma norm_at_slabTime_le {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k : ℕ) : ‖euclideanSite (X (slabTime v X k))‖ ≤ slabRadiusSum v X k := by
  induction k with
  | zero => simp [slabTime_zero,slabRadiusSum,hX.1,euclideanSite_zero]
  | succ k ih =>
    have hh := iterated_cutSuffix v X hX.1 k (slabs v X k).1
    rw [← slab_word_path v X k le_rfl,← slabTime_succ] at hh
    have heq : X (slabTime v X (k+1)) = X (slabTime v X k) + wordPath (slabs v X k) (slabs v X k).1 := by
      rw [hh]
      abel
    rw [heq,euclideanSite_add]
    have hb := norm_wordPath_le_radius (slabs v X k) (j := (slabs v X k).1) le_rfl
    rw [(hX.2 k).2.1,sub_zero] at hb
    rw [slabRadiusSum,Finset.sum_range_succ]
    exact (norm_add_le _ _).trans (add_le_add ih hb)

lemma norm_in_slab_le {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k j : ℕ) (hj : j ≤ (slabs v X k).1) :
    ‖euclideanSite (X (slabTime v X k + j))‖ ≤ slabRadiusSum v X (k+1) := by
  have hh := iterated_cutSuffix v X hX.1 k j
  rw [← slab_word_path v X k hj] at hh
  have heq : X (slabTime v X k+j) = X (slabTime v X k) + wordPath (slabs v X k) j := by
    rw [hh]
    abel
  rw [heq,euclideanSite_add]
  have hb := norm_wordPath_le_radius (slabs v X k) hj
  rw [(hX.2 k).2.1,sub_zero] at hb
  rw [slabRadiusSum,Finset.sum_range_succ]
  exact (norm_add_le _ _).trans (add_le_add (norm_at_slabTime_le v X hX k) hb)

lemma height_in_slab {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k j : ℕ) (hj : j < (slabs v X k).1) :
    slabHeightSum v X k ≤ height v (X (slabTime v X k+j)) ∧
    height v (X (slabTime v X k+j)) < slabHeightSum v X (k+1) := by
  have hh := congrArg (height v) (iterated_cutSuffix v X hX.1 k j)
  rw [← slab_word_path v X k hj.le,height_sub,height_at_slabTime v X hX.1] at hh
  have hb := (hX.2 k).2.2.2.1 j hj
  have heq : slabHeightSum v X (k+1) = slabHeightSum v X k + slabWidth v (slabs v X k) :=
    Finset.sum_range_succ _ _
  rw [heq]
  change 0 ≤ height v (wordPath (slabs v X k) j) ∧
    height v (wordPath (slabs v X k) j) < slabWidth v (slabs v X k) at hb
  constructor <;> linarith [hb.1,hb.2]

noncomputable def truncatedMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ := ∫ x, min (f x) t ∂P

lemma integrable_min_const {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => min (f x) t) P := by
  apply (integrable_const t).mono' (hfm.min measurable_const).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf x) ht)]
    exact min_le_right _ _)

lemma truncatedMoment_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ truncatedMoment P f t := integral_nonneg (fun x => le_min (hf x) ht)

lemma truncatedMoment_mono {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    truncatedMoment P f s ≤ truncatedMoment P f t :=
  integral_mono (integrable_min_const P f hfm hf s hs)
    (integrable_min_const P f hfm hf t (hs.trans hst)) (fun _ => min_le_min_left _ hst)

lemma min_mul_le_mul_min {r t C : ℝ} (hr : 0 ≤ r) (hC : 1 ≤ C) :
    min r (C*t) ≤ C * min r t := by
  by_cases hrt : r ≤ t
  · rw [min_eq_left hrt]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right (le_of_not_ge hrt)]
    exact min_le_right _ _

lemma truncatedMoment_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {t C : ℝ} (ht : 0 ≤ t) (hC : 1 ≤ C) :
    truncatedMoment P f (C*t) ≤ C * truncatedMoment P f t := by
  unfold truncatedMoment
  rw [← integral_const_mul]
  exact integral_mono (integrable_min_const P f hfm hf _ (mul_nonneg (by linarith) ht))
    ((integrable_min_const P f hfm hf t ht).const_mul C)
    (fun x => min_mul_le_mul_min (hf x) hC)

lemma truncatedMoment_sublinear {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) :
    Tendsto (fun t : ℝ => truncatedMoment P f t / t) atTop (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (F := fun t : ℝ => fun x => min (f x) t / t) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun t => ((hfm.min measurable_const).div_const t).aestronglyMeasurable))
    (show ∀ᶠ t : ℝ in atTop, ∀ᵐ x ∂P, ‖min (f x) t / t‖ ≤ (1 : ℝ) from by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (le_min (hf x) ht.le) ht.le)]
        exact (div_le_one ht).mpr (min_le_right _ _)))
    (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun x => by
      apply Tendsto.congr' (f₁ := fun t : ℝ => f x / t) ?_
        (tendsto_const_nhds.div_atTop tendsto_id)
      filter_upwards [eventually_ge_atTop (f x)] with t ht
      rw [min_eq_left ht]))
  simpa only [integral_div,integral_zero,truncatedMoment] using hlim

lemma integrable_of_truncatedMoment_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (B : ℝ)
    (hb : ∀ n : ℕ, truncatedMoment P f n ≤ B) : Integrable f P := by
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (min (f x) (n : ℝ)) ∂P)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂P)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (hfm.min measurable_const).ennreal_ofReal.aemeasurable
    · exact Eventually.of_forall (fun x n m hnm =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnm)))
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
          (eventually_ge_atTop (f x))] with n hn
        rw [min_eq_left hn])
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂P) ≤ ENNReal.ofReal B := by
    apply le_of_tendsto hlim
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_min_const P f hfm hf (n : ℝ) (Nat.cast_nonneg _))
        (Eventually.of_forall (fun x => le_min (hf x) (Nat.cast_nonneg _)))]
      exact ENNReal.ofReal_le_ofReal (hb n))
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf)).mpr
    (hbound.trans_lt ENNReal.ofReal_lt_top)

lemma exists_truncatedMoment_gt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hnot : ¬Integrable f P) (B : ℝ) :
    ∃ n : ℕ, B < truncatedMoment P f n := by
  by_contra h
  push Not at h
  exact hnot (integrable_of_truncatedMoment_bounded P f hfm hf B h)

lemma truncatedMoment_scaled_sublinear {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun a : ℝ => truncatedMoment P f (C*a) / a) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => C*a) atTop atTop := tendsto_id.const_mul_atTop hC
  have hh := ((truncatedMoment_sublinear P f hfm hf).comp ht).const_mul C
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  dsimp
  field_simp

lemma exists_truncation_multiple {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hnot : ¬Integrable f P) {a b : ℝ} (ha : 0 < a) :
    ∃ n : ℕ, 0 < n ∧ b ≤ truncatedMoment P f (a*n) := by
  obtain ⟨j,hj⟩ := exists_truncatedMoment_gt P f hfm hf hnot b
  obtain ⟨n,hn⟩ := exists_nat_gt ((j : ℝ)/a)
  refine ⟨n+1,Nat.succ_pos _,hj.le.trans ?_⟩
  apply truncatedMoment_mono P f hfm hf (Nat.cast_nonneg _)
  have hh : (j : ℝ) < (n : ℝ)*a := (div_lt_iff₀ ha).mp hn
  push_cast
  nlinarith

lemma radius_scales {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hnot : ¬Integrable f P) {η : ℝ} (hη : 0 < η)
    (M : ℕ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, 0 < a ∧ ∃ N : ℕ, max 2 M ≤ N ∧
      η*a ≤ truncatedMoment P f (a*N) ∧ truncatedMoment P f (a*N) < 2*η*a ∧
      truncatedMoment P f (D*a) < η*a/4 ∧
      ∀ m : ℕ, 0 < m → m < N → truncatedMoment P f (a*m) < η*a := by
  let K := max 2 M
  have hK : (0 : ℝ) < K := by dsimp [K]; exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (le_max_left 2 M))
  have hs := (truncatedMoment_scaled_sublinear P f hfm hf hK).eventually
    (gt_mem_nhds hη)
  have hsmall := (truncatedMoment_scaled_sublinear P f hfm hf hD).eventually
    (gt_mem_nhds (show (0 : ℝ) < η/4 by positivity))
  filter_upwards [eventually_gt_atTop (0 : ℝ),hs,hsmall] with a ha hs hsmall
  obtain hex := exists_truncation_multiple P f hfm hf hnot (b := η*a) ha
  let N := Nat.find hex
  have hN := Nat.find_spec hex
  have hmin : ∀ m : ℕ, 0 < m → m < N → truncatedMoment P f (a*m) < η*a := by
    intro m hm hmN
    have hh := Nat.find_min hex hmN
    exact lt_of_not_ge (fun h => hh ⟨hm,h⟩)
  have hKN : K < N := by
    by_contra hh
    have hNK : N ≤ K := le_of_not_gt hh
    have hhN := truncatedMoment_mono P f hfm hf (mul_nonneg ha.le (Nat.cast_nonneg N))
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hNK) ha.le)
    have hhK : truncatedMoment P f (a*K) < η*a := by
      rw [mul_comm a]
      exact (div_lt_iff₀ ha).mp hs
    exact (not_lt_of_ge hN.2) (hhN.trans_lt hhK)
  have hN2 : 2 ≤ N := (le_max_left 2 M).trans hKN.le
  have hNm : 0 < N-1 := by omega
  have hm := hmin (N-1) hNm (by omega)
  have hstep : truncatedMoment P f (a*N) ≤ 2*truncatedMoment P f (a*((N-1 : ℕ) : ℝ)) := by
    apply (truncatedMoment_mono P f hfm hf (mul_nonneg ha.le (Nat.cast_nonneg N)) ?_).trans
      (truncatedMoment_mul_le P f hfm hf (mul_nonneg ha.le (by positivity)) (by norm_num : (1 : ℝ) ≤ 2))
    have hNN : (N : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2*(N-1) by omega)
    nlinarith
  refine ⟨ha,N,hKN.le,hN.2,?_,?_,hmin⟩
  · nlinarith
  · exact (div_lt_iff₀ ha).mp hsmall |>.trans_le (by ring_nf; exact le_rfl)

lemma stationary_truncated_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → Ω)
    (hT : MeasurePreserving T P P) (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    P.real (initialAverageBad T f a n) ≤ 2*truncatedMoment P f (a*n)/a := by
  classical
  let A : ℝ := a*n
  have hA : 0 < A := mul_pos ha (Nat.cast_pos.mpr hn)
  let g : Ω → ℝ := fun x => min (f x) A
  have hgm : Measurable g := hfm.min measurable_const
  have hgi : Integrable g P := integrable_min_const P f hfm hf A hA.le
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min (hf x) hA.le
  have htail : P.real {x | A < f x} ≤ truncatedMoment P f A / A := by
    have hb := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hg0) hgi A
    have hm : P.real {x | A < f x} ≤ P.real {x | A ≤ g x} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      change A < f x at hx
      exact le_min hx.le le_rfl
    apply (le_div_iff₀ hA).mpr
    calc
      P.real {x | A < f x} * A ≤ A * P.real {x | A ≤ g x} := by nlinarith
      _ ≤ _ := hb
  let B : Set Ω := ⋃ j ∈ Finset.range n, {x | A < f (T^[j] x)}
  have hB : P.real B ≤ (n : ℝ)*truncatedMoment P f A/A := by
    apply (measureReal_biUnion_finset_le (Finset.range n) _).trans
    have heq (j : ℕ) : P.real {x | A < f (T^[j] x)} = P.real {x | A < f x} := by
      apply congrArg ENNReal.toReal
      exact (hT.iterate j).measure_preimage (measurableSet_lt measurable_const hfm).nullMeasurableSet
    simp_rw [heq]
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
  have hsub : initialAverageBad T f a n ⊆ initialAverageBad T g a n ∪ B := by
    intro x hx
    by_cases hb : x ∈ B
    · exact Or.inr hb
    · left
      obtain ⟨k,hk,hkn,hkw⟩ := hx
      refine ⟨k,hk,hkn,?_⟩
      have heq : ∑ j ∈ Finset.range k, g (T^[j] x) = ∑ j ∈ Finset.range k, f (T^[j] x) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply min_eq_left
        by_contra hbad
        exact hb (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr
          ((Finset.mem_range.mp hj).trans_le hkn),lt_of_not_ge hbad⟩⟩)
      rwa [heq]
  have havg := stationary_initial_average_bound P T hT g hgm hgi hg0 a ha n
  calc
    P.real (initialAverageBad T f a n) ≤
        P.real (initialAverageBad T g a n) + P.real B :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ truncatedMoment P f A/a + (n : ℝ)*truncatedMoment P f A/A := add_le_add havg hB
    _ = 2*truncatedMoment P f (a*n)/a := by dsimp [A]; field_simp; ring

lemma linear_envelope_of_tendsto (s : ℕ → ℝ) {m c C : ℝ}
    (hm : Tendsto (fun n : ℕ => s n / n) atTop (𝓝 m)) (hc : c < m) (hC : m < C) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ k : ℕ, c*k-b ≤ s k ∧ s k ≤ C*k+b := by
  have hh : ∀ᶠ k : ℕ in atTop, 0 < k ∧ c*k ≤ s k ∧ s k ≤ C*k := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),hm (Ioo_mem_nhds hc hC)] with k hk hkm
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    exact ⟨hk,(le_div_iff₀ hk').mp hkm.1.le,(div_le_iff₀ hk').mp hkm.2.le⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp hh
  let b : ℝ := ∑ k ∈ Finset.range K, (|c*k-s k|+|s k-C*k|)
  have hb : 0 ≤ b := Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨b,hb,?_⟩
  intro k
  by_cases hk : K ≤ k
  · obtain ⟨_,hl,hu⟩ := hK k hk
    constructor <;> linarith
  · have hkb : |c*k-s k|+|s k-C*k| ≤ b := by
      dsimp [b]
      exact Finset.single_le_sum (fun j _ => add_nonneg (abs_nonneg (c*j-s j))
        (abs_nonneg (s j-C*j))) (Finset.mem_range.mpr (Nat.lt_of_not_ge hk))
    constructor <;> linarith [le_abs_self (c*k-s k),le_abs_self (s k-C*k),
      abs_nonneg (c*k-s k),abs_nonneg (s k-C*k)]

end DirectionalZeroOne

end OAI
