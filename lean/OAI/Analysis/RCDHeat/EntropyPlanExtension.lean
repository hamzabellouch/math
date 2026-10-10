import Mathlib
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EntropyPlanExtension, LastMeeting, GeodesicSplice, CrossingGeometry, BoundedDensityLp. -/



namespace RegularPointCoordinates

section

open Set MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def entropyPlanExtension (μ : Measure X) (plan : Measure C(Time,X)) (t : ℝ) : ℝ :=
  boltzmannEntropy μ (plan.map (fun γ => geodesicExtension γ t))

omit [BorelSpace X] in
lemma entropyPlanExtension_eq (μ : Measure X) (plan : Measure C(Time,X)) (t : Time) :
    entropyPlanExtension μ plan t = boltzmannEntropy μ (plan.map (fun γ => γ t)) := by
  simp only [entropyPlanExtension,geodesicExtension_eq]

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def lastMeeting (b : Time) (z : C(Time,X) × C(Time,X)) : Time :=
  sSup {t : Time | t = 0 ∨ (t ≤ b ∧ z.1 t = z.2 t)}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lastMeeting_mem (b : Time) (z : C(Time,X) × C(Time,X)) :
    lastMeeting b z = 0 ∨ (lastMeeting b z ≤ b ∧ z.1 (lastMeeting b z) = z.2 (lastMeeting b z)) := by
  apply IsClosed.sSup_mem (s := {t : Time | t = 0 ∨ (t ≤ b ∧ z.1 t = z.2 t)})
    ⟨0,Or.inl rfl⟩
  exact isClosed_singleton.union (isClosed_Iic.inter (isClosed_eq z.1.continuous z.2.continuous))

omit [MeasurableSpace X] [BorelSpace X] in
lemma lastMeeting_le (b : Time) (z : C(Time,X) × C(Time,X)) : lastMeeting b z ≤ b := by
  rcases lastMeeting_mem b z with h | h
  · rw [h]; exact b.2.1
  · exact h.1

omit [MeasurableSpace X] [BorelSpace X] in
lemma lastMeeting_eq (b : Time) (z : C(Time,X) × C(Time,X)) (h0 : z.1 0 = z.2 0) :
    z.1 (lastMeeting b z) = z.2 (lastMeeting b z) := by
  rcases lastMeeting_mem b z with h | h
  · simpa only [h] using h0
  · exact h.2

omit [MeasurableSpace X] [BorelSpace X] in
lemma le_lastMeeting (b : Time) (z : C(Time,X) × C(Time,X)) {t : Time}
    (ht : t ≤ b) (he : z.1 t = z.2 t) : t ≤ lastMeeting b z :=
  le_sSup (Or.inr ⟨ht,he⟩)

omit [MeasurableSpace X] [BorelSpace X] in
lemma ne_after_lastMeeting (b : Time) (z : C(Time,X) × C(Time,X)) {t : Time}
    (ht : lastMeeting b z < t) (htb : t ≤ b) : z.1 t ≠ z.2 t := by
  intro he
  exact (not_lt_of_ge (le_lastMeeting b z htb he)) ht

omit [MeasurableSpace X] [BorelSpace X] in
lemma measurable_lastMeeting [SeparableSpace X] (b : Time) : Measurable (lastMeeting (X := X) b) := by
  apply measurable_of_Ici
  intro a
  have he : (lastMeeting (X := X) b) ⁻¹' Ici a =
      Prod.fst '' {w : (C(Time,X) × C(Time,X)) × Time |
        a ≤ w.2 ∧ (w.2 = 0 ∨ (w.2 ≤ b ∧ w.1.1 w.2 = w.1.2 w.2))} := by
    ext z
    constructor
    · intro hz
      exact ⟨(z,lastMeeting b z),⟨hz,lastMeeting_mem b z⟩,rfl⟩
    · rintro ⟨⟨z',t⟩,⟨ha,ht⟩,rfl⟩
      exact ha.trans (le_sSup ht)
  rw [he]
  apply IsClosed.measurableSet
  apply isClosedMap_fst_of_compactSpace
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_eq continuous_snd continuous_const).union
      ((isClosed_le continuous_snd continuous_const).inter
        (isClosed_eq (by fun_prop) (by fun_prop))))

noncomputable def spliceAt (γ η : C(Time,X)) (t : Time) (he : γ t = η t) : C(Time,X) := by
  classical
  exact ⟨(Iic t).piecewise γ η,γ.continuous.piecewise (fun u hu =>
    by have h : u = t := frontier_Iic_subset t hu; simpa only [h] using he) η.continuous⟩

omit [MeasurableSpace X] [BorelSpace X] in
lemma spliceAt_apply (γ η : C(Time,X)) (t : Time) (he : γ t = η t) (u : Time) :
    spliceAt γ η t he u = if u ≤ t then γ u else η u := by
  classical
  rfl

noncomputable def lastMeetingSplice (b : Time) (z : C(Time,X) × C(Time,X)) : C(Time,X) := by
  classical
  exact if h : z.1 0 = z.2 0 then
    spliceAt z.1 z.2 (lastMeeting b z) (lastMeeting_eq b z h) else z.1

lemma measurable_path_of_eval [CompleteSpace X] [SeparableSpace X] {A : Type*} [MeasurableSpace A]
    (f : A → C(Time,X)) (hf : ∀ t : Time, Measurable (fun a => f a t)) : Measurable f := by
  obtain ⟨d,hd⟩ := exists_dense_seq Time
  let e : C(Time,X) → ℕ → X := fun γ k => γ (d k)
  have hm : Measurable e := Measurable.of_eval fun k => measurable_path_eval (d k)
  have hinj : Function.Injective e := by
    intro γ η he
    apply ContinuousMap.ext
    have hh : (γ : Time → X) = η := hd.equalizer γ.continuous η.continuous he
    exact congrFun hh
  exact hm.measurableEmbedding hinj |>.measurable_comp_iff.mp
    (Measurable.of_eval fun k => hf (d k))

lemma measurable_lastMeetingSplice [CompleteSpace X] [SeparableSpace X] (b : Time) :
    Measurable (lastMeetingSplice (X := X) b) := by
  apply measurable_path_of_eval
  intro u
  have hh : MeasurableSet {z : C(Time,X) × C(Time,X) | z.1 0 = z.2 0} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
  have ht : MeasurableSet {z : C(Time,X) × C(Time,X) | u ≤ lastMeeting b z} :=
    measurableSet_le measurable_const (measurable_lastMeeting b)
  classical
  have he : (fun z : C(Time,X) × C(Time,X) => lastMeetingSplice b z u) =
    fun z => if z.1 0 = z.2 0 then (if u ≤ lastMeeting b z then z.1 u else z.2 u) else z.1 u := by
    funext z
    by_cases h0 : z.1 0 = z.2 0
    · simp only [lastMeetingSplice,dite_eq_left h0,ite_eq_left h0,spliceAt_apply]
    · simp only [lastMeetingSplice,dite_eq_right h0,ite_eq_right h0]
  rw [he]
  exact (((measurable_path_eval u).comp measurable_fst).piecewise ht
    ((measurable_path_eval u).comp measurable_snd)).piecewise hh
      ((measurable_path_eval u).comp measurable_fst)

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
lemma isGeodesic_of_upper (γ : C(Time,X))
    (h : ∀ s t : Time, dist (γ s) (γ t) ≤ |(s:ℝ)-(t:ℝ)| *dist (γ 0) (γ 1)) : IsGeodesic γ := by
  have hh (s t : Time) (hst : s ≤ t) :
      dist (γ s) (γ t) = |(s:ℝ)-(t:ℝ)| *dist (γ 0) (γ 1) := by
    apply le_antisymm (h s t)
    have h0 := h 0 s
    have h1 := h t 1
    simp only [show ((0:Time):ℝ)=0 from rfl,zero_sub,abs_neg,abs_of_nonneg s.2.1] at h0
    rw [show ((1:Time):ℝ)=1 from rfl,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr t.2.2)] at h1
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst))]
    have ht := dist_triangle (γ 0) (γ s) (γ 1)
    have hu := dist_triangle (γ s) (γ t) (γ 1)
    nlinarith only [h0,h1,ht,hu]
  intro s t
  rcases le_total s t with hst | hts
  · exact hh s t hst
  · simpa only [dist_comm,abs_sub_comm (t:ℝ)] using hh t s hts

omit [MeasurableSpace X] [BorelSpace X] in
lemma spliceAt_zero (γ η : C(Time,X)) (t : Time) (he : γ t = η t) :
    spliceAt γ η t he 0 = γ 0 := by
  rw [spliceAt_apply,ite_eq_left (show (0:Time) ≤ t from t.2.1)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma spliceAt_one (γ η : C(Time,X)) (t : Time) (he : γ t = η t) :
    spliceAt γ η t he 1 = η 1 := by
  rw [spliceAt_apply]
  split_ifs with ht
  · have hh : t = 1 := le_antisymm t.2.2 ht
    simpa only [hh] using he
  · rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma geodesic_speeds_equal_of_initial_segment (γ η : C(Time,X))
    (hg : IsGeodesic γ) (hη : IsGeodesic η) (a : Time) (ha : 0 < (a:ℝ))
    (h0 : γ 0 = η 0) (hea : γ a = η a) : dist (γ 0) (γ 1) = dist (η 0) (η 1) := by
  have hγa := hg 0 a
  have hηa := hη 0 a
  simp only [show ((0:Time):ℝ)=0 from rfl,zero_sub,abs_neg,abs_of_nonneg a.2.1,h0,hea] at hγa hηa
  rw [h0]
  nlinarith only [hγa,hηa,ha]

omit [MeasurableSpace X] [BorelSpace X] in
lemma isGeodesic_spliceAt (γ η : C(Time,X)) (hg : IsGeodesic γ) (hη : IsGeodesic η)
    (h0 : γ 0 = η 0) (hl : dist (γ 0) (γ 1) = dist (η 0) (η 1))
    (c : Time) (he : γ c = η c) : IsGeodesic (spliceAt γ η c he) := by
  let ξ := spliceAt γ η c he
  have hlen : dist (ξ 0) (ξ 1) = dist (η 0) (η 1) := by
    rw [spliceAt_zero,spliceAt_one,h0]
  have hh (s t : Time) (hst : s ≤ t) :
      dist (ξ s) (ξ t) ≤ |(s:ℝ)-(t:ℝ)| *dist (ξ 0) (ξ 1) := by
    rw [hlen]
    dsimp only [ξ]
    rw [spliceAt_apply,spliceAt_apply]
    by_cases hsc : s ≤ c
    · rw [ite_eq_left hsc]
      by_cases htc : t ≤ c
      · rw [ite_eq_left htc,hg,hl]
      · rw [ite_eq_right htc]
        have hct : c ≤ t := le_of_lt (lt_of_not_ge htc)
        have hh := dist_triangle (γ s) (γ c) (η t)
        rw [hg,he,hη,hl,abs_sub_comm (s:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (c:ℝ) from hsc)),
          abs_sub_comm (c:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (c:ℝ) ≤ (t:ℝ) from hct))] at hh
        rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst))]
        nlinarith only [hh]
    · have htc : ¬t ≤ c := fun ht => hsc (hst.trans ht)
      rw [ite_eq_right hsc,ite_eq_right htc,hη]
  apply isGeodesic_of_upper
  intro s t
  rcases le_total s t with hst | hts
  · exact hh s t hst
  · simpa only [dist_comm,abs_sub_comm (t:ℝ)] using hh t s hts

omit [MeasurableSpace X] [BorelSpace X] in
lemma lastMeetingSplice_properties (b : Time) (z : C(Time,X) × C(Time,X))
    (hg : IsGeodesic z.1) (hη : IsGeodesic z.2) (a : Time) (ha : 0 < (a:ℝ))
    (hag : ∀ t : Time, t ≤ a → z.1 t = z.2 t) :
    IsGeodesic (lastMeetingSplice b z) ∧ lastMeetingSplice b z 0 = z.1 0 ∧
    lastMeetingSplice b z 1 = z.2 1 ∧
    (∀ t : Time, t ≤ lastMeeting b z → lastMeetingSplice b z t = z.1 t) ∧
    (∀ t : Time, lastMeeting b z < t → t ≤ b → lastMeetingSplice b z t ≠ z.1 t) := by
  have h0 := hag 0 a.2.1
  have hl := geodesic_speeds_equal_of_initial_segment z.1 z.2 hg hη a ha h0 (hag a le_rfl)
  classical
  dsimp only [lastMeetingSplice]
  rw [dite_eq_left h0]
  refine ⟨isGeodesic_spliceAt z.1 z.2 hg hη h0 hl _ _,spliceAt_zero _ _ _ _,
    spliceAt_one _ _ _ _,?_,?_⟩
  · intro t ht
    rw [spliceAt_apply,ite_eq_left ht]
  · intro t ht htb
    rw [spliceAt_apply,ite_eq_right (not_le.mpr ht)]
    exact (ne_after_lastMeeting b z ht htb).symm

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

lemma weighted_square_equality {a A B c : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hA : 0 ≤ A) (_ : 0 ≤ B) (hc : 0 ≤ c)
    (hbound : c ≤ a*A+(1-a)*B) (heq : c^2 = a*A^2+(1-a)*B^2) :
    A = B ∧ c = A := by
  have hsq := mul_self_le_mul_self hc hbound
  have hp : a*(1-a)*(A-B)^2 ≤ 0 := by nlinarith only [hsq,heq]
  have ha' : 0 < a*(1-a) := mul_pos ha (sub_pos.mpr ha1)
  have hABsq : (A-B)^2 ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge hp) (mul_pos ha' (lt_of_not_ge hn))
  have hAB : A = B := by nlinarith only [hABsq,sq_nonneg (A-B)]
  refine ⟨hAB,?_⟩
  rw [←hAB] at heq
  nlinarith only [heq,hA,hc]

noncomputable def crossingSplice (a : Time) (z : C(Time,X) × C(Time,X)) : C(Time,X) := by
  classical
  exact if h : z.1 a = z.2 a then spliceAt z.1 z.2 a h else z.1

omit [MeasurableSpace X] [BorelSpace X] in
lemma crossingSplice_apply (a : Time) (z : C(Time,X) × C(Time,X))
    (he : z.1 a = z.2 a) (u : Time) :
    crossingSplice a z u = if u ≤ a then z.1 u else z.2 u := by
  classical
  simp only [crossingSplice,dite_eq_left he,spliceAt_apply]

lemma measurable_crossingSplice [CompleteSpace X] [SeparableSpace X] (a : Time) :
    Measurable (crossingSplice (X := X) a) := by
  apply measurable_path_of_eval
  intro u
  have hh : MeasurableSet {z : C(Time,X) × C(Time,X) | z.1 a = z.2 a} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
  classical
  have he : (fun z : C(Time,X) × C(Time,X) => crossingSplice a z u) =
      fun z => if z.1 a = z.2 a then (if u ≤ a then z.1 u else z.2 u) else z.1 u := by
    funext z
    by_cases h : z.1 a = z.2 a
    · simp only [crossingSplice,dite_eq_left h,ite_eq_left h,spliceAt_apply]
    · simp only [crossingSplice,dite_eq_right h,ite_eq_right h]
  rw [he]
  apply Measurable.piecewise hh _ ((measurable_path_eval u).comp measurable_fst)
  split_ifs
  · exact (measurable_path_eval u).comp measurable_fst
  · exact (measurable_path_eval u).comp measurable_snd

omit [MeasurableSpace X] [BorelSpace X] in
lemma isGeodesic_spliceAt_of_cross_length (γ η : C(Time,X))
    (hg : IsGeodesic γ) (hη : IsGeodesic η)
    (hl : dist (γ 0) (γ 1) = dist (η 0) (η 1))
    (hcross : dist (γ 0) (η 1) = dist (γ 0) (γ 1))
    (a : Time) (he : γ a = η a) : IsGeodesic (spliceAt γ η a he) := by
  let ξ := spliceAt γ η a he
  have hlen : dist (ξ 0) (ξ 1) = dist (γ 0) (γ 1) := by
    rw [spliceAt_zero,spliceAt_one,hcross]
  have hh (s t : Time) (hst : s ≤ t) :
      dist (ξ s) (ξ t) ≤ |(s:ℝ)-(t:ℝ)| *dist (ξ 0) (ξ 1) := by
    rw [hlen]
    dsimp only [ξ]
    rw [spliceAt_apply,spliceAt_apply]
    by_cases hsa : s ≤ a
    · rw [ite_eq_left hsa]
      by_cases hta : t ≤ a
      · rw [ite_eq_left hta,hg]
      · rw [ite_eq_right hta]
        have hat : a ≤ t := le_of_lt (lt_of_not_ge hta)
        have hh := dist_triangle (γ s) (γ a) (η t)
        rw [hg,he,hη,←hl,abs_sub_comm (s:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (a:ℝ) from hsa)),
          abs_sub_comm (a:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (a:ℝ) ≤ (t:ℝ) from hat))] at hh
        rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst))]
        nlinarith only [hh]
    · have hta : ¬t ≤ a := fun ht => hsa (hst.trans ht)
      rw [ite_eq_right hsa,ite_eq_right hta,hη,←hl]
  apply isGeodesic_of_upper
  intro s t
  rcases le_total s t with hst | hts
  · exact hh s t hst
  · simpa only [dist_comm,abs_sub_comm (t:ℝ)] using hh t s hts

omit [MeasurableSpace X] [BorelSpace X] in
lemma crossing_geodesic_distance_bound (γ η : C(Time,X)) (hg : IsGeodesic γ)
    (hη : IsGeodesic η) (a : Time) (he : γ a = η a) :
    dist (γ 0) (η 1) ≤ (a:ℝ)*dist (γ 0) (γ 1)+(1-(a:ℝ))*dist (η 0) (η 1) := by
  have hh := dist_triangle (γ 0) (γ a) (η 1)
  rw [hg,he,hη] at hh
  simpa only [show ((0:Time):ℝ)=0 from rfl,show ((1:Time):ℝ)=1 from rfl,
    zero_sub,abs_neg,abs_of_nonneg a.2.1,abs_sub_comm (a:ℝ),abs_of_nonneg (sub_nonneg.mpr a.2.2)] using hh

end

 

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
variable {X : Type*} [MeasurableSpace X]

theorem bounded_density_lp_realization (μ ν : Measure X) [SigmaFinite μ]
    [IsProbabilityMeasure ν] {C : ℝ} (hC : 0 ≤ C)
    (hν : ν ≤ ENNReal.ofReal C • μ) {S : Set X} (hS : MeasurableSet S)
    (hSf : μ S ≠ ∞) (hs : ∀ᵐ x ∂ν, x ∈ S) :
    ∃ f : Lp ℝ 2 μ, 0 ≤ f ∧ (∀ᵐ x ∂μ, f x ≤ C) ∧
      (∫ x, f x ∂μ) = 1 ∧ (∀ᵐ x ∂μ, f x ≠ 0 → x ∈ S) ∧
      μ.withDensity (fun x => ENNReal.ofReal (f x)) = ν := by
  have hac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  let ρ : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hρm : Measurable ρ := (ν.measurable_rnDeriv μ).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun _ => ENNReal.toReal_nonneg
  have hρC : ∀ᵐ x ∂μ, ρ x ≤ C := by
    filter_upwards [rnDeriv_le_const_of_le_smul μ ν hν] with x hx
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx)
      ENNReal.ofReal_ne_top).mpr hx |>.trans_eq (ENNReal.toReal_ofReal hC)
  have hρs : ∀ᵐ x ∂μ, ρ x ≠ 0 → x ∈ S := by
    filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae (μ := ν) μ hs] with x hx
    intro hz
    apply hx
    intro he
    apply hz
    simp [ρ,he]
  have hρ : MemLp ρ 2 μ := by
    apply (memLp_indicator_const (μ := μ) 2 hS C (Or.inr hSf)).mono' hρm.aestronglyMeasurable
    filter_upwards [hρC,hρs] with x hx hsx
    rw [Real.norm_eq_abs,abs_of_nonneg (hρ0 x)]
    by_cases hxS : x ∈ S
    · simpa only [indicator_of_mem hxS] using hx
    · rw [indicator_of_notMem hxS]
      have hz : ρ x = 0 := by_contra (fun hn => hxS (hsx hn))
      exact hz.le
  refine ⟨hρ.toLp ρ,?_,?_,?_,?_,?_⟩
  · apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hρ.coeFn_toLp] with x hx
    rw [hx]
    exact hρ0 x
  · exact hρ.coeFn_toLp.le.trans hρC
  · rw [integral_congr_ae hρ.coeFn_toLp]
    simpa [ρ,Measure.real,measure_univ] using Measure.integral_toReal_rnDeriv hac
  · filter_upwards [hρ.coeFn_toLp,hρs] with x hx hsx
    rwa [hx]
  · rw [withDensity_congr_ae (hρ.coeFn_toLp.mono fun x hx => congrArg ENNReal.ofReal hx)]
    calc
      μ.withDensity (fun x => ENNReal.ofReal (ρ x)) = μ.withDensity (ν.rnDeriv μ) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
        exact ENNReal.ofReal_toReal hx.ne
      _ = ν := Measure.withDensity_rnDeriv_eq _ _ hac


end RegularPointCoordinates

end OAI
