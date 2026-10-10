import OAI.Analysis.RotationWeights.PhaseWeights

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

section
def negLower (α s : ℝ) : ℝ := max 0 (s-1+α)
def negUpper (ℓ α s : ℝ) : ℝ :=
  min 1 (min (s-α) (min (ℓ*s/(1+ℓ)) (ℓ*(1-s)/(1-ℓ))))

lemma neg_support_strict {ℓ α s t : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1) :
    (0<t ∧ t<1 ∧ α<delta (s-t) ∧ t<ℓ*delta (s-t)) ↔
      t ∈ Ioo (negLower α s) (negUpper ℓ α s) := by
  have hp : 0<1+ℓ := by linarith
  have hm : 0<1-ℓ := by linarith
  simp only [negLower,negUpper,mem_Ioo,max_lt_iff,lt_min_iff,
    delta, mul_min_of_nonneg _ _ hℓ.le,lt_div_iff₀ hp,lt_div_iff₀ hm]
  constructor
  · rintro ⟨ht0,ht1,⟨hα1,hα2⟩,⟨ha,hb⟩⟩
    refine ⟨⟨ht0,by linarith⟩,ht1,by linarith,?_,?_⟩ <;> nlinarith
  · rintro ⟨⟨ht0,ha⟩,ht1,hb,hc,hd⟩
    refine ⟨ht0,ht1,⟨by linarith,by linarith⟩,?_,?_⟩ <;> nlinarith

def negArcLeft (ℓ α s r : ℝ) : Set ℝ :=
  Ioo (negLower α s) (min (negUpper ℓ α s) (min (s-1+1/(ℓ*r)) (s-1/2)))
def negArcRight (ℓ α s r : ℝ) : Set ℝ :=
  Ioo (max (negLower α s) (max (s-1/(ℓ*r)) (s-1/2))) (negUpper ℓ α s)

lemma negative_superlevel_intervals {ℓ α s t r : ℝ}
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hr : 0<r)
    (ht : t∈Ico 0 1) (hne1 : t≠s-α) (hne2 : t≠s-1+α)
    (hne3 : t≠s-1/2) :
    r < weight ℓ α (s-t) t ↔ t∈negArcLeft ℓ α s r ∪ negArcRight ℓ α s r := by
  have hdc : α ≤ delta (s-t) ↔ α < delta (s-t) := by
    constructor
    · intro h
      obtain ⟨h1,h2⟩ := le_min_iff.mp h
      apply lt_min
      · exact lt_of_le_of_ne h1 (by intro he; apply hne1; linarith)
      · exact lt_of_le_of_ne h2 (by intro he; apply hne2; linarith)
    · exact le_of_lt
  have hrℓ : 0<ℓ*r := mul_pos hℓ hr
  have hinv {d : ℝ} (hd : 0<d) : r<1/(ℓ*d) ↔ d<1/(ℓ*r) := by
    rw [lt_div_iff₀ (mul_pos hℓ hd),lt_div_iff₀ hrℓ]
    constructor <;> intro h <;> nlinarith
  have hw : r<weight ℓ α (s-t) t ↔
      (0<t ∧ t<1 ∧ α<delta (s-t) ∧ t<ℓ*delta (s-t)) ∧
        delta (s-t)<1/(ℓ*r) := by
    unfold weight
    split_ifs with h
    · rw [hinv (lt_of_lt_of_le hα h.1)]
      simp only [h.2.1,ht.2,hdc.mp h.1,h.2.2,true_and]
    · constructor
      · exact fun h0 ↦ (not_lt_of_ge hr.le h0).elim
      · rintro ⟨⟨h0,_,ha,hb⟩,_⟩
        exact (h ⟨ha.le,h0,hb⟩).elim
  rw [hw,neg_support_strict hℓ hℓ1]
  simp only [negArcLeft,negArcRight,mem_union,mem_Ioo,max_lt_iff,lt_min_iff]
  obtain ht' | ht' : t<s-1/2 ∨ s-1/2<t := lt_or_gt_of_ne hne3
  · have he : delta (s-t)=1-(s-t) := by
      apply min_eq_right
      linarith
    rw [he]
    constructor
    · rintro ⟨⟨ha,hb⟩,hc⟩
      exact Or.inl ⟨ha,hb,by linarith,ht'⟩
    · rintro (⟨ha,hb,hc,_⟩ | ⟨⟨_,_,hc⟩,_⟩)
      · exact ⟨⟨ha,hb⟩,by linarith⟩
      · linarith
  · have he : delta (s-t)=s-t := by
      apply min_eq_left
      linarith
    rw [he]
    constructor
    · rintro ⟨⟨ha,hb⟩,hc⟩
      exact Or.inr ⟨⟨ha,by linarith,ht'⟩,hb⟩
    · rintro (⟨_,_,_,hc⟩ | ⟨⟨ha,hc,_⟩,hb⟩)
      · linarith
      · exact ⟨⟨ha,hb⟩,by linarith⟩

lemma negArcs_sub_Ioo (ℓ α s r : ℝ) :
    negArcLeft ℓ α s r ⊆ Ioo 0 1 ∧ negArcRight ℓ α s r ⊆ Ioo 0 1 := by
  constructor
  · intro t ht
    exact ⟨(le_max_left _ _).trans_lt ht.1,
      ht.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
  · intro t ht
    exact ⟨((le_max_left _ _).trans (le_max_left _ _)).trans_lt ht.1,
      ht.2.trans_le (min_le_left _ _)⟩

lemma negArcs_disjoint (ℓ α s r : ℝ) :
    Disjoint (negArcLeft ℓ α s r) (negArcRight ℓ α s r) := by
  apply disjoint_left.mpr
  intro t ht hu
  have ht' : t < s-1/2 := ht.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hu' : s-1/2 < t := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hu.1
  exact (lt_asymm ht' hu')

lemma preimage_repr_interval {a b : ℝ} (ha : 0≤a) (hb : b≤1) :
    repr ⁻¹' Ioo a b = ((↑) : ℝ → CircleX) '' Ioo a b := by
  ext x
  constructor
  · intro hx
    exact ⟨repr x,hx,coe_repr x⟩
  · rintro ⟨t,ht,rfl⟩
    change repr (t : CircleX) ∈ Ioo a b
    rw [repr_coe ⟨ha.trans ht.1.le,ht.2.trans_le hb⟩]
    exact ht

lemma repr_ne_ae (a : ℝ) : ∀ᵐ t : CircleX, repr t ≠ a := by
  have h : ∀ᵐ t : CircleX, t ≠ (a : CircleX) := by
    rw [ae_iff]
    simpa using volume_singleton_zero (a : CircleX)
  filter_upwards [h] with t ht he
  apply ht
  rw [← coe_repr t,he]

lemma uNeg_superlevel_ae {ℓ α r : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1)
    (hα : 0<α) (hr : 0<r) (s : CircleX) :
    {t | r<uNeg ℓ α s t} =ᵐ[volume]
      repr ⁻¹' (negArcLeft ℓ α (repr s) r ∪ negArcRight ℓ α (repr s) r) := by
  filter_upwards [repr_ne_ae (repr s-α),repr_ne_ae (repr s-1+α),
    repr_ne_ae (repr s-1/2)] with t h1 h2 h3
  apply propext
  have hu := uNeg_unwrapped hℓ hℓ1 hα (repr_mem s) (repr_mem t)
  rw [coe_repr,coe_repr] at hu
  rw [hu]
  exact negative_superlevel_intervals hℓ hℓ1 hα hr (repr_mem t) h1 h2 h3

lemma interval_image_ball (a b : ℝ) :
    ((↑) : ℝ → CircleX) '' Ioo a b = Metric.ball (((a+b)/2 : ℝ) : CircleX) ((b-a)/2) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, ← AddCircle.coe_sub]
    apply lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm)
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  · intro hx
    obtain ⟨t⟩ := x
    change (t : CircleX) ∈ Metric.ball (((a+b)/2 : ℝ) : CircleX) ((b-a)/2) at hx
    change (t : CircleX) ∈ ((↑) : ℝ → CircleX) '' Ioo a b
    rw [Metric.mem_ball, dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hx
    simp only [inv_one, one_mul, mul_one] at hx
    let u : ℝ := t - (round (t - (a+b)/2) : ℤ)
    refine ⟨u, ?_, ?_⟩
    · rw [mem_Ioo]
      have hu : |u - (a+b)/2| < (b-a)/2 := by
        convert! hx using 1
        congr 1
        dsimp [u]
        ring
      rw [abs_lt] at hu
      dsimp [u] at *
      constructor <;> linarith [hu.1, hu.2]
    · dsimp [u]
      have hz (z : ℤ) : ((z : ℝ) : CircleX) = 0 := by
        apply (AddCircle.coe_eq_zero_iff 1).mpr
        exact ⟨z, by simp⟩
      rw [hz, sub_zero]

def IsTwoArcs (A : Set CircleX) : Prop :=
  ∃ (c d : CircleX) (r q : ℝ),
    Disjoint (Metric.ball c r) (Metric.ball d q) ∧
    A =ᵐ[volume] (Metric.ball c r ∪ Metric.ball d q : Set CircleX)

lemma uNeg_isTwoArcs {ℓ α r : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1)
    (hα : 0<α) (hr : 0<r) (s : CircleX) :
    IsTwoArcs {t | r<uNeg ℓ α s t} := by
  let a := negLower α (repr s)
  let b := min (negUpper ℓ α (repr s)) (min (repr s-1+1/(ℓ*r)) (repr s-1/2))
  let c := max (negLower α (repr s)) (max (repr s-1/(ℓ*r)) (repr s-1/2))
  let d := negUpper ℓ α (repr s)
  have hA : repr ⁻¹' negArcLeft ℓ α (repr s) r =
      Metric.ball (((a+b)/2 : ℝ) : CircleX) ((b-a)/2) := by
    change repr ⁻¹' Ioo a b = _
    rw [preimage_repr_interval (show 0≤a from le_max_left _ _)
      (show b≤1 from (min_le_left _ _).trans (min_le_left _ _)),interval_image_ball]
  have hB : repr ⁻¹' negArcRight ℓ α (repr s) r =
      Metric.ball (((c+d)/2 : ℝ) : CircleX) ((d-c)/2) := by
    change repr ⁻¹' Ioo c d = _
    rw [preimage_repr_interval (show 0≤c from (le_max_left _ _).trans (le_max_left _ _))
      (show d≤1 from min_le_left _ _),interval_image_ball]
  refine ⟨(((a+b)/2 : ℝ) : CircleX),(((c+d)/2 : ℝ) : CircleX),(b-a)/2,(d-c)/2,?_,?_⟩
  · rw [←hA,←hB]
    exact Disjoint.preimage repr (negArcs_disjoint ℓ α (repr s) r)
  · rw [←hA,←hB,←preimage_union]
    exact uNeg_superlevel_ae hℓ hℓ1 hα hr s

lemma uPos_isTwoArcs {ℓ α r : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1)
    (_hα : 0<α) (hr : 0<r) (s : CircleX) :
    IsTwoArcs {t | r<uPos ℓ α s t} := by
  classical
  by_cases h : α≤delta (repr s) ∧ r<1/(ℓ*delta (repr s))
  · let b := ℓ*delta (repr s)
    have hb1 : b<1 := by
      have hd := delta_le_half (repr s)
      dsimp [b]
      nlinarith
    have he : {t | r<uPos ℓ α s t} = repr ⁻¹' Ioo 0 b := by
      ext t
      simp only [uPos,weight,mem_ofPred_eq,mem_preimage,mem_Ioo]
      split_ifs with ht
      · exact iff_of_true h.2 ht.2
      · constructor
        · exact fun hh ↦ (not_lt_of_ge hr.le hh).elim
        · exact fun hh ↦ (ht ⟨h.1,hh⟩).elim
    refine ⟨(((0+b)/2 : ℝ) : CircleX),0,(b-0)/2,0,?_,?_⟩
    · simp
    · rw [he,preimage_repr_interval le_rfl hb1.le,interval_image_ball]
      simp only [Metric.ball_zero,union_empty]
      exact Filter.EventuallyEq.rfl
  · have he : {t | r<uPos ℓ α s t} = ∅ := by
      ext t
      simp only [uPos,weight,mem_ofPred_eq,mem_empty_iff_false,iff_false]
      split_ifs with ht
      · exact fun hr' ↦ h ⟨ht.1,hr'⟩
      · exact not_lt_of_ge hr.le
    refine ⟨0,0,0,0,by simp,?_⟩
    simp only [he,Metric.ball_zero,union_empty]
    exact Filter.EventuallyEq.rfl


lemma prod_eventuallyEq_of_marginals {μ : Measure (CircleX × CircleX)}
    (hμ1 : Measure.map Prod.fst μ ≪ (volume : Measure CircleX))
    (hμ2 : Measure.map Prod.snd μ ≪ (volume : Measure CircleX))
    {A A' B B' : Set CircleX} (hA : A =ᵐ[volume] A') (hB : B =ᵐ[volume] B') :
    A ×ˢ B =ᵐ[μ] A' ×ˢ B' := by
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable (hμ1.ae_le hA),
    ae_of_ae_map measurable_snd.aemeasurable (hμ2.ae_le hB)] with z hz1 hz2
  apply propext
  change (z.1∈A ∧ z.2∈B) ↔ (z.1∈A' ∧ z.2∈B')
  rw [show (z.1∈A)=(z.1∈A') from hz1,show (z.2∈B)=(z.2∈B') from hz2]

lemma disjoint_prod_of_left {X : Type uX} {Y : Type uY} {A B : Set X} (C D : Set Y)
    (h : Disjoint A B) : Disjoint (A ×ˢ C) (B ×ˢ D) := by
  exact disjoint_left.mpr fun _ hx hy ↦ disjoint_left.mp h hx.1 hy.1
lemma disjoint_prod_of_right {X : Type uX} {Y : Type uY} (A B : Set X) {C D : Set Y}
    (h : Disjoint C D) : Disjoint (A ×ˢ C) (B ×ˢ D) := by
  exact disjoint_left.mpr fun _ hx hy ↦ disjoint_left.mp h hx.2 hy.2

lemma measureReal_two_unions (μ : Measure (CircleX × CircleX)) [IsFiniteMeasure μ]
    {A B C D : Set CircleX} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hAB : Disjoint A B) (hCD : Disjoint C D) :
    μ.real ((A∪B) ×ˢ (C∪D)) =
      (μ.real (A×ˢC)+μ.real (A×ˢD)) + (μ.real (B×ˢC)+μ.real (B×ˢD)) := by
  rw [union_prod, measureReal_union (disjoint_prod_of_left _ _ hAB) (hB.prod (hC.union hD)),
    prod_union,measureReal_union (disjoint_prod_of_right _ _ hCD) (hA.prod hD),
    prod_union,measureReal_union (disjoint_prod_of_right _ _ hCD) (hB.prod hD)]

lemma twoArcs_rectangle_discrepancy {μ ν : Measure (CircleX × CircleX)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ1 : Measure.map Prod.fst μ ≪ (volume : Measure CircleX))
    (hμ2 : Measure.map Prod.snd μ ≪ (volume : Measure CircleX))
    (hν1 : Measure.map Prod.fst ν ≪ (volume : Measure CircleX))
    (hν2 : Measure.map Prod.snd ν ≪ (volume : Measure CircleX))
    {ε : ℝ} (hdisc : ∀ c d : CircleX, ∀ r q : ℝ,
      |μ.real (Metric.ball c r ×ˢ Metric.ball d q) -
       ν.real (Metric.ball c r ×ˢ Metric.ball d q)| ≤ ε)
    {A B : Set CircleX} (hA : IsTwoArcs A) (hB : IsTwoArcs B) :
    |μ.real (A×ˢB)-ν.real (A×ˢB)| ≤ 4*ε := by
  obtain ⟨c,d,r,q,hcd,hA⟩ := hA
  obtain ⟨e,f,s,t,hef,hB⟩ := hB
  rw [measureReal_congr (prod_eventuallyEq_of_marginals hμ1 hμ2 hA hB),
    measureReal_congr (prod_eventuallyEq_of_marginals hν1 hν2 hA hB),
    measureReal_two_unions μ measurableSet_ball measurableSet_ball measurableSet_ball
      measurableSet_ball hcd hef,
    measureReal_two_unions ν measurableSet_ball measurableSet_ball measurableSet_ball
      measurableSet_ball hcd hef]
  have h1 := abs_le.mp (hdisc c e r s)
  have h2 := abs_le.mp (hdisc c f r t)
  have h3 := abs_le.mp (hdisc d e q s)
  have h4 := abs_le.mp (hdisc d f q t)
  rw [abs_le]
  constructor <;> linarith

end

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

lemma boundedLayercake {f : Ω → ℝ} {B : ℝ}
    (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    ∫ x, f x ∂μ = ∫ t in Ioc 0 B, μ.real {x | t < f x} := by
  rw [hfi.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf0)]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi
    Ioc_subset_Ioi_self
  apply Filter.Eventually.of_forall
  intro t ht
  have hBt : B < t := lt_of_not_ge (fun h ↦ ht.2 ⟨ht.1, h⟩)
  have he : {x | t < f x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt.mpr (le_trans (hfB x) (le_of_lt hBt))
  simp [he]

lemma boundedLayercake_weighted [IsFiniteMeasure μ] {f g : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B) :
    ∫ x, f x * g x ∂μ =
      ∫ s in Ioc 0 B, ∫ x in {x | s < f x}, g x ∂μ := by
  have hi : Integrable (fun z : ℝ × Ω ↦
      if z.1 < f z.2 then g z.2 else 0)
      ((volume.restrict (Ioc 0 B)).prod μ) :=
    Integrable.of_bound
      ((hg.comp measurable_snd).ite
        (measurableSet_lt measurable_fst (hf.comp measurable_snd)) measurable_const).aestronglyMeasurable B (Filter.Eventually.of_forall fun z ↦ by
        split_ifs
        · simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 z.2)] using hgB z.2
        · simp only [norm_zero]
          by_cases h : Nonempty Ω
          · exact le_trans (hg0 (Classical.choice h)) (hgB (Classical.choice h))
          · exact False.elim (h ⟨z.2⟩))
  have he : (fun s : ℝ ↦ ∫ x in {x | s < f x}, g x ∂μ) =
      (fun s ↦ ∫ x, (if s < f x then g x else 0) ∂μ) := by
    funext s
    rw [← integral_indicator (measurableSet_lt measurable_const hf)]
    rfl
  rw [he, integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hset : (Ioc 0 B ∩ Iio (f x)) = Ioo 0 (f x) := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, le_trans (le_of_lt h.2) (hfB x)⟩, h.2⟩
  have hid : (fun s : ℝ ↦ if s < f x then g x else 0) =
      (Iio (f x)).indicator (fun _ ↦ g x) := rfl
  change f x * g x = ∫ s in Ioc 0 B, if s < f x then g x else 0
  rw [hid, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, hset, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (hf0 x),
    smul_eq_mul]

lemma boundedLayercake_product [IsFiniteMeasure μ] {f g : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B) :
    ∫ x, f x * g x ∂μ =
      ∫ s in Ioc 0 B, ∫ t in Ioc 0 B, μ.real {x | s < f x ∧ t < g x} := by
  rw [boundedLayercake_weighted hf hg hf0 hfB hg0 hgB]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hgi : Integrable g (μ.restrict {x | s < f x}) :=
    Integrable.of_bound hg.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hgB x)
  dsimp only
  rw [boundedLayercake hgi hg0 hgB]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [Measure.real, Measure.restrict_apply (measurableSet_lt measurable_const hg)]
  congr 2
  ext x
  exact and_comm

lemma integrable_superlevel_measure [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) (B : ℝ) :
    Integrable (fun z : ℝ × ℝ ↦ μ.real {x | z.1 < f x ∧ z.2 < g x})
      ((volume.restrict (Ioc 0 B)).prod (volume.restrict (Ioc 0 B))) := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ μ {x | z.1 < f x ∧ z.2 < g x}) :=
    measurable_measure_prodMk_left
      ((measurableSet_lt (measurable_fst.comp measurable_fst)
        (hf.comp measurable_snd)).inter
       (measurableSet_lt (measurable_snd.comp measurable_fst)
        (hg.comp measurable_snd)))
  exact Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable (μ.real univ)
      (Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_mono (subset_univ _))

lemma superlevel_discrepancy [IsFiniteMeasure μ] {ν : Measure Ω} [IsFiniteMeasure ν]
    {f g : Ω → ℝ} {B ε : ℝ} (hB : 0 ≤ B)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B)
    (hdisc : ∀ s ∈ Ioc 0 B, ∀ t ∈ Ioc 0 B,
      |μ.real {x | s < f x ∧ t < g x} - ν.real {x | s < f x ∧ t < g x}| ≤ ε) :
    |(∫ x, f x * g x ∂μ) - (∫ x, f x * g x ∂ν)| ≤ B ^ 2 * ε := by
  rw [boundedLayercake_product hf hg hf0 hfB hg0 hgB,
    boundedLayercake_product hf hg hf0 hfB hg0 hgB]
  have hiμ := integrable_superlevel_measure (μ := μ) hf hg B
  have hiν := integrable_superlevel_measure (μ := ν) hf hg B
  rw [integral_integral hiμ, integral_integral hiν, ← integral_sub hiμ hiν,
    ← Real.norm_eq_abs]
  have hb : ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioc 0 B)).prod
      (volume.restrict (Ioc 0 B))),
      ‖μ.real {x | z.1 < f x ∧ z.2 < g x} -
        ν.real {x | z.1 < f x ∧ z.2 < g x}‖ ≤ ε := by
    have hm : ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioc 0 B)).prod
        (volume.restrict (Ioc 0 B))), z ∈ Ioc 0 B ×ˢ Ioc 0 B := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioc.prod measurableSet_Ioc)]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ⟨hs, ht⟩
    filter_upwards [hm] with z hz
    exact hdisc z.1 hz.1 z.2 hz.2
  convert! norm_integral_le_of_norm_le (integrable_const ε) hb using 1
  simp [Measure.prod_apply, Measure.real, Real.volume_Ioc, hB, pow_two, mul_assoc]



end CircleSampling

end

end OAI
