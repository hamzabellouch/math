import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.OptionalPastPalm

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Classical
namespace SLEExactGauge.CandidateCover
open Deterministic

lemma closedBall_subset_triple_of_inter {X : Type*} [PseudoMetricSpace X]
    {x y : X} {r s : ℝ} (hrs : r ≤ s)
    (hi : ¬Disjoint (closedBall x r) (closedBall y s)) :
    closedBall x r ⊆ closedBall y (3*s) := by
  obtain ⟨z,hzx,hzy⟩ := Set.not_disjoint_iff.mp hi
  apply closedBall_subset_closedBall'
  have hd : dist x y ≤ r+s :=
    (dist_triangle_left x y z).trans (add_le_add hzx hzy)
  linarith

 

theorem finite_disjoint_triples {X ι : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (x : ι→X) (r : ι→ℝ) (hr : ∀i∈s,0 ≤ r i) :
    ∃t : Finset ι,t ⊆ s ∧
      ((t : Set ι).PairwiseDisjoint (fun i=>closedBall (x i) (r i))) ∧
      ∀i∈s,∃j∈t,closedBall (x i) (r i) ⊆ closedBall (x j) (3*r j) := by
  revert hr
  refine Finset.strongInductionOn s ?_
  intro s ih hr
  by_cases hs : s.Nonempty
  · obtain ⟨a,ha,hmax⟩ := s.exists_max_image r hs
    let s' := s.filter (fun i=>Disjoint (closedBall (x i) (r i)) (closedBall (x a) (r a)))
    have hstrict : s' ⊂ s := by
      apply Finset.filter_ssubset.mpr
      refine ⟨a,ha,?_⟩
      intro hd
      have hx : x a∈closedBall (x a) (r a) := mem_closedBall_self (hr a ha)
      exact Set.disjoint_left.mp hd hx hx
    obtain ⟨t,ht,hd,hcover⟩ := ih s' hstrict (fun i hi=>hr i (Finset.mem_filter.mp hi).1)
    refine ⟨insert a t,?_,?_,?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with hia | hit
      · simpa only [hia] using ha
      · exact (Finset.mem_filter.mp (ht hit)).1
    · rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
      refine ⟨hd,?_⟩
      intro j hj _
      exact (Finset.mem_filter.mp (ht hj)).2.symm
    · intro i hi
      by_cases hi' : i∈s'
      · obtain ⟨j,hj,hij⟩ := hcover i hi'
        exact ⟨j,Finset.mem_insert_of_mem hj,hij⟩
      · have hn : ¬Disjoint (closedBall (x i) (r i)) (closedBall (x a) (r a)) := by
          intro hdi
          exact hi' (Finset.mem_filter.mpr ⟨hi,hdi⟩)
        exact ⟨a,Finset.mem_insert_self _ _,closedBall_subset_triple_of_inter (hmax i hi) hn⟩
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    exact ⟨∅,by simp,by simp,by simp⟩

lemma ediam_closedBall_le_of_nonneg {X : Type*} [PseudoMetricSpace X]
    (x : X) (r : ℝ) : ediam (closedBall x r) ≤ ENNReal.ofReal (2*r) := by
  apply ediam_le_of_forall_dist_le
  intro y hy z hz
  change dist y x ≤ r at hy
  change dist z x ≤ r at hz
  exact (dist_triangle_right y z x).trans (by linarith : dist y x+dist z x ≤ 2*r)

lemma diameterCost_le_radius {h : ℝ→ℝ} (hh : Target.IsHausdorffGauge h)
    {D : ℝ≥0∞} {R : ℝ} (hR : 0 ≤ R) (hD : D ≤ ENNReal.ofReal R) :
    diameterCost h D ≤ ENNReal.ofReal (h R) := by
  have hDfin : D≠∞ := (hD.trans_lt ENNReal.ofReal_lt_top).ne
  rw [diameterCost,ite_eq_right hDfin]
  apply ENNReal.ofReal_le_ofReal
  apply hh.2.1 ENNReal.toReal_nonneg hR
  simpa only [ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hD

lemma disjoint_charge {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (t : Finset ι) (A : ι→Set X)
    (hm : ∀i∈t,MeasurableSet (A i)) (hd : (t : Set ι).PairwiseDisjoint A)
    (B : Set X) (hB : ∀i∈t,A i ⊆ B) (cost : ι→ℝ≥0∞) (C : ℝ≥0∞)
    (hcost : ∀i∈t,cost i ≤ C*μ (A i)) :
    (∑i∈t,cost i) ≤ C*μ B := by
  calc
    (∑i∈t,cost i) ≤ ∑i∈t,C*μ (A i) := Finset.sum_le_sum hcost
    _ = C*(∑i∈t,μ (A i)) := (Finset.mul_sum t _ C).symm
    _ = C*μ (⋃i∈t,A i) := by rw [measure_biUnion_finset hd hm]
    _ ≤ C*μ B := mul_le_mul le_rfl (measure_mono (iUnion₂_subset hB)) zero_le zero_le

 

theorem finite_candidate_charge {X ι : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : Finset ι) (x : ι→X) (r : ι→ℝ)
    (hr : ∀i∈s,0 ≤ r i) (H B : Set X) (hH : MeasurableSet H)
    (hB : ∀i∈s,closedBall (x i) (r i)∩H ⊆ B)
    (cost : ι→ℝ≥0∞) (C : ℝ≥0∞)
    (hc : ∀i∈s,cost i ≤ C*μ (closedBall (x i) (r i)∩H)) :
    ∃t : Finset ι,t ⊆ s ∧
      ((t : Set ι).PairwiseDisjoint (fun i=>closedBall (x i) (r i))) ∧
      (∀i∈s,∃j∈t,closedBall (x i) (r i) ⊆ closedBall (x j) (3*r j)) ∧
      (∑i∈t,cost i) ≤ C*μ B := by
  obtain ⟨t,ht,hd,hcover⟩ := finite_disjoint_triples s x r hr
  refine ⟨t,ht,hd,hcover,?_⟩
  apply disjoint_charge μ t (fun i=>closedBall (x i) (r i)∩H)
    (fun _ _=>measurableSet_closedBall.inter hH)
    (hd.mono (fun _=>inter_subset_left)) B (fun i hi=>hB i (ht hi)) cost C
  exact fun i hi=>hc i (ht hi)

lemma quadratic_multiple_le {ι : Type*} [Nonempty ι] (d : ℝ) (b ρ : ι→ℝ)
    (hb : ∀i,0 ≤ b i) (hρ : ∀i,0<ρ i) (C : ℝ) (hC : 1 ≤ C) (i : ι) :
    QuadraticGauge.gauge d b ρ (C*ρ i) ≤ C^2*b i*(ρ i)^d := by
  calc
    _ ≤ QuadraticGauge.entry d (b i) (ρ i) (C*ρ i) :=
      QuadraticGauge.gauge_le_entry hb hρ _ i
    _ = _ := by
      unfold QuadraticGauge.entry
      rw [mul_div_cancel_right₀ C (hρ i).ne',max_eq_right (by nlinarith : 1 ≤ C^2)]
      ring

 

lemma quadratic_candidate_cost {ι : Type*} [Nonempty ι]
    (d : ℝ) (b ρ : ι→ℝ) (hb : ∀i,0 ≤ b i) (hρ : ∀i,0<ρ i)
    (hh : Target.IsHausdorffGauge (QuadraticGauge.gauge d b ρ))
    (μ : Measure ℂ) (H : Set ℂ) (z : ℂ) (i : ι) (A c : ℝ)
    (hA : 1 ≤ A) (hc : 0<c)
    (hqual : ENNReal.ofReal (c*b i*(ρ i)^d) ≤ μ (closedBall z (A*ρ i)∩H)) :
    diameterCost (QuadraticGauge.gauge d b ρ) (ediam (closedBall z (3*(A*ρ i)))) ≤
      ENNReal.ofReal ((6*A)^2/c)*μ (closedBall z (A*ρ i)∩H) := by
  have hmul : (6*A)^2/c*(c*b i*(ρ i)^d)=(6*A)^2*b i*(ρ i)^d := by
    field_simp
  have hscale : 1 ≤ 6*A := by linarith
  have hR : 0 ≤ 6*A*ρ i := by have := hρ i; positivity
  calc
    _ ≤ ENNReal.ofReal (QuadraticGauge.gauge d b ρ ((6*A)*ρ i)) :=
      diameterCost_le_radius hh hR (by
        convert ediam_closedBall_le_of_nonneg z (3*(A*ρ i)) using 1; ring_nf)
    _ ≤ ENNReal.ofReal ((6*A)^2*b i*(ρ i)^d) :=
      ENNReal.ofReal_le_ofReal (quadratic_multiple_le d b ρ hb hρ _ hscale i)
    _ = ENNReal.ofReal ((6*A)^2/c)*ENNReal.ofReal (c*b i*(ρ i)^d) := by
      rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ (6*A)^2/c),hmul]
    _ ≤ _ := mul_le_mul le_rfl hqual zero_le zero_le

 

theorem finite_quadratic_candidates {ι η : Type*} [Nonempty ι]
    (d : ℝ) (b ρ : ι→ℝ) (hb : ∀i,0 ≤ b i) (hρ : ∀i,0<ρ i)
    (hh : Target.IsHausdorffGauge (QuadraticGauge.gauge d b ρ))
    (μ : Measure ℂ) (s : Finset η) (x : η→ℂ) (entry : η→ι)
    (H B : Set ℂ) (hH : MeasurableSet H) (A c : ℝ) (hA : 1 ≤ A) (hc : 0<c)
    (hB : ∀j∈s,closedBall (x j) (A*ρ (entry j))∩H ⊆ B)
    (hqual : ∀j∈s,ENNReal.ofReal (c*b (entry j)*(ρ (entry j))^d) ≤
      μ (closedBall (x j) (A*ρ (entry j))∩H)) :
    ∃t : Finset η,t ⊆ s ∧
      ((t : Set η).PairwiseDisjoint (fun j=>closedBall (x j) (A*ρ (entry j)))) ∧
      (∀j∈s,∃k∈t,closedBall (x j) (A*ρ (entry j)) ⊆
        closedBall (x k) (3*(A*ρ (entry k)))) ∧
      (∑j∈t,diameterCost (QuadraticGauge.gauge d b ρ)
        (ediam (closedBall (x j) (3*(A*ρ (entry j)))))) ≤
        ENNReal.ofReal ((6*A)^2/c)*μ B := by
  apply finite_candidate_charge μ s x (fun j=>A*ρ (entry j))
    (fun j _=>mul_nonneg (by linarith) (hρ _).le) H B hH hB
  exact fun j hj=>quadratic_candidate_cost d b ρ hb hρ hh μ H (x j) (entry j) A c hA hc (hqual j hj)

end SLEExactGauge.CandidateCover
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.BoundaryGreen
open ExactSLEMain ExactSLEGenerator ExactSLEGreen

 
lemma height_power_lintegral (α H : ℝ) (hα : α<1) (hH : 0≤H) :
    (∫⁻y in Ioc (0:ℝ) H,ENNReal.ofReal (y^(-α)))=
      ENNReal.ofReal (H^(1-α)/(1-α)) := by
  have hI : IntegrableOn (fun y : ℝ=>y^(-α)) (Ioc 0 H) volume := by
    simpa only [uIoc_of_le hH] using
      (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=H) (r:=-α) (by linarith)).def'
  have hn : 0≤ᵐ[volume.restrict (Ioc (0:ℝ) H)] (fun y : ℝ=>y^(-α)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact Real.rpow_nonneg hy.1.le _
  rw [←ofReal_integral_eq_lintegral_ofReal hI hn,
    ←intervalIntegral.integral_of_le hH,integral_rpow (Or.inl (by linarith : -1< -α))]
  rw [show -α+1=1-α by ring,Real.zero_rpow (by linarith : 1-α≠0),sub_zero]

 
def rectangle (l u H : ℝ) : Set UpperPlane :=
  {z | z.1.re∈Icc l u ∧ z.1.im≤H}

lemma rectangle_measurable (l u H : ℝ) : MeasurableSet (rectangle l u H) := by
  exact ((Complex.measurable_re.comp measurable_subtype_coe) measurableSet_Icc).inter
    (measurableSet_le (Complex.measurable_im.comp measurable_subtype_coe) measurable_const)

lemma image_rectangle (l u H : ℝ) :
    Subtype.val '' rectangle l u H=
      Complex.measurableEquivRealProd ⁻¹' (Icc l u ×ˢ Ioc 0 H) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨hw.1,w.2,hw.2⟩
  · rintro ⟨hzx,hzy⟩
    exact ⟨⟨z,hzy.1⟩,⟨hzx,hzy.2⟩,rfl⟩

lemma rectangle_height_integral (α l u H : ℝ) (hα : α<1) (hH : 0≤H) :
    (∫⁻z in rectangle l u H,ENNReal.ofReal (z.1.im^(-α))∂upperArea)=
      ENNReal.ofReal (u-l)*ENNReal.ofReal (H^(1-α)/(1-α)) := by
  have hs := setLIntegral_subtype (μ:=(volume : Measure ℂ)) upperPlane_open.measurableSet
    (rectangle l u H) (fun z=>ENNReal.ofReal (z.im^(-α)))
  change (∫⁻z in rectangle l u H,ENNReal.ofReal (z.1.im^(-α))∂upperArea)=_ at hs
  rw [hs]
  change (∫⁻z in (Subtype.val : UpperPlane → ℂ) '' rectangle l u H,
    ENNReal.ofReal (z.im^(-α))∂volume)=_
  rw [image_rectangle l u H]
  have ht := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun z : ℝ×ℝ=>ENNReal.ofReal (z.2^(-α))) (Icc l u ×ˢ Ioc 0 H)
  change (∫⁻z in Complex.measurableEquivRealProd ⁻¹' (Icc l u ×ˢ Ioc 0 H),
    ENNReal.ofReal (z.im^(-α))∂volume)=_ at ht
  rw [ht]
  change (∫⁻z in Icc l u ×ˢ Ioc (0:ℝ) H, ENNReal.ofReal (z.2^(-α))
    ∂(volume : Measure ℝ).prod volume)=_
  rw [←Measure.prod_restrict,lintegral_prod _ (by fun_prop)]
  dsimp only
  rw [height_power_lintegral α H hα hH,lintegral_const,Measure.restrict_apply_univ,
    Real.volume_Icc,mul_comm]

lemma initialGreen_height_bound (a : ℝ) (ha : 1/4<a) (z : UpperPlane) :
    initialGreen a z ≤ Real.exp (-alpha a*Real.log 2)*z.1.im^(-alpha a) := by
  have hn : 0<‖z.1‖ := z.2.trans_le (Complex.im_le_norm z.1)
  have hs : z.1.im/‖z.1‖≤1 := (div_le_one hn).mpr (Complex.im_le_norm z.1)
  have hpow : (z.1.im/‖z.1‖)^(p a)≤1 :=
    Real.rpow_le_one (div_nonneg z.2.le hn.le) hs (by unfold p; linarith)
  rw [initialGreen,physicalGreen_eq_radius_sine a (z.1,0) z.2]
  have he : physicalRadius (z.1,(0:ℝ))=z.1.im := by simp [physicalRadius,Y,J]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact mul_le_of_le_one_right (Real.rpow_nonneg z.2.le _) hpow

 
theorem initialGreen_rectangle_bound (a : ℝ) (ha : 1/4<a)
    (l u H : ℝ) (hH : 0≤H) :
    initialGreenMeasure a (rectangle l u H) ≤
      ENNReal.ofReal (Real.exp (-alpha a*Real.log 2))*
      ENNReal.ofReal (u-l)*ENNReal.ofReal (H^(1-alpha a)/(1-alpha a)) := by
  have hα : alpha a<1 := by
    unfold alpha
    have h : 0<1/(4*a) := div_pos zero_lt_one (by linarith)
    linarith
  rw [initialGreenMeasure,withDensity_apply _ (rectangle_measurable l u H)]
  calc
    _ ≤ ∫⁻z in rectangle l u H,
        ENNReal.ofReal (Real.exp (-alpha a*Real.log 2))*
        ENNReal.ofReal (z.1.im^(-alpha a))∂upperArea := by
      apply lintegral_mono
      intro z
      dsimp only
      rw [←ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (initialGreen_height_bound a ha z)
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),
        rectangle_height_integral (alpha a) l u H hα hH,mul_assoc]

lemma initialGreen_rectangle_finite (a : ℝ) (ha : 1/4<a)
    (l u H : ℝ) (hH : 0≤H) : initialGreenMeasure a (rectangle l u H)<∞ :=
  (initialGreen_rectangle_bound a ha l u H hH).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top)

open FlowIdentification TraceMassContinuity

 

theorem canonical_rectangle_mean {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver}
    {μ : ℝ≥0∞→GDriver→Measure UpperPlane} (D : CanonicalMassData κ a ha W μ)
    (l u H : ℝ) (hH : 0≤H) :
    (∫⁻b,μ ∞ b (rectangle l u H)∂W)=initialGreenMeasure a (rectangle l u H) ∧
    (∫⁻b,μ ∞ b (rectangle l u H)∂W)<∞ ∧
    ∀ᵐ b∂W,μ ∞ b (rectangle l u H)<∞ := by
  have hmeas : Measurable (fun b=>μ ∞ b (rectangle l u H)) :=
    (Measure.measurable_measure.mp D.terminal_measurable) _ (rectangle_measurable l u H)
  have he : (∫⁻b,μ ∞ b (rectangle l u H)∂W)=initialGreenMeasure a (rectangle l u H) := by
    rw [←Measure.bind_apply (rectangle_measurable l u H) D.terminal_measurable.aemeasurable,D.mean]
  have hf := initialGreen_rectangle_finite a ha l u H hH
  exact ⟨he,he.trans_lt hf,ae_lt_top hmeas (he.trans_lt hf).ne⟩

end SLEExactGauge.BoundaryGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.BoxGrid

def box (m : ℝ) : Set ℂ := {z | z.re∈Icc (-m) m ∧ z.im∈Icc 0 m}

def region (m : ℝ) : Set ℂ := {z | z.re∈Icc (-(m+2)) (m+2) ∧ z.im≤ m+2}

lemma region_measurable (m : ℝ) : MeasurableSet (region m) :=
  (Complex.measurable_re measurableSet_Icc).inter
    (measurableSet_le Complex.measurable_im measurable_const)

lemma preimage_region (m : ℝ) :
    (Subtype.val : ExactSLEGreen.UpperPlane→ℂ) ⁻¹' region m =
      BoundaryGreen.rectangle (-(m+2)) (m+2) (m+2) := rfl

def columns (m r : ℝ) : ℕ := ⌊2*m/r⌋₊+1

def rows (m r : ℝ) : ℕ := ⌊m/r⌋₊+1

abbrev Cells (m r : ℝ) := Fin (columns m r) × Fin (rows m r)

def center (m r : ℝ) (i j : ℕ) : ℂ :=
  ⟨-m+((i:ℝ)+1/2)*r,((j:ℝ)+1/2)*r⟩

lemma center_im_pos (m r : ℝ) (hr : 0<r) (i j : ℕ) : 0<(center m r i j).im := by
  dsimp [center]
  positivity

lemma columns_width (m r : ℝ) (hm : 0≤ m) (hr : 0<r) :
    (columns m r:ℝ)*r ≤ 2*m+r := by
  have h := Nat.floor_le (div_nonneg (by positivity : 0≤2*m) hr.le)
  have hh := (le_div_iff₀ hr).mp h
  simp only [columns,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma rows_height (m r : ℝ) (hm : 0≤ m) (hr : 0<r) :
    (rows m r:ℝ)*r ≤ m+r := by
  have h := Nat.floor_le (div_nonneg hm hr.le)
  have hh := (le_div_iff₀ hr).mp h
  simp only [rows,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma center_bounds (m r : ℝ) (hm : 0≤ m) (hr : 0<r) (k : Cells m r) :
    -m≤(center m r k.1 k.2).re ∧ (center m r k.1 k.2).re≤ m+r ∧
      0<(center m r k.1 k.2).im ∧ (center m r k.1 k.2).im≤ m+r := by
  have hi : (k.1.1:ℝ)+1≤columns m r := by exact_mod_cast k.1.2
  have hj : (k.2.1:ℝ)+1≤rows m r := by exact_mod_cast k.2.2
  have hx := columns_width m r hm hr
  have hy := rows_height m r hm hr
  have hip := mul_le_mul_of_nonneg_right hi hr.le
  have hjp := mul_le_mul_of_nonneg_right hj hr.le
  have hn := Nat.cast_nonneg (α:=ℝ) k.1.1
  refine ⟨?_,?_,center_im_pos m r hr _ _,?_⟩ <;> dsimp [center] <;> nlinarith

lemma covered (m r : ℝ) (_hm : 0≤ m) (hr : 0<r) :
    box m ⊆ ⋃k : Cells m r,closedBall (center m r k.1 k.2) r := by
  intro z hz
  let i : ℕ := ⌊(z.re+m)/r⌋₊
  let j : ℕ := ⌊z.im/r⌋₊
  have hix : i<columns m r := Nat.lt_succ_of_le (Nat.floor_mono
    ((div_le_div_iff_of_pos_right hr).mpr (by linarith [hz.1.2])))
  have hjy : j<rows m r := Nat.lt_succ_of_le (Nat.floor_mono
    ((div_le_div_iff_of_pos_right hr).mpr hz.2.2))
  refine mem_iUnion.mpr ⟨(⟨i,hix⟩,⟨j,hjy⟩),?_⟩
  have hi0 := (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg (show 0≤z.re+m by linarith [hz.1.1]) hr.le))
  have hi1 := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one ((z.re+m)/r))
  have hj0 := (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg hz.2.1 hr.le))
  have hj1 := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (z.im/r))
  change dist z (center m r i j) ≤ r
  rw [dist_eq_norm]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have hx : |z.re-(-m+((i:ℝ)+1/2)*r)|≤r/2 := by
    apply abs_le.mpr
    dsimp [i]
    constructor <;> linarith
  have hy : |z.im-((j:ℝ)+1/2)*r|≤r/2 := by
    apply abs_le.mpr
    dsimp [j]
    constructor <;> linarith
  simpa only [Complex.sub_re,Complex.sub_im,center] using add_le_add hx hy |>.trans_eq (by ring)

lemma ball_subset_region (m r R : ℝ) (hm : 0≤ m) (hr : 0<r) (hr1 : r≤1)
    (hR : R≤1) (k : Cells m r) :
    closedBall (center m r k.1 k.2) R ⊆ region m := by
  intro z hz
  have hd : ‖z-center m r k.1 k.2‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hx := (Complex.abs_re_le_norm (z-center m r k.1 k.2)).trans hd
  have hy := (Complex.abs_im_le_norm (z-center m r k.1 k.2)).trans hd
  have h := center_bounds m r hm hr k
  simp only [Complex.sub_re,Complex.sub_im,abs_le] at hx hy
  exact ⟨⟨by linarith [h.1],by linarith [h.2.1]⟩,by linarith [h.2.2.2]⟩

end SLEExactGauge.BoxGrid
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Finset intervalIntegral
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BoundaryRows

 
def rowConstant (α : ℝ) : ℝ := (1/2:ℝ)^(-α)+1/(1-α)

lemma rowConstant_pos {α : ℝ} (hα : α<1) : 0<rowConstant α := by
  unfold rowConstant
  exact add_pos (Real.rpow_pos_of_pos (by norm_num) _) (div_pos zero_lt_one (by linarith))

 

theorem half_integer_sum (α : ℝ) (hα : 0≤α) (hα1 : α<1) (N : ℕ) :
    (∑j∈Finset.range N,((j:ℝ)+1/2)^(-α))≤rowConstant α*(N:ℝ)^(1-α) := by
  rcases N with _ | N
  · simp [Real.zero_rpow (by linarith : 1-α≠0)]
  have hn : (0:ℝ)≤N := Nat.cast_nonneg N
  have hb : 0<1-α := by linarith
  have hanti : AntitoneOn (fun x : ℝ=>x^(-α)) (Icc (1/2) (1/2+(N:ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1] : 0<x) hxy (neg_nonpos.mpr hα)
  have hsum := hanti.sum_le_integral
  have hi : (∫x in (1/2:ℝ)..1/2+N,x^(-α))=
      (((N:ℝ)+1/2)^(1-α)-(1/2:ℝ)^(1-α))/(1-α) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))]
    rw [show -α+1=1-α by ring,add_comm (1/2:ℝ) (N:ℝ)]
  have hpow : ((N:ℝ)+1/2)^(1-α)≤((N:ℝ)+1)^(1-α) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hb.le
  have hpone : 1≤((N:ℝ)+1)^(1-α) := Real.one_le_rpow (by linarith) hb.le
  rw [Finset.sum_range_succ']
  have he : (∑j∈Finset.range N,((↑(j+1):ℝ)+1/2)^(-α))≤
      (((N:ℝ)+1/2)^(1-α)-(1/2:ℝ)^(1-α))/(1-α) := by
    convert hsum.trans_eq hi using 1; congr 1
    ext j
    congr 1
    ring
  simp only [Nat.cast_zero,zero_add,Nat.cast_succ]
  simp only [Nat.cast_add,Nat.cast_one] at he
  calc
    _ ≤ (((N:ℝ)+1/2)^(1-α)-(1/2:ℝ)^(1-α))/(1-α)+(1/2:ℝ)^(-α) := add_le_add he le_rfl
    _ ≤ ((N:ℝ)+1)^(1-α)/(1-α)+(1/2:ℝ)^(-α) := by
      apply add_le_add_left
      exact (div_le_div_iff_of_pos_right hb).mpr
        ((sub_le_self _ (Real.rpow_nonneg (by norm_num) _)).trans hpow)
    _ ≤ ((N:ℝ)+1)^(1-α)/(1-α)+(1/2:ℝ)^(-α)*((N:ℝ)+1)^(1-α) :=
      add_le_add le_rfl (le_mul_of_one_le_right (Real.rpow_nonneg (by norm_num : (0:ℝ)≤1/2) (-α)) hpone)
    _ = _ := by unfold rowConstant; ring

lemma scaled_half_integer_sum (α : ℝ) (hα : 0≤α) (hα1 : α<1)
    (r : ℝ) (hr : 0<r) (N : ℕ) :
    (∑j∈Finset.range N,(((j:ℝ)+1/2)*r)^(-α))≤
      rowConstant α/r*((N:ℝ)*r)^(1-α) := by
  have hsplit : (∑j∈Finset.range N,(((j:ℝ)+1/2)*r)^(-α))=
      r^(-α)*(∑j∈Finset.range N,((j:ℝ)+1/2)^(-α)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow (by positivity) hr.le,mul_comm]
  have hscale : r^(-α)=r^(1-α)/r := by
    rw [show 1-α=(-α)+1 by ring,Real.rpow_add hr,Real.rpow_one,mul_div_cancel_right₀ _ hr.ne']
  calc
    _ = r^(-α)*(∑j∈Finset.range N,((j:ℝ)+1/2)^(-α)) := hsplit
    _ ≤ r^(-α)*(rowConstant α*(N:ℝ)^(1-α)) :=
      mul_le_mul_of_nonneg_left (half_integer_sum α hα hα1 N) (Real.rpow_nonneg hr.le _)
    _ = _ := by rw [hscale,Real.mul_rpow (Nat.cast_nonneg N) hr.le]; ring

 

theorem rows_below_height (α : ℝ) (hα : 0≤α) (hα1 : α<1)
    (r : ℝ) (hr : 0<r) (N : ℕ) (Y : ℝ) (hY : (N:ℝ)*r≤Y) :
    (∑j∈Finset.range N,(((j:ℝ)+1/2)*r)^(-α))≤rowConstant α/r*Y^(1-α) := by
  refine (scaled_half_integer_sum α hα hα1 r hr N).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hY (by linarith))
    (div_nonneg (rowConstant_pos hα1).le hr.le)

 

theorem truncated_rows (α : ℝ) (hα : 0≤α) (hα1 : α<1)
    (r : ℝ) (hr : 0<r) (N : ℕ) (ε : ℝ) (hε : 0≤ε) :
    (∑j∈(Finset.range N).filter (fun j : ℕ=>((j:ℝ)+1/2)*r<ε),
      (((j:ℝ)+1/2)*r)^(-α))≤rowConstant α/r*(ε+r)^(1-α) := by
  have hsub : (Finset.range N).filter (fun j : ℕ=>((j:ℝ)+1/2)*r<ε) ⊆
      Finset.range ⌈ε/r⌉₊ := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨_,hj⟩
    apply Finset.mem_range.mpr
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hr).mpr
    nlinarith
  have htop : (⌈ε/r⌉₊:ℝ)*r≤ε+r := by
    have he := (mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hε hr.le)) hr).le
    rwa [add_mul,div_mul_cancel₀ _ hr.ne',one_mul] at he
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _=>Real.rpow_nonneg (by positivity) _)).trans
    (rows_below_height α hα hα1 r hr _ _ htop)

 

theorem rectangle_rows (α : ℝ) (hα : 0≤α) (hα1 : α<1)
    (r : ℝ) (hr : 0<r) (M N : ℕ) (X Y : ℝ)
    (hX : (M:ℝ)*r≤X) (hY : (N:ℝ)*r≤Y) :
    (∑_i∈Finset.range M,∑j∈Finset.range N,(((j:ℝ)+1/2)*r)^(-α))≤
      rowConstant α*X*Y^(1-α)/r^2 := by
  have hy : 0≤Y := (mul_nonneg (Nat.cast_nonneg N) hr.le).trans hY
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  calc
    _ ≤ (M:ℝ)*(rowConstant α/r*Y^(1-α)) :=
      mul_le_mul_of_nonneg_left (rows_below_height α hα hα1 r hr N Y hY) (Nat.cast_nonneg M)
    _ ≤ (X/r)*(rowConstant α/r*Y^(1-α)) :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hr).mpr hX)
        (mul_nonneg (div_nonneg (rowConstant_pos hα1).le hr.le) (Real.rpow_nonneg hy _))
    _ = _ := by ring

 
theorem rectangle_truncated_rows (α : ℝ) (hα : 0≤α) (hα1 : α<1)
    (r : ℝ) (hr : 0<r) (M N : ℕ) (X ε : ℝ)
    (hX : (M:ℝ)*r≤X) (hε : 0≤ε) :
    (∑_i∈Finset.range M,
      ∑j∈(Finset.range N).filter (fun j : ℕ=>((j:ℝ)+1/2)*r<ε),
        (((j:ℝ)+1/2)*r)^(-α))≤rowConstant α*X*(ε+r)^(1-α)/r^2 := by
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  calc
    _ ≤ (M:ℝ)*(rowConstant α/r*(ε+r)^(1-α)) :=
      mul_le_mul_of_nonneg_left (truncated_rows α hα hα1 r hr N ε hε) (Nat.cast_nonneg M)
    _ ≤ (X/r)*(rowConstant α/r*(ε+r)^(1-α)) :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hr).mpr hX)
        (mul_nonneg (div_nonneg (rowConstant_pos hα1).le hr.le) (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

end SLEExactGauge.BoundaryRows
end
end

end OAI
