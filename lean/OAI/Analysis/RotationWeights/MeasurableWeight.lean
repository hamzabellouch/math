import OAI.Analysis.RotationWeights.Parameters

namespace OAI

noncomputable section

namespace CircleModel

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
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
section
abbrev CircleX := AddCircle (1:ℝ)
def repr (x : CircleX) : ℝ := (AddCircle.measurableEquivIco 1 0 x).val
lemma repr_mem (x : CircleX) : repr x ∈ Ico 0 1 := by
  simpa [repr] using (AddCircle.measurableEquivIco 1 0 x).property
lemma repr_mk (x : ℝ) : repr (x : CircleX) = Int.fract x := by
  change (AddCircle.equivIco 1 0 (x : CircleX)).val = _
  simpa only [div_one,mul_one] using AddCircle.coe_equivIco_mk_apply (p := (1:ℝ)) x
lemma repr_coe (x : CircleX) : ((repr x : ℝ) : CircleX) = x := by
  exact (AddCircle.measurableEquivIco 1 0).symm_apply_apply x
lemma measurable_repr : Measurable repr :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

def Xi (q : ℕ → ℕ) (i : ℕ) (x : CircleX) : ℝ := repr (q i • x)
def beta (q : ℕ → ℕ) (θ : CircleX) (i : ℕ) : ℝ := Xi q i θ
def shift (θ : CircleX) (k : ℤ) (x : CircleX) : CircleX := x+k•θ

lemma Xi_shift (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (i : ℕ) (x : CircleX) :
    Xi q i (shift θ k x) = Int.fract (Xi q i x + k*beta q θ i) := by
  rw [← repr_mk]
  have hk : (((k:ℝ)*repr (q i • θ) : ℝ) : CircleX) = k • (q i • θ) := by
    rw [← zsmul_eq_mul,AddCircle.coe_zsmul,repr_coe]
  change repr (q i • (x+k•θ)) = repr ((repr (q i • x)+(k:ℝ)*repr (q i • θ) : ℝ) : CircleX)
  rw [AddCircle.coe_add,repr_coe,hk,nsmul_add,smul_comm]

lemma floor_cocycle (x a : ℝ) (k n : ℤ) :
    ⌊x+(k+n)*a⌋ = ⌊x+k*a⌋ + ⌊Int.fract (x+k*a)+n*a⌋ := by
  have h : x+(k+n)*a = Int.fract (x+k*a)+n*a+(⌊x+k*a⌋:ℝ) := by
    rw [Int.fract]; ring
  rw [h,Int.floor_add_intCast]
  omega

def floorTerm (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x : CircleX) (i : ℕ) : ℤ :=
  ⌊Xi q i x + k*beta q θ i⌋

def good0 (q : ℕ → ℕ) (θ : CircleX) : Set CircleX :=
  {x | ∀ k : ℤ, (Function.support (floorTerm q θ k x)).Finite}

def good (q : ℕ → ℕ) (θ : CircleX) : Set CircleX :=
  {x | ∀ a : ℤ, shift θ a x ∈ good0 q θ}

lemma shift_add (θ : CircleX) (k n : ℤ) (x : CircleX) :
    shift θ n (shift θ k x) = shift θ (k+n) x := by
  simp [shift,add_zsmul,add_assoc]
lemma shift_zero (θ : CircleX) (x : CircleX) : shift θ 0 x=x := by simp [shift]
lemma good_shift (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x : CircleX) :
    shift θ k x ∈ good q θ ↔ x ∈ good q θ := by
  constructor
  · intro h a
    have := h (a-k)
    simpa [shift_add] using this
  · intro h a
    simpa [shift_add] using h (k+a)

lemma good_subset_good0 (q : ℕ → ℕ) (θ : CircleX) : good q θ ⊆ good0 q θ := by
  intro x hx
  simpa [shift_zero] using hx 0

lemma floorTerm_add (q : ℕ → ℕ) (θ : CircleX) (k n : ℤ) (x : CircleX) (i : ℕ) :
    floorTerm q θ (k+n) x i = floorTerm q θ k x i + floorTerm q θ n (shift θ k x) i := by
  simp only [floorTerm,Xi_shift,floor_cocycle,Int.cast_add]

lemma floorTerm_zero (q : ℕ → ℕ) (θ : CircleX) (x : CircleX) (i : ℕ) :
    floorTerm q θ 0 x i = 0 := by
  simp only [floorTerm,Int.cast_zero,zero_mul,add_zero]
  exact Int.floor_eq_iff.mpr (by simpa [Xi] using repr_mem (q i • x))

lemma floorTerm_mono (q : ℕ → ℕ) (θ : CircleX) (x : CircleX) (i : ℕ) :
    Monotone fun k : ℤ ↦ floorTerm q θ k x i := by
  intro k l h
  apply Int.floor_mono
  gcongr
  exact (repr_mem _).1

def exponent (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x : CircleX) : ℝ :=
  ∑' i, c i * (floorTerm q θ k x i : ℝ)

def cocycle (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x : CircleX) : ℝ :=
  if x ∈ good q θ then Real.exp (-exponent q θ c k x) else 1

lemma summable_exponent {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k : ℤ) {x : CircleX}
    (hx : x∈good q θ) : Summable (fun i ↦ c i*(floorTerm q θ k x i:ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (good_subset_good0 q θ hx k).subset
  intro i hi
  contrapose! hi
  simp only [Function.mem_support] at *
  simp [hi]

lemma exponent_add {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k n : ℤ) {x : CircleX}
    (hx : x∈good q θ) :
    exponent q θ c (k+n) x = exponent q θ c n (shift θ k x)+exponent q θ c k x := by
  simp only [exponent,floorTerm_add,Int.cast_add,mul_add]
  rw [(summable_exponent c k hx).tsum_add (summable_exponent c n ((good_shift q θ k x).mpr hx)),add_comm]

lemma cocycle_add (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k n : ℤ) (x : CircleX) :
    cocycle q θ c (k+n) x = cocycle q θ c n (shift θ k x)*cocycle q θ c k x := by
  unfold cocycle
  by_cases hx : x∈good q θ
  · rw [ite_eq_left hx,ite_eq_left hx,ite_eq_left ((good_shift q θ k x).mpr hx),exponent_add c k n hx,neg_add,Real.exp_add]
  · rw [ite_eq_right hx,ite_eq_right hx,ite_eq_right (mt (good_shift q θ k x).mp hx),one_mul]

lemma cocycle_pos (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x : CircleX) :
    0<cocycle q θ c k x := by
  unfold cocycle
  split_ifs
  · exact Real.exp_pos _
  · norm_num

lemma cocycle_zero (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (x : CircleX) :
    cocycle q θ c 0 x = 1 := by
  simp [cocycle,exponent,floorTerm_zero]

lemma cocycle_antitone (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (hc : ∀ i, 0≤c i) (x : CircleX) :
    Antitone fun k : ℤ ↦ cocycle q θ c k x := by
  intro k l hkl
  unfold cocycle
  split_ifs with hx
  · apply Real.exp_le_exp.mpr
    apply _root_.neg_le_neg
    exact (summable_exponent c k hx).tsum_le_tsum (fun i ↦ mul_le_mul_of_nonneg_left
      (by exact_mod_cast floorTerm_mono q θ x i hkl) (hc i)) (summable_exponent c l hx)
  · exact le_rfl


lemma measurable_Xi (q : ℕ → ℕ) (i : ℕ) : Measurable (Xi q i) :=
  measurable_repr.comp (continuous_id.nsmul (q i)).measurable

lemma measurePreserving_XiMap {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) :
    MeasurePreserving (fun x : CircleX ↦ q i • x) volume volume := by
  simpa only [natCast_zsmul] using
    (Measure.measurePreserving_zsmul (volume : Measure CircleX) (by exact_mod_cast hq i : (q i:ℤ)≠0))

lemma measure_repr_lower {r : ℝ} : volume {x : CircleX | repr x < r} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Iio r) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (measurable_repr measurableSet_Iio)]
  have hs : ((↑) : ℝ → CircleX) ⁻¹' {x | repr x < r} ∩ Ioc 0 (0+1) ⊆ Ioo 0 r ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨hsI.1,?_⟩
      change repr (s : CircleX)<r at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Ioo 0 r ∪ {1}) := measure_mono hs
    _ ≤ volume (Ioo 0 r) + volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma measure_repr_upper {r : ℝ} : volume {x : CircleX | 1-r≤repr x} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Ici (1-r)) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (measurable_repr measurableSet_Ici)]
  have hs : ((↑) : ℝ → CircleX) ⁻¹' {x | 1-r≤repr x} ∩ Ioc 0 (0+1) ⊆ Icc (1-r) 1 ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨?_,by simpa using hsI.2⟩
      change 1-r≤repr (s : CircleX) at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Icc (1-r) 1 ∪ {1}) := measure_mono hs
    _ ≤ volume (Icc (1-r) 1)+volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma floorTerm_event_bound {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX) (k : ℤ) (i : ℕ) :
    volume {x : CircleX | floorTerm q θ k x i≠0} ≤ ENNReal.ofReal (2 * |(k:ℝ)| * beta q θ i) := by
  let t := |(k:ℝ)| * beta q θ i
  have ht : 0≤t := mul_nonneg (abs_nonneg _) (repr_mem _).1
  have hs : {x : CircleX | floorTerm q θ k x i≠0} ⊆
      {x | Xi q i x<t} ∪ {x | 1-t≤Xi q i x} := by
    intro x hx
    by_contra! hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] at hh
    apply hx
    apply Int.floor_eq_iff.mpr
    have hβ : 0 ≤ beta q θ i := (repr_mem (q i • θ)).1
    have ha : -(t) ≤ (k:ℝ)*beta q θ i := by
      dsimp [t]; nlinarith [neg_abs_le (k:ℝ)]
    have hb : (k:ℝ)*beta q θ i ≤ t := by
      dsimp [t]; nlinarith [le_abs_self (k:ℝ)]
    constructor <;> push_cast <;> linarith
  have h1 : volume {x : CircleX | Xi q i x<t} ≤ ENNReal.ofReal t := by
    rw [show {x : CircleX | Xi q i x<t} = (fun x : CircleX ↦ q i • x) ⁻¹' (repr ⁻¹' Iio t) from rfl,
      (measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Iio).nullMeasurableSet]
    exact measure_repr_lower
  have h2 : volume {x : CircleX | 1-t≤Xi q i x} ≤ ENNReal.ofReal t := by
    rw [show {x : CircleX | 1-t≤Xi q i x} = (fun x : CircleX ↦ q i • x) ⁻¹' (repr ⁻¹' Ici (1-t)) from rfl,
      (measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Ici).nullMeasurableSet]
    exact measure_repr_upper
  calc
    _ ≤ volume {x : CircleX | Xi q i x<t}+volume {x : CircleX | 1-t≤Xi q i x} :=
      (measure_mono hs).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal t+ENNReal.ofReal t := add_le_add h1 h2
    _ = _ := by rw [← ENNReal.ofReal_add ht ht]; congr 1; dsimp [t]; ring

lemma ae_good0 {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX)
    (hβ : Summable (beta q θ)) : ∀ᵐ x : CircleX ∂volume, x∈good0 q θ := by
  apply ae_all_iff.mpr
  intro k
  apply ae_finite_setOfPred_mem
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (floorTerm_event_bound hq θ k))
  exact (hβ.mul_left (2*|(k:ℝ)|)).tsum_ofReal_lt_top

lemma ae_good {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX)
    (hβ : Summable (beta q θ)) : ∀ᵐ x : CircleX ∂volume, x∈good q θ := by
  apply ae_all_iff.mpr
  intro a
  exact (measurePreserving_add_right (volume : Measure CircleX) (a•θ)).quasiMeasurePreserving.ae (ae_good0 hq θ hβ)

lemma measurable_floorTerm (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (i : ℕ) :
    Measurable (fun x ↦ floorTerm q θ k x i) :=
  ((measurable_Xi q i).add_const _).floor

lemma finite_support_iff (f : ℕ → ℤ) : (Function.support f).Finite ↔ ∃ N, ∀ i≥N, f i=0 := by
  constructor
  · intro hf
    obtain ⟨N,hN⟩ := hf.bddAbove
    refine ⟨N+1,fun i hi ↦ ?_⟩
    by_contra h
    have := hN h
    omega
  · rintro ⟨N,hN⟩
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro i hi
    simp only [Finset.mem_coe,Finset.mem_range]
    by_contra! h
    exact hi (hN i h)

lemma measurableSet_good0 (q : ℕ → ℕ) (θ : CircleX) : MeasurableSet (good0 q θ) := by
  change MeasurableSet {x | ∀ k : ℤ, (Function.support (floorTerm q θ k x)).Finite}
  simp only [finite_support_iff,Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iUnion fun N ↦
    MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun (_h : N ≤ i) ↦
      (measurable_floorTerm q θ k i) (measurableSet_singleton 0)

lemma measurableSet_good (q : ℕ → ℕ) (θ : CircleX) : MeasurableSet (good q θ) := by
  change MeasurableSet {x | ∀ a : ℤ, shift θ a x ∈ good0 q θ}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun a : ℤ ↦
    (continuous_id.add continuous_const).measurable (measurableSet_good0 q θ)

lemma measurable_exponent (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) :
    Measurable (exponent q θ c k) :=
  Measurable.tsum fun i ↦ measurable_const.mul ((continuous_of_discreteTopology : Continuous (fun n : ℤ ↦ (n : ℝ))).measurable.comp (measurable_floorTerm q θ k i))

lemma measurable_cocycle (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) :
    Measurable (cocycle q θ c k) :=
  ((measurable_exponent q θ c k).neg.exp).piecewise (measurableSet_good q θ) measurable_const

end
open Set MeasureTheory Filter
open scoped BigOperators

lemma floor_unit_interval_bounds {s a : ℝ} (hs : s∈Ico 0 1) :
    ⌊a⌋ ≤ ⌊s+a⌋ ∧ ⌊s+a⌋ ≤ ⌊a⌋+1 := by
  constructor
  · exact Int.floor_mono (by linarith [hs.1])
  · have hlt : s+a < (⌊a⌋+1:ℤ)+1 := by
      push_cast
      linarith [Int.lt_floor_add_one a,hs.2]
    exact Int.lt_add_one_iff.mp ((Int.floor_lt).mpr (by simpa only [Int.cast_add,Int.cast_one] using hlt))

lemma floorTerm_difference_le_one (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x y : CircleX) (i : ℕ) :
    floorTerm q θ k x i ≤ floorTerm q θ k y i+1 := by
  have hx := floor_unit_interval_bounds (a:=(k:ℝ)*beta q θ i) (repr_mem (q i • x))
  have hy := floor_unit_interval_bounds (a:=(k:ℝ)*beta q θ i) (repr_mem (q i • y))
  change ⌊Xi q i x+(k:ℝ)*beta q θ i⌋ ≤ ⌊Xi q i y+(k:ℝ)*beta q θ i⌋+1
  dsimp [Xi] at *
  omega

lemma floorTerm_ordered {q : ℕ → ℕ} {θ : CircleX} (k : ℤ) {x y : CircleX} {i : ℕ}
    (h : Xi q i x ≤ Xi q i y) : floorTerm q θ k x i ≤ floorTerm q θ k y i :=
  Int.floor_mono (by linarith)

lemma cocycle_ratio_exp {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k : ℤ) {x y : CircleX}
    (hx : x∈good q θ) (hy : y∈good q θ) :
    cocycle q θ c k y/cocycle q θ c k x = Real.exp (exponent q θ c k x-exponent q θ c k y) := by
  simp only [cocycle,ite_eq_left hx,ite_eq_left hy,←Real.exp_sub]
  congr 1
  ring

lemma cocycle_ratio_nonneg (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x y : CircleX) :
    0 ≤ cocycle q θ c k y/cocycle q θ c k x :=
  (div_pos (cocycle_pos q θ c k y) (cocycle_pos q θ c k x)).le

lemma cocycle_ratio_tail_bound {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ)
    (hc : ∀ i,0≤c i) (D : ℕ) (k : ℤ) {x y : CircleX}
    (hx : x∈good q θ) (hy : y∈good q θ) (hxy : ∀ i, D ≤ i → Xi q i x≤Xi q i y) :
    cocycle q θ c k y/cocycle q θ c k x ≤ Real.exp (∑ i∈Finset.range D,c i) := by
  have hf : Summable (fun i : ℕ => if i<D then c i else 0) :=
    summable_of_ne_finset_zero (s:=Finset.range D) (by intro i hi; simp_all)
  have hsum : (∑' i : ℕ, if i<D then c i else 0) = ∑ i∈Finset.range D,c i := by
    rw [tsum_eq_sum (s:=Finset.range D) (by intro i hi; simp_all)]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hb : exponent q θ c k x ≤ exponent q θ c k y+∑ i∈Finset.range D,c i := by
    rw [← hsum,exponent,exponent,← (summable_exponent c k hy).tsum_add hf]
    apply (summable_exponent c k hx).tsum_le_tsum _ ((summable_exponent c k hy).add hf)
    intro i
    by_cases hi : i<D
    · simp only [ite_eq_left hi]
      have h := floorTerm_difference_le_one q θ k x y i
      have h' : (floorTerm q θ k x i:ℝ) ≤ (floorTerm q θ k y i:ℝ)+1 := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_left h' (hc i)]
    · simp only [ite_eq_right hi,add_zero]
      exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr (floorTerm_ordered k (hxy i (by omega)))) (hc i)
  rw [cocycle_ratio_exp c k hx hy]
  exact Real.exp_le_exp.mpr (by linarith)

lemma cocycle_ratio_ordered {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ)
    (hc : ∀ i,0≤c i) (k : ℤ) {x y : CircleX}
    (hx : x∈good q θ) (hy : y∈good q θ) (hxy : ∀ i,Xi q i x≤Xi q i y) :
    cocycle q θ c k y/cocycle q θ c k x ≤ 1 := by
  simpa using cocycle_ratio_tail_bound c hc 0 k hx hy (fun i _ => hxy i)

lemma floor_crossing {s t a : ℝ} (hs : s∈Ico 0 1) (ht : t∈Ico 0 1)
    (hlo : s<1-Int.fract a) (hhi : 1-Int.fract a≤t) : ⌊t+a⌋=⌊s+a⌋+1 := by
  have ha : a=Int.fract a+(⌊a⌋:ℝ) := by rw [Int.fract]; ring
  have hs0 : ⌊s+Int.fract a⌋=0 := Int.floor_eq_iff.mpr (by
    push_cast; constructor <;> linarith [Int.fract_nonneg a,hs.1])
  have ht1 : ⌊t+Int.fract a⌋=1 := Int.floor_eq_iff.mpr (by
    push_cast; constructor <;> linarith [Int.fract_lt_one a,ht.2])
  rw [ha,←add_assoc,←add_assoc,Int.floor_add_intCast,Int.floor_add_intCast,hs0,ht1]
  omega

lemma cocycle_ratio_crossing {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (hc : ∀ i,0≤c i)
    (k : ℤ) {x y : CircleX} (hx : x∈good q θ) (hy : y∈good q θ)
    (hxy : ∀ i,Xi q i x≤Xi q i y) (i : ℕ)
    (hlo : Xi q i x<1-Int.fract ((k:ℝ)*beta q θ i))
    (hhi : 1-Int.fract ((k:ℝ)*beta q θ i)≤Xi q i y) :
    cocycle q θ c k y/cocycle q θ c k x ≤ Real.exp (-c i) := by
  have hcross : floorTerm q θ k y i=floorTerm q θ k x i+1 :=
    floor_crossing (repr_mem _) (repr_mem _) hlo hhi
  have hs : Summable (fun a => c a*((floorTerm q θ k y a:ℝ)-(floorTerm q θ k x a:ℝ))) := by
    simpa only [mul_sub] using (summable_exponent c k hy).sub (summable_exponent c k hx)
  have hn : ∀ a,0≤c a*((floorTerm q θ k y a:ℝ)-(floorTerm q θ k x a:ℝ)) := by
    intro a
    exact mul_nonneg (hc a) (sub_nonneg.mpr (Int.cast_le.mpr (floorTerm_ordered k (hxy a))))
  have hb := hs.le_tsum i (fun a _ => hn a)
  have he : (∑' a,c a*((floorTerm q θ k y a:ℝ)-(floorTerm q θ k x a:ℝ))) =
      exponent q θ c k y-exponent q θ c k x := by
    simp only [mul_sub,exponent,(summable_exponent c k hy).tsum_sub (summable_exponent c k hx)]
  rw [he,hcross,Int.cast_add,Int.cast_one] at hb
  rw [cocycle_ratio_exp c k hx hy]
  exact Real.exp_le_exp.mpr (by nlinarith)


end CircleModel

end

end OAI
