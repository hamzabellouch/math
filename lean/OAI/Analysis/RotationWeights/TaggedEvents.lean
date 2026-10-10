import OAI.Analysis.RotationWeights.ActualDigits

namespace OAI

noncomputable section

universe uι uX uΩ

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
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CircleCoupling

lemma independent_one_tag_bound {ι : Type uι} [DecidableEq ι] {X : ι → Type uX}
    [∀ i,MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i)) [∀ i,IsProbabilityMeasure (μ i)]
    (s : Finset ι) (tag good : (i : ι) → Set (X i))
    (htag : ∀ i,MeasurableSet (tag i)) (hgood : ∀ i,MeasurableSet (good i))
    (hdis : ∀ i∈s,Disjoint (tag i) (good i)) {p a : ℝ} (hp : 0≤p) (ha : 0≤a)
    (ht : ∀ i∈s,p≤(μ i).real (tag i)) (hg : ∀ i∈s,a≤(μ i).real (good i)) :
    (s.card:ℝ)*p*a^(s.card-1) ≤
      (Measure.infinitePi μ).real (⋃ i∈s, Set.pi (s:Set ι) (fun k => if k=i then tag k else good k)) := by
  classical
  let A (i : ι) : Set (∀ k,X k) := Set.pi (s:Set ι) (fun k => if k=i then tag k else good k)
  have hA (i : ι) : MeasurableSet (A i) := by
    apply MeasurableSet.pi s.countable_toSet
    intro k _
    by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;> first | exact htag k | exact hgood k
  have hd : (s:Set ι).PairwiseDisjoint A := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    have hx : ω i∈tag i := by simpa [A] using hωi i hi
    have hy : ω i∈good i := by simpa [A,hij] using hωj i hi
    exact Set.disjoint_left.mp (hdis i hi) hx hy
  change _≤(Measure.infinitePi μ).real (⋃ i∈s,A i)
  rw [measureReal_biUnion_finset hd (fun i _ => hA i)]
  calc
    _ = ∑ _i∈s,p*a^(s.card-1) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have he : (Measure.infinitePi μ).real (A i)=
          ∏ k∈s, (μ k).real (if k=i then tag k else good k) := by
        unfold Measure.real A
        rw [Measure.infinitePi_pi μ (by
          intro k _; by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;> first | exact htag k | exact hgood k)]
        exact ENNReal.toReal_prod _ _
      rw [he]
      have hv : (∏ k∈s,if k=i then p else a)=p*a^(s.card-1) := by
        rw [←Finset.mul_prod_erase s (fun k => if k=i then p else a) hi]
        simp only [ite_true]
        have hn : ∀ k∈s.erase i,k≠i := fun k hk => (Finset.mem_erase.mp hk).1
        simp only [Finset.mem_erase] at hn
        simp_rw [Finset.prod_congr rfl (fun k hk => ite_eq_right ((Finset.mem_erase.mp hk).1))]
        simp [Finset.card_erase_of_mem hi]
      rw [←hv]
      apply Finset.prod_le_prod₀
      · intro k _; split <;> assumption
      · intro k hk
        by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;> first | exact ht k hk | exact hg k hk

lemma log_one_sub_lower {t : ℝ} (ht : 0≤t) (ht1 : t≤1/2) : -2*t≤Real.log (1-t) := by
  have hp : 0<1-t := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1-t)⁻¹= -t/(1-t) := by field_simp; ring
  rw [he] at hh
  apply le_trans _ hh
  rw [le_div_iff₀ hp]
  nlinarith

lemma one_tag_survival (m : ℕ) (hm : 200 ≤ m) : Real.exp (-86)≤(1-43/(m:ℝ))^(m-1) := by
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have ht : 0≤43/(m:ℝ) := by positivity
  have ht1 : 43/(m:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hm0]
    have hh : (200:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hb : 0<1-43/(m:ℝ) := by linarith
  rw [←Real.exp_log (pow_pos hb _),Real.log_pow,Real.exp_le_exp]
  calc
    -(86:ℝ) ≤ ((m-1:ℕ):ℝ)*(-2*(43/(m:ℝ))) := by
      rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]
      field_simp
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (log_one_sub_lower ht ht1) (Nat.cast_nonneg _)

open MeasureTheory Set
open scoped BigOperators ENNReal

lemma count_fin_lower (l : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ((Finset.univ.filter fun d : Fin l => (d.val:ℝ)<a).card:ℝ) ≤ a+1 := by
  classical
  have hc : (Finset.univ.filter fun d : Fin l => (d.val:ℝ)<a).card ≤ ⌈a⌉₊ := by
    calc
      _ ≤ (Finset.range ⌈a⌉₊).card := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro i hi
          exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (Finset.mem_filter.mp hi).2)
        · exact Fin.val_injective.injOn
      _ = _ := Finset.card_range _
  exact (Nat.cast_le.mpr hc).trans (Nat.ceil_lt_add_one ha).le

lemma finite_fiber_mass {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {l : ℕ} (f : Ω → Fin l) (_hf : Measurable f) {B : ℝ} (hB : ∀ d,μ.real {ω | f ω=d} ≤ B)
    (s : Finset (Fin l)) : μ.real {ω | f ω∈s} ≤ (s.card:ℝ)*B := by
  classical
  have he : {ω | f ω∈s}=⋃ d∈s,{ω | f ω=d} := by ext ω; simp
  rw [he]
  calc
    _ ≤ ∑ d∈s,μ.real {ω | f ω=d} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _d∈s,B := Finset.sum_le_sum (fun d _ => hB d)
    _ = _ := by simp

lemma finite_lower_fiber_mass {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {l : ℕ} (f : Ω → Fin l) (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ d,μ.real {ω | f ω=d} ≤ B) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ((f ω).val:ℝ)<a} ≤ (a+1)*B := by
  classical
  have hh := finite_fiber_mass μ f hf hB (Finset.univ.filter fun d => (d.val:ℝ)<a)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (count_fin_lower l ha) hB0)

namespace CoordinateParameters
variable (P : CoordinateParameters)

def tagEvent : Set P.Sample := {z | z.1=some (4 : Fin 5)}
def marginEvent : Set P.Sample := {z | ((z.2.1.val:ℝ)+1)/(P.l:ℝ) ≤ 1-2/(P.m:ℝ) ∧
    2/(P.m:ℝ) ≤ (z.2.2.val:ℝ)/(P.l:ℝ)}
def untaggedMargin : Set P.Sample := P.tagEventᶜ ∩ P.marginEvent

lemma law_tag_mass : (P.law true).real P.tagEvent=1/(P.m:ℝ) := by
  rw [Measure.real,tagEvent,law,sixLaw_tag,ENNReal.toReal_ofReal (P.τ_nonneg true)]
  rfl
lemma tag_forces_margin {z : P.Sample}
    (hz : supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) z)
    (ht : z∈P.tagEvent) : z∈P.marginEvent := by
  have ht' : z.1=some (4:Fin 5) := ht
  simp only [supportCondition,ht'] at hz
  norm_num at hz
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hm := P.m_pos
  have h3 : (3:ℝ) ≤ P.m := by exact_mod_cast (by have := P.hm; omega : 3 ≤ P.m)
  have hx : (z.2.1.val:ℝ)+1 ≤ roundedTag P.l P.m := by exact_mod_cast hz.1
  have hy : (P.l:ℝ)-(roundedTag P.l P.m:ℝ) ≤ z.2.2.val := by
    have hh : (P.l:ℝ) ≤ (z.2.2.val:ℝ)+(roundedTag P.l P.m:ℝ) := by exact_mod_cast hz.2
    linarith
  have hb := P.tag_bounds.2.2.2
  constructor
  · apply (div_le_div_of_nonneg_right hx hl.le).trans
    rw [div_le_iff₀ hl]
    have hh : (P.l:ℝ)/P.m ≤ (1-2/(P.m:ℝ))*P.l := by
      apply (div_le_iff₀ hm).mpr
      field_simp
      nlinarith
    exact hb.trans hh
  · rw [le_div_iff₀ hl]
    have hh : (2/(P.m:ℝ))*P.l ≤ (P.l:ℝ)-(P.l:ℝ)/P.m := by
      calc
        _ = (2*P.l)/(P.m:ℝ) := by ring
        _ ≤ ((P.l:ℝ)*P.m-P.l)/P.m := div_le_div_of_nonneg_right (by nlinarith) hm.le
        _ = _ := by field_simp
    linarith

lemma law_lower_digit (tagged e : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (P.law tagged).real {z | ((digitEndpoint e z.2).val:ℝ)/(P.l:ℝ)<t} ≤ 10*(t+1/(P.l:ℝ)) := by
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hh := finite_lower_fiber_mass (P.law tagged) (fun z => digitEndpoint e z.2)
    ((digitEndpoint_measurable e).comp measurable_snd) (by positivity : 0 ≤ 10/(P.l:ℝ))
    (P.law_density_ten tagged e) (mul_nonneg ht hl.le)
  simp_rw [div_lt_iff₀ hl]
  convert hh using 1; field_simp

lemma law_upper_digit (tagged e : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (P.law tagged).real {z | 1-t<((digitEndpoint e z.2).val+1:ℝ)/(P.l:ℝ)} ≤ 10*(t+1/(P.l:ℝ)) := by
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hf : ∀ d : Fin P.l, (P.law tagged).real {z | (digitEndpoint e z.2).rev=d} ≤ 10/(P.l:ℝ) := by
    intro d
    have he : {z : P.Sample | (digitEndpoint e z.2).rev=d}={z | digitEndpoint e z.2=d.rev} := by
      ext z
      change (digitEndpoint e z.2).rev=d ↔ digitEndpoint e z.2=d.rev
      constructor <;> intro h
      · simpa using congrArg Fin.rev h
      · rw [h]; simp
    rw [he]
    exact P.law_density_ten tagged e d.rev
  have hh := finite_lower_fiber_mass (P.law tagged) (fun z => (digitEndpoint e z.2).rev)
    (by measurability) (by positivity : 0 ≤ 10/(P.l:ℝ)) hf (mul_nonneg ht hl.le)
  have he : {z : P.Sample | 1-t<((digitEndpoint e z.2).val+1:ℝ)/(P.l:ℝ)}=
      {z : P.Sample | (((digitEndpoint e z.2).rev).val:ℝ)<t*P.l} := by
    ext z
    simp only [Set.mem_ofPred_eq,lt_div_iff₀ hl,Fin.val_rev]
    rw [Nat.cast_sub (by omega : (digitEndpoint e z.2).val+1 ≤ P.l)]
    push_cast
    constructor <;> intro h <;> linarith
  rw [he]
  convert hh using 1; field_simp

lemma law_untagged_margin_mass : 1-43/(P.m:ℝ) ≤ (P.law true).real P.untaggedMargin := by
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hm := P.m_pos
  have hh : (P.law true).real P.untaggedMarginᶜ ≤
      1/(P.m:ℝ)+10*(2/(P.m:ℝ)+1/(P.l:ℝ))+10*(2/(P.m:ℝ)+1/(P.l:ℝ)) := by
    have he : P.untaggedMarginᶜ=P.tagEvent ∪ {z | 1-2/(P.m:ℝ)<((z.2.1.val:ℝ)+1)/(P.l:ℝ)} ∪
        {z | (z.2.2.val:ℝ)/(P.l:ℝ)<2/(P.m:ℝ)} := by
      ext z
      simp only [untaggedMargin,marginEvent,Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_union,not_and_or,not_not,not_le,or_assoc]
    rw [he]
    calc
      _ ≤ (P.law true).real (P.tagEvent ∪ {z | 1-2/(P.m:ℝ)<((z.2.1.val:ℝ)+1)/(P.l:ℝ)})+
          (P.law true).real {z | (z.2.2.val:ℝ)/(P.l:ℝ)<2/(P.m:ℝ)} := measureReal_union_le _ _
      _ ≤ ((P.law true).real P.tagEvent + (P.law true).real {z | 1-2/(P.m:ℝ)<((z.2.1.val:ℝ)+1)/(P.l:ℝ)})+
          (P.law true).real {z | (z.2.2.val:ℝ)/(P.l:ℝ)<2/(P.m:ℝ)} := add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ _ := by rw [P.law_tag_mass]; exact add_le_add (add_le_add le_rfl (P.law_upper_digit true false (t:=2/(P.m:ℝ)) (by positivity))) (P.law_lower_digit true true (t:=2/(P.m:ℝ)) (by positivity))
  rw [measureReal_compl (by measurability : MeasurableSet P.untaggedMargin)] at hh
  simp only [probReal_univ] at hh
  have hr : 1/(P.l:ℝ) ≤ 1/(100*(P.m:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast P.hl
  have hb : 1/(P.m:ℝ)+20*(2/(P.m:ℝ)+1/(P.l:ℝ)) ≤ 43/(P.m:ℝ) := by
    calc
      _ ≤ 1/(P.m:ℝ)+20*(2/(P.m:ℝ)+1/(100*(P.m:ℝ))) := by gcongr
      _ ≤ _ := by field_simp; nlinarith
  linarith
end CoordinateParameters
end CircleCoupling

namespace CircleCoupling.DigitSystem
open MeasureTheory Set
open scoped BigOperators
variable (S : DigitSystem)

def coordinateTag : (n : ℕ) → Set (S.Sample n)
  | 0 => ∅
  | n+1 => (S.coord n).tagEvent

def coordinateMargin : (n : ℕ) → Set (S.Sample n)
  | 0 => Set.univ
  | n+1 => (S.coord n).marginEvent

def coordinateUntaggedMargin (n : ℕ) : Set (S.Sample n) :=
  (S.coordinateTag n)ᶜ ∩ S.coordinateMargin n

lemma measurableSet_coordinateTag (n : ℕ) : MeasurableSet (S.coordinateTag n) := by
  cases n <;> measurability
lemma measurableSet_coordinateMargin (n : ℕ) : MeasurableSet (S.coordinateMargin n) := by
  cases n <;> measurability
lemma measurableSet_coordinateUntaggedMargin (n : ℕ) : MeasurableSet (S.coordinateUntaggedMargin n) :=
  (S.measurableSet_coordinateTag n).compl.inter (S.measurableSet_coordinateMargin n)

def oneTagEvent (I : Finset ℕ) : Set S.Samples :=
  ⋃ i∈I, Set.pi (I:Set ℕ) (fun k => if k=i then S.coordinateTag k else S.coordinateUntaggedMargin k)
lemma measurableSet_oneTagEvent (I : Finset ℕ) : MeasurableSet (S.oneTagEvent I) := by
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro i _
  apply MeasurableSet.pi I.countable_toSet
  intro k _
  by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;>
    first | exact S.measurableSet_coordinateTag k | exact S.measurableSet_coordinateUntaggedMargin k

lemma oneTagEvent_mass (tagged : ℕ → Bool) (I : Finset ℕ) (m : ℕ)
    (hm : 200 ≤ m) (hc : I.card=m) (hzero : 0∉I)
    (hmI : ∀ n, n+1∈I → (S.coord n).m=m)
    (htI : ∀ n, n+1∈I → tagged n=true) :
    Real.exp (-86) ≤ (S.probability tagged).real (S.oneTagEvent I) := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : 0 ≤ 1-43/(m:ℝ) := by
    have hh : (200:ℝ) ≤ m := by exact_mod_cast hm
    have hd : 43/(m:ℝ) ≤ 1 := (div_le_one hm0).mpr (by linarith)
    linarith
  have hh := independent_one_tag_bound (S.law tagged) I S.coordinateTag S.coordinateUntaggedMargin
    S.measurableSet_coordinateTag S.measurableSet_coordinateUntaggedMargin
    (fun i _ => Set.disjoint_left.mpr (fun _ ht hg => hg.1 ht))
    (by positivity : 0 ≤ 1/(m:ℝ)) ha (fun i hi => ?_) (fun i hi => ?_)
  · change _ ≤ (S.probability tagged).real (S.oneTagEvent I) at hh
    rw [hc] at hh
    have hid : (m:ℝ)*(1/(m:ℝ))=1 := by field_simp
    rw [hid,one_mul] at hh
    exact (one_tag_survival m hm).trans hh
  · cases i with
    | zero => exact False.elim (hzero hi)
    | succ n =>
      change 1/(m:ℝ) ≤ ((S.coord n).law (tagged n)).real (S.coord n).tagEvent
      rw [htI n hi,(S.coord n).law_tag_mass,hmI n hi]
  · cases i with
    | zero => exact False.elim (hzero hi)
    | succ n =>
      change 1-43/(m:ℝ) ≤ ((S.coord n).law (tagged n)).real (S.coord n).untaggedMargin
      rw [htI n hi,←hmI n hi]
      exact (S.coord n).law_untagged_margin_mass

lemma oneTagEvent_margins {I : Finset ℕ} {ω : S.Samples}
    (hw : ω∈S.supported) (hω : ω∈S.oneTagEvent I) :
    (∃ i∈I, ω i∈S.coordinateTag i) ∧ ∀ i∈I, ω i∈S.coordinateMargin i := by
  obtain ⟨a,ha,h⟩ := Set.mem_iUnion₂.mp hω
  have hat : ω a∈S.coordinateTag a := by simpa using h a ha
  refine ⟨⟨a,ha,hat⟩,?_⟩
  intro i hi
  by_cases hia : i=a
  · subst i
    cases a with
    | zero => exact Set.mem_univ _
    | succ n => exact (S.coord n).tag_forces_margin (hw.2 n) hat
  · have hg : ω i∈S.coordinateUntaggedMargin i := by simpa [hia] using h i hi
    exact hg.2
end CircleCoupling.DigitSystem

namespace CircleSampling
open MeasureTheory Set CircleCoupling
open scoped BigOperators ENNReal

def blockCoordinates (j : ℕ) : Finset ℕ := Finset.Ico (blockEnd j+1) (blockEnd (j+1)+1)
lemma blockCoordinates_card (j : ℕ) : (blockCoordinates j).card=blockLength j := by
  rw [blockCoordinates,Nat.card_Ico]
  have h := blocks.step j
  change blockEnd (j+1)=blockEnd j+blockLength j at h
  omega
lemma blockCoordinates_zero (j : ℕ) : 0 ∉ blockCoordinates j := by simp [blockCoordinates]
lemma blockCoordinates_block (j n : ℕ) (hn : n+1 ∈ blockCoordinates j) : coordinateBlock n=j := by
  have hh := Finset.mem_Ico.mp hn
  exact blocks.number_eq (by change blockEnd j ≤ n; omega) (by change n<blockEnd (j+1); omega)

def stageTagEvent (j : ℕ) : Set actualSystem.Samples := actualSystem.oneTagEvent (blockCoordinates j)
lemma stageTagEvent_measurable (j : ℕ) : MeasurableSet (stageTagEvent j) := actualSystem.measurableSet_oneTagEvent _
lemma stageTagEvent_mass (j : ℕ) : Real.exp (-86) ≤ (actualSystem.probability (stageTagged j)).real (stageTagEvent j) := by
  apply actualSystem.oneTagEvent_mass (stageTagged j) (blockCoordinates j) (blockLength j)
    (blockLength_ge_twoHundred j) (blockCoordinates_card j) (blockCoordinates_zero j)
  · intro n hn
    change blockLength (coordinateBlock n)=_
    rw [blockCoordinates_block j n hn]
  · intro n hn
    simp only [stageTagged,blockCoordinates_block j n hn,decide_true]

lemma stageTagEvent_margins (j : ℕ) {ω : actualSystem.Samples} (hw : ω∈actualSystem.supported)
    (hω : ω∈stageTagEvent j) :
    (∃ n, n+1∈blockCoordinates j ∧ (ω (n+1)).1=some (4:Fin 5)) ∧
    ∀ n, n+1∈blockCoordinates j →
      (((ω (n+1)).2.1.val:ℝ)+1)/(coordinateRadix n:ℝ) ≤ 1-2/(blockLength j:ℝ) ∧
      2/(blockLength j:ℝ) ≤ ((ω (n+1)).2.2.val:ℝ)/(coordinateRadix n:ℝ) := by
  obtain ⟨⟨i,hi,hit⟩,hm⟩ := actualSystem.oneTagEvent_margins hw hω
  constructor
  · cases i with
    | zero => exact False.elim (blockCoordinates_zero j hi)
    | succ n => exact ⟨n,hi,hit⟩
  · intro n hn
    have hh := hm (n+1) hn
    change (((ω (n+1)).2.1.val:ℝ)+1)/(coordinateRadix n:ℝ) ≤ 1-2/(blockLength (coordinateBlock n):ℝ) ∧
      2/(blockLength (coordinateBlock n):ℝ) ≤ ((ω (n+1)).2.2.val:ℝ)/(coordinateRadix n:ℝ) at hh
    rwa [blockCoordinates_block j n hn] at hh
end CircleSampling

end

end OAI
