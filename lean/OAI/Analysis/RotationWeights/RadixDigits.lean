import OAI.Analysis.RotationWeights.CoordinateLaws

namespace OAI

noncomputable section

namespace CircleDigits

universe uι uX

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
section
abbrev CircleX := AddCircle (1 : ℝ)

def denominator (b : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i∈Finset.range n, b i

@[simp] lemma denominator_zero (b : ℕ → ℕ) : denominator b 0 = 1 := by simp [denominator]
@[simp] lemma denominator_succ (b : ℕ → ℕ) (n : ℕ) :
    denominator b (n+1) = denominator b n * b n := by simp [denominator,Finset.prod_range_succ]

lemma denominator_pos {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (n : ℕ) : 0<denominator b n := by
  exact Finset.prod_pos fun i _ ↦ lt_of_lt_of_le (by norm_num) (hb i)

lemma denominator_geometric {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (n : ℕ) :
    2^n ≤ denominator b n := by
  induction n with
  | zero => simp
  | succ n hn => rw [denominator_succ,pow_succ]; exact Nat.mul_le_mul hn (hb n)

lemma denominator_inv_bound {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (n : ℕ) :
    (denominator b n : ℝ)⁻¹ ≤ (1/2 : ℝ)^n := by
  rw [one_div,inv_pow]
  apply (inv_le_inv₀ (by exact_mod_cast denominator_pos hb n) (by positivity)).mpr
  exact_mod_cast denominator_geometric hb n

lemma denominator_inv_tendsto {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) :
    Tendsto (fun n ↦ (denominator b n : ℝ)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ by positivity) (denominator_inv_bound hb)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

abbrev Digits (b : ℕ → ℕ) := ∀ i, Fin (b i)

def digitTerm (b : ℕ → ℕ) (d : Digits b) (i : ℕ) : ℝ := (d i : ℝ)/denominator b (i+1)

def expansion (b : ℕ → ℕ) (d : Digits b) : ℝ := ∑' i, digitTerm b d i

def endpoint (b : ℕ → ℕ) (d : Digits b) : CircleX := (expansion b d : CircleX)

lemma digitTerm_nonneg (b : ℕ → ℕ) (d : Digits b) (i : ℕ) : 0≤digitTerm b d i := by
  unfold digitTerm; positivity

lemma digitTerm_le_inverse {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (i : ℕ) :
    digitTerm b d i ≤ (denominator b i : ℝ)⁻¹ := by
  have hq : (0:ℝ)<denominator b i := by exact_mod_cast denominator_pos hb i
  have hbi : (0:ℝ)<b i := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb i)
  rw [digitTerm,denominator_succ,Nat.cast_mul,div_le_iff₀ (mul_pos hq hbi)]
  rw [inv_mul_cancel_left₀ hq.ne']
  exact_mod_cast (d i).isLt.le

lemma digitTerm_summable {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) :
    Summable (digitTerm b d) := by
  apply Summable.of_nonneg_of_le (digitTerm_nonneg b d)
    (fun i ↦ (digitTerm_le_inverse hb d i).trans (denominator_inv_bound hb i))
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma digitTerm_le_telescope {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (i : ℕ) :
    digitTerm b d i ≤ (denominator b i : ℝ)⁻¹-(denominator b (i+1) : ℝ)⁻¹ := by
  have hq : (0:ℝ)<denominator b i := by exact_mod_cast denominator_pos hb i
  have hbi : (0:ℝ)<b i := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb i)
  rw [digitTerm,denominator_succ,Nat.cast_mul,div_le_iff₀ (mul_pos hq hbi)]
  have h : (d i : ℝ) ≤ (b i : ℝ)-1 := by
    have hh : (d i : ℝ)+1≤(b i : ℝ) := by exact_mod_cast (d i).isLt
    linarith
  rw [sub_mul,inv_mul_cancel_left₀ hq.ne']
  rw [inv_mul_cancel₀ (mul_ne_zero hq.ne' hbi.ne')]
  exact h

lemma digitPartial_bound {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (n : ℕ) :
    ∑ i∈Finset.range n, digitTerm b d i ≤ 1-(denominator b n : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ i∈Finset.range n, ((denominator b i : ℝ)⁻¹-(denominator b (i+1) : ℝ)⁻¹) :=
      Finset.sum_le_sum fun i _ ↦ digitTerm_le_telescope hb d i
    _ = _ := by rw [Finset.sum_range_sub']; simp

lemma expansion_nonneg {b : ℕ → ℕ} (d : Digits b) : 0≤expansion b d :=
  tsum_nonneg (digitTerm_nonneg b d)

lemma expansion_le_one {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) : expansion b d≤1 := by
  apply le_of_tendsto ((digitTerm_summable hb d).hasSum.tendsto_sum_nat)
  exact Eventually.of_forall fun n ↦ (digitPartial_bound hb d n).trans (sub_le_self _ (by positivity))

lemma expansion_tail_bound {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (n : ℕ) :
    0≤expansion b d-∑ i∈Finset.range n, digitTerm b d i ∧
    expansion b d-∑ i∈Finset.range n, digitTerm b d i ≤ (denominator b n : ℝ)⁻¹ := by
  have hsum := (digitTerm_summable hb d).sum_add_tsum_nat_add n
  change _ = expansion b d at hsum
  rw [← hsum,add_sub_cancel_left]
  refine ⟨tsum_nonneg fun i ↦ digitTerm_nonneg b d (i+n),?_⟩
  apply le_of_tendsto (((digitTerm_summable hb d).comp_injective (add_left_injective n)).hasSum.tendsto_sum_nat)
  apply Eventually.of_forall
  intro m
  calc
    ∑ i∈Finset.range m, digitTerm b d (i+n) ≤
      ∑ i∈Finset.range m, ((denominator b (i+n) : ℝ)⁻¹-(denominator b (i+n+1) : ℝ)⁻¹) :=
        Finset.sum_le_sum fun i _ ↦ digitTerm_le_telescope hb d (i+n)
    _ = (denominator b n : ℝ)⁻¹-(denominator b (m+n) : ℝ)⁻¹ := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Finset.sum_range_sub' (fun i ↦ (denominator b (i+n) : ℝ)⁻¹) m
    _ ≤ _ := sub_le_self _ (by positivity)

lemma measurable_digitTerm (b : ℕ → ℕ) (i : ℕ) : Measurable (fun d : Digits b ↦ digitTerm b d i) := by
  exact ((measurable_of_finite (fun x : Fin (b i) ↦ (x : ℝ))).comp (measurable_pi_apply i)).div_const _

lemma measurable_expansion (b : ℕ → ℕ) : Measurable (expansion b) :=
  Measurable.tsum fun i ↦ measurable_digitTerm b i

lemma measurable_endpoint (b : ℕ → ℕ) : Measurable (endpoint b) :=
  (AddCircle.continuous_mk' 1).measurable.comp (measurable_expansion b)

lemma expansion_mono {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) {d e : Digits b}
    (h : ∀ i, d i≤e i) : expansion b d≤expansion b e := by
  apply (digitTerm_summable hb d).tsum_le_tsum _ (digitTerm_summable hb e)
  intro i
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h i



variable (b : ℕ → ℕ)

def digitLaw (i : ℕ) [NeZero (b i)] : Measure (Fin (b i)) := (PMF.uniformOfFintype (Fin (b i))).toMeasure

instance (i : ℕ) [NeZero (b i)] : IsProbabilityMeasure (digitLaw b i) := by
  unfold digitLaw; infer_instance

def uniformDigits [∀ i, NeZero (b i)] : Measure (Digits b) := Measure.infinitePi (fun i ↦ digitLaw b i)
instance [∀ i, NeZero (b i)] : IsProbabilityMeasure (uniformDigits b) := by
  unfold uniformDigits; infer_instance

lemma integral_digitLaw (i : ℕ) [NeZero (b i)] (f : Fin (b i) → ℂ) :
    ∫ d, f d ∂digitLaw b i = (b i : ℂ)⁻¹*∑ d, f d := by
  rw [digitLaw,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,← Finset.mul_sum]

omit b in
def character (k : ℤ) : AddChar CircleX ℂ where
  toFun := fourier k
  map_zero_eq_one' := fourier_eval_zero k
  map_add_eq_mul' x y := by simp [fourier_apply,smul_add,AddCircle.toCircle_add]

omit b in
lemma character_div_eq_one {k : ℤ} {q : ℕ} (hq : q≠0) :
    character k ((1/(q : ℝ) : ℝ) : CircleX) = 1 ↔ (q : ℤ)∣k := by
  change (AddCircle.toCircle (k • ((1/(q : ℝ) : ℝ) : CircleX)) : ℂ) = 1 ↔ _
  rw [show (1 : ℂ) = (1 : Circle) by rfl,Circle.coe_inj,← AddCircle.toCircle_zero,
    (AddCircle.injective_toCircle (by norm_num : (1:ℝ)≠0)).eq_iff]
  rw [← AddCircle.coe_zsmul,AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul,mul_one,one_div]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hq' : (q:ℝ)≠0 := by exact_mod_cast hq
    have h : (k:ℝ) = (q:ℝ)*z := by rw [hz]; field_simp
    exact_mod_cast h
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hq' : (q:ℝ)≠0 := by exact_mod_cast hq
    rw [hz,Int.cast_mul,Int.cast_natCast]
    field_simp

omit b in
lemma character_div_mul (k : ℤ) (q r : ℕ) (d : ℕ) :
    character k ((d/(q*r : ℕ) : ℝ) : CircleX) =
      (character k ((1/(q*r : ℕ) : ℝ) : CircleX))^d := by
  rw [← AddChar.map_nsmul_eq_pow,← AddCircle.coe_nsmul]
  congr 1
  simp [nsmul_eq_mul,div_eq_mul_inv]

lemma integral_digitLaw_character_zero {b : ℕ → ℕ} (hb : ∀ i, 2≤b i)
    [∀ i, NeZero (b i)] (i : ℕ) (k : ℤ)
    (hdiv : (denominator b i : ℤ)∣k) (hnot : ¬(denominator b (i+1) : ℤ)∣k) :
    (∫ d : Fin (b i), character k ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX)
      ∂digitLaw b i) = 0 := by
  rw [integral_digitLaw]
  suffices ∑ d : Fin (b i), character k ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX)=0 by rw [this,mul_zero]
  simp_rw [denominator_succ,character_div_mul]
  rw [Fin.sum_univ_eq_sum_range]
  let z := character k ((1/(denominator b i*b i : ℕ) : ℝ) : CircleX)
  change ∑ d∈Finset.range (b i), z^d = 0
  have hz : z≠1 := by
    apply mt (character_div_eq_one (Nat.mul_ne_zero (denominator_pos hb i).ne' (NeZero.ne _))).mp
    simpa only [denominator_succ] using hnot
  have hpow : z^(b i)=1 := by
    rw [← AddChar.map_nsmul_eq_pow,← AddCircle.coe_nsmul]
    have hq : (denominator b i : ℝ)≠0 := by exact_mod_cast (denominator_pos hb i).ne'
    have hbi : (b i : ℝ)≠0 := by exact_mod_cast (show b i≠0 from NeZero.ne _)
    convert (character_div_eq_one (denominator_pos hb i).ne').mpr hdiv using 1
    congr 1
    simp only [nsmul_eq_mul,Nat.cast_mul]
    field_simp
  rw [geom_sum_eq hz,hpow,sub_self,zero_div]

lemma exists_nondividing_digit {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) {k : ℤ} (hk : k≠0) :
    ∃ i, (denominator b i : ℤ)∣k ∧ ¬(denominator b (i+1) : ℤ)∣k := by
  have hex : ∃ n, ¬(denominator b n : ℤ)∣k := by
    have hlarge : k.natAbs < denominator b (k.natAbs+1) :=
      (lt_of_le_of_lt (by omega : k.natAbs≤k.natAbs+1) (Nat.lt_two_pow_self)).trans_le
        (denominator_geometric hb (k.natAbs+1))
    refine ⟨k.natAbs+1,fun hd ↦ ?_⟩
    have hle := Int.natAbs_le_of_dvd_ne_zero hd hk
    simpa only [Int.natAbs_natCast] using not_le_of_gt hlarge hle
  let n := Nat.find hex
  have hn : n≠0 := by
    intro he
    have hh := Nat.find_spec hex
    change ¬(denominator b n : ℤ)∣k at hh
    simp [he] at hh
  refine ⟨n-1,?_,?_⟩
  · by_contra h
    exact Nat.find_min hex (show n-1<n by omega) h
  · simpa only [Nat.sub_add_cancel (by omega : 1≤n)] using Nat.find_spec hex

end

section

lemma character_sum {ι : Type uι} (k : ℤ) (s : Finset ι) (f : ι → CircleX) :
    character k (∑ i∈s, f i) = ∏ i∈s, character k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma integral_digitPartial {b : ℕ → ℕ} [∀ i, NeZero (b i)] (k : ℤ) (n : ℕ) :
    (∫ d : Digits b, character k ((∑ i∈Finset.range n, digitTerm b d i : ℝ) : CircleX)
      ∂uniformDigits b) =
    ∏ i∈Finset.range n, ∫ d : Fin (b i), character k ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX)
      ∂digitLaw b i := by
  classical
  have hcoe (d : Digits b) :
      ((∑ i∈Finset.range n, digitTerm b d i : ℝ) : CircleX) =
        ∑ i∈Finset.range n, (digitTerm b d i : CircleX) := by
    exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))) _ _
  simp_rw [hcoe,character_sum]
  let f := fun (d : ∀ i : Finset.range n, Fin (b i)) ↦
    ∏ i : Finset.range n, character k ((d i/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX)
  have hf : Measurable f := measurable_of_finite _
  have h := integral_restrict_infinitePi (fun i ↦ digitLaw b i) hf.aestronglyMeasurable
  change (∫ d, f ((Finset.range n).restrict d) ∂uniformDigits b) = _ at h
  simp only [f,Finset.restrict_def] at h
  change (∫ d : Digits b, ∏ i∈Finset.range n,
    character k ((d i/(denominator b (i+1) : ℕ) : ℝ) : CircleX) ∂uniformDigits b) = _
  have hp := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (i : Finset.range n) (d : Fin (b i)) ↦
      character k ((d/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX))
    (μ := fun i ↦ digitLaw b i)
  calc
    _ = ∫ d : Digits b, ∏ i : Finset.range n,
        character k ((d i/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX) ∂uniformDigits b := by
      apply integral_congr_ae
      exact ae_of_all _ fun d ↦ (Finset.prod_coe_sort (Finset.range n)
        (fun i ↦ character k ((d i/(denominator b (i+1) : ℕ) : ℝ) : CircleX))).symm
    _ = ∏ i : Finset.range n, ∫ d : Fin (b i), character k
        ((d/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX) ∂digitLaw b i := h.trans hp
    _ = _ := Finset.prod_coe_sort (Finset.range n)
      (fun i ↦ ∫ d : Fin (b i), character k
        ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX) ∂digitLaw b i)

lemma integral_endpoint_character {b : ℕ → ℕ} (hb : ∀ i, 2≤b i)
    [∀ i, NeZero (b i)] (k : ℤ) :
    (∫ d : Digits b, character k (endpoint b d) ∂uniformDigits b) = if k=0 then 1 else 0 := by
  classical
  by_cases hk : k=0
  · subst k
    change (∫ d : Digits b, fourier 0 (endpoint b d) ∂uniformDigits b) = _
    simp
  rw [ite_eq_right hk]
  let F := fun n (d : Digits b) ↦
    character k ((∑ i∈Finset.range n, digitTerm b d i : ℝ) : CircleX)
  have hmeas (n : ℕ) : Measurable (F n) :=
    (fourier k).continuous.measurable.comp ((AddCircle.continuous_mk' 1).measurable.comp
      (Finset.measurable_sum _ fun i _ ↦ measurable_digitTerm b i))
  have hlim := tendsto_integral_of_dominated_convergence (μ := uniformDigits b) (fun _ ↦ (1:ℝ))
    (fun n ↦ (hmeas n).aestronglyMeasurable) (integrable_const 1)
    (fun n ↦ ae_of_all _ fun d ↦ by exact (Circle.norm_coe _).le)
    (ae_of_all _ fun d ↦ ((fourier k).continuous.continuousAt.tendsto.comp
      ((AddCircle.continuous_mk' 1).continuousAt.tendsto.comp
        (digitTerm_summable hb d).hasSum.tendsto_sum_nat)))
  obtain ⟨i,hdiv,hnot⟩ := exists_nondividing_digit hb hk
  have hzero : ∀ᶠ n in atTop, (∫ d, F n d ∂uniformDigits b) = (0:ℂ) := by
    filter_upwards [eventually_gt_atTop i] with n hn
    rw [show (∫ d, F n d ∂uniformDigits b) = _ from integral_digitPartial k n]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) (integral_digitLaw_character_zero hb i k hdiv hnot)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun _ h ↦ h.symm))

lemma continuous_integral {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ] :
    Continuous (fun f : C(X,ℂ) ↦ ∫ x, f x ∂μ) := by
  apply LipschitzWith.continuous (K := 1)
  rw [lipschitzWith_iff_dist_le_mul]
  intro f g
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  have hi (f : C(X,ℂ)) : Integrable f μ :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)
  rw [← integral_sub (hi f) (hi g)]
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ fun x ↦ (f-g).norm_coe_le_norm x)

lemma circle_measure_eq_of_fourier (μ ν : Measure CircleX) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ k : ℤ, (∫ x, fourier k x ∂μ) = ∫ x, fourier k x ∂ν) : μ=ν := by
  have hi (m : Measure CircleX) [IsProbabilityMeasure m] (f : C(CircleX,ℂ)) : Integrable f m :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)
  have hc : IsClosed {f : C(CircleX,ℂ) | (∫ x, f x ∂μ) = ∫ x, f x ∂ν} :=
    isClosed_eq (continuous_integral μ) (continuous_integral ν)
  have hs : (↑(Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) : Set C(CircleX,ℂ)) ⊆
      {f | (∫ x, f x ∂μ) = ∫ x, f x ∂ν} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨k,rfl⟩ := hf; exact h k
    | zero => simp
    | add f g _ _ hf hg =>
      change (∫ x, f x+g x ∂μ) = ∫ x, f x+g x ∂ν
      rw [integral_add (hi μ f) (hi μ g),integral_add (hi ν f) (hi ν g),hf,hg]
    | smul a f _ hf =>
      change (∫ x, a • f x ∂μ) = ∫ x, a • f x ∂ν
      rw [integral_smul,integral_smul,hf]
  have hall := closure_minimal hs hc
  rw [← Submodule.topologicalClosure_coe,span_fourier_closure_eq_top,Submodule.top_coe] at hall
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(CircleX,ℂ) := ⟨fun x ↦ (f x:ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hfg := hall (a := g) (Set.mem_univ _)
  change (∫ x, (f x:ℂ) ∂μ) = ∫ x, (f x:ℂ) ∂ν at hfg
  simpa only [integral_complex_ofReal,Complex.ofReal_inj] using hfg

lemma endpoint_measurePreserving {b : ℕ → ℕ} (hb : ∀ i, 2≤b i)
    [∀ i, NeZero (b i)] : MeasurePreserving (endpoint b) (uniformDigits b) volume := by
  let : IsProbabilityMeasure (volume : Measure CircleX) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
    infer_instance
  refine ⟨measurable_endpoint b,?_⟩
  have : IsProbabilityMeasure ((uniformDigits b).map (endpoint b)) :=
    inferInstance
  apply circle_measure_eq_of_fourier
  intro k
  rw [integral_map (measurable_endpoint b).aemeasurable (fourier k).continuous.aestronglyMeasurable]
  change (∫ d, character k (endpoint b d) ∂uniformDigits b) = _
  rw [integral_endpoint_character hb]
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  have hm : (AddCircle.haarAddCircle : Measure CircleX) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; norm_num
  simpa [fourierCoeff,Pi.single_apply,eq_comm,hm] using hh.symm

end


def prefixNumeral (b : ℕ → ℕ) (d : Digits b) : ℕ → ℕ
  | 0 => 0
  | n+1 => b n * prefixNumeral b d n + d n

def scaledTail (b : ℕ → ℕ) (d : Digits b) (n : ℕ) : ℝ :=
  denominator b n * expansion b d - prefixNumeral b d n

def gridFree (b : ℕ → ℕ) : Set CircleX := {x | ∀ n, denominator b n • x  ≠  0}

lemma prefixNumeral_sum {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    ∑ i∈Finset.range n, digitTerm b d i = prefixNumeral b d n / (denominator b n : ℝ) := by
  induction n with
  | zero => simp [prefixNumeral]
  | succ n hn =>
    rw [Finset.sum_range_succ,hn]
    simp only [prefixNumeral,denominator_succ,digitTerm,Nat.cast_add,Nat.cast_mul]
    have hq : (denominator b n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos hb n).ne'
    have hb' : (b n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) (hb n)).ne'
    field_simp

lemma scaledTail_bounds {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    0 ≤ scaledTail b d n ∧ scaledTail b d n ≤ 1 := by
  have h := expansion_tail_bound hb d n
  rw [prefixNumeral_sum hb] at h
  have hq : (0:ℝ)<denominator b n := by exact_mod_cast denominator_pos hb n
  have he : scaledTail b d n = denominator b n * (expansion b d-prefixNumeral b d n/(denominator b n : ℝ)) := by
    unfold scaledTail; field_simp
  rw [he]
  exact ⟨mul_nonneg hq.le h.1, (mul_le_mul_of_nonneg_left h.2 hq.le).trans_eq (mul_inv_cancel₀ hq.ne')⟩

lemma scaledTail_coe {b : ℕ → ℕ} (d : Digits b) (n : ℕ) :
    ((scaledTail b d n : ℝ) : CircleX) = denominator b n • endpoint b d := by
  simp only [scaledTail,AddCircle.coe_sub,← nsmul_eq_mul,AddCircle.coe_nsmul,endpoint]
  have h : ((prefixNumeral b d n : ℝ) : CircleX) = 0 := by
    rw [show (prefixNumeral b d n : ℝ) = prefixNumeral b d n • (1:ℝ) by simp, AddCircle.coe_nsmul, AddCircle.coe_period, smul_zero]
  rw [h,sub_zero]

lemma ae_gridFree (b : ℕ → ℕ) (hb : ∀ i, 2 ≤ b i) :
    ∀ᵐ x : CircleX ∂volume, x ∈ gridFree b := by
  change ∀ᵐ x : CircleX ∂volume, ∀ n, denominator b n • x ≠ 0
  rw [ae_all_iff]
  intro n
  have hp : MeasurePreserving (fun x : CircleX ↦ denominator b n • x) volume volume := by
    simpa only [natCast_zsmul] using
      (Measure.measurePreserving_zsmul (volume : Measure CircleX)
        (by exact_mod_cast (denominator_pos hb n).ne' : (denominator b n : ℤ) ≠ 0))
  have hz : ∀ᵐ x : CircleX ∂volume, x ≠ 0 := by
    apply ae_iff.mpr
    simp only [not_not, Set.ofPred_eq_eq_singleton]
    rw [← Metric.closedBall_zero,AddCircle.volume_closedBall]
    norm_num
  exact hp.quasiMeasurePreserving.ae (p := fun x : CircleX => x ≠ 0) hz

lemma scaledTail_lt_one {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) : scaledTail b d n<1 := by
  apply lt_of_le_of_ne (scaledTail_bounds hb d n).2
  intro he
  apply hd n
  rw [← scaledTail_coe d n,he]
  exact_mod_cast (AddCircle.coe_period (1:ℝ))

lemma scaledTail_repr {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) :
    ((AddCircle.measurableEquivIco 1 0 (denominator b n • endpoint b d)).val : ℝ) =
      scaledTail b d n := by
  rw [← scaledTail_coe d n]
  change (AddCircle.equivIco 1 0 ((scaledTail b d n : ℝ) : CircleX)).val = _
  rw [AddCircle.coe_equivIco_mk_apply]
  simp only [div_one,mul_one]
  exact Int.fract_eq_self.mpr ⟨(scaledTail_bounds hb d n).1,scaledTail_lt_one hb d hd n⟩

lemma scaledTail_recurrence (b : ℕ → ℕ) (d : Digits b) (n : ℕ) :
    (b n : ℝ)*scaledTail b d n = (d n : ℝ)+scaledTail b d (n+1) := by
  simp only [scaledTail,prefixNumeral,denominator_succ,Nat.cast_add,Nat.cast_mul]
  ring

lemma digit_interval {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) :
    (d n : ℝ)/(b n : ℝ)  ≤  scaledTail b d n ∧
    scaledTail b d n < ((d n : ℝ)+1)/(b n : ℝ) := by
  have hpos : (0:ℝ)<b n := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb n)
  rw [div_le_iff₀ hpos,lt_div_iff₀ hpos,mul_comm (scaledTail b d n),scaledTail_recurrence]
  exact ⟨le_add_of_nonneg_right (scaledTail_bounds hb d (n+1)).1,
    add_lt_add_right (scaledTail_lt_one hb d hd (n+1)) _⟩

lemma recover_digit {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) :
    ⌊(b n : ℝ)*((AddCircle.measurableEquivIco 1 0 (denominator b n • endpoint b d)).val : ℝ)⌋ =
      (d n : ℤ) := by
  rw [scaledTail_repr hb d hd,scaledTail_recurrence]
  apply Int.floor_eq_iff.mpr
  push_cast
  exact ⟨le_add_of_nonneg_right (scaledTail_bounds hb d (n+1)).1,
    add_lt_add_right (scaledTail_lt_one hb d hd (n+1)) _⟩

lemma scaledTail_tsum {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    scaledTail b d n = (denominator b n : ℝ) * ∑' i, digitTerm b d (i+n) := by
  have h := (digitTerm_summable hb d).sum_add_tsum_nat_add n
  rw [prefixNumeral_sum hb] at h
  change _ = expansion b d at h
  rw [scaledTail,← h,mul_add]
  have hq : (denominator b n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos hb n).ne'
  rw [mul_div_cancel₀ _ hq]
  ring

lemma scaledTail_mono {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) {d e : Digits b}
    (hde : ∀ i, d i ≤ e i) (n : ℕ) : scaledTail b d n ≤ scaledTail b e n := by
  rw [scaledTail_tsum hb,scaledTail_tsum hb]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply ((digitTerm_summable hb d).comp_injective (add_left_injective n)).tsum_le_tsum _
    ((digitTerm_summable hb e).comp_injective (add_left_injective n))
  intro i
  exact div_le_div_of_nonneg_right (by exact_mod_cast hde (i+n)) (by positivity)



end CircleDigits

end

end OAI
