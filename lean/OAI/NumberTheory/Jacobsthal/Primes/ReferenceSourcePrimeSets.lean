import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceCutoffRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceMertens

open _root_.Filter Asymptotics
open scoped Topology
open ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

noncomputable def normalization (w : ℝ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant)/(Real.log w*primeProduct w)

noncomputable def referenceProduct (w b : ℝ) (closed : Bool) : ℝ :=
  availableProduct w (w^b) closed

theorem normalization_pos {w : ℝ} (hw : 1 < w) : 0 < normalization w :=
  div_pos (Real.exp_pos _) (mul_pos (Real.log_pos hw) (actual_primeProduct_pos w))

theorem normalization_eq_exp {w : ℝ} (hw : 1 < w) :
    normalization w=Real.exp (-_root_.Erdos970.Mertens.E₃ w) := by
  unfold normalization primeProduct
  rw [_root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hw,Real.exp_neg]
  field_simp [ne_of_gt (Real.log_pos hw)]
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]

theorem normalization_tendsto_one : Tendsto normalization atTop (𝓝 1) := by
  have h := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have hl : Tendsto (fun w => Real.exp (-_root_.Erdos970.Mertens.E₃ w)) atTop (𝓝 1) := by
    convert! Real.continuous_exp.continuousAt.tendsto.comp h.neg using 1
    norm_num
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with w hw
  exact (normalization_eq_exp hw).symm

theorem closed_normalized_identity {w b : ℝ} (hw : 1 < w) (hb : 1 ≤ b) :
    referenceProduct w b true/(normalization w/b)=
      primeProduct (w^b)/(Real.exp (-Real.eulerMascheroniConstant)/Real.log (w^b)) := by
  have hw0 : 0 < w := by linarith
  have hb0 : 0 < b := by linarith
  have hwb : w ≤ w^b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw.le hb
  rw [referenceProduct,closed_product_ratio hw0.le hwb,normalization,Real.log_rpow hw0]
  field_simp [ne_of_gt (actual_primeProduct_pos w),ne_of_gt (Real.log_pos hw),ne_of_gt hb0]

theorem exp_error_mono_rate {c₁ c₂ t : ℝ} (hc : c₂ ≤ c₁) :
    Real.exp (-c₁*Real.sqrt t) ≤ Real.exp (-c₂*Real.sqrt t) :=
  Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg t])

theorem reference_product_strong : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,
      |referenceProduct w b closed/(normalization w/b)-1| ≤
        C*Real.exp (-c*Real.sqrt (b*Real.log w)) := by
  obtain ⟨c,C,x₀,hc,hC,hx₀,hprod⟩ := prime_product_strong
  let c' := min c 1
  let W := max x₀ (Real.exp 1)
  have hc' : 0 < c' := lt_min hc zero_lt_one
  refine ⟨c',3*C+2,W,hc',by positivity,
    (by have hh := le_max_left x₀ (Real.exp 1); dsimp [W]; linarith),?_⟩
  intro w hw b hb closed
  have hwX : x₀ ≤ w := (le_max_left _ _).trans hw
  have hwE : Real.exp 1 ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := by linarith [hx₀.trans hwX]
  have hw0 : 0 < w := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hxw : w ≤ w^b := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1.le hb1
  have hx2 : 2 ≤ w^b := (hx₀.trans hwX).trans hxw
  have hx0 : 0 < w^b := Real.rpow_pos_of_pos hw0 b
  have hlog : 1 ≤ Real.log (w^b) := by
    have hh := Real.log_le_log (Real.exp_pos 1) (hwE.trans hxw)
    simpa only [Real.log_exp] using hh
  let E := Real.exp (-c'*Real.sqrt (b*Real.log w))
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc'.le) (Real.sqrt_nonneg _))
  have hclosed : |referenceProduct w b true/(normalization w/b)-1| ≤ C*E := by
    rw [closed_normalized_identity hw1 hb1]
    have h := hprod (w^b) (hwX.trans hxw)
    have hm := exp_error_mono_rate (t:=Real.log (w^b)) (min_le_left c 1)
    rw [Real.log_rpow hw0] at h hm ⊢
    exact h.trans (mul_le_mul_of_nonneg_left hm hC.le)
  cases closed with
  | true => exact hclosed.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ 3*C+2) hEpos.le)
  | false =>
    let D := normalization w/b
    let q := referenceProduct w b true/D
    let k := referenceProduct w b false/referenceProduct w b true
    have hD : 0 < D := div_pos (normalization_pos hw1) hb0
    have hP : 0 < referenceProduct w b true := availableProduct_pos _ _ _
    have hq0 : 0 < q := div_pos hP hD
    have hq : q ≤ C+1 := by
      have hh := (abs_le.mp hclosed).2
      have hh' := mul_le_mul_of_nonneg_left hE1 hC.le
      dsimp only [q,D]
      linarith
    have hk : |k-1| ≤ 2/(w^b) := endpoint_relative_bound hx2
    have hrec : 1/(w^b) ≤ E := by
      have h := ErdosPrimeInputs.MertensStrong.reciprocal_le_decay (min_le_right c 1) hx0 hlog
      simpa only [E,ErdosPrimeInputs.PrimeErrorDecay.decay,Real.log_rpow hw0] using h
    have heq : referenceProduct w b false/D=k*q := by
      dsimp only [k,q]
      field_simp
    change |referenceProduct w b false/D-1| ≤ (3*C+2)*E
    rw [heq]
    calc
      _ = |(k-1)*q+(q-1)| := by congr 1; ring
      _ ≤ |(k-1)*q|+|q-1| := abs_add_le _ _
      _ = |k-1| *q+|q-1| := by rw [abs_mul,abs_of_pos hq0]
      _ ≤ (2/(w^b))*(C+1)+C*E :=
        add_le_add (mul_le_mul hk hq hq0.le (by positivity)) hclosed
      _ ≤ 2*E*(C+1)+C*E := by
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ C+1)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrec (by norm_num : (0:ℝ) ≤ 2)
      _ = _ := by ring

end NumberTheoryLean.ReferenceMertens

end

section

namespace NumberTheoryLean.ReferenceSourcePrimeSets

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeTiltGeometry ReferenceAdmission ReferencePruning ReferenceProductsBasics
open ReferenceMertens ReferenceCutoffRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

noncomputable def sourcePrimes (w b : ℝ) (closed : Bool) : Finset ℕ := availablePrimes w (w^b) closed
noncomputable def highPrimes (w b : ℝ) (closed : Bool) : Finset ℕ :=
  (sourcePrimes w b closed).filter (fun p => w^(2:ℝ)<(p:ℝ))

theorem availablePrimes_membership {a x : ℝ} (hx : 0 ≤ x) (closed : Bool) (p : ℕ) :
    p ∈ availablePrimes a x closed ↔ p.Prime ∧ a<(p:ℝ) ∧ (if closed then (p:ℝ) ≤ x else (p:ℝ)<x) := by
  simp only [availablePrimes,primesBetween,Finset.mem_filter,Nat.mem_primesLE,Nat.le_floor_iff hx]
  cases closed
  · simp only [Bool.false_eq_true,false_or,ite_false]
    constructor
    · rintro ⟨⟨⟨_,hp⟩,ha⟩,hx⟩
      exact ⟨hp,ha,hx⟩
    · rintro ⟨hp,ha,hx⟩
      exact ⟨⟨⟨hx.le,hp⟩,ha⟩,hx⟩
  · simp only [true_or,ite_true,and_true]
    tauto

theorem sourcePrimes_membership {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (p : ℕ) :
    p ∈ sourcePrimes w b closed ↔ p.Prime ∧ 1<primeExponent w p ∧ capGuard closed b (primeExponent w p) := by
  rw [sourcePrimes,availablePrimes_membership (Real.rpow_pos_of_pos (by linarith : 0 < w) b).le]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    refine ⟨hp,?_,?_⟩
    · exact (lt_exponent_iff hw hp0).mpr (by simpa only [Real.rpow_one] using hlo)
    · cases closed with
      | false => exact (exponent_lt_iff hw hp0).mpr hhi
      | true => exact (exponent_le_iff hw hp0).mpr hhi
  · rintro ⟨hp,hlo,hhi⟩
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    refine ⟨hp,?_,?_⟩
    · simpa only [Real.rpow_one] using (lt_exponent_iff hw hp0).mp hlo
    · cases closed with
      | false => exact (exponent_lt_iff hw hp0).mp hhi
      | true => exact (exponent_le_iff hw hp0).mp hhi

theorem highPrimes_membership {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (p : ℕ) :
    p ∈ highPrimes w b closed ↔ p.Prime ∧ 2<primeExponent w p ∧ capGuard closed b (primeExponent w p) := by
  rw [highPrimes,Finset.mem_filter,sourcePrimes_membership hw]
  constructor
  · rintro ⟨⟨hp,_hlo,hcap⟩,hhi⟩
    exact ⟨hp,(lt_exponent_iff hw (by exact_mod_cast hp.pos)).mpr hhi,hcap⟩
  · rintro ⟨hp,hhi,hcap⟩
    exact ⟨⟨hp,by linarith,hcap⟩,(lt_exponent_iff hw (by exact_mod_cast hp.pos)).mp hhi⟩

@[simp] theorem sourcePrimes_boundary (w : ℝ) : sourcePrimes w 2 true=boundaryPrimes w := by
  simp only [sourcePrimes,availablePrimes_closed,boundaryPrimes]

theorem boundary_subset_source {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    boundaryPrimes w ⊆ sourcePrimes w b closed := by
  intro p hp
  have hpl := (sourcePrimes_membership hw 2 true p).mp (by rwa [sourcePrimes_boundary])
  apply (sourcePrimes_membership hw b closed p).mpr
  refine ⟨hpl.1,hpl.2.1,?_⟩
  have hle : primeExponent w p ≤ 2 := hpl.2.2
  cases closed with
  | false => exact hle.trans_lt hb
  | true => exact hle.trans hb.le

theorem sourcePrimes_partition {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    sourcePrimes w b closed=highPrimes w b closed ∪ boundaryPrimes w := by
  ext p
  constructor
  · intro hp
    by_cases hhi : w^(2:ℝ)<(p:ℝ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp,hhi⟩))
    · have hpm := (sourcePrimes_membership hw b closed p).mp hp
      apply Finset.mem_union.mpr
      right
      rw [← sourcePrimes_boundary]
      apply (sourcePrimes_membership hw 2 true p).mpr
      refine ⟨hpm.1,hpm.2.1,?_⟩
      exact (exponent_le_iff hw (by exact_mod_cast hpm.1.pos)).mpr (le_of_not_gt hhi)
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · exact boundary_subset_source hw hb closed hp

theorem highPrimes_above_boundary {w b : ℝ} (hw : 1 < w) (closed : Bool) :
    Above (highPrimes w b closed) (boundaryPrimes w) := by
  intro p hp q hq
  have hpHi := (Finset.mem_filter.mp hp).2
  have hqB := boundary_prime_exponent_upper hw hq
  have hqP : q.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have hqLe := (exponent_le_iff hw (by exact_mod_cast hqP.pos)).mp hqB
  exact_mod_cast hqLe.trans_lt hpHi

theorem rpow_primeExponent {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p.Prime) :
    w^primeExponent w p=(p:ℝ) := by
  have hw0 : 0 < w := by linarith
  rw [Real.rpow_def_of_pos hw0]
  have he : Real.log w*primeExponent w p=Real.log p := by
    unfold primeExponent
    field_simp [ne_of_gt (Real.log_pos hw)]
  rw [he,Real.exp_log (by exact_mod_cast hp.pos)]

theorem sourcePrimes_at_selected {w b : ℝ} (hw : 1 < w) (closed : Bool) {p : ℕ}
    (hp : p ∈ sourcePrimes w b closed) :
    sourcePrimes w (primeExponent w p) false=(sourcePrimes w b closed).filter (fun q => q<p) := by
  have hpM := (sourcePrimes_membership hw b closed p).mp hp
  have hpCap : primeExponent w p ≤ b := by
    cases closed with
    | false => exact hpM.2.2.le
    | true => exact hpM.2.2
  ext q
  rw [sourcePrimes_membership hw,Finset.mem_filter,sourcePrimes_membership hw]
  constructor
  · rintro ⟨hq,hqLo,hqCap⟩
    have hqCap' : primeExponent w q < primeExponent w p := hqCap
    have hqP : q<p := by
      have hreal := (exponent_lt_iff hw (by exact_mod_cast hq.pos)).mp hqCap'
      rw [rpow_primeExponent hw hpM.1] at hreal
      exact_mod_cast hreal
    refine ⟨⟨hq,hqLo,?_⟩,hqP⟩
    cases closed with
    | false => exact hqCap'.trans_le hpCap
    | true => exact hqCap'.le.trans hpCap
  · rintro ⟨⟨hq,hqLo,_hqCap⟩,hqp⟩
    refine ⟨hq,hqLo,?_⟩
    apply (exponent_lt_iff hw (by exact_mod_cast hq.pos)).mpr
    rw [rpow_primeExponent hw hpM.1]
    exact_mod_cast hqp

end NumberTheoryLean.ReferenceSourcePrimeSets

end

end Erdos970

end OAI
