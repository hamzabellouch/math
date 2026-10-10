import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma log_probability_fifth {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (1-Real.log p)^5 ≤ 251^5*p^(-1/50:ℝ) := by
  have hlog : 0 ≤ 1-Real.log p := by linarith [Real.log_nonpos hp.le hp1]
  have h := Real.log_le_rpow_div (inv_nonneg.mpr hp.le) (by norm_num : (0:ℝ) < 1/250)
  rw [Real.log_inv,Real.inv_rpow hp.le,←Real.rpow_neg hp.le] at h
  have hpow : 1 ≤ p^(-1/250:ℝ) := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1 (by norm_num)
  have hlin : 1-Real.log p ≤ 251*p^(-1/250:ℝ) := by linarith
  have H := pow_le_pow_left₀ hlog hlin 5
  apply H.trans_eq
  rw [mul_pow]
  congr 1
  rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]
  norm_num

lemma probability_of_log_fifth {p b d : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hb : 0 < b) (hd : 0 ≤ d)
    (h : b^2 ≤ d*(1-Real.log p)^5) :
    p ≤ (251^5*d)^50/b^100 := by
  have H := h.trans (mul_le_mul_of_nonneg_left (log_probability_fifth hp hp1) hd)
  have hpw : 0 < p^(1/50:ℝ) := Real.rpow_pos_of_pos hp _
  have H' := mul_le_mul_of_nonneg_right H hpw.le
  have he : p^(-1/50:ℝ)*p^(1/50:ℝ)=1 := by
    rw [←Real.rpow_add hp]; norm_num
  have HH : b^2*p^(1/50:ℝ) ≤ 251^5*d := by
    calc
      _ ≤ d*(251^5*p^(-1/50:ℝ))*p^(1/50:ℝ) := H'
      _ = (251^5*d)*(p^(-1/50:ℝ)*p^(1/50:ℝ)) := by ring
      _ = _ := by rw [he,mul_one]
  have Hpow := pow_le_pow_left₀ (by positivity : 0 ≤ b^2*p^(1/50:ℝ)) HH 50
  have he' : (p^(1/50:ℝ))^50=p := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]; norm_num
  rw [mul_pow,he',←pow_mul] at Hpow
  norm_num only [Nat.mul_one] at Hpow
  apply (le_div_iff₀ (pow_pos hb 100)).mpr
  nlinarith only [Hpow]
end NeutralAtom

namespace NeutralAtom
lemma le_discrete_tail_sum (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k)
    {x : ℝ} (_ : 0 ≤ x) (N : ℕ) (hxN : x ≤ t N) :
    x ≤ t 0+∑ k∈Finset.range N,t (k+1)*(if t k<x then 1 else 0) := by
  induction N with
  | zero => simpa using hxN
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : x ≤ t N
    · have hn : 0 ≤ t (N+1)*(if t N<x then 1 else 0) := by split_ifs <;> simp only [mul_one,mul_zero]; exact ht _; exact le_rfl
      linarith [ih h]
    · rw [ite_eq_left (lt_of_not_ge h),mul_one]
      have hsum : 0 ≤ ∑ k∈Finset.range N,t (k+1)*(if t k<x then 1 else 0) := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs <;> simp only [mul_one,mul_zero]; exact ht _; exact le_rfl
      linarith [ht 0]

lemma firstMoment_le_discrete_tails {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ z,0 ≤ f z) (t b : ℕ → ℝ) (ht : ∀ k,0 ≤ t k)
    (N : ℕ) (hbound : ∀ z,f z ≤ t N)
    (htail : ∀ k,P.real {z | t k<f z} ≤ b k)
    (hsum : Summable (fun k => t (k+1)*b k)) :
    (∫ z,f z ∂P) ≤ t 0+∑' k,t (k+1)*b k := by
  let F : ℕ → Ω → ℝ := fun k => ({z | t k<f z}).indicator (fun _ => (1:ℝ))
  have hF : ∀ k,Integrable (F k) P := fun k =>
    (integrable_const 1).indicator (measurableSet_lt measurable_const hf)
  have hfi : Integrable f P := by
    apply Integrable.of_bound hf.aestronglyMeasurable (t N)
    exact Eventually.of_forall (fun z => by rw [Real.norm_of_nonneg (hf0 z)]; exact hbound z)
  have hgi : Integrable (fun z => t 0+∑ k∈Finset.range N,t (k+1)*F k z) P :=
    (integrable_const _).add (integrable_finsetSum _ (fun k _ => (hF k).const_mul _))
  have H := integral_mono hfi hgi (fun z => le_discrete_tail_sum t ht (hf0 z) N (hbound z))
  have he : (∫ z,t 0+∑ k∈Finset.range N,t (k+1)*F k z ∂P)=
      t 0+∑ k∈Finset.range N,t (k+1)*P.real {z | t k<f z} := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => (hF k).const_mul _)),
      integral_finsetSum _ (fun k _ => (hF k).const_mul _)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    congr 1
    exact integral_indicator_const _ (measurableSet_lt measurable_const hf) |>.trans (by simp)
  rw [he] at H
  apply H.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ k∈Finset.range N,t (k+1)*b k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (htail k) (ht _))
    _ ≤ ∑' k,t (k+1)*b k :=
      hsum.sum_le_tsum _ (fun k _ => mul_nonneg (ht _) (measureReal_nonneg.trans (htail k)))

lemma positive_part_tail {Ω : Type*} (f : Ω → ℝ) {C k : ℝ} (hk : 0 ≤ k) :
    {z | k < max (f z-C) 0}={z | C+k < f z} := by
  ext z
  simp only [mem_ofPred_eq,lt_max_iff,not_lt_of_ge hk,or_false]
  constructor <;> intro h <;> linarith

theorem logarithmic_tail_integral : ∃ K : ℝ,0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ}, Measurable f → ∀ {B C d : ℝ}, (∀ z,f z ≤ B) → 1 ≤ C → 0 ≤ d →
    (∀ b : ℝ,2*C ≤ b → 0 < P.real {z | b<f z} →
      (b-C)^2 ≤ d*(1-Real.log (P.real {z | b<f z}))^5) →
    (∫ z,max (f z-2*C) 0 ∂P) ≤ K*d^50 := by
  let W := fun k : ℕ => ((k:ℝ)+1)^(-99:ℝ)
  have hW : Summable W := by
    have H := (Real.summable_nat_rpow.mpr (by norm_num : (-99:ℝ) < -1))
    simpa only [W,Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr H
  let K : ℝ := 251^(250:ℕ)*((∑' k,W k)+1)
  have hW0 : ∀ k,0 ≤ W k := fun k => by dsimp [W]; positivity
  have hK : 0 < K := mul_pos (pow_pos (by norm_num) 250) (by have h : 0 ≤ ∑' k,W k := tsum_nonneg hW0; linarith)
  refine ⟨K,hK,?_⟩
  intro Ω inst P instP f hf B C d hB hC hd hprob
  let A : ℝ := (251^5*d)^50
  have hA : 0 ≤ A := pow_nonneg (mul_nonneg (pow_nonneg (by norm_num) 5) hd) 50
  let t : ℕ → ℝ := fun k => k
  let b : ℕ → ℝ := fun k => A/((k:ℝ)+1)^100
  have hsEq (k : ℕ) : t (k+1)*b k=A*W k := by
    have hk : (k:ℝ)+1 ≠ 0 := by positivity
    simp only [t,b,W,Nat.cast_add,Nat.cast_one]
    rw [show (-99:ℝ)= -((99:ℕ):ℝ) by norm_num,Real.rpow_neg_natCast]
    simp only [zpow_neg,zpow_natCast]
    rw [show (((k:ℝ)+1)^100)=((k:ℝ)+1)*((k:ℝ)+1)^99 by rw [pow_succ']]
    field_simp [hk]
  have hsum : Summable (fun k => t (k+1)*b k) := by
    simp_rw [hsEq]
    exact hW.mul_left A
  have htail (k : ℕ) : P.real {z | t k < max (f z-2*C) 0} ≤ b k := by
    rw [positive_part_tail f (show 0 ≤ t k from Nat.cast_nonneg k)]
    by_cases hp : 0 < P.real {z | 2*C+(k:ℝ)<f z}
    · have H := probability_of_log_fifth hp (measureReal_le_one)
        (by have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k; linarith : 0 < (2*C+(k:ℝ))-C) hd
        (hprob (2*C+k) (by have hk := Nat.cast_nonneg (α:=ℝ) k; linarith) hp)
      apply H.trans
      apply div_le_div_of_nonneg_left hA (by positivity)
      apply pow_le_pow_left₀ (by positivity : 0 ≤ (k:ℝ)+1)
      linarith
    · have he : P.real {z | 2*C+(k:ℝ)<f z}=0 := le_antisymm (le_of_not_gt hp) measureReal_nonneg
      change P.real {z | 2*C+(k:ℝ)<f z} ≤ _
      rw [he]
      exact div_nonneg hA (pow_nonneg (by positivity) 100)
  obtain ⟨N,hN⟩ := exists_nat_ge B
  have hbnd (z : Ω) : max (f z-2*C) 0 ≤ t N := by
    apply max_le
    · dsimp [t]; linarith [hB z]
    · exact Nat.cast_nonneg N
  have H := firstMoment_le_discrete_tails P ((hf.sub measurable_const).max measurable_const)
    (fun _ => le_max_right _ _) t b (fun k => Nat.cast_nonneg k) N hbnd htail hsum
  simp_rw [hsEq,tsum_mul_left] at H
  simp only [t,Nat.cast_zero,zero_add] at H
  apply H.trans
  have he : A=251^(250:ℕ)*d^50 := by dsimp [A]; rw [mul_pow,←pow_mul]
  rw [he]
  dsimp [K]
  calc
    _ ≤ 251^250*d^50*((∑' k,W k)+1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (mul_nonneg (pow_nonneg (by norm_num) 250) (pow_nonneg hd 50))
    _ = _ := by ac_rfl
end NeutralAtom
end

end

end OAI
