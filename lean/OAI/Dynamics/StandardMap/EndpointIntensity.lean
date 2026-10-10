import OAI.Dynamics.StandardMap.EndpointCompact

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma preimage_sub_Ico (a b r:ℝ) : (fun x:ℝ => x-r)⁻¹'Ico a b=Ico (a+r) (b+r) := by
  ext x; simp only [mem_preimage,mem_Ico]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
lemma invariant_Ico_translate (μ:Measure ℝ) (r:ℝ) (h:μ.map (fun x:ℝ => x-r)=μ) (a b:ℝ) :
    μ (Ico (a+r) (b+r))=μ (Ico a b) := by
  rw [←preimage_sub_Ico,←Measure.map_apply (show Measurable (fun x:ℝ => x-r) from measurable_id.sub measurable_const) measurableSet_Ico,h]
lemma measure_Ico_split (μ:Measure ℝ) {a b c:ℝ} (hab:a≤b) (hbc:b≤c) :
    μ (Ico a c)=μ (Ico a b)+μ (Ico b c) := by
  have hu : Ico a c=Ico a b∪Ico b c := by
    ext x; simp only [mem_Ico,mem_union]; constructor
    · rintro ⟨ha,hc⟩; by_cases h:x<b
      · exact Or.inl ⟨ha,h⟩
      · exact Or.inr ⟨le_of_not_gt h,hc⟩
    · rintro (⟨ha,hb⟩|⟨hb,hc⟩)
      · exact ⟨ha,hb.trans_le hbc⟩
      · exact ⟨hab.trans hb,hc⟩
  rw [hu,measure_union (by rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy.1) hx.2) measurableSet_Ico]
lemma stationary_Ico_nat (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (a:ℤ) (n:ℕ) :
    μ (Ico (a:ℝ) ((a:ℝ)+(n:ℝ)))=(n:ℝ≥0∞)*μ (Ico 0 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n+1:ℕ)))=μ (Ico 0 1) := by
      have hh := invariant_Ico_translate μ (dyadicInt (a+n):ℝ) (ht (dyadicInt (a+n))) 0 1
      convert! hh using 2 ; simp only [dyadicInt_val,Int.cast_add,Int.cast_natCast,Nat.cast_add,Nat.cast_one] ; ring_nf
    rw [show ((a:ℝ)+(n+1:ℕ))=(a:ℝ)+(n:ℝ)+1 by push_cast; ring,
      measure_Ico_split μ (show (a:ℝ)≤(a:ℝ)+(n:ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg n)) (by linarith),ih]
    have he' : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n:ℝ)+1))=μ (Ico 0 1) := by convert! he using 2 ; push_cast ; ring_nf
    rw [he',Nat.cast_add,Nat.cast_one,add_mul,one_mul]
lemma stationary_scaling_zero (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ)
    (hs:μ.map (fun x:ℝ => x/2)=μ) (hf:μ (Ico 0 1)<∞) : μ=0 := by
  have htwo : μ (Ico 0 2)=μ (Ico 0 1) := by
    have he : (fun x:ℝ => x/2)⁻¹'Ico 0 1=Ico 0 2 := by ext x; simp only [mem_preimage,mem_Ico]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [←he,←Measure.map_apply (show Measurable (fun x:ℝ => x/2) from measurable_id.div_const 2) measurableSet_Ico,hs]
  have h1 : μ (Ico 1 2)=μ (Ico 0 1) := by
    convert! invariant_Ico_translate μ (dyadicInt 1:ℝ) (ht (dyadicInt 1)) 0 1 using 2 ; norm_num
  have hz : μ (Ico 0 1)=0 := by
    rw [measure_Ico_split μ (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2),h1] at htwo
    apply (ENNReal.add_left_inj hf.ne).mp
    simpa only [zero_add] using htwo
  apply Measure.measure_univ_eq_zero.mp
  have he : (univ:Set ℝ)=⋃n:ℤ,Ico (n:ℝ) ((n:ℝ)+1) := by
    ext x; simp only [mem_univ,mem_iUnion,true_iff]
    exact ⟨⌊x⌋,Int.floor_le x,Int.lt_floor_add_one x⟩
  rw [he]
  apply measure_iUnion_null
  intro n
  have hh := stationary_Ico_nat μ ht n 1
  simpa only [Nat.cast_one,hz,mul_zero] using hh
end StandardMapEntropy

end OAI
