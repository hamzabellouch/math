import OAI.Dynamics.StandardMap.ArrayGrid

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
noncomputable def dyadicUnit (n : ℕ) : DyadicTime := ⟨(1:ℝ)/(2:ℝ)^n,n,1,by simp⟩
@[simp] lemma dyadicUnit_val (n : ℕ) : (dyadicUnit n:ℝ)=(1:ℝ)/(2:ℝ)^n := rfl
lemma dyadicUnit_pos (n : ℕ) : 0<(dyadicUnit n:ℝ) := by change 0<(1:ℝ)/(2:ℝ)^n; positivity
lemma dyadic_common_grid (s t : DyadicTime) :
    ∃ m : ℕ, ∃ a b : ℤ,s=a • dyadicUnit m ∧ t=b • dyadicUnit m := by
  obtain ⟨n,a,hs⟩ := dyadicTime_mem s
  obtain ⟨m,b,ht⟩ := dyadicTime_mem t
  refine ⟨n+m,a*2^m,b*2^n,?_,?_⟩
  · apply Subtype.ext
    rw [dyadic_zsmul_val,dyadicUnit_val,hs,pow_add]
    push_cast
    field_simp
  · apply Subtype.ext
    rw [dyadic_zsmul_val,dyadicUnit_val,ht,pow_add]
    push_cast
    field_simp
lemma dyadic_unit_power (n : ℕ) : (2:ℤ)^n • dyadicUnit n=dyadicInt 1 := by
  apply Subtype.ext
  simp only [dyadic_zsmul_val,dyadicUnit_val,dyadicInt_val,Int.cast_pow,Int.cast_ofNat,Int.cast_one]
  field_simp
lemma array_affine_values_of_zero (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (s t : DyadicTime) : d.val s t=d.val 0 (dyadicInt 1)*|(t:ℝ)-(s:ℝ)| := by
  obtain ⟨m,a,b,rfl,rfl⟩ := dyadic_common_grid s t
  have hpow : (0:ℝ)<(2:ℝ)^m := by positivity
  have hc := array_grid_distance d hz (dyadicUnit m) (dyadicUnit_pos m) 0 ((2:ℤ)^m)
  simp only [zero_smul,dyadic_unit_power,Int.cast_pow,Int.cast_ofNat,Int.cast_zero,sub_zero,abs_of_pos hpow] at hc
  have he := array_grid_distance d hz (dyadicUnit m) (dyadicUnit_pos m) a b
  rw [he,dyadic_zsmul_val,dyadic_zsmul_val,dyadicUnit_val]
  rw [show (b:ℝ)*((1:ℝ)/2^m)-(a:ℝ)*((1:ℝ)/2^m)=((b:ℝ)-(a:ℝ))*((1:ℝ)/2^m) by ring,abs_mul,
    abs_of_pos (by positivity : (0:ℝ)<1/(2:ℝ)^m),hc]
  field_simp
lemma array_affine_of_zero_tests (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0) : d∈affineLocus := by
  let w := d.val 0 (dyadicInt 1)
  have hw0 : 0 ≤ w := d.property.1 _ _
  have hw1 : w ≤ 1 := by
    by_contra hn
    have hp : 0<w-1 := by linarith
    obtain ⟨n,hn⟩ := exists_nat_gt (2/(w-1))
    have hbig : 2<(n:ℝ)*(w-1) := (div_lt_iff₀ hp).mp hn
    have hb := d.property.2.2.2.2 0 (dyadicInt (n:ℤ))
    rw [array_affine_values_of_zero d hz] at hb
    simp only [dyadicInt_val,Int.cast_natCast,ZeroMemClass.coe_zero,sub_zero,Nat.abs_cast] at hb
    change w*(n:ℝ) ≤ (n:ℝ)+2 at hb
    nlinarith
  refine ⟨⟨w,hw0,hw1⟩,?_⟩
  apply Subtype.ext
  funext s t
  exact (array_affine_values_of_zero d hz s t).symm
abbrev ArrayTestIndex := {p : DyadicTime × DyadicTime // (p.1:ℝ)<(p.2:ℝ)}
noncomputable def arrayTest (i : ArrayTestIndex) (d : DistanceArray) : ℝ := arrayJ i.val.1 i.val.2 d+arrayV i.val.1 i.val.2 d
lemma continuous_arrayTest (i : ArrayTestIndex) : Continuous (arrayTest i) :=
  (continuous_arrayJ _ _).add (continuous_arrayV _ _)
lemma arrayTest_nonneg (i : ArrayTestIndex) (d : DistanceArray) : 0 ≤ arrayTest i d :=
  add_nonneg (arrayJ_nonneg _ _ i.property d) (arrayV_nonneg _ _ d)
lemma arrayTest_affine_zero (i : ArrayTestIndex) (w : Icc (0:ℝ) 1) : arrayTest i (affineArray w)=0 := by
  obtain ⟨⟨s,t⟩,hst⟩ := i
  have hmid := dyadicMid_val s t
  have h1 : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have h2 : 0<((s:ℝ)+(t:ℝ))/2-(s:ℝ) := by linarith
  have h3 : 0<(t:ℝ)-((s:ℝ)+(t:ℝ))/2 := by linarith
  have hs (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ)) :
      arrayShortfall u v (affineArray w)=1-w.val := by
    unfold arrayShortfall affineArray
    dsimp only
    rw [abs_of_pos (sub_pos.mpr huv),mul_div_cancel_right₀ _ (sub_ne_zero.mpr huv.ne')]
  unfold arrayTest arrayJ arrayV
  dsimp only
  rw [hs s t hst,hs s (dyadicMid s t) (by rw [dyadicMid_val]; linarith),
    hs (dyadicMid s t) t (by rw [dyadicMid_val]; linarith)]
  ring
lemma nonaffine_iff_positive_test (d : DistanceArray) : d∉affineLocus ↔ ∃ i : ArrayTestIndex,0<arrayTest i d := by
  constructor
  · intro hd
    by_contra hn
    push Not at hn
    apply hd
    apply array_affine_of_zero_tests d
    intro s t hst
    exact le_antisymm (hn ⟨(s,t),hst⟩) (arrayTest_nonneg ⟨(s,t),hst⟩ d)
  · rintro ⟨i,hi⟩ ⟨w,rfl⟩
    rw [arrayTest_affine_zero] at hi
    exact lt_irrefl _ hi
end StandardMapEntropy

end OAI
