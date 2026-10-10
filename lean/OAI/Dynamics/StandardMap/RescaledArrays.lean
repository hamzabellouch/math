import OAI.Dynamics.StandardMap.ArrayAffinity

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma floor_difference_bound (x y : ℝ) : |(⌊y⌋:ℝ)-(⌊x⌋:ℝ)|≤|y-x|+1 := by
  have hx0 := Int.floor_le x
  have hx1 := Int.lt_floor_add_one x
  have hy0 := Int.floor_le y
  have hy1 := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith [le_abs_self (y-x),neg_le_abs (y-x)]
noncomputable def rescaledDistance (k : ℝ) (z : Torus) (n : ℕ) (s t : DyadicTime) : ℝ :=
  productDistance k z ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋/(n:ℝ)
lemma rescaledDistance_bound (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n) (s t : DyadicTime) :
    rescaledDistance k z n s t≤|(t:ℝ)-(s:ℝ)|+1/(n:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h := (productDistance_le k hk z ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋).trans (floor_difference_bound _ _)
  rw [← mul_sub,abs_mul,abs_of_pos hn'] at h
  unfold rescaledDistance
  apply (div_le_iff₀ hn').mpr
  rw [add_mul,div_mul_cancel₀ _ hn'.ne']
  nlinarith
noncomputable def sampleArray (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n) : DistanceArray :=
  ⟨rescaledDistance k z n,by
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro s t; exact div_nonneg (productDistance_nonneg k hk z _ _) hn'.le
    · intro s; simp [rescaledDistance]
    · intro s t; unfold rescaledDistance; rw [productDistance_symm]
    · intro s t u
      dsimp only [rescaledDistance]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (productDistance_triangle k hk z _ _ _) hn'.le
    · intro s t
      have h1 : 1/(n:ℝ)≤1 := (div_le_one hn').mpr (by exact_mod_cast hn)
      linarith [rescaledDistance_bound k hk z n hn s t]⟩
lemma continuous_sampleArray (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) : Continuous (fun z => sampleArray k hk z n hn) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact (continuous_productDistance k hk _ _).div_const _
lemma rescaledDistance_aligned (k : ℝ) (z : Torus) (n : ℕ) (s t : DyadicTime) (a b : ℤ)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(b:ℝ)) :
    rescaledDistance k z n s t=productDistance k z a b/(n:ℝ) := by
  simp only [rescaledDistance,hs,ht,Int.floor_intCast]
lemma sampleArray_dilate (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n) :
    arrayDilate (sampleArray k hk z n hn)=sampleArray k hk z (n+n) (by omega) := by
  apply Subtype.ext
  funext s t
  change (productDistance k z ⌊(n:ℝ)*(↑(s+s):ℝ)⌋ ⌊(n:ℝ)*(↑(t+t):ℝ)⌋/(n:ℝ))/2=
    productDistance k z ⌊((n+n:ℕ):ℝ)*(s:ℝ)⌋ ⌊((n+n:ℕ):ℝ)*(t:ℝ)⌋/((n+n:ℕ):ℝ)
  simp only [AddSubgroup.coe_add,Nat.cast_add]
  rw [show (n:ℝ)*((s:ℝ)+(s:ℝ))=((n:ℝ)+(n:ℝ))*(s:ℝ) by ring,
    show (n:ℝ)*((t:ℝ)+(t:ℝ))=((n:ℝ)+(n:ℝ))*(t:ℝ) by ring]
  ring
lemma sampleArray_translate (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    arrayTranslate r (sampleArray k hk z n hn)=sampleArray k hk (torusIter k a z) n hn := by
  apply Subtype.ext
  funext s t
  change productDistance k z ⌊(n:ℝ)*(↑(s+r):ℝ)⌋ ⌊(n:ℝ)*(↑(t+r):ℝ)⌋/(n:ℝ)=
    productDistance k (torusIter k a z) ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋/(n:ℝ)
  rw [productDistance_shift]
  simp only [AddSubgroup.coe_add,mul_add,ha,Int.floor_add_intCast]
end StandardMapEntropy

end OAI
