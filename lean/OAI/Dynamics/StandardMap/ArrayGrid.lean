import OAI.Dynamics.StandardMap.ArrayTests

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma dyadic_zsmul_val (i : ℤ) (h : DyadicTime) : ((i • h : DyadicTime):ℝ)=(i:ℝ)*(h:ℝ) := by
  simp only [AddSubgroup.coe_zsmul,zsmul_eq_mul]
lemma dyadic_mid_grid (h : DyadicTime) (i : ℤ) : dyadicMid (i • h) ((i+2) • h)=(i+1) • h := by
  apply Subtype.ext
  simp only [dyadicMid_val,dyadic_zsmul_val,Int.cast_add,Int.cast_one,Int.cast_ofNat]
  ring
lemma int_constant_of_succ (f : ℤ → ℝ) (hf : ∀ i,f (i+1)=f i) (i : ℤ) : f i=f 0 := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [hf,ih]
  | pred n ih => rw [← hf (- (n:ℤ)-1),sub_add_cancel,ih]
lemma array_grid_edges (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i : ℤ) :
    d.val (i • h) ((i+1) • h)=d.val 0 h := by
  let f : ℤ → ℝ := fun i => d.val (i • h) ((i+1) • h)
  have hf (i : ℤ) : f (i+1)=f i := by
    have hi : ((i • h : DyadicTime):ℝ)<(((i+2) • h : DyadicTime):ℝ) := by
      simp only [dyadic_zsmul_val,Int.cast_add,Int.cast_ofNat]; nlinarith
    obtain ⟨hL,hR⟩ := array_zero_test_halves (i • h) ((i+2) • h) hi d (hz _ _ hi)
    rw [dyadic_mid_grid] at hL hR
    dsimp only [f]
    simpa only [show i+1+1=i+2 by ring] using hR.trans hL.symm
  have he := int_constant_of_succ f hf i
  simpa only [f,zero_smul,zero_add,one_zsmul] using he
lemma array_grid_upper (d : DistanceArray) (h : DyadicTime) (c : ℝ)
    (he : ∀ i : ℤ,d.val (i • h) ((i+1) • h)=c) (i : ℤ) (n : ℕ) :
    d.val (i • h) ((i+(n:ℤ)) • h) ≤ (n:ℝ)*c := by
  induction n with
  | zero => simpa using (show d.val (i • h) (i • h) ≤ 0 by rw [d.property.2.1])
  | succ n ih =>
      have ht := d.property.2.2.2.1 (i • h) ((i+(n:ℤ)) • h) ((i+((n+1:ℕ):ℤ)) • h)
      have hn : i+((n+1:ℕ):ℤ)=i+(n:ℤ)+1 := by omega
      rw [hn,he] at ht
      rw [hn]
      push_cast
      linarith
lemma array_grid_power (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i : ℤ) (m : ℕ) :
    d.val (i • h) ((i+(2:ℤ)^m) • h)=(2:ℝ)^m*d.val 0 h := by
  induction m with
  | zero => simpa using array_grid_edges d hz h hh i
  | succ m ih =>
      have hm : (0:ℝ)<(2:ℝ)^(m+1) := by positivity
      have hi : ((i • h : DyadicTime):ℝ)<(((i+(2:ℤ)^(m+1)) • h : DyadicTime):ℝ) := by
        simp only [dyadic_zsmul_val,Int.cast_add,Int.cast_pow,Int.cast_ofNat]
        nlinarith
      have hmid : dyadicMid (i • h) ((i+(2:ℤ)^(m+1)) • h)=(i+(2:ℤ)^m) • h := by
        apply Subtype.ext
        simp only [dyadicMid_val,dyadic_zsmul_val,Int.cast_add,Int.cast_pow,Int.cast_ofNat,pow_succ]
        push_cast
        ring
      have hl := (array_zero_test_halves _ _ hi d (hz _ _ hi)).1
      rw [hmid,ih] at hl
      calc
        _ = 2*((2:ℝ)^m*d.val 0 h) := by linarith
        _ = _ := by rw [pow_succ]; ring
lemma nat_le_two_power (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 1 ≤ (2:ℕ)^n := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      omega
lemma array_grid_distance_nat (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i : ℤ) (n : ℕ) :
    d.val (i • h) ((i+(n:ℤ)) • h)=(n:ℝ)*d.val 0 h := by
  have he := array_grid_edges d hz h hh
  apply le_antisymm (array_grid_upper d h (d.val 0 h) he i n)
  let N : ℕ := 2^n
  have hn : n ≤ N := nat_le_two_power n
  have hu := array_grid_upper d h (d.val 0 h) he (i+(n:ℤ)) (N-n)
  have hidx : i+(n:ℤ)+((N-n:ℕ):ℤ)=i+(2:ℤ)^n := by
    rw [Nat.cast_sub hn]
    dsimp only [N]
    push_cast; ring
  rw [hidx] at hu
  have ht := d.property.2.2.2.1 (i • h) ((i+(n:ℤ)) • h) ((i+(2:ℤ)^n) • h)
  rw [array_grid_power d hz h hh i n] at ht
  have hcast : ((N-n:ℕ):ℝ)=(2:ℝ)^n-(n:ℝ) := by rw [Nat.cast_sub hn]; simp [N]
  rw [hcast] at hu
  nlinarith
lemma array_grid_distance (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i j : ℤ) :
    d.val (i • h) (j • h)=|(j:ℝ)-(i:ℝ)| *d.val 0 h := by
  wlog hij : i ≤ j generalizing i j
  · rw [d.property.2.2.1,abs_sub_comm]
    exact this j i (le_of_not_ge hij)
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  have he := array_grid_distance_nat d hz h hh i (j-i).toNat
  rw [hn] at he
  have hcast : ((j-i).toNat:ℝ)=(j:ℝ)-(i:ℝ) := by
    have hh := congrArg (fun a : ℤ => (a:ℝ)) (Int.toNat_of_nonneg (sub_nonneg.mpr hij))
    simpa only [Int.cast_natCast,Int.cast_sub] using hh
  rw [hcast] at he
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hij))]
  exact he
end StandardMapEntropy

end OAI
