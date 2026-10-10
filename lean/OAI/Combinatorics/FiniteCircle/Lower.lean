import OAI.Combinatorics.FiniteCircle.Codes

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

def lowerCap (n : ℕ) : ℕ := (n^4)^(32*(n^4)^2)

 theorem lowerCap_ge (n : ℕ) : n≤lowerCap n := by
  by_cases hn : n=0
  · subst n; exact Nat.zero_le _
  have hn1 : 1≤n := by omega
  exact (le_self_pow₀ hn1 (by norm_num) : n≤n^4).trans
    (le_self_pow₀ (one_le_pow₀ hn1) (by simp [hn]) : n^4≤(n^4)^(32*(n^4)^2))

 theorem lower_parameter (d : ℕ) (hd : lowerCap 1000000≤d) :
    ∃ q : ℕ, 500000≤q ∧ lowerCap (2*q)≤d ∧ d<lowerCap (2*(q+1)) := by
  classical
  let P := fun q : ℕ => lowerCap (2*q)≤d
  let q := Nat.findGreatest P d
  have h0 : 500000≤d := by have := lowerCap_ge 1000000; omega
  have hp : P 500000 := hd
  have hq : 500000≤q := by
    by_contra hn
    have ht := Nat.findGreatest_is_greatest (P:=P) (show q<500000 by omega) h0
    exact ht hp
  refine ⟨q,hq,Nat.findGreatest_spec h0 hp,?_⟩
  by_contra hn
  have hnext : P (q+1) := by dsimp [P]; omega
  have hb : q+1≤d := by have := lowerCap_ge (2*(q+1)); dsimp [P] at hnext; omega
  exact Nat.findGreatest_is_greatest (P:=P) (show q<q+1 by omega) hb hnext

 theorem log_lowerCap {n : ℕ} : Real.log (lowerCap n) = 128*(n:ℝ)^8*Real.log n := by
  simp only [lowerCap,Nat.cast_pow,Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  ring

 theorem cap_log_bound {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hd : d<lowerCap (2*(q+1))) :
    Real.log (d:ℝ) ≤ 65536*((2*q:ℕ):ℝ)^8*Real.log (2*q:ℕ) := by
  let n : ℝ := (2*q:ℕ)
  let n' : ℝ := (2*(q+1):ℕ)
  have hn : (1000000:ℝ)≤n := by dsimp [n]; exact_mod_cast (show 1000000≤2*q by omega)
  have hn0 : 0<n := by linarith
  have hn' : 1≤n' := by dsimp [n']; exact_mod_cast (show 1≤2*(q+1) by omega)
  have hnn : n'≤2*n := by dsimp [n,n']; exact_mod_cast (show 2*(q+1)≤2*(2*q) by omega)
  have hl2 : Real.log 2≤Real.log n := Real.log_le_log (by norm_num) (by linarith)
  have hln' : Real.log n'≤2*Real.log n := by
    calc
      _ ≤ Real.log (2*n) := Real.log_le_log (by linarith) hnn
      _ = Real.log 2+Real.log n := Real.log_mul (by norm_num) hn0.ne'
      _ ≤ _ := by linarith
  calc
    _ ≤ Real.log (lowerCap (2*(q+1))) := Real.log_le_log (by exact_mod_cast (show 0<d by omega))
      (by exact_mod_cast hd.le)
    _ = 128*(n')^8*Real.log n' := log_lowerCap
    _ ≤ 128*(2*n)^8*(2*Real.log n) := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hnn 8) (by norm_num))
      hln' (Real.log_nonneg hn') (by positivity)
    _ = _ := by ring

 theorem cap_loglog_bound {n t : ℝ} (hn : 1000000≤n) (ht : 0<t)
    (hb : t≤65536*n^8*Real.log n) : Real.log t≤32*Real.log n := by
  have hn0 : 0<n := by linarith
  have hln : 0<Real.log n := Real.log_pos (by linarith)
  have hc := Real.log_le_log ht hb
  have he : Real.log (65536*n^8*Real.log n) = Real.log 65536+8*Real.log n+Real.log (Real.log n) := by
    rw [Real.log_mul (by positivity) hln.ne',Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),Real.log_pow]
    norm_num
  rw [he] at hc
  have hconst : Real.log 65536≤Real.log n := Real.log_le_log (by norm_num) (by linarith)
  have hl := Real.log_le_sub_one_of_pos hln
  linarith

 theorem scale_bound_of_logs {n : ℝ} {d : ℕ} (hn : 1≤n) (hd : 2≤d)
    (hc : Real.log (d:ℝ) ≤ 65536*n^8*Real.log n)
    (hl : Real.log (Real.log (d:ℝ))≤32*Real.log n) :
    exponentScale d≤2048*n^4*Real.log n := by
  have hln := Real.log_nonneg hn
  have hld : 0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤d by omega))
  have hprod : Real.log (d:ℝ)*Real.log (Real.log (d:ℝ)) ≤ (2048*n^4*Real.log n)^2 := by
    calc
      _ ≤ Real.log (d:ℝ)*(32*Real.log n) := mul_le_mul_of_nonneg_left hl hld
      _ ≤ (65536*n^8*Real.log n)*(32*Real.log n) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2097152*(n^4*Real.log n)^2 := by ring
      _ ≤ 4194304*(n^4*Real.log n)^2 := mul_le_mul_of_nonneg_right
        (show (2097152:ℝ)≤4194304 by norm_num) (sq_nonneg (n^4*Real.log n))
      _ = _ := by ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity,hprod⟩

 theorem all_length_inversion {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hd : d<lowerCap (2*(q+1))) :
    Real.exp ((1/8192)*exponentScale d) ≤ ((2*q:ℕ):ℝ)^(4*q^4) := by
  let n : ℝ := (2*q:ℕ)
  have hn : (1000000:ℝ)≤n := by dsimp [n]; exact_mod_cast (show 1000000≤2*q by omega)
  have hn0 : 0<n := by linarith
  have hc := cap_log_bound hq hd0 hd
  have hl := cap_loglog_bound hn (Real.log_pos (show 1<(d:ℝ) by exact_mod_cast (show 1<d by omega))) hc
  have hs := scale_bound_of_logs (show 1≤n by linarith) hd0 hc hl
  have hr : (1/8192)*exponentScale d ≤ (4*q^4:ℕ)*Real.log n := by
    calc
      _ ≤ (1/8192)*(2048*n^4*Real.log n) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by dsimp [n]; push_cast; ring
  calc
    _ ≤ Real.exp (Real.log (n^(4*q^4))) := by
      apply Real.exp_le_exp.mpr
      simpa only [Real.log_pow] using hr
    _ = _ := Real.exp_log (pow_pos hn0 _)

 theorem mask_witness_parameter {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hl : lowerCap (2*q)≤d) (hu : d<lowerCap (2*(q+1))) :
    MaskWitness (1/268435456) 67108928 (1/1048576) (1/8192) d := by
  classical
  let n := 2*q
  let h := n^4
  have hn : 1000000≤n := by dsimp [n]; omega
  have hh : 100000000≤h := by
    exact (show 100000000≤1000000^4 by norm_num).trans (Nat.pow_le_pow_left hn 4)
  obtain ⟨p,hp⟩ := standingPrimes_exists h (by omega)
  obtain ⟨w,c,hc,ho⟩ := (two_codes (MaskAlphabet h p h) (hp.mask_alphabet_ge (by omega) h)).1
  let L := maskLength h p (h^(2*h)) (circleSize h p) h
  have hL : 0<L := hp.mask_length_pos (by omega) (pow_pos (by omega) _) h
  have hcap : w*L≤lowerCap n := coded_length_cap hh
    (by have := hp.mask_alphabet_ge (by omega) h; omega)
    (hp.mask_alphabet_bound (by omega)) hc.2.1 (hp.mask_length_bound (by omega))
  refine ⟨h,by omega,p,hp.maskPrimes,w,c,hc,ho,w*L,Nat.mul_pos hc.1 hL,hcap.trans hl,?_,?_⟩
  · intro v
    simp only [length_encode,length_maskWord,L]
  · exact (all_length_inversion hq hd0 hu).trans
      (mask_binary_distortion hn (show n^4=4*(4*q^4) by dsimp [n]; ring) hp c hc)

 theorem excluded_witness_parameter {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hl : lowerCap (2*q)≤d) (hu : d<lowerCap (2*(q+1))) :
    ExcludedWitness (1/268435456) 67108928 (1/1048576) (1/8192) d := by
  classical
  let n := 2*q
  let h := n^4
  have hn : 1000000≤n := by dsimp [n]; omega
  have hh : 100000000≤h := by
    exact (show 100000000≤1000000^4 by norm_num).trans (Nat.pow_le_pow_left hn 4)
  obtain ⟨p,hp⟩ := standingPrimes_exists h (by omega)
  obtain ⟨w,c,hc,ho⟩ := (two_codes (ExcludedAlphabet h (circleSize h p) h)
    (hp.excluded_alphabet_ge (by omega) h)).2
  let L := excludedLength h p (h^(2*h)) (circleSize h p) h
  have hL : 0<L := hp.excluded_length_pos (by omega) (pow_pos (by omega) _) h
  have hcap : w*L≤lowerCap n := coded_length_cap hh
    (by have := hp.excluded_alphabet_ge (by omega) h; omega)
    (hp.excluded_alphabet_bound (by omega)) hc.2.1 (hp.excluded_length_bound (by omega))
  refine ⟨h,by omega,p,hp.excludedPrimes (by omega),w,c,hc,ho,w*L,Nat.mul_pos hc.1 hL,hcap.trans hl,?_,?_⟩
  · intro v
    simp only [length_encode,length_excludedWord,L]
  · exact (all_length_inversion hq hd0 hu).trans
      (excluded_binary_distortion hn (show n^4=4*(4*q^4) by dsimp [n]; ring) hp c hc)

 theorem both_witnesses {d : ℕ} (hd : lowerCap 1000000≤d) :
    MaskWitness (1/268435456) 67108928 (1/1048576) (1/8192) d ∧
    ExcludedWitness (1/268435456) 67108928 (1/1048576) (1/8192) d := by
  obtain ⟨q,hq,hl,hu⟩ := lower_parameter d hd
  have hd0 : 2≤d := by have := lowerCap_ge 1000000; omega
  exact ⟨mask_witness_parameter hq hd0 hl hu,excluded_witness_parameter hq hd0 hl hu⟩

end FiniteCircle

end OAI
