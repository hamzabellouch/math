import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.SparseNumerics

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Sparse

lemma sparse_amplitudes_small (b h k : ℕ) {L : ℝ} (hb : b≤16000)
    (hh : (h:ℝ)≤100000*k) (hL : (10:ℝ)^26≤L) :
    ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ))^2≤Real.exp ((k:ℝ)*L/2000000000) ∧
    ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2≤Real.exp ((k:ℝ)*L/2000000000) ∧
    (2:ℝ)^k≤Real.exp ((k:ℝ)*L/2000000000) := by
  have hbR : (b:ℝ)≤16000 := by exact_mod_cast hb
  have h2 : Real.log 2≤2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
  have h4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hbK := mul_le_mul_of_nonneg_right hbR (show (0:ℝ)≤k by positivity)
  have hhB := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤b by positivity)
  have hLK := mul_le_mul_of_nonneg_right hL (show (0:ℝ)≤k by positivity)
  have hp (n : ℕ) : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  constructor
  · rw [hp,←Real.exp_add,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h2K := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤(k+k*b:ℕ) by positivity)
    push_cast at h2K ⊢
    nlinarith only [h2K,hhB,hbK,hLK]
  constructor
  · rw [hp,←Real.exp_add,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h2K := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤k by positivity)
    have h4K := mul_le_mul_of_nonneg_right h4 (show (0:ℝ)≤k*b by positivity)
    norm_num
    nlinarith only [h2K,h4K,hhB,hbK,hLK]
  · rw [hp]
    apply Real.exp_le_exp.mpr
    have h2K := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤k by positivity)
    nlinarith only [h2K,hLK]

lemma few_hs_scalar (b h k wv wl : ℕ) {L g v x y : ℝ} (C : Fin b → ℝ)
    (hb : b≤16000) (hk : 1≤k) (hh : (h:ℝ)≤100000*k) (hL : (10:ℝ)^26≤L)
    (htv : (k:ℝ)≤8*(((wv+1)/2:ℕ):ℝ)) (htl : (k:ℝ)≤128000*wl)
    (hg0 : 0≤g) (hg : g≤Real.exp (-L/640000))
    (hv0 : 0≤v) (hv : v≤Real.exp (-L/3200))
    (hx0 : 0≤x) (hx : x≤Real.exp (-L/3200))
    (hy0 : 0≤y) (hy : y≤Real.exp (-L/3200))
    (hC0 : ∀j,0≤C j) (hC : ∀j,C j≤Real.exp ((k:ℝ)*L/2000000000)) :
    ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*g^((k+1)/2))^2+
      ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl))≤
      Real.exp (-(k:ℝ)*L/1000000000000) := by
  have hL0 : 0≤L := (by positivity : (0:ℝ)≤10^26).trans hL
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hbR : (b:ℝ)≤16000 := by exact_mod_cast hb
  have hKL := mul_nonneg (Nat.cast_nonneg k) hL0
  have hkt : (k:ℝ)≤2*(((k+1)/2:ℕ):ℝ) := by exact_mod_cast (show k≤2*((k+1)/2) from by omega)
  obtain ⟨hA,hB,h2⟩ := sparse_amplitudes_small b h k hb hh hL
  have hgpow : (g^((k+1)/2))^2≤Real.exp (-(k:ℝ)*L/1000000000) := by
    have he := nat_pow_le_exp_of_le hg0 hg ((k+1)/2)
    have he2 := pow_le_pow_left₀ (pow_nonneg hg0 _) he 2
    rw [←Real.exp_nat_mul] at he2
    refine he2.trans (Real.exp_le_exp.mpr ?_)
    have ht := mul_le_mul_of_nonneg_right hkt hL0
    norm_num
    nlinarith only [ht,hKL]
  have hpow (a : ℝ) (ha0 : 0≤a) (ha : a≤Real.exp (-L/3200))
      (t : ℕ) (ht : (k:ℝ)≤128000*t) :
      a^t≤Real.exp (-2*(k:ℝ)*L/1000000000) := by
    apply (nat_pow_le_exp_of_le ha0 ha t).trans (Real.exp_le_exp.mpr ?_)
    have he := mul_le_mul_of_nonneg_right ht hL0
    nlinarith only [he,hKL]
  have hlx := hpow x hx0 hx wl htl
  have hly := hpow y hy0 hy wl htl
  have hlv := hpow v hv0 hv ((wv+1)/2) (htv.trans (by nlinarith only [show (0:ℝ)≤(((wv+1)/2:ℕ):ℝ) by positivity]))
  have hgood : ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*g^((k+1)/2))^2 ≤
      Real.exp (-(k:ℝ)*L/2000000000) := by
    rw [mul_pow]
    refine (mul_le_mul hA hgpow (by positivity) (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    ring
  have hvertex : (2:ℝ)^k*v^((wv+1)/2)≤Real.exp (-(k:ℝ)*L/1000000000) := by
    refine (mul_le_mul h2 hlv (by positivity) (Real.exp_pos _).le).trans ?_
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hKL]
  have hholes : (2:ℝ)^k*x^wl≤Real.exp (-(k:ℝ)*L/1000000000) := by
    refine (mul_le_mul h2 hlx (by positivity) (Real.exp_pos _).le).trans ?_
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hKL]
  have hparticles (j : Fin b) : C j*(2:ℝ)^k*y^wl≤Real.exp (-(k:ℝ)*L/1000000000) := by
    have hc0 := hC0 j
    refine (mul_le_mul (mul_le_mul (hC j) h2 (by positivity) (Real.exp_pos _).le)
      hly (by positivity) (by positivity)).trans_eq ?_
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hevents : (2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl) ≤
      (1+2*b)*Real.exp (-(k:ℝ)*L/1000000000) := by
    refine (add_le_add hvertex (Finset.sum_le_sum (fun j _ => add_le_add hholes (hparticles j)))).trans_eq ?_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hbad : ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl)) ≤
      (1+2*b)*Real.exp (-(k:ℝ)*L/2000000000) := by
    have hev0 : 0≤ (2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl) := by
      apply add_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro j _
      have hc0 := hC0 j
      positivity
    refine (mul_le_mul hB hevents hev0 (Real.exp_pos _).le).trans_eq ?_
    rw [mul_left_comm,←Real.exp_add]
    congr 1
    ring_nf
  have hcount : 2+2*(b:ℝ)≤Real.exp ((k:ℝ)*L/4000000000) := by
    apply (show 2+2*(b:ℝ)≤(k:ℝ)*L/4000000000+1 from ?_).trans (Real.add_one_le_exp _)
    have hh := mul_le_mul_of_nonneg_right hkR hL0
    nlinarith only [hh,hL,hbR]
  calc
    _ ≤ (2+2*b)*Real.exp (-(k:ℝ)*L/2000000000) := by nlinarith only [hgood,hbad]
    _ ≤ Real.exp ((k:ℝ)*L/4000000000)*Real.exp (-(k:ℝ)*L/2000000000) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ ≤ _ := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hKL]

end BinaryCoordinateSweeps.Sparse

end

end OAI
