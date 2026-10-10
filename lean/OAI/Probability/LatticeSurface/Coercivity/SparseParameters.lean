import Mathlib

namespace OAI

noncomputable section

namespace ExtremalEdges

def gradientConstant (D : ℕ) : ℝ := 2^(D+1)+4*D+1

end ExtremalEdges

namespace SparseBlocks

structure Parameters where
  L : ℕ
  even : Even L
  δ : ℝ
  δ₀ : ℝ
  k₀ : ℕ
  s₀ : ℝ
  δpos : 0 < δ
  δle : δ ≤ δ₀
  δ₀le : δ₀ ≤ 1/16
  klarge : 4/δ₀ ≤ k₀
  spos : 0 < s₀
  Llarge : 8*((k₀:ℝ)+2)/δ₀ ≤ L

def q (u : ℝ) : ℝ := (ExtremalEdges.gradientConstant 6*u)^(1/ExtremalEdges.gradientConstant 6)

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

lemma q_root (r : ℝ) (hr : 0 ≤ r) : q (r^153/153) = r := by
  have hC : ExtremalEdges.gradientConstant 6 = 153 := by
    norm_num [ExtremalEdges.gradientConstant]
  rw [q,hC,show (153:ℝ)*(r^153/153) = r^153 by ring,
    ← Real.rpow_natCast,← Real.rpow_mul hr]
  norm_num

lemma exists_window (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ u : ℝ, 0 < u ∧ u ≤ b ∧ u ≤ 1/8 ∧ q u ≤ a := by
  let r := min a (min b (1/8))
  have hr : 0 < r := lt_min ha (lt_min hb (by norm_num))
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hr8 : r ≤ 1/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hr1 : r ≤ 1 := hr8.trans (by norm_num)
  have hp : r^153 ≤ r := by
    simpa only [pow_one] using pow_le_pow_of_le_one hr.le hr1 (show 1 ≤ 153 by norm_num)
  have hu : r^153/153 ≤ r := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 153)).mpr
    nlinarith
  exact ⟨r^153/153,div_pos (pow_pos hr _) (by norm_num),hu.trans hrb,
    hu.trans hr8,by rw [q_root r hr.le];exact hra⟩

lemma sparse_parameters (η : ℝ) (hη : 0 < η) :
    ∃ p : Parameters, q (2*p.δ₀) ≤ 1/16 ∧ p.s₀ ≤ 1/8 ∧
      ((3*p.L+1:ℕ):ℝ)^4*q p.δ ≤ η ∧
      ((3*p.L+1:ℕ):ℝ)^4*(1/2:ℝ)^p.k₀ ≤ η ∧ 4*q p.s₀ ≤ η := by
  obtain ⟨ε,hε,hε8,_,hεq⟩ := exists_window (1/16) (1/8) (by norm_num) (by norm_num)
  let δ₀ := ε/2
  have hδ₀ : 0 < δ₀ := div_pos hε (by norm_num)
  have hδ₀16 : δ₀ ≤ 1/16 := by dsimp [δ₀];linarith
  obtain ⟨N,hN⟩ := exists_nat_gt (4/δ₀)
  have hscale : 8/δ₀ ≤ 2*(N:ℝ) := by
    rw [show 8/δ₀ = 2*(4/δ₀) by ring]
    linarith
  have hlim : Tendsto (fun k : ℕ => (18*(N:ℝ)+1)^4*((k:ℝ)^4*(1/2:ℝ)^k))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 4
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul ((18*(N:ℝ)+1)^4)
  have hsmall := hlim.eventually (gt_mem_nhds hη)
  have hlarge : ∀ᶠ k : ℕ in atTop, 4/δ₀ ≤ (k:ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
  obtain ⟨k,hk,hk1,hsmallk⟩ := (hlarge.and ((eventually_ge_atTop 1).and hsmall)).exists
  let L := 2*N*(k+2)
  have hLlarge : 8*((k:ℝ)+2)/δ₀ ≤ L := by
    have hh := mul_le_mul_of_nonneg_right hscale (show 0 ≤ (k:ℝ)+2 by positivity)
    calc
      8*((k:ℝ)+2)/δ₀ = (8/δ₀)*((k:ℝ)+2) := by ring
      _ ≤ 2*(N:ℝ)*((k:ℝ)+2) := hh
      _ = (L:ℝ) := by dsimp [L];push_cast;ring
  have hpoly : ((3*L+1:ℕ):ℝ) ≤ (18*(N:ℝ)+1)*(k:ℝ) := by
    dsimp [L]
    push_cast
    have hk1' : (1:ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hfar : ((3*L+1:ℕ):ℝ)^4*(1/2:ℝ)^k ≤ η := by
    calc
      _ ≤ ((18*(N:ℝ)+1)*(k:ℝ))^4*(1/2:ℝ)^k :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hpoly 4) (by positivity)
      _ = (18*(N:ℝ)+1)^4*((k:ℝ)^4*(1/2:ℝ)^k) := by ring
      _ ≤ η := hsmallk.le
  have hsize : (0:ℝ) < ((3*L+1:ℕ):ℝ)^4 := by positivity
  obtain ⟨δ,hδ,hδle,hδ8,hδq⟩ := exists_window (η/((3*L+1:ℕ):ℝ)^4) δ₀
    (div_pos hη hsize) hδ₀
  obtain ⟨s,hs,hs8,_,hsq⟩ := exists_window (η/4) (1/8) (by positivity) (by norm_num)
  have heven : Even L := ⟨N*(k+2), by dsimp [L]; ring⟩
  let p : Parameters := {
    L := L
    even := heven
    δ := δ
    δ₀ := δ₀
    k₀ := k
    s₀ := s
    δpos := hδ
    δle := hδle
    δ₀le := hδ₀16
    klarge := hk
    spos := hs
    Llarge := hLlarge }
  refine ⟨p,?_,hs8,?_,hfar,?_⟩
  · change q (2*(ε/2)) ≤ 1/16
    simpa only [show 2*(ε/2) = ε by ring] using hεq
  · change ((3*L+1:ℕ):ℝ)^4*q δ ≤ η
    have hh := (le_div_iff₀ hsize).mp hδq
    linarith
  · change 4*q s ≤ η
    linarith

end SparseBlocks

end

end OAI
