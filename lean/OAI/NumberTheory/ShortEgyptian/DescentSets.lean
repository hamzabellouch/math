import OAI.NumberTheory.ShortEgyptian.DoubleCount

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

def HasUnitSum (M Q u k : ℕ) : Prop :=
  ∃ ns, IsUnitSum ((u:ℚ)/(M*Q)) ns ∧ ns.length ≤ k

lemma HasUnitSum.mono {M Q u k l : ℕ} (h : HasUnitSum M Q u k) (hkl : k ≤ l) : HasUnitSum M Q u l := by
  obtain ⟨ns,hs,hl⟩ := h
  exact ⟨ns,hs,hl.trans hkl⟩

lemma hasUnitSum_zero (M Q k : ℕ) : HasUnitSum M Q 0 k := by
  exact ⟨[],⟨by simp,by simp⟩,by simp⟩

lemma HasUnitSum.scale {M Q Q' u k : ℕ} (h : HasUnitSum M Q' u k)
    (hM : 0 < M) (hQ : 0 < Q) (hQ' : 0 < Q') (hd : Q' ∣ Q) : HasUnitSum M Q u k := by
  obtain ⟨ns,hs,hl⟩ := h
  let g := Q/Q'
  have hg : 0 < g := Nat.div_pos (Nat.le_of_dvd hQ hd) hQ'
  have heq : (g:ℚ)*Q'=Q := by exact_mod_cast Nat.div_mul_cancel hd
  refine ⟨ns.map (g*·),⟨?_,?_⟩,by simpa using hl⟩
  · intro n hn
    obtain ⟨n',hn',he⟩ := List.mem_map.mp hn
    subst n
    exact (hs.1 n' hn').trans (Nat.le_mul_of_pos_left _ hg)
  · rw [unitSum_scale,hs.2]
    have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hQq : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hQ'q : (Q':ℚ) ≠ 0 := by exact_mod_cast hQ'.ne'
    have hgq : (g:ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp
    nlinarith

noncomputable def levelBad (S : ℝ) (M C K j : ℕ) : Finset ℕ :=
  (Icc 1 ⌊level S j⌋₊).filter fun u => ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j))

lemma mem_levelBad (S : ℝ) (M C K j u : ℕ) :
    u ∈ levelBad S M C K j ↔ 0 < u ∧ (u:ℝ) ≤ level S j ∧
      ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j)) := by
  constructor
  · intro hu
    obtain ⟨hu,hn⟩ := mem_filter.mp hu
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
    exact ⟨by omega,(Nat.cast_le.mpr hhi).trans (Nat.floor_le (level_pos S j).le),hn⟩
  · rintro ⟨hu0,hu,hn⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu0,Nat.le_floor hu⟩,hn⟩

lemma levelBad_card_le (S : ℝ) (M C K j : ℕ) :
    ((levelBad S M C K j).card:ℝ) ≤ level S j := by
  have hh : (levelBad S M C K j).card ≤ ⌊level S j⌋₊ := by
    apply (card_le_card (filter_subset _ _)).trans
    simp
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (level_pos S j).le)

lemma level_fraction_lt (S : ℝ) (h : ListScale S) (C M j u : ℕ)
    (hM : Real.exp S < (M:ℝ)) (hC : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hu : (u:ℝ) ≤ level S j) : u < M*levelMultiplier S C j := by
  have hm : 1 ≤ M := by
    have hp : (0:ℝ)<M := (Real.exp_pos S).trans hM
    exact_mod_cast (show (1:ℕ)≤M by exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hp.ne'))
  unfold levelMultiplier
  split_ifs with hx
  · have hu' : (u:ℝ)<C := by
      apply hu.trans_lt
      apply (level_antitone S (Nat.zero_le j)).trans_lt
      rw [level_zero]
      apply (Real.exp_lt_exp.mpr ?_).trans_le hC
      have hd : (dimX:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
      exact mul_lt_mul_of_pos_right hd h.S_pos
    exact (by exact_mod_cast hu' : u < C).trans_le (Nat.le_mul_of_pos_left _ hm)
  · simp only [mul_one]
    exact_mod_cast hu.trans_lt ((le_of_not_gt hx).trans_lt hM)

lemma levelBad_terminal (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C) :
    levelBad S R.M C (terminalLength S) (depth S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨_,hu,hn⟩ := (mem_levelBad S R.M C _ _ u).mp hu
  have hc := levelMultiplier_last S C h.m_pos h.m_bounds.2.2
  have hcap := hu.trans (depth_level S h.m_pos h.m_bounds.2.2).1
  obtain ⟨ns,hs,hl⟩ := residueSystem_terminal S h C R u hcap
  apply hn
  refine ⟨ns,?_,by simpa using hl⟩
  simpa only [hc,Nat.cast_one,mul_one] using hs

lemma levelBad_inherit (S : ℝ) (C M K j u : ℕ) (hM : 0 < M) (hC : 0 < C)
    (hu : u ∈ levelBad S M C K j) (hy : (u:ℝ) ≤ level S (j+1)) :
    u ∈ levelBad S M C K (j+1) := by
  obtain ⟨hu0,_,hn⟩ := (mem_levelBad S M C K j u).mp hu
  apply (mem_levelBad S M C K (j+1) u).mpr
  refine ⟨hu0,hy,?_⟩
  intro hh
  apply hn
  exact (hh.scale hM (levelMultiplier_pos S C j hC) (levelMultiplier_pos S C (j+1) hC)
    (levelMultiplier_dvd S C j)).mono (by omega)

lemma levelBad_residue (S : ℝ) (C M K j u t : ℕ) (hM : 0 < M) (hC : 0 < C)
    (hj : j < depth S) (huM : u < M*levelMultiplier S C j)
    (hu : u ∈ levelBad S M C K j) (ht : 0 < t) (htM : t ∣ M)
    (hy : (residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u):ℝ) ≤ level S (j+1)) :
    residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u) ∈ levelBad S M C K (j+1) := by
  let v := residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u)
  obtain ⟨hu0,_,hn⟩ := (mem_levelBad S M C K j u).mp hu
  have hlift (hv : HasUnitSum M (levelMultiplier S C (j+1)) v (K+(depth S-(j+1)))) : False := by
    have hh := residue_lift hM (levelMultiplier_pos S C j hC) (levelMultiplier_pos S C (j+1) hC)
      (levelMultiplier_dvd S C j) hu0 huM ht htM hv
    apply hn
    exact HasUnitSum.mono hh (by omega)
  apply (mem_levelBad S M C K (j+1) v).mpr
  refine ⟨?_,hy,hlift⟩
  by_contra hv
  have hv0 : v = 0 := by omega
  exact hlift (hv0 ▸ hasUnitSum_zero M (levelMultiplier S C (j+1)) _)

end ShortEgyptian

end OAI
