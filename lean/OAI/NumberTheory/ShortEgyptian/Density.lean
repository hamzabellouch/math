import OAI.NumberTheory.ShortEgyptian.DensityBounds

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

noncomputable def densityConstant : ℝ := terminalConstant+3*(dimX:ℝ)*10000

lemma densityConstant_pos : 0 < densityConstant := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  dsimp [densityConstant,terminalConstant]
  positivity

structure DenseData (S : ℝ) (C : ℕ) where
  M : ℕ
  G : Finset ℕ
  M_lower : Real.exp S < (M:ℝ)
  M_upper : (M:ℝ) ≤ Real.exp ((dimM:ℝ)*S)
  G_subset : G ⊆ Icc 1 ⌊Real.exp ((dimX:ℝ)*S)⌋₊
  bad_card : ((Icc 1 ⌊Real.exp ((dimX:ℝ)*S)⌋₊ \ G).card:ℝ) ≤ Real.exp ((dimX:ℝ)*S)/8
  expansion : ∀ u ∈ G, ∃ ns, IsUnitSum ((u:ℚ)/(M*C)) ns ∧ (ns.length:ℝ) ≤ densityConstant*Real.log S

lemma density_from_residueSystem (S : ℝ) (h : ListScale S) (hm : MomentScale S) (hq : 2 ≤ S^(1/4:ℝ))
    (hnum : (depth S:ℝ)*Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/8)
    (C : ℕ) (R : ResidueSystem S C) (hClo : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) : Nonempty (DenseData S C) := by
  let H := levelBad S R.M C (terminalLength S) 0
  let U := Icc 1 ⌊Real.exp ((dimX:ℝ)*S)⌋₊
  let G := U \ H
  have hden := (density_unrolled S h hm hq C R hClo hChi).trans hnum
  have hH : (H.card:ℝ) ≤ Real.exp ((dimX:ℝ)*S)/8 := by
    have hh := (div_le_iff₀ (level_pos S 0)).mp hden
    simpa only [H,level_zero,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hmul : levelMultiplier S C 0=C := by
    apply ite_eq_left
    rw [level_zero]
    apply Real.exp_lt_exp.mpr
    have hD : (1:ℝ)<dimX := by norm_num [dimX,dimM]
    nlinarith [h.S_pos]
  refine ⟨⟨R.M,G,R.M_lower,R.M_upper,sdiff_subset,?_,?_⟩⟩
  · apply le_trans _ hH
    apply Nat.cast_le.mpr
    apply card_le_card
    intro u hu
    obtain ⟨hu,hug⟩ := mem_sdiff.mp hu
    by_contra huh
    exact hug (mem_sdiff.mpr ⟨hu,huh⟩)
  · intro u hu
    obtain ⟨hu,hn⟩ := mem_sdiff.mp hu
    have hu' := mem_Icc.mp hu
    have huR : (u:ℝ) ≤ level S 0 := by
      rw [level_zero]
      exact (Nat.cast_le.mpr hu'.2).trans (Nat.floor_le (Real.exp_nonneg _))
    have hex : HasUnitSum R.M C u (terminalLength S+depth S) := by
      by_contra he
      apply hn
      apply (mem_levelBad S R.M C _ 0 u).mpr
      exact ⟨hu'.1,huR,by simpa only [hmul,Nat.sub_zero] using he⟩
    obtain ⟨ns,hns,hlen⟩ := hex
    refine ⟨ns,hns,?_⟩
    have hh : (ns.length:ℝ) ≤ ((terminalLength S+depth S:ℕ):ℝ) := by exact_mod_cast hlen
    push_cast at hh
    have ht := terminalLength_bound S h.log_one
    have hd := depth_bound S h.S_pos h.log_one h.m_bounds.1 h.m_bounds.2.2
    dsimp [densityConstant]
    nlinarith

lemma eventually_density : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
    Real.exp ((dimC:ℝ)*S) ≤ C → (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S) → Nonempty (DenseData S C) := by
  filter_upwards [eventually_ListScale,eventually_MomentScale,eventually_density_numeric,
    eventually_log_pow_le 2 0 (by norm_num : (0:ℝ)<1/4)] with S h hm hnum hq
  simp only [pow_zero,mul_one] at hq
  intro C hClo hChi
  obtain ⟨R⟩ := exists_residueSystem S h C hClo hChi
  exact density_from_residueSystem S h hm hq hnum C R hClo hChi

end ShortEgyptian

end OAI
