import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PowerValidation
import OAI.Combinatorics.RamseyFive.Probability.UniformTails

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_three_validation_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (O : ℙ K V→Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
      (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (t : ℝ),
      finrank K V=4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      O x=C a∪C b → (S.card:ℝ) ≤ 10*Real.exp (2*σ) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=3) S C ((L₀:ℝ)/100) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) →
      scale (K:=K) 3 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        Real.exp (-P η σ D R/2) := by
  have ht := eventually_validation_original_tail hη hη' Cb hCb
  have hd := eventually_dyad_power_payment hη hη'
  have hc := eventually_power_absorption hη hη' (4*2^200) 0 (1/200)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc] with σ hσ ht hd hc
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c O F Lines Q t
    hdim hq hr hL hb₀ hbhi hτ hS ha hb hC hO hSn hn hf hF hx hLines hxQ hgood ht₀
  have hS0 : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hδ : 0 < pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength]
    exact div_pos (by exact_mod_cast Nat.card_pos (α:=K)) hS0
  have hlarge : (4*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (200⁻¹:ℝ)] using hc D R hr
  have hcard : ((outsideAt x S (O x)).card:ℝ) ≤ Real.exp (3*σ) := by
    have he : (10:ℝ) ≤ Real.exp σ := by linarith [Real.add_one_le_exp σ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr (outsideAt_card_le x S (O x))
      _ ≤ 10*Real.exp (2*σ) := hSn
      _ ≤ Real.exp σ*Real.exp (2*σ) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm (H:F) : mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H) ≤ 2 := by
    rw [hO]
    exact (actual_radial_mass_bounds x S C hS a b c ha hb hC F hF hf hn H).2.2.trans (by norm_num)
  have hh := score_pair_three_moment x hdim S O (pointStrength S) hδ F
    (fun H hH => (hF H hH).1) S.card (P η σ D R/200) hS0 hlarge Lines hLines Q hxQ hm hgood 200 (le_refl _)
  have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
  have hmoment : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200) ≤
        (scale (K:=K) 3 S.card)^2*Real.exp (P η σ D R/50) := by
    apply hh.trans
    change 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
      (((Nat.card K:ℝ)^3/S.card)^2*Real.exp (2*(P η σ D R/200))) ≤ _
    calc
      _ = ((Nat.card K:ℝ)^3/S.card)^2*(2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
          Real.exp (2*(P η σ D R/200))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
  have hpairs (u : ℝ) (hu : 0 < u) (_hu2 : u ≤ 2) :=
    validation_pairs_from_power x (outsideAt x S (O x)) (pointStrength S) F 200 _ hmoment u hu
  simp only [hO] at hpairs
  exact ht 3 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
    ha hb hC (by convert hSn using 1; norm_num; ring) hn hf hF hx hpairs ht₀

end

section
open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

lemma score_degree_three_off_strong_zero (hdim : finrank K V=4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (a : ℝ) (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hgood : x∉badCenters S O δ a Lines Q 1) (H : F) :
    (Finset.univ.filter fun H':F => H≠H' ∧ a ≤ mass
      (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H∩pencilLines x F H')).card=0 := by
  have hlocal : (localLines S O δ a Lines x).card=0 := by
    by_contra hn
    have hc : (1:ℝ) ≤ (localLines S O δ a Lines x).card := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    exact hgood (Finset.mem_filter.mpr ⟨hxQ,hc⟩)
  have hh := score_pair_count_three x hdim (outsideAt x S (O x)) δ hδ F hF a
  have hr := richRadials_le_localLines x S O δ a (by exact_mod_cast hδ) Lines hLines
  rw [hlocal] at hr
  have hpc : (Finset.univ.filter fun z : DistinctPairs F => a ≤ strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) δ) z).card=0 := by
    simpa only [Nat.le_zero.mp hr,zero_mul,Nat.le_zero] using hh
  rw [Finset.card_eq_zero] at hpc ⊢
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H' hH'
  obtain ⟨hne,hm⟩ := (Finset.mem_filter.mp hH').2
  have hm' : (⟨H,⟨H',hne.symm⟩⟩:DistinctPairs F)∈Finset.univ.filter
      (fun z : DistinctPairs F => a ≤ strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) z) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
  rw [hpc] at hm'
  exact Finset.notMem_empty _ hm'

end

open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_ambient_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (O : ℙ K V→Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
      (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (t : ℝ),
      finrank K V=4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      O x=C a∪C b → (S.card:ℝ) ≤ 10*Real.exp (2*σ) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=3) S C ((L₀:ℝ)/100) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) →
      x∉badCenters S O (pointStrength S) (1/(100*(momentOrder σ (P η σ D R):ℝ))) Lines Q 1 →
      scale (K:=K) 3 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤ (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have ht := eventually_low_original_tail hη hη' Cb hCb
  have hd := eventually_dyad_power_payment hη hη'
  have hc := eventually_power_absorption hη hη' (40*2^200) 0 (1/200)
    (by positivity) (by norm_num) (by norm_num)
  have h₁₀ := eventually_power_absorption hη hη' 10 0 (1/10000)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc,h₁₀] with σ hσ ht hd hc h₁₀
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c O F Lines Q t
    hdim hq hr hL hb₀ hbhi hτ hS ha hb hC hO hSn hn hf hF hx hLines hxQ hgood hstrong ht₀
  have hS0 : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hδ : 0<pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength]
    exact div_pos (by exact_mod_cast Nat.card_pos (α:=K)) hS0
  have hP0 : 0 ≤ P η σ D R := by unfold P;rw [←hL];positivity
  have hlarge : (40*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (200⁻¹:ℝ)] using hc D R hr
  have hten : (10:ℝ) ≤ Real.exp (P η σ D R/10000) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (10000⁻¹:ℝ)] using h₁₀ D R hr
  have hnq : (S.card:ℝ) ≤ 10*(Nat.card K:ℝ)^2 := by
    rw [hq,←Real.exp_nat_mul];norm_num;exact hSn
  have hSlow : (S.card:ℝ) ≤ (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) := by
    have hh := mul_le_mul_of_nonneg_left hten (sq_nonneg (Nat.card K:ℝ))
    linarith only [hnq,hh]
  have hcard : ((outsideAt x S (O x)).card:ℝ) ≤ Real.exp (3*σ) := by
    have he : (10:ℝ) ≤ Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
    calc
      _  ≤  (S.card:ℝ) := Nat.cast_le.mpr (outsideAt_card_le x S (O x))
      _  ≤  10*Real.exp (2*σ) := hSn
      _  ≤  Real.exp σ*Real.exp (2*σ) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm (H:F) : mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H) ≤ 2 := by
    rw [hO]
    exact (actual_radial_mass_bounds x S C hS a b c ha hb hC F hF hf hn H).2.2.trans (by norm_num)
  have hl₁ : (4*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by linarith only [hlarge]
  have hl₂ : (40*2^199:ℝ) ≤ Real.exp (2*(P η σ D R/100)) := by
    have hh : Real.exp (P η σ D R/200) ≤ Real.exp (2*(P η σ D R/100)) := Real.exp_le_exp.mpr (by linarith only [hP0])
    norm_num at hlarge ⊢
    linarith only [hlarge,hh]
  have hpair := score_pair_three_moment x hdim S O (pointStrength S) hδ F
    (fun H hH => (hF H hH).1) S.card (P η σ D R/200) hS0 hl₁ Lines hLines Q hxQ hm hgood 200 (le_refl _)
  have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
  have hmoment : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200) ≤
        (scale (K:=K) 3 S.card)^2*Real.exp (P η σ D R/50) := by
    apply hpair.trans
    change 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
      (((Nat.card K:ℝ)^3/S.card)^2*Real.exp (2*(P η σ D R/200))) ≤ _
    calc
      _ = ((Nat.card K:ℝ)^3/S.card)^2*(2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
          Real.exp (2*(P η σ D R/200))) := by ring
      _  ≤  _ := mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
  apply ht 3 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
    ha hb hC (by convert hSn using 1; norm_num; ring) hSlow hn hf hF hx _ _ _ ht₀
  · intro u hu hu2
    have hh := power_tail_mul (fun z : DistinctPairs F => strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z) (strength_nonneg _ _) 200 u _ hu hmoment
    simp only [hO,strength] at hh
    convert hh using 1
    congr 2
  · intro H u hu hu2
    have hh := score_degree_three_normalized x hdim (outsideAt x S (O x)) (pointStrength S) hδ F
      (fun H hH => (hF H hH).1) H S.card u (P η σ D R/100) hS0 hu hu2 (hm H) hnq hl₂
    simpa only [hO,show 2*(P η σ D R/100)=P η σ D R/50 by ring,scale] using hh
  · intro H
    have hh := score_degree_three_off_strong_zero x hdim S O (pointStrength S) hδ F
      (fun H hH => (hF H hH).1) _ Lines hLines Q hxQ hstrong H
    rw [hO] at hh
    rw [hh,Nat.cast_zero]
    unfold scale;positivity

end SharpRamseyFive.ScoreGeometry

end OAI
