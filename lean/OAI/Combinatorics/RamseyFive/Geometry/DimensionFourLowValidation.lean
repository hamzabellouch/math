import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PowerValidation
import OAI.Combinatorics.RamseyFive.Probability.UniformTails

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_four_low_validation_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (O : ℙ K V→Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
      (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      O x=C a∪C b → (S.card:ℝ) ≤ 10*Real.exp (5*σ/2) →
      (S.card:ℝ) ≤ (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) →
      scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        Real.exp (-P η σ D R/2) := by
  have ht := eventually_validation_original_tail hη hη' Cb hCb
  have hd := eventually_dyad_power_payment hη hη'
  have hc := eventually_power_absorption hη hη' (11*2^200) 0 (1/200)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc] with σ hσ ht hd hc
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c O F Lines Q t
    hdim hq hr hL hb₀ hbhi hτ hS ha hb hC hO hSn hLow hn hf hF hx hLines hxQ hgood ht₀
  have hS0 : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hδ : 0 < pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength]
    exact div_pos (by exact_mod_cast Nat.card_pos (α:=K)) hS0
  have hlarge : (11*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (200⁻¹:ℝ)] using hc D R hr
  have hcard : ((outsideAt x S (O x)).card:ℝ) ≤ Real.exp (3*σ) := by
    have he : (10:ℝ) ≤ Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr (outsideAt_card_le x S (O x))
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm (H:F) : mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H) ≤ 2 := by
    rw [hO]
    exact (actual_radial_mass_bounds x S C hS a b c ha hb hC F hF hf hn H).2.2.trans (by norm_num)
  have hP0 : 0≤P η σ D R := by unfold P;rw [←hL];positivity
  have hmass : (pointStrength (K:=K) S:ℝ)*S.card≤Nat.card K := by
    rw [coe_pointStrength,div_mul_cancel₀ _ hS0.ne']
  have hlow : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp ((P η σ D R/200)/2) :=
    hLow.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hP0])) (sq_nonneg _))
  have hh := score_pair_low_moment x hdim S O (pointStrength S) hδ F
    (fun H hH => (hF H hH).1) S.card (P η σ D R/200) hS0 hmass hlow hlarge Lines hLines Q hxQ hm
    (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) x hgood) 200 (le_refl _)
  have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
  have hmoment : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200) ≤
        (scale (K:=K) 4 S.card)^2*Real.exp (P η σ D R/50) := by
    apply hh.trans
    change 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
      (((Nat.card K:ℝ)^4/S.card)^2*Real.exp (2*(P η σ D R/200))) ≤ _
    calc
      _ = ((Nat.card K:ℝ)^4/S.card)^2*(2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
          Real.exp (2*(P η σ D R/200))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
  have hpairs (u : ℝ) (hu : 0 < u) (_hu2 : u ≤ 2) :=
    validation_pairs_from_power x (outsideAt x S (O x)) (pointStrength S) F 200 _ hmoment u hu
  simp only [hO] at hpairs
  exact ht 4 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
    ha hb hC (by convert hSn using 1; norm_num) hn hf hF hx hpairs ht₀

end SharpRamseyFive.ScoreGeometry

end OAI
