import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PlaneExceptionScalars

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma four_strong_normalize {N q n a P : ℝ} {k : ℕ} (hq : 0<q) (hn : 0<n) (ha : 0<a)
    (hN : N*a^2≤40*q^k) (hsmall : n≤q^(4-k)*Real.exp (-4*P))
    (hk : k≤4) (habs : 40/a^2≤Real.exp P) : N≤(q^4/n)*Real.exp (-3*P) := by
  have h₁ : N≤q^k*Real.exp P := by
    calc
      N≤40*q^k/a^2 := (le_div_iff₀ (sq_pos_of_pos ha)).mpr hN
      _=q^k*(40/a^2) := by ring
      _≤q^k*Real.exp P := mul_le_mul_of_nonneg_left habs (pow_nonneg hq.le k)
  apply h₁.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  calc
    _≤(q^k*Real.exp P)*(q^(4-k)*Real.exp (-4*P)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _=(q^k*q^(4-k))*(Real.exp P*Real.exp (-4*P)) := by ring
    _=q^4*Real.exp (-3*P) := by rw [←pow_add,Nat.add_sub_of_le hk,←Real.exp_add];congr 2;ring
end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence GlobalRadial PoissonScore WeightedPrograms
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_ambient_degree {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0)
      (F : Finset (ℙ K (Dual K V))) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ → Range η σ D R →
      S.Nonempty → (S.card:ℝ)≤10*Real.exp (5*σ/2) → 0<δ →
      (∀H∈F,Incident x H) →
      (∀H:F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)≤2) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      (x∉badCenters S O δ ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 ∨
        (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P η σ D R)) →
      ∀H:F,((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(momentOrder σ (P η σ D R):ℝ))≤ mass
        (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        ((Nat.card K:ℝ)^4/S.card)*Real.exp (-3*P η σ D R) := by
  have he := eventually_power_absorption hη hη' (40*1000200^2) 2 1
    (by positivity) (by norm_num) (by norm_num)
  have hm := eventually_plane_ambient_margins hη hη'
  filter_upwards [eventually_ge_atTop (100:ℝ),he,hm] with σ hσ he hm
  intro D R K V _ _ _ _ _ x _ S O δ F Lines Q hdim hq hr hS hn hδ hF hmass hLines hxQ hstrong H
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn0 : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hm := hm D R hr
  have hP1 : 1≤P η σ D R := by linarith only [hm.1]
  have hp := momentOrder_bounds (by linarith only [hσ]) hP1
  have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
  let a : ℝ := 1/(100*(momentOrder σ (P η σ D R):ℝ))
  have ha : 0<a := by dsimp [a];positivity
  have ha2 : a≤2 := hm.2.2.2.2.1
  have habs : 40/a^2≤Real.exp (P η σ D R) := by
    have he := he D R hr
    rw [Real.rpow_two] at he
    calc
      40/a^2=40*(100*(momentOrder σ (P η σ D R):ℝ))^2 := by dsimp [a];field_simp
      _≤40*(100*(10002*σ))^2 := by gcongr;exact hp.2.2.2.2
      _=(40*1000200^2)*σ^2 := by ring
      _≤_ := by simpa only [one_mul] using he
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3*Real.exp (-4*P η σ D R) := by
    have he10 : (10:ℝ)≤Real.exp (P η σ D R) := by linarith only [hm.2.2.2.2.2]
    calc
      _≤10*Real.exp (5*σ/2) := hn
      _≤Real.exp (P η σ D R)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he10 (Real.exp_nonneg _)
      _=Real.exp (P η σ D R+5*σ/2) := (Real.exp_add _ _).symm
      _≤Real.exp (3*σ-4*P η σ D R) := Real.exp_le_exp.mpr (by linarith only [hm.2.2.1,hP1])
      _=_ := by rw [hq,←Real.exp_nat_mul,←Real.exp_add];congr 1;norm_num;ring
  let N : ℝ := (Finset.univ.filter fun H':F => H≠H' ∧ a≤ mass
    (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H∩pencilLines x F H')).card
  change N≤_
  rcases hstrong with hstrong|hsmall
  · have hh := score_degree_truncated x hdim (outsideAt x S (O x)) δ hδ F hF H a ha.le
      (radial_lt_off_exception x S O δ (a/2) Lines hLines Q hxQ hstrong)
    have hmsq : (mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤4 := by
      calc
        _≤(2:ℝ)^2 := pow_le_pow_left₀ (mass_nonneg _ _) (hmass H) 2
        _=4 := by norm_num
    have hN : N*a^2≤40*(Nat.card K:ℝ)^1 := by
      have hh := hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hmsq] : 2*(mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤8) (by positivity))
      change N*a^2≤8*((Nat.card K:ℝ)+1) at hh
      simp only [pow_one];linarith only [hh,hq1]
    exact ScoreScalars.four_strong_normalize hq0 hn0 ha hN hcap (by norm_num) habs
  · have hh := score_degree_four x hdim (outsideAt x S (O x)) δ hδ F hF H a ha.le
    have hq2 : (Nat.card K:ℝ)≤(Nat.card K:ℝ)^2 := le_self_pow₀ hq1 (by norm_num : (2:ℕ)≠0)
    have hq3 : (Nat.card K:ℝ)^2+Nat.card K+1≤3*(Nat.card K:ℝ)^2 := by nlinarith only [hq1,hq2]
    have hmsq : (mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤4 := by
      calc
        _≤(2:ℝ)^2 := pow_le_pow_left₀ (mass_nonneg _ _) (hmass H) 2
        _=4 := by norm_num
    have hN : N*a^2≤40*(Nat.card K:ℝ)^2 := by
      apply hh.trans
      calc
        _≤2*2*(3*(Nat.card K:ℝ)^2)*2+2*4*((Nat.card K:ℝ)+1) := by gcongr;exact hmass H
        _≤40*(Nat.card K:ℝ)^2 := by nlinarith only [hq1,hq2]
    exact ScoreScalars.four_strong_normalize hq0 hn0 ha hN hsmall (by norm_num) habs
end SharpRamseyFive.ScoreGeometry

end OAI
