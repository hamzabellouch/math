import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.DimensionThreeTails

namespace OAI

namespace SharpRamseyFive.ScoreScalars
lemma three_ambient_degree_small {N q n a P : ℝ} (hq : 0<q) (hn : 0<n) (ha : 0<a)
    (hN : N*a≤4*q) (hsmall : n≤q^2*Real.exp (-4*P)) (habs : 4/a≤Real.exp P) :
    N≤(q^3/n)*Real.exp (-3*P) := by
  have h₁ : N≤q*Real.exp P := by
    calc
      N≤4*q/a := (le_div_iff₀ ha).mpr hN
      _=q*(4/a) := by ring
      _≤q*Real.exp P := mul_le_mul_of_nonneg_left habs hq.le
  apply h₁.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  calc
    _≤(q*Real.exp P)*(q^2*Real.exp (-4*P)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _=q^3*Real.exp (-3*P) := by
      rw [show (q*Real.exp P)*(q^2*Real.exp (-4*P))=q^3*(Real.exp P*Real.exp (-4*P)) by ring,
        ←Real.exp_add]
      congr 2
      ring
end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_ambient_tail_cases {η : ℝ} (hη : 0<η) (hη' : η<1/10)
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
      (x∉badCenters S O (pointStrength S) (1/(100*(momentOrder σ (P η σ D R):ℝ))) Lines Q 1 ∨
        (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P η σ D R)) →
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
  have hsmall := eventually_power_absorption hη hη' 4000800 1 1
    (by norm_num) (by norm_num) (by norm_num)
  have hmargin := eventually_score_margins hη hη' Cb hCb
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc,h₁₀,hsmall,hmargin] with σ hσ ht hd hc h₁₀ hsmall hmargin
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
    rcases hstrong with hstrong|hSnSmall
    · have hh := score_degree_three_off_strong_zero x hdim S O (pointStrength S) hδ F
        (fun H hH => (hF H hH).1) _ Lines hLines Q hxQ hstrong H
      rw [hO] at hh
      rw [hh,Nat.cast_zero]
      unfold scale;positivity
    · have hP1 : 1≤P η σ D R := by linarith only [(hmargin D b₀ τ R hr hb₀ hbhi hτ).2.1]
      have hσ1 : 1≤σ := by linarith only [hσ]
      have hp := momentOrder_bounds hσ1 hP1
      have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
      let a₀ : ℝ := 1/(100*(momentOrder σ (P η σ D R):ℝ))
      have ha₀ : 0<a₀ := by dsimp [a₀];positivity
      have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
      have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
      have hh := score_degree_three x hdim (outsideAt x S (O x)) (pointStrength S) hδ F
        (fun H hH => (hF H hH).1) H a₀ ha₀.le
      have hN : ((Finset.univ.filter fun H':F => H≠H' ∧ a₀≤ mass
          (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a₀≤4*Nat.card K := by
        have hh' : _≤(2:ℝ)*((Nat.card K:ℝ)+1) := hh.trans (mul_le_mul_of_nonneg_right (hm H) (by positivity))
        linarith only [hh',hq1]
      have habs : 4/a₀≤Real.exp (P η σ D R) := by
        have hsc := hsmall D R hr
        simp only [Real.rpow_one,one_mul] at hsc
        calc
          4/a₀=400*(momentOrder σ (P η σ D R):ℝ) := by dsimp [a₀];field_simp;ring
          _≤400*(10002*σ) := mul_le_mul_of_nonneg_left hp.2.2.2.2 (by norm_num)
          _=4000800*σ := by ring
          _≤_ := hsc
      have hs := ScoreScalars.three_ambient_degree_small hq0 hS0 ha₀ hN hSnSmall habs
      simpa only [hO,scale] using hs

end SharpRamseyFive.ScoreGeometry

end OAI
