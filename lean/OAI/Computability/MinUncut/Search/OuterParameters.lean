import Mathlib
import OAI.Computability.MinUncut.Search.InnerParameters

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner

lemma exists_list_scale (M u θ : ℝ) (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ, listTerm M u θ q k < ε := by
  let C : ℝ := (⌈M^2/u^2⌉₊ : ℝ)*(⌈M^2/θ^2⌉₊ : ℝ)
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨k,hk⟩ := shared_hint_rate_vanishes q (show 0<ε/(C+1) by positivity)
  refine ⟨k,?_⟩
  have hr := pow_nonneg (hintRate_nonnegative q) k
  have hx := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hk
  change C*hintRate q^k<ε
  nlinarith

lemma exists_remainder_scales {M θ p : ℝ} (hθ : 0<θ) (hp : 0<p) :
    ∃ u : ℚ, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧ ∀ q k : ℕ,
      ∃ t : ℕ, 1≤t ∧ k≤t ∧ remainderTerm M u θ q k t < p/2 := by
  let C : ℝ := 256/θ^4
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨u,hu,hub⟩ := exists_rat_btwn (show (0:ℝ)< min 1 (p/(8*C*(M^2+1))) by positivity)
  obtain ⟨hu1,huB⟩ := lt_min_iff.mp hub
  have hsmall : C*(u:ℝ)^2*M^2<p/8 := by
    have hb := (lt_div_iff₀ (show (0:ℝ)<8*C*(M^2+1) by positivity)).mp huB
    have hs : (u:ℝ)^2≤(u:ℝ) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hs (show 0≤C*M^2 by positivity)
    nlinarith
  refine ⟨u,hu,hu1,?_⟩
  intro q k
  let R : ℝ := (M+M^2/(u:ℝ))^4
  have hR : 0≤R := by dsimp [R]; positivity
  let e : ℝ := p/(8*C*(R+1))
  have he : 0<e := by dsimp [e]; positivity
  let B : ℝ := ((2:ℝ)^(4*(q+3)*k)-1)*(k:ℝ)^2
  obtain ⟨t,ht⟩ := exists_nat_gt (max (k+1:ℝ) (B/e^2))
  have htk : (k:ℝ)+1<t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht0 : (0:ℝ)<t := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hb : B/(t:ℝ)<e^2 := by
    apply (div_lt_iff₀ ht0).mpr
    have hx := (div_lt_iff₀ (show 0<e^2 by positivity)).mp (lt_of_le_of_lt (le_max_right _ _) ht)
    nlinarith
  have hs := (Real.sqrt_lt' he).mpr hb
  have hs0 := Real.sqrt_nonneg (B/(t:ℝ))
  have hr : C*Real.sqrt (B/(t:ℝ))*R<p/8 := by
    have hx := (lt_div_iff₀ (show 0<8*C*(R+1) by positivity)).mp hs
    nlinarith
  refine ⟨t,by exact_mod_cast (show (1:ℝ)≤t by have := Nat.cast_nonneg (α := ℝ) k; linarith),
    by exact_mod_cast (show (k:ℝ)≤t by linarith),?_⟩
  change C*((u:ℝ)^2*M^2+Real.sqrt (B/(t:ℝ))*R)<p/2
  nlinarith

structure OuterParameters (J : ℝ) (P : InnerParameters J) where
  u : ℚ
  b4 : ℚ
  k : ℕ
  t : ℕ
  hu : 0<(u:ℝ)
  hb4 : 0<(b4:ℝ)
  ht : 1≤t
  hk : k≤t
  hgap : listTerm (Real.sqrt (P.n^P.m:ℕ)/sourceSigma J) u P.θ
      (Fintype.card (Row P.m P.n)-1) k +
    (64/(P.θ^2*(sourceSigma J)^2))*J*b4 +
    remainderTerm (Real.sqrt (P.n^P.m:ℕ)/sourceSigma J) u P.θ
      (Fintype.card (Row P.m P.n)-1) k t < P.p

lemma exists_outerParameters {J : ℝ} (hJ : 1≤J) (P : InnerParameters J) :
    Nonempty (OuterParameters J P) := by
  have hJ0 : 0<J := by linarith
  have hσ := sourceSigma_pos hJ
  have hp := P.hp
  have hθ := P.hθ
  let M : ℝ := Real.sqrt (P.n^P.m:ℕ)/sourceSigma J
  let q := Fintype.card (Row P.m P.n)-1
  obtain ⟨u,hu,_,hrem⟩ := exists_remainder_scales (M := M) P.hθ P.hp
  obtain ⟨b,hb,hbB⟩ := exists_rat_btwn (show (0:ℝ)<(P.p:ℝ)*P.θ^2*(sourceSigma J)^2/(256*J) by positivity)
  have hbudget : (64/(P.θ^2*(sourceSigma J)^2))*J*(b:ℝ)<(P.p:ℝ)/4 := by
    have hx := (lt_div_iff₀ (show 0<256*J by positivity)).mp hbB
    have he : (64/(P.θ^2*(sourceSigma J)^2))*J*(b:ℝ) = (64*J*(b:ℝ))/(P.θ^2*(sourceSigma J)^2) := by ring
    rw [he]
    apply (div_lt_iff₀ (show 0<P.θ^2*(sourceSigma J)^2 by positivity)).mpr
    nlinarith
  obtain ⟨k,hk⟩ := exists_list_scale M u P.θ q (show 0<(P.p:ℝ)/4 by positivity)
  obtain ⟨t,ht,hkt,hR⟩ := hrem q k
  exact ⟨⟨u,b,k,t,hu,hb,ht,hkt,by dsimp [M,q] at hk hR; linarith⟩⟩

end MinUncut.Outer

end
end

end OAI
