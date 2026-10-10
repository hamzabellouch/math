import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.DimensionTwoIntegrals

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter
open scoped Topology

theorem eventually_procedure_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ),Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      let Q := P η σ D R
      let κ := b+8*Q*τ+Real.log 16
      104≤Q ∧ κ+8*Q*τ+Real.log 3200000000≤Q/2000 ∧
      8*Q*τ+Real.log 1600≤L η σ D/1000 ∧
      8*Q*τ+Real.log 16≤Q ∧ κ≤Q := by
  have he := eventually_score_slack hη hη' Cb (Real.log 16+Real.log 3200000000)
    16 (1/2000) hCb (by norm_num) (by norm_num)
  have hs := eventually_score_slack hη hη' Cb (Real.log 1600)
    8 (1/1000) hCb (by norm_num) (by norm_num)
  have hu := eventually_score_slack hη hη' Cb (Real.log 16)
    8 1 hCb (by norm_num) (by norm_num)
  have hm := eventually_score_margins hη hη' Cb hCb
  filter_upwards [he,hs,hu,hm] with σ he hs hu hm
  intro D b τ R hr hb hbhi hτ
  have he := he D R b τ hr hb hbhi hτ
  have hs := hs D R b τ hr hb hbhi hτ
  have hu := hu D R b τ hr hb hbhi hτ
  have hm := hm D b τ R hr hb hbhi hτ
  have hL : 0≤L η σ D := by linarith only [hm.1]
  have hLP : L η σ D≤P η σ D R := by linarith only [hm.2.2.2.1,hL]
  dsimp only
  refine ⟨by linarith only [hm.2.1],?_,?_,?_,?_⟩
  all_goals linarith only [he,hs,hu,hLP,hb]

end SharpRamseyFive.ParameterHierarchy
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory PoissonScore ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_procedure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (X U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
      (ia ib ic : ℙ K V→J) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆X → S⊆U → X.card≤4*S.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (S.card:ℝ)≤10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → (Nat.card K:ℝ)*P η σ D R≤S.card →
      (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
    Real.exp (-8*P η σ D R*τ)/4≤
    (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
      {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*P η σ D R) ∧
        (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ)} := by
  have hi := eventually_two_score_integrals hη hη' Cb hCb
  have hp := eventually_procedure_margins hη hη' Cb hCb
  have hm := eventually_score_margins hη hη' Cb hCb
  have ht := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/10))
  have hl := eventually_hierarchy hη hη' Cb 1 10000000000 hCb (by norm_num)
  filter_upwards [eventually_ge_atTop (10:ℝ),hi,hp,hm,ht,hl] with σ hσ hi hp hm ht hl
  rw [←neg_mul] at ht
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ J _ X U S C ia ib ic T hdim hq hr hL hb hbhi hτ hτhi
    hS hSX hSU hret hdens hprod hC hCS hCc hn hdiv hnP hf
  have hP : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hi := hi D b τ R L₀ K V U S C ia ib ic hdim hq hr hL hb hbhi hτhi
    hS hC hCS hCc hn hdiv hf
  have hp := hp D b τ R hr hb hbhi hτhi
  have hm := hm D b τ R hr hb hbhi hτhi
  have hlarge : 10000000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b τ hr hbhi hτhi).1
  have hq10 : (10:ℝ)≤Nat.card K := by rw [hq];linarith only [Real.add_one_le_exp σ,hσ]
  have hτ8 : 8*τ≤4/5 := by linarith only [hτhi,ht]
  have hbcount := irregular_card_bound (d:=2) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have hpay := ScoreScalars.exp_sub_le_scaled (a:=0) (b:=2*((L₀:ℝ)/100))
    (C:=20000000) (by norm_num) (by
      linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤20000000),hlarge])
  simp only [neg_zero,Real.exp_zero] at hpay
  rw [show -(2*((L₀:ℝ)/100))=(-2)*((L₀:ℝ)/100) by ring] at hpay
  have hbad : ((irregular (d:=2) S C ((L₀:ℝ)/100)).card:ℝ)≤(S.card:ℝ)/100 := by
    apply hbcount.trans
    nlinarith only [mul_le_mul_of_nonneg_right hpay (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)]
  have hh := cell_score_from_integrals (d:=2) hdim (by norm_num) hq10 X U S hSX hSU hS hret C hC ia ib hf T L₀ R b τ 0
    hτ hτ8 hdens hprod (by rw [hP];exact hp.1) le_rfl (by rwa [hP]) hbad
    (by rw [hP];dsimp only at hp;linarith only [hp.2.1])
    (by rw [hP,hL];exact hp.2.2.1)
    (by rw [hP];exact hp.2.2.2.1)
    (by rw [hP];exact hp.2.2.2.2)
    (by rw [hP,hL];exact hm.2.2.2.2.2.2.1)
    (by rw [hL];exact hm.2.2.2.2.2.2.2)
    (by simpa only [hP] using hi.1)
    (by simpa only [hP,zero_mul,Real.exp_zero,mul_one] using hi.2)
  simpa only [hP,zero_add] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
