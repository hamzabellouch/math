import Mathlib
import OAI.Probability.ThreeStateClauses.BranchGrowth
import OAI.Probability.ThreeStateClauses.ScalarBounds

namespace OAI

/-! Positive Fixed. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

def qExact (lam : ℝ) : ℝ := (37/27)/(2+lam)
def cExact (lam : ℝ) : ℝ := 37/27+2*lam*qExact lam

def jMean (Q : Law) : ℝ := ∫ m, symEntropy m.1 ∂Q.probability.toMeasure

def edgeJMean (Q : Law) (lam : ℝ) : ℝ := ∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure

lemma edgeJ_integrable (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    Integrable (fun m ↦ symEntropy (edgeMessage lam m)) Q.probability.toMeasure :=
  compact_integrable (continuous_symEntropy_comp (continuous_edgeMessage lam)
    (fun m i ↦ (edge_positive hl₀ hl₁ m).1 i))

lemma residual_integrable (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (hp : ∀ᵐ m ∂Q.probability.toMeasure, PositiveMessage m.1)
    (hJ : Integrable (fun m : Message ↦ symEntropy m.1) Q.probability.toMeasure) :
    Integrable (fun m : Message ↦ residual m.1 lam) Q.probability.toMeasure := by
  have h := (((edgeJ_integrable Q hl₀.le hl₁).div_const (lam^2)).sub hJ).const_mul (2/(1-lam))
  apply h.congr
  filter_upwards [hp] with m hm
  change 2/(1-lam)*(symEntropy (edge lam m.1)/lam^2-symEntropy m.1) = _
  rw [symEntropy_edge_residual hm ⟨hl₀.le,hl₁.le⟩]
  field_simp [ne_of_gt hl₀, ne_of_gt (sub_pos.mpr hl₁)]
  ring

lemma momentA_integrable (Q : Law)
    (hp : ∀ᵐ m ∂Q.probability.toMeasure, PositiveMessage m.1)
    (hJ : Integrable (fun m : Message ↦ symEntropy m.1) Q.probability.toMeasure) :
    Integrable (fun m : Message ↦ momentA m.1) Q.probability.toMeasure := by
  have h := ((compact_integrable continuous_yMoment).sub ((compact_integrable continuous_xMoment).const_mul 2)).add (hJ.const_mul 2)
  apply h.congr
  filter_upwards [hp] with m hm
  exact (momentA_identity hm).symm

lemma momentQ_integrable (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (hp : ∀ᵐ m ∂Q.probability.toMeasure, PositiveMessage m.1)
    (hJ : Integrable (fun m : Message ↦ symEntropy m.1) Q.probability.toMeasure) :
    Integrable (fun m : Message ↦ momentQ m.1 lam) Q.probability.toMeasure := by
  have hC := residual_integrable Q hl₀ hl₁ hp hJ
  have h := (((compact_integrable continuous_xMoment).sub hJ).sub (hC.div_const 2)).div_const lam
  apply h.congr
  filter_upwards [hp] with m hm
  have he := symEntropy_residual hm ⟨hl₀.le,hl₁.le⟩
  apply (div_eq_iff (ne_of_gt hl₀)).2
  change momentX (centered m.1)-symEntropy m.1-residual m.1 lam/2 = _
  linarith

lemma expected_moment_bounds (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (hp : ∀ᵐ m ∂Q.probability.toMeasure, PositiveMessage m.1)
    (hJ : Integrable (fun m : Message ↦ symEntropy m.1) Q.probability.toMeasure)
    (hadd : edgeJMean Q lam = lam^2*jMean Q) :
    0 ≤ jMean Q ∧ jMean Q ≤ Q.mu-lam*qExact lam*Q.nu ∧ cExact lam*Q.nu ≤ Q.eta := by
  have hC := residual_integrable Q hl₀ hl₁ hp hJ
  have hA := momentA_integrable Q hp hJ
  have hQ := momentQ_integrable Q hl₀ hl₁ hp hJ
  have hx := compact_integrable continuous_xMoment (μ := Q.probability.toMeasure)
  have hx₂ := compact_integrable (continuous_xMoment.pow 2) (μ := Q.probability.toMeasure)
  have hcx : (∫ m, residual m.1 lam ∂Q.probability.toMeasure) = 0 := by
    have he := integral_congr_ae (hp.mono (fun m hm ↦ symEntropy_edge_residual hm ⟨hl₀.le,hl₁.le⟩))
    change edgeJMean Q lam = (∫ m : Message, lam^2*(symEntropy m.1+(1-lam)*residual m.1 lam/2) ∂Q.probability.toMeasure) at he
    rw [integral_const_mul,
      integral_add (f := fun m : Message ↦ symEntropy m.1) (g := fun m ↦ (1-lam)*residual m.1 lam/2)
        hJ ((hC.const_mul _).div_const _), integral_div, integral_const_mul] at he
    change edgeJMean Q lam = lam^2*(jMean Q+(1-lam)*(∫ m, residual m.1 lam ∂Q.probability.toMeasure)/2) at he
    have hc : 0 < lam^2*(1-lam) := mul_pos (sq_pos_of_pos hl₀) (sub_pos.mpr hl₁)
    nlinarith [hadd]
  have hjx : jMean Q = Q.mu-lam*(∫ m, momentQ m.1 lam ∂Q.probability.toMeasure) := by
    have he := integral_congr_ae (hp.mono (fun m hm ↦ symEntropy_residual hm ⟨hl₀.le,hl₁.le⟩))
    change jMean Q = (∫ m : Message, xMoment m-lam*momentQ m.1 lam-residual m.1 lam/2 ∂Q.probability.toMeasure) at he
    rw [integral_sub (f := fun m : Message ↦ xMoment m-lam*momentQ m.1 lam)
      (g := fun m ↦ residual m.1 lam/2) (hx.sub (hQ.const_mul _)) (hC.div_const _),
      integral_sub (f := xMoment) (g := fun m ↦ lam*momentQ m.1 lam) hx (hQ.const_mul _),
      integral_const_mul, integral_div, hcx] at he
    simpa only [sub_zero, zero_div, jMean, Law.mu] using he
  have hyx : Q.eta = (∫ m, momentA m.1 ∂Q.probability.toMeasure)+
      2*lam*(∫ m, momentQ m.1 lam ∂Q.probability.toMeasure) := by
    have he := integral_congr_ae (hp.mono (fun m hm ↦ momentY_residual hm ⟨hl₀.le,hl₁.le⟩))
    rw [integral_add (f := fun m : Message ↦ momentA m.1+2*lam*momentQ m.1 lam)
      (g := fun m ↦ residual m.1 lam) (hA.add (hQ.const_mul _)) hC,
      integral_add (f := fun m : Message ↦ momentA m.1) (g := fun m ↦ 2*lam*momentQ m.1 lam) hA (hQ.const_mul _),
      integral_const_mul, hcx, add_zero] at he
    exact he
  have hAb : (37/27)*Q.nu ≤ ∫ m, momentA m.1 ∂Q.probability.toMeasure := by
    have h := integral_mono_ae (f := fun m : Message ↦ (37/27)*xMoment m^2)
      (g := fun m ↦ momentA m.1) (hx₂.const_mul (37/27)) hA
      (hp.mono (fun m hm ↦ momentA_lower hm))
    rwa [integral_const_mul] at h
  have hQb : qExact lam*Q.nu ≤ ∫ m, momentQ m.1 lam ∂Q.probability.toMeasure := by
    have h := integral_mono_ae (f := fun m : Message ↦ momentA m.1/(2+lam))
      (g := fun m ↦ momentQ m.1 lam) (hA.div_const _) hQ
      (hp.mono (fun m hm ↦ momentQ_lower hm hl₀.le hl₁.le))
    rw [integral_div] at h
    have hden : 0 < 2+lam := by linarith
    have hx := (div_le_div_iff_of_pos_right hden).2 hAb
    have hh := hx.trans h
    simpa only [qExact, div_mul_eq_mul_div] using hh
  refine ⟨integral_nonneg_of_ae (hp.mono (fun m hm ↦ symEntropy_nonneg hm)), ?_, ?_⟩
  · rw [hjx]; nlinarith [mul_nonneg hl₀.le (sub_nonneg.mpr hQb)]
  · rw [hyx]
    dsimp only [cExact]
    nlinarith [mul_nonneg hl₀.le (sub_nonneg.mpr hQb)]

theorem regular_fixed_moment_bounds (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) (n : ℕ)
    (hcrit : (n:ℝ)*lam^2 = 1) (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) :
    0 ≤ jMean Q ∧ jMean Q ≤ Q.mu-lam*qExact lam*Q.nu ∧ cExact lam*Q.nu ≤ Q.eta := by
  have hp := finite_positive Q hl₀.le hl₁ n
  have hJ := finite_integrable_symEntropy Q hl₀.le hl₁ n
  rw [← hfixed] at hp hJ
  apply expected_moment_bounds Q hl₀ hl₁ hp hJ
  have he := finiteLaw_symEntropy Q hl₀.le hl₁ n
  change (∫ m, symEntropy m.1 ∂(finiteProbability Q hl₀.le hl₁ n).toMeasure) = (n:ℝ)*edgeJMean Q lam at he
  rw [← hfixed] at he
  change jMean Q = (n:ℝ)*edgeJMean Q lam at he
  calc
    edgeJMean Q lam = ((n:ℝ)*lam^2)*edgeJMean Q lam := by rw [hcrit]; ring
    _ = lam^2*((n:ℝ)*edgeJMean Q lam) := by ring
    _ = lam^2*jMean Q := by rw [← he]

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open scoped BigOperators
namespace ThreeState.TreeClauses.Positive

lemma branch_sum_first (k : ℕ) :
    (∑ j ∈ Finset.range k, ((j:ℝ)+1)) = (k:ℝ)*((k:ℝ)+1)/2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma branch_sum_second (k : ℕ) :
    (∑ j ∈ Finset.range k, ((j:ℝ)+1)*(j:ℝ)) = (k:ℝ)*((k:ℝ)+1)*((k:ℝ)-1)/3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma reciprocal_tangent {a q : ℝ} (ha : 0 ≤ a) (_hq : 0 ≤ q) :
    1+2*q-a ≤ (1+q)^2/(1+a) := by
  apply (le_div_iff₀ (by positivity : 0 < 1+a)).2
  nlinarith [sq_nonneg (a-q)]

lemma weighted_branch_jensen {lam mu : ℝ} (hmu : 0 ≤ mu) (k : ℕ)
    (hcrit : ((k:ℝ)+1)*lam^2 = 1) :
    (k:ℝ)*((k:ℝ)+1)/(2*(1+2*mu/3)) ≤
      ∑ j ∈ Finset.range k, ((j:ℝ)+1)/(1+(j:ℝ)*(lam^2*mu)) := by
  let q := 2*mu/3
  let beta := lam^2*mu
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hh := Finset.sum_le_sum (s := Finset.range k) (fun j _ ↦
    mul_le_mul_of_nonneg_right (reciprocal_tangent (mul_nonneg (Nat.cast_nonneg j) hb) hq)
      (show (0:ℝ) ≤ (j:ℝ)+1 by positivity))
  have hleft : (∑ j ∈ Finset.range k, (1+2*q-(j:ℝ)*beta)*((j:ℝ)+1)) =
      (1+2*q)*((k:ℝ)*((k:ℝ)+1)/2)-beta*((k:ℝ)*((k:ℝ)+1)*((k:ℝ)-1)/3) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hid : (∑ j ∈ Finset.range k, (j:ℝ)*beta*((j:ℝ)+1)) =
        beta*∑ j ∈ Finset.range k, ((j:ℝ)+1)*(j:ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hid, branch_sum_first, branch_sum_second]
  have hright : (∑ j ∈ Finset.range k, ((1+q)^2/(1+(j:ℝ)*beta))*((j:ℝ)+1)) =
      (1+q)^2*∑ j ∈ Finset.range k, ((j:ℝ)+1)/(1+(j:ℝ)*beta) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hleft, hright] at hh
  have hbB : beta*((k:ℝ)*((k:ℝ)+1)*((k:ℝ)-1)/3) ≤ q*((k:ℝ)*((k:ℝ)+1)/2) := by
    have he : beta*((k:ℝ)*((k:ℝ)+1)*((k:ℝ)-1)/3) = mu*(k:ℝ)*((k:ℝ)-1)/3 := by
      dsimp [beta]
      linear_combination (mu*(k:ℝ)*((k:ℝ)-1)/3)*hcrit
    rw [he]
    dsimp [q]
    nlinarith [mul_nonneg hmu (Nat.cast_nonneg k)]
  have hd : 0 < 1+q := by positivity
  have hh' : (k:ℝ)*((k:ℝ)+1)/2 ≤
      (1+q)*(∑ j ∈ Finset.range k, ((j:ℝ)+1)/(1+(j:ℝ)*beta)) := by
    apply le_of_mul_le_mul_left (a := 1+q) _ hd
    nlinarith
  apply (div_le_iff₀ (show 0 < 2*(1+2*mu/3) by positivity)).2
  dsimp [q, beta] at hh'
  nlinarith

lemma sqrt_branch_sum {lam : ℝ} (hl : 0 < lam) (k : ℕ)
    (hcrit : ((k:ℝ)+1)*lam^2 = 1) :
    lam^4*(∑ j ∈ Finset.range k, Real.sqrt ((j:ℝ)+1)) ≤
      (1-lam^2)*lam/Real.sqrt 2 := by
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs2p := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hl2 : 0 < lam^2 := sq_pos_of_pos hl
  have hp := Finset.sum_le_sum (s := Finset.range k) (fun j _ ↦
    sq_nonneg (Real.sqrt ((j:ℝ)+1)-1/(lam*Real.sqrt 2)))
  have hpoint (j : ℕ) :
      2*lam*Real.sqrt 2*Real.sqrt ((j:ℝ)+1) ≤ 2*lam^2*((j:ℝ)+1)+1 := by
    have hh := sq_nonneg (lam*Real.sqrt 2*Real.sqrt ((j:ℝ)+1)-1)
    have he : (lam*Real.sqrt 2*Real.sqrt ((j:ℝ)+1))^2 = 2*lam^2*((j:ℝ)+1) := by
      calc
        _ = lam^2*(Real.sqrt 2)^2*(Real.sqrt ((j:ℝ)+1))^2 := by ring
        _ = _ := by rw [hs2, Real.sq_sqrt (by positivity)]; ring
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.range k) (fun j _ ↦ hpoint j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, branch_sum_first] at hh
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hh
  have he : 2*lam^2*((k:ℝ)*((k:ℝ)+1)/2)+(k:ℝ) = 2*(k:ℝ) := by
    linear_combination (k:ℝ)*hcrit
  rw [he] at hh
  have he' : (k:ℝ)*lam^2 = 1-lam^2 := by nlinarith [hcrit]
  apply (le_div_iff₀ hs2p).2
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ lam^3/2 by positivity)
  nlinarith

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

lemma truncated_quadratic {a b t L C : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hL : 0 ≤ L) (ht : L ≤ t) (hC : 0 ≤ C)
    (hbound : a*t-b*Real.sqrt t ≤ C) : a*L-b*Real.sqrt L ≤ C := by
  have hsL := Real.sqrt_nonneg L
  have hst := Real.sqrt_nonneg t
  have hsqL := Real.sq_sqrt hL
  have hsqt := Real.sq_sqrt (hL.trans ht)
  have hsle := Real.sqrt_le_sqrt ht
  by_cases h : a*Real.sqrt L-b ≤ 0
  · have hh := mul_nonpos_of_nonneg_of_nonpos hsL h
    nlinarith
  · have hh := mul_nonneg (sub_nonneg.mpr hsle) (le_of_lt (lt_of_not_ge h))
    have hh' := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hsle)) hst
    nlinarith

lemma product_cubic_bound (Q R : Law) (hnu : R.nu ≤ Q.nu) :
    Q.eta*R.eta ≤ Real.sqrt Q.mu*Q.nu*Real.sqrt R.mu := by
  have hmu := Q.mu_nonneg
  have hnuQ := Q.nu_nonneg
  have hR : R.eta^2 ≤ R.mu*Q.nu :=
    R.moment_discriminant.trans (mul_le_mul_of_nonneg_left hnu R.mu_nonneg)
  have hprod := mul_le_mul Q.moment_discriminant hR (sq_nonneg R.eta)
    (mul_nonneg Q.mu_nonneg Q.nu_nonneg)
  have hs : (Real.sqrt Q.mu*Q.nu*Real.sqrt R.mu)^2 = (Q.mu*Q.nu)*(R.mu*Q.nu) := by
    calc
      _ = (Real.sqrt Q.mu)^2*Q.nu^2*(Real.sqrt R.mu)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt Q.mu_nonneg, Real.sq_sqrt R.mu_nonneg]; ring
  have hp : 0 ≤ Real.sqrt Q.mu*Q.nu*Real.sqrt R.mu := by positivity
  nlinarith [sq_nonneg (Q.eta*R.eta-Real.sqrt Q.mu*Q.nu*Real.sqrt R.mu)]

lemma correlation_truncated (Q R : Law) {lam L : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hnu : R.nu ≤ Q.nu) (hL : 0 ≤ L) (hproj : L ≤ R.mu) :
    3*lam^2*Q.mu*L-lam^3*Real.sqrt Q.mu*Q.nu*Real.sqrt L ≤ 3*pairCorrelation R Q lam := by
  have hmu := Q.mu_nonneg
  have hnuQ := Q.nu_nonneg
  have hi := pairCorrelation_increment R Q hl₀ hl₁
  have he := product_cubic_bound Q R hnu
  have hh : 3*lam^2*Q.mu*R.mu-(lam^3*Real.sqrt Q.mu*Q.nu)*Real.sqrt R.mu ≤
      3*pairCorrelation R Q lam := by
    nlinarith [mul_nonneg (pow_nonneg hl₀ 3) (sub_nonneg.mpr he)]
  exact truncated_quadratic (by positivity) (by positivity) hL hproj
    (mul_nonneg (by norm_num) (pairCorrelation_nonneg R Q hl₀ hl₁)) hh

lemma finite_increment_bound (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hfixed : Q.probability = finiteProbability Q hl₀ hl₁ N) :
    3*lam^4*Q.mu^2*(j:ℝ)/(1+((j:ℝ)-1)*(lam^2*Q.mu))-
      lam^4*Q.mu*Q.nu*Real.sqrt j ≤ 3*pairCorrelation (finiteLaw Q hl₀ hl₁ j) Q lam := by
  have hmu := Q.mu_nonneg
  have hnuQ := Q.nu_nonneg
  let L : ℝ := (j:ℝ)*(lam^2*Q.mu)/(1+((j:ℝ)-1)*(lam^2*Q.mu))
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hd : 1 ≤ 1+((j:ℝ)-1)*(lam^2*Q.mu) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hj') (mul_nonneg (sq_nonneg lam) Q.mu_nonneg)]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hproj := finite_projection Q hl₀ hl₁ j hj
  have hnu : (finiteLaw Q hl₀ hl₁ j).nu ≤ Q.nu := by
    have hh := finite_nu_mono Q hl₀ hl₁ hjN
    change _ ≤ ∫ m, xMoment m^2 ∂(finiteProbability Q hl₀ hl₁ N).toMeasure at hh
    rw [← hfixed] at hh
    exact hh
  have hc := correlation_truncated Q (finiteLaw Q hl₀ hl₁ j) hl₀ hl₁ hnu hL hproj
  have hLu : L ≤ (j:ℝ)*(lam^2*Q.mu) := by
    dsimp only [L]
    exact div_le_self (by positivity) hd
  have hs : Real.sqrt L ≤ lam*Real.sqrt Q.mu*Real.sqrt j := by
    have he : (lam*Real.sqrt Q.mu*Real.sqrt j)^2 = (j:ℝ)*(lam^2*Q.mu) := by
      calc
        _ = lam^2*(Real.sqrt Q.mu)^2*(Real.sqrt j)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt Q.mu_nonneg, Real.sq_sqrt (Nat.cast_nonneg j)]; ring
    have hp : 0 ≤ lam*Real.sqrt Q.mu*Real.sqrt j := by positivity
    nlinarith [Real.sq_sqrt hL, Real.sqrt_nonneg L]
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ lam^3*Real.sqrt Q.mu*Q.nu by positivity)
  have heq : (lam^3*Real.sqrt Q.mu*Q.nu)*(lam*Real.sqrt Q.mu*Real.sqrt j) =
      lam^4*Q.mu*Q.nu*Real.sqrt j := by
    calc
      _ = lam^4*(Real.sqrt Q.mu)^2*Q.nu*Real.sqrt j := by ring
      _ = _ := by rw [Real.sq_sqrt Q.mu_nonneg]
  rw [heq] at hmul
  have hmain : 3*lam^2*Q.mu*L = 3*lam^4*Q.mu^2*(j:ℝ)/(1+((j:ℝ)-1)*(lam^2*Q.mu)) := by
    dsimp only [L]; ring
  rw [hmain] at hc
  linarith

lemma finite_correlation_sum (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (N : ℕ) (hfixed : Q.probability = finiteProbability Q hl₀ hl₁ N)
    (k : ℕ) (hk : k+1 ≤ N) :
    (∑ j ∈ Finset.range k,
      (3*lam^4*Q.mu^2*((j:ℝ)+1)/(1+(j:ℝ)*(lam^2*Q.mu))-
        lam^4*Q.mu*Q.nu*Real.sqrt ((j:ℝ)+1))) ≤ 3*correlationEntropy Q lam (k+1) := by
  induction k with
  | zero =>
    simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (correlationEntropy_nonneg Q hl₀ hl₁ 1)
  | succ k ih =>
    have hprev := ih (by omega)
    have hi := finite_increment_bound Q hl₀ hl₁ N (k+1) (by omega) (by omega) hfixed
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hi
    rw [Finset.sum_range_succ, correlationEntropy_succ Q hl₀ hl₁ (k+1)]
    linarith

theorem regular_fixed_correlation_bounds (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (n : ℕ) (hn : 2 ≤ n) (hcrit : (n:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) :
    3*Q.mu^2/(2*(1+2*Q.mu/3))-lam/Real.sqrt 2*Q.mu*Q.nu ≤
      3*correlationEntropy Q lam n/(1-lam^2) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hc : ((k:ℝ)+1)*lam^2 = 1 := by simpa using hcrit
  have halpha : 0 < 1-lam^2 := by nlinarith [mul_pos (sub_pos.mpr hl₁) (by linarith : 0 < 1+lam)]
  have hmu := Q.mu_nonneg
  have hnu := Q.nu_nonneg
  have hh := finite_correlation_sum Q hl₀.le hl₁ (k+1) hfixed k (by omega)
  have hid : (∑ j ∈ Finset.range k,
      (3*lam^4*Q.mu^2*((j:ℝ)+1)/(1+(j:ℝ)*(lam^2*Q.mu))-
        lam^4*Q.mu*Q.nu*Real.sqrt ((j:ℝ)+1))) =
      (3*lam^4*Q.mu^2)*(∑ j ∈ Finset.range k, ((j:ℝ)+1)/(1+(j:ℝ)*(lam^2*Q.mu)))-
      (Q.mu*Q.nu)*(lam^4*∑ j ∈ Finset.range k, Real.sqrt ((j:ℝ)+1)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [hid] at hh
  have hJ := mul_le_mul_of_nonneg_left (weighted_branch_jensen hmu k hc)
    (show 0 ≤ 3*lam^4*Q.mu^2 by positivity)
  have hS := mul_le_mul_of_nonneg_left (sqrt_branch_sum hl₀ k hc) (mul_nonneg hmu hnu)
  have he : lam^4*(k:ℝ)*((k:ℝ)+1) = 1-lam^2 := by
    calc
      _ = ((k:ℝ)*lam^2)*(((k:ℝ)+1)*lam^2) := by ring
      _ = 1-lam^2 := by rw [hc]; nlinarith [hc]
  have heJ : 3*lam^4*Q.mu^2*((k:ℝ)*((k:ℝ)+1)/(2*(1+2*Q.mu/3))) =
      (1-lam^2)*(3*Q.mu^2/(2*(1+2*Q.mu/3))) := by
    calc
      _ = (lam^4*(k:ℝ)*((k:ℝ)+1))*(3*Q.mu^2/(2*(1+2*Q.mu/3))) := by ring
      _ = _ := by rw [he]
  rw [heJ] at hJ
  apply (le_div_iff₀ halpha).2
  calc
    _ = (1-lam^2)*(3*Q.mu^2/(2*(1+2*Q.mu/3)))-Q.mu*Q.nu*((1-lam^2)*lam/Real.sqrt 2) := by ring
    _ ≤ 3*correlationEntropy Q lam (k+1) := by linarith

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

lemma fixed_edgeJ (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) (n : ℕ)
    (hcrit : (n:ℝ)*lam^2 = 1) (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) :
    edgeJMean Q lam = lam^2*jMean Q := by
  have h := finiteLaw_symEntropy Q hl₀.le hl₁ n
  change (∫ m, symEntropy m.1 ∂(finiteProbability Q hl₀.le hl₁ n).toMeasure) = _ at h
  rw [← hfixed] at h
  change jMean Q = (n:ℝ)*edgeJMean Q lam at h
  rw [h]
  calc
    _ = ((n:ℝ)*lam^2)*edgeJMean Q lam := by rw [hcrit, one_mul]
    _ = _ := by ring

lemma regular_fixed_entropy_radial (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) (n : ℕ)
    (hcrit : (n:ℝ)*lam^2 = 1) (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) :
    (1-lam^2)/2*Q.nu ≤ (8/5)*(1-lam^2)*(jMean Q)^2-3*correlationEntropy Q lam n := by
  have hp := finite_positive Q hl₀.le hl₁ n
  have hJ := finite_integrable_symEntropy Q hl₀.le hl₁ n
  have hB := finite_integrable_correction Q hl₀.le hl₁ n
  rw [← hfixed] at hp hJ hB
  have hI : Integrable (fun m : Message ↦ info m.1) Q.probability.toMeasure :=
    compact_integrable (continuous_info_comp continuous_subtype_val)
  have hJe := edgeJ_integrable Q hl₀.le hl₁
  have hIe : Integrable (fun m : Message ↦ info (edgeMessage lam m)) Q.probability.toMeasure :=
    compact_integrable (continuous_info_comp (continuous_edgeMessage lam))
  have hBe : Integrable (fun m : Message ↦ correction (edgeMessage lam m)) Q.probability.toMeasure :=
    compact_integrable (continuous_correction_comp (continuous_edgeMessage lam) (fun m i ↦ (edge_positive hl₀.le hl₁ m).1 i))
  have hF : Integrable (fun m : Message ↦ functional m.1) Q.probability.toMeasure :=
    (hI.const_mul 3 |>.sub (hJ.const_mul 2)).add (hB.const_mul (4/5))
  have hFe : Integrable (fun m : Message ↦ functional (edgeMessage lam m)) Q.probability.toMeasure :=
    (hIe.const_mul 3 |>.sub (hJe.const_mul 2)).add (hBe.const_mul (4/5))
  have hrad := integral_mono_ae (μ := Q.probability.toMeasure)
    (f := fun m : Message ↦ (1-lam^2)/2*xMoment m^2)
    (g := fun m ↦ functional m.1-(lam^2)⁻¹*functional (edgeMessage lam m))
    ((compact_integrable (continuous_xMoment.pow 2)).const_mul _) (hF.sub (hFe.const_mul _))
    (hp.mono (fun m hm ↦ radial_inequality m.1 hm lam hl₀ hl₁))
  rw [integral_const_mul, integral_sub hF (hFe.const_mul _), integral_const_mul] at hrad
  change (1-lam^2)/2*Q.nu ≤ _ at hrad
  have hJid := finiteLaw_symEntropy Q hl₀.le hl₁ n
  have hBid := finiteLaw_correction Q hl₀.le hl₁ n
  have hIid := finiteLaw_info Q hl₀.le hl₁ n
  change (∫ m, symEntropy m.1 ∂(finiteProbability Q hl₀.le hl₁ n).toMeasure) = _ at hJid
  change (∫ m, correction m.1 ∂(finiteProbability Q hl₀.le hl₁ n).toMeasure) = _ at hBid
  change (∫ m, info m.1 ∂(finiteProbability Q hl₀.le hl₁ n).toMeasure) = _ at hIid
  rw [← hfixed] at hJid hBid hIid
  have hninv : (lam^2)⁻¹ = (n:ℝ) := by
    apply mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos hl₀))
    rw [mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hl₀))]
    nlinarith [hcrit]
  have hFid : (∫ m, functional m.1 ∂Q.probability.toMeasure) =
      3*(∫ m, info m.1 ∂Q.probability.toMeasure)-2*jMean Q+
      (4/5)*(∫ m, correction m.1 ∂Q.probability.toMeasure) := by
    unfold functional
    rw [integral_add (f := fun m : Message ↦ 3*info m.1-2*symEntropy m.1)
      (g := fun m ↦ (4/5)*correction m.1) ((hI.const_mul _).sub (hJ.const_mul _)) (hB.const_mul _),
      integral_sub (f := fun m : Message ↦ 3*info m.1) (g := fun m ↦ 2*symEntropy m.1)
        (hI.const_mul _) (hJ.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  have hFeid : (∫ m, functional (edgeMessage lam m) ∂Q.probability.toMeasure) =
      3*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-2*edgeJMean Q lam+
      (4/5)*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure) := by
    unfold functional
    rw [integral_add (f := fun m : Message ↦ 3*info (edgeMessage lam m)-2*symEntropy (edgeMessage lam m))
      (g := fun m ↦ (4/5)*correction (edgeMessage lam m)) ((hIe.const_mul _).sub (hJe.const_mul _)) (hBe.const_mul _),
      integral_sub (f := fun m : Message ↦ 3*info (edgeMessage lam m)) (g := fun m ↦ 2*symEntropy (edgeMessage lam m))
        (hIe.const_mul _) (hJe.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  rw [hFid, hFeid, hninv, hIid, hBid] at hrad
  change jMean Q = (n:ℝ)*edgeJMean Q lam at hJid
  change _ ≤ 3*((n:ℝ)*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-correlationEntropy Q lam n)-
    2*jMean Q+(4/5)*((n:ℝ)*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)+
      2*((n:ℝ)^2-n)*(edgeJMean Q lam)^2)-
    (n:ℝ)*(3*(∫ m, info (edgeMessage lam m) ∂Q.probability.toMeasure)-2*edgeJMean Q lam+
      (4/5)*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure)) at hrad
  have he : ((n:ℝ)^2-n)*(edgeJMean Q lam)^2 = (1-lam^2)*(jMean Q)^2 := by
    rw [fixed_edgeJ Q hl₀ hl₁ n hcrit hfixed]
    have hn : ((n:ℝ)^2-n)*lam^4 = 1-lam^2 := by
      nlinarith [sq_nonneg ((n:ℝ)*lam^2-1), hcrit]
    calc
      _ = (((n:ℝ)^2-n)*lam^4)*(jMean Q)^2 := by ring
      _ = _ := by rw [hn]
  nlinarith [hJid, he]

end ThreeState.TreeClauses.Positive

end 

noncomputable section
namespace ThreeState.TreeClauses.Positive

lemma qExact_lower {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1) :
    (37/81:ℝ) ≤ qExact lam := by
  unfold qExact
  apply (le_div_iff₀ (by positivity : 0 < 2+lam)).2
  linarith

lemma cExact_lower {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1) :
    cLower lam ≤ cExact lam := by
  have hq := qExact_lower hl₀ hl₁
  unfold cExact cLower
  nlinarith [mul_nonneg hl₀ (sub_nonneg.mpr hq)]

lemma qExact_coefficient {lam : ℝ} :
    8*(37/27)*lam*qExact lam ≤ cExact lam^2 := by
  unfold cExact
  nlinarith [sq_nonneg ((37/27:ℝ)-2*lam*qExact lam)]

lemma jMean_square_bound {lam mu nu J : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hJ : 0 ≤ J) (hupper : J ≤ mu-lam*qExact lam*nu)
    (hregion : cExact lam^2*nu ≤ mu) :
    (8/5)*J^2 ≤ (8/5)*mu^2-(113/81)*lam*mu*nu := by
  let t := lam*qExact lam*nu
  have hq := qExact_lower hl₀ hl₁
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hc := mul_le_mul_of_nonneg_right (qExact_coefficient (lam := lam)) hnu
  have htu : 8*(37/27)*t ≤ mu := by dsimp [t]; nlinarith
  have hJsq : J^2 ≤ (mu-t)^2 := by
    have hu : J ≤ mu-t := hupper
    nlinarith
  have htt : t^2 ≤ (27/296)*mu*t := by
    have hh := mul_le_mul_of_nonneg_right htu ht
    nlinarith
  have htl : (37/81)*lam*nu ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg (mul_nonneg hl₀ hnu) (sub_nonneg.mpr hq)]
  have hm := mul_le_mul_of_nonneg_left htl hmu
  nlinarith

lemma strict_correlation_coefficient : (1:ℝ)/Real.sqrt 2+17/25 < 113/81 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hh : (2025:ℝ)/1448 < Real.sqrt 2 := by nlinarith
  have hfrac : (1:ℝ)/Real.sqrt 2 < 1448/2025 := (div_lt_iff₀ hp).2 (by nlinarith)
  linarith

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

theorem regular_fixed_mu_zero (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (n : ℕ) (hn : 2 ≤ n) (hcrit : (n:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) : Q.mu = 0 := by
  by_contra hmu0
  have hmu : 0 < Q.mu := lt_of_le_of_ne Q.mu_nonneg (Ne.symm hmu0)
  have hnu : 0 < Q.nu := (sq_pos_of_pos hmu).trans_le Q.second_moment_lower
  have hinfo := regular_fixed_moment_bounds Q hl₀ hl₁ n hcrit hfixed
  have hcl := cExact_lower hl₀.le hl₁.le
  have hc : 0 < cExact lam := (cLower_pos hl₀.le).trans_le hcl
  have hetaNonneg : 0 ≤ Q.eta := (mul_nonneg hc.le hnu.le).trans hinfo.2.2
  have hsq : (cExact lam*Q.nu)^2 ≤ Q.eta^2 :=
    (sq_le_sq₀ (mul_nonneg hc.le hnu.le) hetaNonneg).2 hinfo.2.2
  have hregion : cExact lam^2*Q.nu ≤ Q.mu := by
    apply (mul_le_mul_iff_right₀ hnu).mp
    nlinarith [Q.moment_discriminant]
  have hmuC : Q.mu*cExact lam^2 ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hmu).mp
    have hh := mul_le_mul_of_nonneg_left Q.second_moment_lower (sq_nonneg (cExact lam))
    nlinarith
  have hregionLower : Q.mu*cLower lam^2 ≤ 1 := by
    have hs : cLower lam^2 ≤ cExact lam^2 :=
      (sq_le_sq₀ (cLower_pos hl₀.le).le hc.le).2 hcl
    exact (mul_le_mul_of_nonneg_left hs hmu.le).trans hmuC
  have hlam : lam^2 ≤ 1/2 := by
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right hn' (sq_nonneg lam)
    nlinarith [hcrit]
  have hstrict := scalar_strict hl₀ hl₁ hmu.le (by norm_num : (0:ℝ) < 1)
    (le_refl (1:ℝ)) hregionLower (Or.inl hlam)
  have hJ := jMean_square_bound hl₀.le hl₁.le hmu.le hnu.le hinfo.1 hinfo.2.1 hregion
  have hH := regular_fixed_correlation_bounds Q hl₀ hl₁ n hn hcrit hfixed
  have hrad := regular_fixed_entropy_radial Q hl₀ hl₁ n hcrit hfixed
  have halpha : 0 < 1-lam^2 := by nlinarith
  have hent : Q.nu/2+3*correlationEntropy Q lam n/(1-lam^2) ≤ (8/5)*(jMean Q)^2 := by
    calc
      _ = ((1-lam^2)/2*Q.nu+3*correlationEntropy Q lam n)/(1-lam^2) := by
        field_simp [ne_of_gt halpha]
      _ ≤ _ := (div_le_iff₀ halpha).2 (by nlinarith)
  have hH' : 3*Q.mu^2/(2*(1+2*Q.mu/3))-(1/Real.sqrt 2)*(lam*Q.mu*Q.nu) ≤
      3*correlationEntropy Q lam n/(1-lam^2) := by
    convert hH using 1
    ring
  have hg := mul_le_mul_of_nonneg_right (le_of_lt strict_correlation_coefficient)
    (show 0 ≤ lam*Q.mu*Q.nu by positivity)
  have hb : Q.nu/2+3*Q.mu^2/(2*(1+2*Q.mu/3))+(17/25)*lam*Q.mu*Q.nu ≤ (8/5)*Q.mu^2 := by
    nlinarith
  have hcoef : 0 ≤ (1-lam^2)/2+17*lam*Q.mu/25 := by positivity
  have hsub := mul_le_mul_of_nonneg_left Q.second_moment_lower hcoef
  have hnecessary : scalarT lam Q.mu 1*Q.mu^2 ≤ (8/5)*Q.mu^2 := by
    calc
      _ = ((1-lam^2)/2+17*lam*Q.mu/25)*Q.mu^2+3*Q.mu^2/(2*(1+2*Q.mu/3)) := by
        unfold scalarT; ring
      _ ≤ ((1-lam^2)/2+17*lam*Q.mu/25)*Q.nu+3*Q.mu^2/(2*(1+2*Q.mu/3)) := by linarith
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg lam) hnu.le]
  have hh := mul_lt_mul_of_pos_right hstrict (sq_pos_of_pos hmu)
  linarith

lemma message_uniform_of_x_zero {m : Message} (h : xMoment m = 0) : m.1 = fun _ ↦ 1 := by
  dsimp [xMoment, momentX, centered, avg] at h
  funext i
  fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (m.1 0-1), sq_nonneg (m.1 1-1), sq_nonneg (m.1 2-1)]

theorem regular_fixed_uniform (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (n : ℕ) (hn : 2 ≤ n) (hcrit : (n:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) :
    ∀ᵐ m ∂Q.probability.toMeasure, m.1 = fun _ ↦ 1 := by
  have hzero := regular_fixed_mu_zero Q hl₀ hl₁ n hn hcrit hfixed
  have he : ∀ᵐ m ∂Q.probability.toMeasure, xMoment m = 0 :=
    (integral_eq_zero_iff_of_nonneg xMoment_nonneg (compact_integrable continuous_xMoment)).1 hzero
  exact he.mono (fun _ hm ↦ message_uniform_of_x_zero hm)

end ThreeState.TreeClauses.Positive

end

end OAI
