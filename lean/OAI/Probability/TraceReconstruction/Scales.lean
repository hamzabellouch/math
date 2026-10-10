import Mathlib

namespace OAI

/-!
# Scales

Exact block exponents, deletion reduction, induction depth, backward target scales, and uniform power absorption.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction
/-- The exact real scale exponents in the scale inequalities; natural indices are zero-based. -/
def scaleA (b j : ℕ) (ε : ℝ) : ℝ := (1+ε)* (2:ℝ)^j / (2:ℝ)^b - ε

def scaleKappa (b j : ℕ) (ε : ℝ) : ℝ :=
  scaleA b (j-1) ε - 3*((2:ℝ)^j-1)*ε

def sourceEpsilon (B D : ℕ) : ℝ := 1 / ((2:ℝ)^(4*B+100) * (D+1))

theorem scaleA_top (b : ℕ) (ε : ℝ) : scaleA b b ε = 1 := by
  unfold scaleA
  field_simp
  ring

theorem scaleA_step (b j : ℕ) (ε : ℝ) : scaleA b (j+1) ε - 2*scaleA b j ε = ε := by
  unfold scaleA
  rw [pow_succ]
  ring

theorem scaleKappa_step (b j : ℕ) (ε : ℝ) (hj : 1 ≤ j) :
    2*scaleKappa b j ε - scaleKappa b (j+1) ε - ε = ε := by
  unfold scaleKappa scaleA
  simp only [Nat.add_sub_cancel]
  rw [show j = (j-1)+1 from by omega, pow_succ]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

def forcedDecay (b : ℕ) (ε d : ℝ) : ℝ :=
  ε/2 + ∑ k ∈ Finset.range (b-1),
    ((2:ℝ)^b / (2:ℝ)^(k+2))*(scaleKappa b (k+2) ε / 2 + ε) +
  (2:ℝ)^b * scaleA b 0 ε * d

theorem forcedDecay_summand (b k : ℕ) (ε : ℝ) :
    ((2:ℝ)^b / (2:ℝ)^(k+2))*(scaleKappa b (k+2) ε / 2 + ε) =
      (1+ε)/4 - 3*((2:ℝ)^b/2)*ε + ((2:ℝ)^b/(2:ℝ)^(k+1))*ε := by
  unfold scaleKappa scaleA
  simp only [show k+2-1=k+1 by omega, pow_succ]
  field_simp
  ring

theorem forcedDecay_lower (b : ℕ) (ε d : ℝ) (hb : 1 ≤ b) (he : 0 ≤ ε) :
    d + ((b:ℝ)-1)/4 - (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2))*ε ≤
      forcedDecay b ε d := by
  have hterm (k : ℕ) : 1/4 - 3*((2:ℝ)^b/2)*ε ≤
      ((2:ℝ)^b / (2:ℝ)^(k+2))*(scaleKappa b (k+2) ε / 2 + ε) := by
    rw [forcedDecay_summand]
    have hp : 0 ≤ ((2:ℝ)^b / (2:ℝ)^(k+1))*ε := by positivity
    linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (b-1)) => hterm k)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Nat.cast_sub hb, Nat.cast_one] at hsum
  have ha : (2:ℝ)^b * scaleA b 0 ε * d = d - ((2:ℝ)^b-1)*d*ε := by
    unfold scaleA
    simp only [pow_zero, mul_one]
    field_simp
    ring
  unfold forcedDecay
  rw [ha]
  have hp : 0 ≤ (2:ℝ)^b*ε := by positivity
  nlinarith

theorem nat_add_one_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem sourceEpsilon_pos (B D : ℕ) : 0 < sourceEpsilon B D := by
  unfold sourceEpsilon
  positivity

theorem sourceEpsilon_loss (B D b : ℕ) (d : ℝ) (hb : b ≤ B)
    (hd0 : 0 ≤ d) (hd : d ≤ 3 + (B:ℝ)*D) :
    (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2))*sourceEpsilon B D < 1/100 := by
  have hpow : (2:ℝ)^b ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) hb
  have hB : (B:ℝ)+1 ≤ (2:ℝ)^B := by exact_mod_cast nat_add_one_le_two_pow B
  have hB0 : (0:ℝ) ≤ B := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hh : (((2:ℝ)^b-1)*d + 3*b*((2:ℝ)^b/2)) ≤
      4*((2:ℝ)^B)^2*((D:ℝ)+1) := by
    have hb' : (b:ℝ) ≤ B := by exact_mod_cast hb
    have h1 := mul_le_mul_of_nonneg_right (show (2:ℝ)^b-1 ≤ (2:ℝ)^B by linarith) hd0
    have h2 := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ)^B by positivity)
    have h3 := mul_le_mul hb' hpow (by positivity : (0:ℝ) ≤ (2:ℝ)^b) hB0
    have h4 := mul_le_mul_of_nonneg_left hB hD0
    have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ (2:ℝ)^B by positivity)
    have h6 := mul_le_mul_of_nonneg_left hB (show 0 ≤ (2:ℝ)^B by positivity)
    nlinarith [sq_nonneg ((2:ℝ)^B)]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hh (sourceEpsilon_pos B D).le)
  unfold sourceEpsilon
  have hpos : 0 < (2:ℝ)^(4*B+100) := by positivity
  have hp2 : (2:ℝ)^(2*B) = ((2:ℝ)^B)^2 := by rw [mul_comm 2 B, pow_mul]
  have hp4 : (2:ℝ)^(4*B+100) = ((2:ℝ)^B)^2 * (2:ℝ)^(2*B+100) := by
    rw [show 4*B+100=2*B+(2*B+100) by omega, pow_add, hp2]
  have hh2 : (400:ℝ) < (2:ℝ)^(2*B+100) := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 9 ≤ 2*B+100)
    norm_num at h ⊢
    linarith
  rw [mul_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [hp4]
  have := mul_lt_mul_of_pos_left hh2 (show 0 < ((2:ℝ)^B)^2*((D:ℝ)+1) by positivity)
  nlinarith

theorem forcedDecay_margin (B D b : ℕ) (d : ℝ) (hb1 : 1 ≤ b) (hb : b ≤ B)
    (hd0 : 0 ≤ d) (hd : d ≤ 3 + (B:ℝ)*D) :
    d + ((b:ℝ)-1)/4 - 1/20 + 3/100 < forcedDecay b (sourceEpsilon B D) d := by
  have h := forcedDecay_lower b (sourceEpsilon B D) d hb1 (sourceEpsilon_pos B D).le
  have hg := sourceEpsilon_loss B D b d hb hd0 hd
  linarith
end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology
namespace TraceReconstruction

def workingDeletion (q : ℝ) : ℝ := min q (1/2)
def blockGain (b : ℕ) : ℝ := ((b:ℝ)-1)/4-1/20
def warmupBlocks (B : ℕ) : ℕ := 5*2^B
def sourceDepth (B : ℕ) (ζ H : ℝ) : ℕ := ⌊(1-ζ)*Real.log H/((B:ℝ)*Real.log 2)⌋₊
def totalScoreExponent (B D : ℕ) : ℝ :=
  11/5+∑ i ∈ Finset.range D, blockGain (if i<warmupBlocks B then 2 else B)
def finalSlope (B : ℕ) (ζ : ℝ) : ℝ := (1-ζ)*blockGain B/((B:ℝ)*Real.log 2)

theorem workingDeletion_bounds {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    workingDeletion q ∈ Set.Ioo 0 1 ∧ q/2 ≤ workingDeletion q ∧ workingDeletion q ≤ q := by
  unfold workingDeletion
  constructor
  · constructor
    · exact lt_min hq.1 (by norm_num)
    · exact (min_le_left _ _).trans_lt hq.2
  constructor
  · exact le_min (by linarith [hq.1]) (by linarith [hq.2])
  · exact min_le_left _ _

theorem workingScale_bounds {q L : ℝ} (hq : q ∈ Set.Ioo 0 1) (hL : 0 ≤ L) :
    q^3*L/8 ≤ (workingDeletion q)^3*L ∧ (workingDeletion q)^3*L ≤ q^3*L := by
  have hw := workingDeletion_bounds hq
  have hl := pow_le_pow_left₀ (div_nonneg hq.1.le (by norm_num)) hw.2.1 3
  have hu := pow_le_pow_left₀ hw.1.1.le hw.2.2 3
  constructor
  · have := mul_le_mul_of_nonneg_right hl hL
    nlinarith only [this]
  · exact mul_le_mul_of_nonneg_right hu hL

theorem blockGain_two : blockGain 2 = 1/5 := by norm_num [blockGain]
theorem blockGain_pos (B : ℕ) (hB : 2 ≤ B) : 0 < blockGain B := by
  have hB' : (2:ℝ) ≤ B := by exact_mod_cast hB
  unfold blockGain
  linarith

theorem totalScoreExponent_exact (B D : ℕ) (hD : warmupBlocks B ≤ D) :
    totalScoreExponent B D = 11/5 + (warmupBlocks B:ℝ)/5 +
      ((D:ℝ)-warmupBlocks B)*blockGain B := by
  unfold totalScoreExponent
  rw [← Nat.add_sub_of_le hD, Finset.sum_range_add]
  have hfirst : (∑ i ∈ Finset.range (warmupBlocks B),
      blockGain (if i<warmupBlocks B then 2 else B)) = (warmupBlocks B:ℝ)/5 := by
    simp only [Finset.sum_congr rfl (fun i hi => congrArg blockGain (ite_eq_left (Finset.mem_range.mp hi))), blockGain_two]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hfirst]
  have hlast : (∑ i ∈ Finset.range (D-warmupBlocks B),
      blockGain (if warmupBlocks B+i<warmupBlocks B then 2 else B)) =
      ((D:ℝ)-warmupBlocks B)*blockGain B := by
    simp only [show ∀ i, ¬warmupBlocks B+i<warmupBlocks B from fun i => by omega, ite_false,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hD]
  rw [hlast]
  simp only [Nat.add_sub_of_le hD]
  ring

theorem sourceDepth_lower (B : ℕ) (ζ H : ℝ) :
    (1-ζ)*Real.log H/((B:ℝ)*Real.log 2)-1 < (sourceDepth B ζ H:ℝ) := by
  have := Nat.lt_floor_add_one ((1-ζ)*Real.log H/((B:ℝ)*Real.log 2))
  change _ < (sourceDepth B ζ H:ℝ)+1 at this
  linarith

theorem totalScoreExponent_slope_lower (B : ℕ) (ζ H : ℝ) (hB : 2 ≤ B)
    (hD : warmupBlocks B ≤ sourceDepth B ζ H) :
    finalSlope B ζ * Real.log H -
      (blockGain B + (warmupBlocks B:ℝ)*blockGain B) <
      totalScoreExponent B (sourceDepth B ζ H) := by
  rw [totalScoreExponent_exact B _ hD]
  have hh := mul_lt_mul_of_pos_right (sourceDepth_lower B ζ H) (blockGain_pos B hB)
  unfold finalSlope
  have he : ((1-ζ)*Real.log H/((B:ℝ)*Real.log 2))*blockGain B =
      ((1-ζ)*blockGain B/((B:ℝ)*Real.log 2))*Real.log H := by ring
  rw [sub_mul, he] at hh
  have hw : (0:ℝ) ≤ warmupBlocks B := by positivity
  linarith

theorem sourceDepth_tendsto (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ < 1)
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    Tendsto (fun k => sourceDepth B ζ (H k)) atTop atTop := by
  have hden : 0 < (B:ℝ)*Real.log 2 := by
    apply mul_pos
    · exact_mod_cast (show 0 < B by omega)
    · exact Real.log_pos (by norm_num)
  have ht := (Real.tendsto_log_atTop.comp hH).const_mul_atTop (sub_pos.mpr hζ)
  have ht' := ht.atTop_div_const hden
  exact tendsto_nat_floor_atTop.comp ht'

/-- A fixed multiplicative constant is absorbed by any strict exponent
slope margin, with two independently diverging instance parameters. -/
theorem eventually_exponent_margin {N H d : ℕ → ℝ} {α c K a : ℝ}
    (hN : Tendsto N atTop atTop) (hH : Tendsto H atTop atTop)
    (hα : c < α) (ha : 0 < a)
    (hd : ∀ᶠ k in atTop, α*Real.log (H k)-K ≤ d k) :
    ∀ᶠ k in atTop, (N k)^(c*Real.log (H k)) ≤ a*(N k)^(d k) := by
  have hlog := (Real.tendsto_log_atTop.comp hH).const_mul_atTop (sub_pos.mpr hα)
  filter_upwards [hd, hlog.eventually_ge_atTop (K+1), hN.eventually_ge_atTop (max 1 (1/a))] with k hd hlog hN
  have hN1 : 1 ≤ N k := (le_max_left _ _).trans hN
  have hNa : 1/a ≤ N k := (le_max_right _ _).trans hN
  simp only [Function.comp_apply] at hlog
  have hex : c*Real.log (H k)+1 ≤ d k := by nlinarith only [hd,hlog]
  have hp := Real.rpow_le_rpow_of_exponent_le hN1 hex
  rw [Real.rpow_add (by linarith : 0 < N k), Real.rpow_one] at hp
  have hapos : 1 ≤ a*N k := (div_le_iff₀ ha).mp hNa |>.trans_eq (mul_comm _ _)
  calc
    (N k)^(c*Real.log (H k)) ≤ (a*N k)*(N k)^(c*Real.log (H k)) := by
      exact le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _) hapos
    _ ≤ a*(N k)^(d k) := by
      have := mul_le_mul_of_nonneg_left hp ha.le
      nlinarith only [this]

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open Filter

/-- Literal source block dimensions, with zero-based block number. -/
def sourceDimension (B i : ℕ) : ℕ := if i < warmupBlocks B then 2 else B

def sourceScaleProduct (B D i : ℕ) : ℝ :=
  ∏j∈Finset.Ico i D,scaleA (sourceDimension B j) 0 (sourceEpsilon B D)

/-- The backwards target scales as an exact product of source exponents. -/
def sourceTargetScale (B D : ℕ) (n : ℝ) (i : ℕ) : ℝ := n ^ sourceScaleProduct B D i

theorem sourceTargetScale_top (B D : ℕ) (n : ℝ) : sourceTargetScale B D n D=n := by
  simp [sourceTargetScale,sourceScaleProduct]

theorem sourceTargetScale_step (B D i : ℕ) (n : ℝ) (hn : 0 ≤ n) (hi : i < D) :
    sourceTargetScale B D n i =
      (sourceTargetScale B D n (i+1))^(scaleA (sourceDimension B i) 0 (sourceEpsilon B D)) := by
  unfold sourceTargetScale sourceScaleProduct
  rw [←Real.rpow_mul hn,Finset.prod_eq_prod_Ico_succ_bot hi]
  rw [mul_comm]

theorem sourceEpsilon_small (B D : ℕ) :
    ((D:ℝ)+1)*(2:ℝ)^B*sourceEpsilon B D ≤ 1/2 := by
  have hp : 2*(2:ℝ)^B ≤ (2:ℝ)^(4*B+100) := by
    rw [←pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  unfold sourceEpsilon
  have hD : 0 < (D:ℝ)+1 := by positivity
  have hpow : 0 < (2:ℝ)^(4*B+100) := by positivity
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have he : ((D:ℝ)+1)*2^B*(1/(2^(4*B+100)*((D:ℝ)+1)))*2 =
      (2*2^B)/2^(4*B+100) := by field_simp
  rw [he]
  exact (div_le_one hpow).mpr hp

theorem scaleA_zero_lower (b B : ℕ) (ε : ℝ) (hb : b ≤ B) (he : 0 ≤ ε) :
    (1/((2:ℝ)^B))*(1-((2:ℝ)^B-1)*ε) ≤ scaleA b 0 ε := by
  have hp : (2:ℝ)^b ≤ 2^B := pow_le_pow_right₀ (by norm_num) hb
  have hpos : 0 < (2:ℝ)^b := by positivity
  have hposB : 0 < (2:ℝ)^B := by positivity
  have hd := div_le_div_of_nonneg_left (show 0 ≤ 1+ε by linarith) hpos hp
  have heq : (1/((2:ℝ)^B))*(1-((2:ℝ)^B-1)*ε) = (1+ε)/2^B-ε := by
    field_simp; ring
  rw [heq]
  unfold scaleA
  norm_num only [pow_zero,mul_one]
  linarith only [hd]

theorem sourceScaleProduct_lower (B D i : ℕ) (hB : 2 ≤ B) :
    1/(2*((2:ℝ)^(B*D))) ≤ sourceScaleProduct B D i := by
  let ε := sourceEpsilon B D
  let u := ((2:ℝ)^B-1)*ε
  let a := (1/(2:ℝ)^B)*(1-u)
  have hε : 0 < ε := sourceEpsilon_pos _ _
  have hp : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hp) hε.le
  have hsmall := sourceEpsilon_small B D
  have hu' : ((D:ℝ)+1)*u ≤ 1/2 := by
    dsimp [u]
    dsimp [ε] at *
    nlinarith only [mul_nonneg (show 0 ≤ (D:ℝ)+1 by positivity) hε.le,hsmall]
  have hu1 : u ≤ 1/2 := by nlinarith only [hu',mul_nonneg (Nat.cast_nonneg D) hu]
  have ha : 0 ≤ a := mul_nonneg (by positivity) (by linarith only [hu1])
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h1 : 1/(2:ℝ)^B ≤ 1 := (div_le_one (by positivity)).mpr hp
    exact (mul_le_mul_of_nonneg_left (by linarith only [hu] : 1-u ≤ 1) (by positivity)).trans (by simpa using h1)
  have hb : 1/2 ≤ (1-u)^D := by
    have H := one_add_mul_le_pow (a := -u) (by linarith only [hu1]) D
    have hd : (D:ℝ)*u ≤ 1/2 := by nlinarith only [hu',hu]
    simpa only [sub_eq_add_neg] using (show (1:ℝ)/2 ≤ (1+-u)^D by nlinarith only [H,hd])
  have hc : (Finset.Ico i D).card ≤ D := by simp only [Nat.card_Ico]; omega
  calc
    _ = (1/(2:ℝ)^B)^D*(1/2) := by rw [div_pow,one_pow,←pow_mul]; field_simp
    _ ≤ (1/(2:ℝ)^B)^D*(1-u)^D := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = a^D := (mul_pow _ _ _).symm
    _ ≤ a^(Finset.Ico i D).card := pow_le_pow_of_le_one ha ha1 hc
    _ = ∏j∈Finset.Ico i D,a := by simp
    _ ≤ sourceScaleProduct B D i := by
      apply Finset.prod_le_prod₀ (fun _ _ => ha)
      intro j _
      apply scaleA_zero_lower _ _ _ _ hε.le
      unfold sourceDimension
      split_ifs <;> omega

theorem sourceDepth_upper (B : ℕ) (ζ H : ℝ) (_hB : 2 ≤ B)
    (hζ : ζ ≤ 1) (hH : 1 ≤ H) :
    (sourceDepth B ζ H:ℝ) ≤ (1-ζ)*Real.log H/((B:ℝ)*Real.log 2) := by
  apply Nat.floor_le
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hζ) (Real.log_nonneg hH))
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))

theorem sourceDepth_power (B : ℕ) (ζ H : ℝ) (hB : 2 ≤ B)
    (hζ : ζ ≤ 1) (hH : 1 ≤ H) :
    (2:ℝ)^(B*sourceDepth B ζ H) ≤ H^(1-ζ) := by
  have hden : 0 < (B:ℝ)*Real.log 2 :=
    mul_pos (by exact_mod_cast (show 0 < B by omega)) (Real.log_pos (by norm_num))
  have hd := (le_div_iff₀ hden).mp (sourceDepth_upper B ζ H hB hζ hH)
  apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos (by linarith) _)).mp
  rw [Real.log_pow,Real.log_rpow (by linarith : 0 < H)]
  push_cast
  nlinarith only [hd]

/-- Source smallest-scale lower bound, with an absolute explicit factor. -/
theorem sourceTargetScale_log_lower (B : ℕ) (ζ H n : ℝ) (i : ℕ) (hB : 2 ≤ B)
    (hζ : ζ ≤ 1) (hH : 1 ≤ H) (hn : 1 < n) :
    Real.log n/(2*H^(1-ζ)) ≤ Real.log (sourceTargetScale B (sourceDepth B ζ H) n i) := by
  have hp := sourceDepth_power B ζ H hB hζ hH
  have hs := sourceScaleProduct_lower B (sourceDepth B ζ H) i hB
  have hfrac : 1/(2*H^(1-ζ)) ≤ 1/(2*(2:ℝ)^(B*sourceDepth B ζ H)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hp])
  have hh := mul_le_mul_of_nonneg_right (hfrac.trans hs) (Real.log_pos hn).le
  unfold sourceTargetScale
  rw [Real.log_rpow (by linarith)]
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh

/-- Polynomial depth losses are negligible compared with the H-zeta gain.
 This statement has no bounded-deletion-rate premise. -/
theorem sourceDepth_polynomial_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    Tendsto (fun k => ((sourceDepth B ζ (H k):ℝ)+1)^h/(H k)^ζ) atTop (nhds 0) := by
  let A := (1-ζ)/((B:ℝ)*Real.log 2)+1
  have hd : 0 < (B:ℝ)*Real.log 2 :=
    mul_pos (by exact_mod_cast (show 0 < B by omega)) (Real.log_pos (by norm_num))
  have hA : 0 < A := by dsimp [A]; positivity [sub_pos.mpr hζ.2]
  have hl := (isLittleO_log_rpow_rpow_atTop (h:ℝ) hζ.1).tendsto_div_nhds_zero.comp hH
  simp only [Real.rpow_natCast] at hl
  have hx := hl.const_mul (A^h)
  simp only [mul_zero] at hx
  apply squeeze_zero' _ _ hx
  · filter_upwards [hH.eventually_gt_atTop 0] with k hk
    exact div_nonneg (by positivity) (Real.rpow_pos_of_pos hk _).le
  · filter_upwards [hH.eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp hH).eventually_ge_atTop 1] with k hk hklog
    have hD := sourceDepth_upper B ζ (H k) hB hζ.2.le hk
    have hDa : (sourceDepth B ζ (H k):ℝ)+1 ≤ A*Real.log (H k) := by
      dsimp [A]
      change 1 ≤ Real.log (H k) at hklog
      calc
        _ ≤ (1-ζ)*Real.log (H k)/((B:ℝ)*Real.log 2)+Real.log (H k) := add_le_add hD hklog
        _ = _ := by ring
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (sourceDepth B ζ (H k):ℝ)+1) hDa h
    rw [mul_pow] at hh
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by dsimp only [Function.comp_def]; ring)

/-- Uniform quantitative scale margin.  This is the source's Lambda*H^zeta
 bound, before any little-o notation or parameter choices. -/
theorem sourceTargetScale_epsilon_log_lower (B : ℕ) (ζ H n Λ : ℝ) (i : ℕ)
    (hB : 2 ≤ B) (hζ : ζ ≤ 1) (hH : 1 ≤ H) (hn : 1 < n)
    (hΛ : 0 < Λ) (hrel : Real.log n=Λ*H) :
    Λ*H^ζ/(2*(2:ℝ)^(4*B+100)*((sourceDepth B ζ H:ℝ)+1)) ≤
      sourceEpsilon B (sourceDepth B ζ H)*
        Real.log (sourceTargetScale B (sourceDepth B ζ H) n i) := by
  have h := mul_le_mul_of_nonneg_left (sourceTargetScale_log_lower B ζ H n i hB hζ hH hn)
    (sourceEpsilon_pos B (sourceDepth B ζ H)).le
  apply le_trans _ h
  rw [hrel,Real.rpow_sub (by linarith : 0 < H), Real.rpow_one]
  unfold sourceEpsilon
  have hH0 : H≠0 := by linarith
  have hHz : H^ζ≠0 := (Real.rpow_pos_of_pos (by linarith : 0 < H) _).ne'
  have hd : (sourceDepth B ζ H:ℝ)+1≠0 := by positivity
  have hp : (2:ℝ)^(4*B+100)≠0 := by positivity
  apply le_of_eq
  field_simp

theorem source_absorption_ratio_bound (B h : ℕ) (ζ H n Λ : ℝ) (i : ℕ)
    (hB : 2 ≤ B) (hζ : ζ ≤ 1) (hH : 1 ≤ H) (hn : 1 < n)
    (hΛ : 0 < Λ) (hrel : Real.log n=Λ*H) :
    ((sourceDepth B ζ H:ℝ)+1)^h*Λ /
      (sourceEpsilon B (sourceDepth B ζ H)*
        Real.log (sourceTargetScale B (sourceDepth B ζ H) n i)) ≤
      (2*(2:ℝ)^(4*B+100))*(((sourceDepth B ζ H:ℝ)+1)^(h+1)/H^ζ) := by
  have hHz : 0 < H^ζ := Real.rpow_pos_of_pos (by linarith) _
  have hlow := sourceTargetScale_epsilon_log_lower B ζ H n Λ i hB hζ hH hn hΛ hrel
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ ((sourceDepth B ζ H:ℝ)+1)^h*Λ)
    (by positivity : 0 < Λ*H^ζ/(2*(2:ℝ)^(4*B+100)*((sourceDepth B ζ H:ℝ)+1))) hlow
  apply hh.trans_eq
  rw [pow_succ]
  field_simp; ring

/-- Joint-regime uniform absorption at the genuine backwards scales,
 with an arbitrary index choice and with the channel unchanged across scales. -/
theorem source_uniform_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ → ℝ} (i : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀k,0 < Λ k) (hrel : ∀k,Real.log (n k)=Λ k*H k) :
    Tendsto (fun k => ((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k /
      (sourceEpsilon B (sourceDepth B ζ (H k))*
        Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) (i k)))) atTop (nhds 0) := by
  have hb := (sourceDepth_polynomial_absorption B (h+1) ζ hB hζ hH).const_mul
    (2*(2:ℝ)^(4*B+100))
  simp only [mul_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1] with k hk hnk
    have hh := sourceTargetScale_epsilon_log_lower B ζ (H k) (n k) (Λ k) (i k)
      hB hζ.2.le hk hnk (hΛ k) (hrel k)
    have hΛk := hΛ k
    have hHk : 0 < H k := by linarith
    exact div_nonneg (by positivity) ((by positivity :
      0 ≤ Λ k*(H k)^ζ/(2*(2:ℝ)^(4*B+100)*((sourceDepth B ζ (H k):ℝ)+1))).trans hh)
  · filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1] with k hk hnk
    exact source_absorption_ratio_bound B h ζ (H k) (n k) (Λ k) (i k)
      hB hζ.2.le hk hnk (hΛ k) (hrel k)

theorem source_uniform_exp_absorption (B h : ℕ) (ζ C δ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) (hC : 0 ≤ C) (hδ : 0 < δ)
    {n Λ H : ℕ → ℝ} (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀k,0 < Λ k) (hrel : ∀k,Real.log (n k)=Λ k*H k) :
    ∀ᶠk in atTop,∀i,
      Real.exp (C*((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k) ≤
        (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i)^
          (δ*sourceEpsilon B (sourceDepth B ζ (H k))) := by
  have hb := (sourceDepth_polynomial_absorption B (h+1) ζ hB hζ hH).const_mul
    (C*(2*(2:ℝ)^(4*B+100)))
  simp only [mul_zero] at hb
  filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1,
    hb.eventually_lt_const hδ] with k hk hnk hbound
  intro i
  have hratio := source_absorption_ratio_bound B h ζ (H k) (n k) (Λ k) i
    hB hζ.2.le hk hnk (hΛ k) (hrel k)
  have hlower := sourceTargetScale_epsilon_log_lower B ζ (H k) (n k) (Λ k) i
    hB hζ.2.le hk hnk (hΛ k) (hrel k)
  have hΛk := hΛ k
  have hHk : 0 < H k := by linarith
  have hden : 0 < sourceEpsilon B (sourceDepth B ζ (H k))*
      Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i) :=
    lt_of_lt_of_le (by positivity) hlower
  have hMul := mul_le_mul_of_nonneg_left hratio hC
  have H' : C*(((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k)/
      (sourceEpsilon B (sourceDepth B ζ (H k))*
        Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i)) ≤ δ := by
    calc
      _ = C*(((sourceDepth B ζ (H k):ℝ)+1)^h*Λ k /
        (sourceEpsilon B (sourceDepth B ζ (H k))*
          Real.log (sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i))) := by ring
      _ ≤ _ := hMul.trans (by simpa only [mul_assoc] using hbound.le)
  have HH := (div_le_iff₀ hden).mp H'
  have hN : 0 < sourceTargetScale B (sourceDepth B ζ (H k)) (n k) i :=
    Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_def_of_pos hN]
  exact Real.exp_le_exp.mpr (by nlinarith only [HH])

/-- Direct instantiation with the manuscript's known deletion rate: Lambda
 is q^{-3}, H=q^3 log n, never recomputed at an intermediate scale. -/
theorem source_deletion_uniform_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ → ℝ} (i : ℕ → ℕ)
    (hq : ∀k,0 < q k) (hn : Tendsto n atTop atTop)
    (hH : Tendsto (fun k => (q k)^3*Real.log (n k)) atTop atTop) :
    Tendsto (fun k =>
      ((sourceDepth B ζ ((q k)^3*Real.log (n k)):ℝ)+1)^h*(q k)^(-3:ℤ) /
      (sourceEpsilon B (sourceDepth B ζ ((q k)^3*Real.log (n k)))*
        Real.log (sourceTargetScale B (sourceDepth B ζ ((q k)^3*Real.log (n k)))
          (n k) (i k)))) atTop (nhds 0) := by
  apply source_uniform_absorption B h ζ hB hζ i hn hH
  · intro k
    exact zpow_pos (hq k) _
  · intro k
    simp only [zpow_neg,zpow_ofNat]
    field_simp [(hq k).ne']

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology

/-- Logarithmic order along a genuine diverging positive scale. -/
def PowerRate (N f : ℕ → ℝ) (a : ℝ) : Prop :=
  (∀ᶠ t in Filter.atTop, 0 < f t) ∧ Tendsto (fun t => Real.log (f t) / Real.log (N t)) Filter.atTop (𝓝 a)

/-- A robust upper order, with arbitrary strictly positive exponent slack. -/
def PowerUpper (N f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ b, a < b → ∀ᶠ t in Filter.atTop, |f t| ≤ (N t)^b

variable {N f g : ℕ → ℝ} {a b : ℝ}

theorem PowerRate.congr (h : PowerRate N f a) (he : f =ᶠ[Filter.atTop] g) : PowerRate N g a := by
  constructor
  · filter_upwards [h.1,he] with t ht he; simpa [←he] using ht
  · exact h.2.congr' (he.mono fun t ht => by simp [ht])

theorem PowerRate.const (hN : Tendsto N Filter.atTop Filter.atTop) {c : ℝ} (hc : 0<c) :
    PowerRate N (fun _ => c) 0 := by
  exact ⟨Eventually.of_forall (fun _ => hc), (Real.tendsto_log_atTop.comp hN).const_div_atTop _⟩

theorem PowerRate.base (hN : Tendsto N Filter.atTop Filter.atTop) : PowerRate N N 1 := by
  have hn := hN.eventually_gt_atTop 1
  refine ⟨hn.mono fun _ h => by linarith, ?_⟩
  apply tendsto_congr' _ |>.mpr tendsto_const_nhds
  filter_upwards [hn] with t ht
  exact div_self (ne_of_gt (Real.log_pos ht))

theorem PowerRate.mul (hf : PowerRate N f a) (hg : PowerRate N g b) :
    PowerRate N (fun t => f t*g t) (a+b) := by
  refine ⟨by filter_upwards [hf.1,hg.1] with t h ht; positivity, ?_⟩
  apply (hf.2.add hg.2).congr'
  filter_upwards [hf.1,hg.1] with t h ht
  rw [Real.log_mul h.ne' ht.ne',add_div]

theorem PowerRate.div (hf : PowerRate N f a) (hg : PowerRate N g b) :
    PowerRate N (fun t => f t/g t) (a-b) := by
  refine ⟨by filter_upwards [hf.1,hg.1] with t h ht; positivity, ?_⟩
  apply (hf.2.sub hg.2).congr'
  filter_upwards [hf.1,hg.1] with t h ht
  rw [Real.log_div h.ne' ht.ne',sub_div]

theorem PowerRate.rpow (hf : PowerRate N f a) (c : ℝ) :
    PowerRate N (fun t => (f t)^c) (a*c) := by
  refine ⟨by filter_upwards [hf.1] with t h; positivity, ?_⟩
  apply (hf.2.mul_const c).congr'
  filter_upwards [hf.1] with t h
  rw [Real.log_rpow h]
  ring

theorem PowerRate.pow (hf : PowerRate N f a) (c : ℕ) :
    PowerRate N (fun t => (f t)^c) (a*c) := by
  simpa only [Real.rpow_natCast] using hf.rpow (c:ℝ)

theorem PowerRate.sqrt (hf : PowerRate N f a) :
    PowerRate N (fun t => Real.sqrt (f t)) (a/2) := by
  simpa only [Real.sqrt_eq_rpow,div_eq_mul_inv, one_mul] using hf.rpow (1/2:ℝ)

theorem PowerRate.inv (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) :
    PowerRate N (fun t=>(f t)⁻¹) (-a) := by
  simpa only [one_div,zero_sub] using (PowerRate.const hN (by norm_num : (0:ℝ)<1)).div hf

theorem PowerRate.const_mul (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0<c) : PowerRate N (fun t=>c*f t) a := by
  simpa only [zero_add] using (PowerRate.const hN hc).mul hf

theorem PowerRate.mul_const (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0<c) : PowerRate N (fun t=>f t*c) a := by
  simpa only [add_zero] using hf.mul (PowerRate.const hN hc)

theorem PowerRate.div_const (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0<c) : PowerRate N (fun t=>f t/c) a := by
  simpa only [sub_zero] using hf.div (PowerRate.const hN hc)

theorem PowerRate.upper (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) :
    PowerUpper N f a := by
  intro b hb
  filter_upwards [hN.eventually_gt_atTop 1,hf.1,hf.2.eventually_lt_const hb] with t hn hp hab
  rw [abs_of_pos hp,←Real.log_le_log_iff hp (Real.rpow_pos_of_pos (by linarith) b),Real.log_rpow (by linarith : 0<N t)]
  exact (div_lt_iff₀ (Real.log_pos hn)).mp hab |>.le

theorem PowerRate.lower (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) {c : ℝ}
    (hc : c<a) : ∀ᶠ t in Filter.atTop, (N t)^c ≤ f t := by
  filter_upwards [hN.eventually_gt_atTop 1,hf.1,hf.2.eventually_const_lt hc] with t hn hp hac
  rw [←Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith) c) hp, Real.log_rpow (by linarith : 0<N t)]
  exact (lt_div_iff₀ (Real.log_pos hn)).mp hac |>.le

theorem PowerRate.tendsto_atTop (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) (ha : 0<a) :
    Tendsto f Filter.atTop Filter.atTop := by
  exact tendsto_atTop_mono' Filter.atTop (hf.lower hN (show a/2<a by linarith))
    ((tendsto_rpow_atTop (show 0<a/2 by linarith)).comp hN)

theorem PowerUpper.mono (hf : PowerUpper N f a) (hab : a≤b) : PowerUpper N f b :=
  fun c hc => hf c (lt_of_le_of_lt hab hc)

theorem PowerUpper.congr (hf : PowerUpper N f a) (he : f =ᶠ[Filter.atTop] g) : PowerUpper N g a := by
  intro b hb
  filter_upwards [hf b hb,he] with t h he
  simpa [←he] using h

theorem PowerUpper.of_abs_le (hg : PowerUpper N g a) (h : ∀ᶠ t in Filter.atTop, |f t|≤|g t|) :
    PowerUpper N f a := by
  intro b hb
  filter_upwards [hg b hb,h] with t ht hh
  exact hh.trans ht

theorem PowerUpper.zero (hN : Tendsto N Filter.atTop Filter.atTop) (a : ℝ) : PowerUpper N (fun _=>0) a := by
  intro b hb
  filter_upwards [hN.eventually_gt_atTop 0] with t ht
  simpa using (Real.rpow_pos_of_pos ht b).le

theorem PowerUpper.mul (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerUpper N f a)
    (hg : PowerUpper N g b) : PowerUpper N (fun t=>f t*g t) (a+b) := by
  intro c hc
  let δ := (c-(a+b))/2
  have hd : 0<δ := by dsimp [δ]; linarith
  filter_upwards [hN.eventually_gt_atTop 0,hf (a+δ) (by linarith),hg (b+δ) (by linarith)] with t hn ht hs
  calc |f t*g t|=|f t| * |g t| := abs_mul _ _
       _ ≤ (N t)^(a+δ)*(N t)^(b+δ) := mul_le_mul ht hs (abs_nonneg _) (by positivity)
       _ = (N t)^c := by rw [←Real.rpow_add hn]; congr 1; dsimp [δ]; ring

theorem PowerUpper.pow (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerUpper N f a)
    (r : ℕ) : PowerUpper N (fun t=>(f t)^r) (a*r) := by
  induction r with
  | zero => simpa using (PowerRate.const hN (by norm_num : (0:ℝ)<1)).upper hN
  | succ r ih =>
    have H := ih.mul hN hf
    convert H using 1
    · ext t; exact pow_succ _ _
    · push_cast; ring

theorem PowerUpper.add (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerUpper N f a)
    (hg : PowerUpper N g a) : PowerUpper N (fun t=>f t+g t) a := by
  intro c hc
  let d := (a+c)/2
  have had : a<d := by dsimp [d]; linarith
  have hdc : d<c := by dsimp [d]; linarith
  have hpow := ((tendsto_rpow_atTop (sub_pos.mpr hdc)).comp hN).eventually_ge_atTop 2
  filter_upwards [hN.eventually_gt_atTop 0,hf d had,hg d had,hpow] with t hn hf hg hp
  calc |f t+g t| ≤ |f t|+|g t| := abs_add_le _ _
       _ ≤ 2*(N t)^d := by linarith
       _ ≤ (N t)^(c-d)*(N t)^d := mul_le_mul_of_nonneg_right hp (by positivity)
       _ = (N t)^c := by rw [←Real.rpow_add hn]; congr 1; ring

theorem PowerUpper.sum {ι : Type*} (hN : Tendsto N Filter.atTop Filter.atTop) (S : Finset ι)
    (f : ι→ℕ→ℝ) (h : ∀i∈S, PowerUpper N (f i) a) :
    PowerUpper N (fun t=>∑i∈S,f i t) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PowerUpper.zero hN a
  | @insert i S hi ih =>
    have hh := (h i (Finset.mem_insert_self _ _)).add hN
      (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh

theorem PowerRate.add_const (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    (ha : 0<a) {c : ℝ} (hc : 0≤c) : PowerRate N (fun t=>f t+c) a := by
  have ht := hf.tendsto_atTop hN ha
  have hratio : Tendsto (fun t=>1+c/f t) Filter.atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (ht.const_div_atTop c))
  have hl : Tendsto (fun t=>Real.log (1+c/f t)/Real.log (N t)) Filter.atTop (𝓝 0) :=
    (hratio.log one_ne_zero).div_atTop (Real.tendsto_log_atTop.comp hN)
  refine ⟨by filter_upwards [hf.1] with t h; positivity, ?_⟩
  have H := hf.2.add hl
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hf.1] with t hp
  have hh : 0<1+c/f t := by positivity
  rw [←add_div,←Real.log_mul hp.ne' hh.ne']
  congr 2
  field_simp

theorem PowerRate.of_tendsto (hN : Tendsto N Filter.atTop Filter.atTop)
    {c : ℝ} (hc : 0<c) (hf : Tendsto f Filter.atTop (𝓝 c)) : PowerRate N f 0 := by
  exact ⟨hf.eventually_const_lt hc,(hf.log hc.ne').div_atTop (Real.tendsto_log_atTop.comp hN)⟩

theorem PowerUpper.tendsto_zero (hN : Tendsto N Filter.atTop Filter.atTop)
    (hf : PowerUpper N f a) (ha : a<0) : Tendsto f Filter.atTop (𝓝 0) := by
  have H := (tendsto_rpow_neg_atTop (show 0< -(a/2) by linarith)).comp hN
  simp only [neg_neg] at H
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs,Function.comp_apply] using hf (a/2) (by linarith)) H

theorem PowerRate.of_ratio (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0<c) (hr : Tendsto (fun t=>g t/f t) Filter.atTop (𝓝 c)) : PowerRate N g a := by
  have hp : ∀ᶠ t in Filter.atTop, 0<g t := by
    filter_upwards [hf.1,hr.eventually_const_lt hc] with t ht hgt
    exact (div_pos_iff.mp hgt).resolve_right (by intro h; linarith [h.2]) |>.1
  refine ⟨hp,?_⟩
  have hh := (hr.log hc.ne').div_atTop (Real.tendsto_log_atTop.comp hN)
  have H := hf.2.add hh
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hf.1,hp] with t hf hg
  simp only [Function.comp_apply]
  rw [Real.log_div hg.ne' hf.ne']
  ring

theorem PowerRate.nat_floor (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    (ha : 0<a) : PowerRate N (fun t=>(⌊f t⌋₊:ℝ)) a := by
  exact hf.of_ratio hN (by norm_num : (0:ℝ)<1)
    (tendsto_nat_floor_div_atTop.comp (hf.tendsto_atTop hN ha))

theorem PowerRate.exp_neg_upper (hN : Tendsto N Filter.atTop Filter.atTop)
    (hf : PowerRate N f a) (ha : 0<a) (c : ℝ) :
    PowerUpper N (fun t=>Real.exp (-f t)) c := by
  intro b hb
  have hh := ((isLittleO_log_rpow_atTop (show 0<a/2 by linarith)).tendsto_div_nhds_zero).comp hN
  have hsmall := (hh.const_mul (-b)).eventually_lt_const (show (-b)*0<1 by simp)
  filter_upwards [hN.eventually_gt_atTop 0,hf.lower hN (show a/2<a by linarith),hsmall] with t hn hl hs
  rw [abs_of_pos (Real.exp_pos _),Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have hpos := Real.rpow_pos_of_pos hn (a/2)
  have hle : -b*Real.log (N t) ≤ (N t)^(a/2) := by
    have H := (div_lt_iff₀ hpos).mp (show (-b*Real.log (N t))/(N t)^(a/2)<1 by simpa only [mul_div_assoc,Function.comp_apply] using hs)
    linarith
  linarith

end TraceReconstruction

end
end
end

end OAI
