import OAI.Probability.TraceReconstruction.ErrorRates

namespace OAI

/-!
# Propagation

Moment restriction, scale margins, sharp budget closure, clipping and error propagation, and dense/warmup overlap.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem evenMomentSq_mono_order (P : FiniteLaw α) (F : α→ℝ) {j k : ℕ}
    (hj : 1≤j) (hjk : j≤k) : P.evenMomentSq F j ≤ P.evenMomentSq F k := by
  have hjp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hp : 1≤(k:ℝ)/j := (one_le_div hjp).mpr (by exact_mod_cast hjk)
  have he (a : α) : (|F a|^(2*j))^((k:ℝ)/j)=|F a|^(2*k) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _),←Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  have H := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ P.mass
    (fun a=>|F a|^(2*j)) (fun a _=>P.nonneg a) P.total (fun _ _=>by positivity) hp
  simp_rw [he] at H
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (P.expect_nonneg _ (fun _=>by positivity)) _) H
    (show 0≤1/(k:ℝ) by positivity)
  change (P.expect (fun a=>|F a|^(2*j))^((k:ℝ)/j))^(1/(k:ℝ)) ≤ _ at hr
  rw [←Real.rpow_mul (P.expect_nonneg _ (fun _=>by positivity))] at hr
  have he' : (k:ℝ)/j*(1/(k:ℝ))=1/(j:ℝ) := by field_simp
  rw [he'] at hr
  exact hr

end FiniteLaw

def OracleTracePair.restrict {q E V : ℝ} {x y : List Bool} {j k : ℕ}
    (C : OracleTracePair q x y k E V) (hj : 1≤j) (hjk : j≤k) :
    OracleTracePair q x y j E V := by
  let := C.finiteOutcome
  exact {C with moment := (C.first.evenMomentSq_mono_order C.score hj hjk).trans C.moment}

/-- Null-mass outcomes are assigned zero score. This proves, rather than
 assumes, the pointwise positivity needed by the finite simulation API. -/
def ConcreteLevelPair.oracle {q N Δ d ω F : ℝ} {hq : q∈Set.Icc 0 1} {i k : ℕ}
    (C : ConcreteLevelPair q hq N Δ d ω F i k) :
    OracleTracePair q C.left C.right k C.error (N^(-d)) := by
  let := C.finiteOutcome
  let Z := fun a=>if C.firstLaw.mass a=0 then 0 else C.score a
  have hden (a) : C.secondLaw.mass a=C.firstLaw.mass a*(1+Z a) := by
    dsimp [Z]
    split_ifs with h
    · simpa only [h,zero_mul] using C.density a
    · exact C.density a
  have hpos (a) : 0≤1+Z a := by
    by_cases h : C.firstLaw.mass a=0
    · simp [Z,h]
    · have hp : 0<C.firstLaw.mass a := lt_of_le_of_ne (C.firstLaw.nonneg a) (Ne.symm h)
      exact (mul_nonneg_iff_of_pos_left hp).mp (by rw [←hden]; exact C.secondLaw.nonneg a)
  have hc : C.firstLaw.expect Z=0 := by
    have hsum := congrArg (fun f : C.Outcome→ℝ=>∑a,f a) (funext hden)
    simp only [Finset.sum_add_distrib,mul_add,mul_one] at hsum
    rw [C.firstLaw.total,C.secondLaw.total] at hsum
    dsimp [FiniteLaw.expect]
    linarith only [hsum]
  have hm : C.firstLaw.evenMomentSq Z k=C.firstLaw.evenMomentSq C.score k := by
    unfold FiniteLaw.evenMomentSq FiniteLaw.expect
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [Z]
    split_ifs with h
    · simp only [h,zero_mul]
    · rfl
  exact {
    Outcome := C.Outcome
    finiteOutcome := C.finiteOutcome
    first := C.firstLaw
    second := C.secondLaw
    decode := C.decode
    first_simulation := C.first_simulation
    second_simulation := C.second_simulation
    score := Z
    density := hden
    likelihood_nonneg := hpos
    centered := hc
    moment := hm.le.trans C.score_bound
  }

theorem sourceScaleProduct_step_le (B D i : ℕ) (hB : 2≤B) (hi : i<D) :
    sourceScaleProduct B D i ≤ sourceScaleProduct B D (i+1) := by
  have he := sourceEpsilon_pos B D
  have hp : (1:ℝ)≤2^(sourceDimension B i) := one_le_pow₀ (by norm_num)
  have ha : scaleA (sourceDimension B i) 0 (sourceEpsilon B D)≤1 := by
    unfold scaleA
    norm_num only [pow_zero,mul_one]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^(sourceDimension B i))).mpr
      (le_mul_of_one_le_right (by linarith only [he] : 0≤1+sourceEpsilon B D) hp)
    linarith only [hh]
  have hs : 0 ≤ sourceScaleProduct B D (i+1) := (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D (i+1) hB)).le
  have hh := mul_le_mul_of_nonneg_right ha hs
  unfold sourceScaleProduct at *
  rw [Finset.prod_eq_prod_Ico_succ_bot hi]
  simpa only [one_mul] using hh

theorem sourceHalfMoment_step (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hi : i<D) (hn : 1<n) :
    sourceHalfMoment B D n (i+1) ≤ sourceHalfMoment B D n i := by
  have hlog : 0<Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_pos (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)) (Real.log_pos hn)
  have hlog' : Real.log (sourceTargetScale B D n i) ≤ Real.log (sourceTargetScale B D n (i+1)) := by
    rw [sourceTargetScale,sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n),Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_le_mul_of_nonneg_right (sourceScaleProduct_step_le B D i hB hi) (Real.log_pos hn).le
  unfold sourceHalfMoment
  apply Nat.ceil_mono
  have hd := (totalScoreExponent_bounds B D hB).1
  have hl := (Real.log_pos hn).le
  exact div_le_div_of_nonneg_left (by positivity) hlog hlog'

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceGapFloor (B : ℕ) : ℝ := 1/(128*(2:ℝ)^(2*B))

theorem sourceGapFloor_pos (B : ℕ) : 0<sourceGapFloor B := by unfold sourceGapFloor; positivity

theorem sourceGapFloor_le_one (B : ℕ) : sourceGapFloor B≤1 := by
  unfold sourceGapFloor
  apply (div_le_one (by positivity)).mpr
  have hh : (1:ℝ)≤2^(2*B) := one_le_pow₀ (by norm_num)
  linarith only [hh]

theorem sourceEpsilon_gap_small (B D : ℕ) : 1000*sourceEpsilon B D ≤ sourceGapFloor B := by
  have hp : (1000:ℝ)*128*2^(2*B) ≤ 2^(4*B+100) := by
    have hpow : (2:ℝ)^(2*B+17) ≤ 2^(4*B+100) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add] at hpow
    norm_num only [show (2:ℝ)^17=131072 by norm_num] at hpow
    have hpos : 0≤(2:ℝ)^(2*B) := by positivity
    linarith only [hpow,hpos]
  have hd : 1≤(D:ℝ)+1 := by linarith [Nat.cast_nonneg D (α:=ℝ)]
  have hh := mul_le_mul_of_nonneg_left hd (show 0≤(2:ℝ)^(4*B+100) by positivity)
  unfold sourceEpsilon sourceGapFloor
  rw [←mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hp,hh]

theorem sourceHalfMoment_strong (B D i : ℕ) {n : ℝ} (hB : 2≤B) (hn : 1<n) :
    (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n ≤
      (sourceHalfMoment B D n i:ℝ)*Real.log (sourceTargetScale B D n i) := by
  have hlog : 0<Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith only [hn] : 0<n)]
    exact mul_pos (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)) (Real.log_pos hn)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil _)

theorem source_clipping_power_delta (B D i : ℕ) {n gap : ℝ}
    (hB : 2≤B) (hn : 4≤n) (hg : sourceGapFloor B ≤ gap) :
    3*(sourceTargetScale B D n i)^(-gap*(sourceHalfMoment B D n i:ℝ)/4) ≤
      n^(-200*(totalScoreExponent B D+B+1)) := by
  let N := sourceTargetScale B D n i
  let A := totalScoreExponent B D+B+1
  let k := sourceHalfMoment B D n i
  have hn1 : 1<n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have hN : 0<N := Real.rpow_pos_of_pos hn0 _
  have hA : 1≤A := by dsimp [A]; linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hlogN : 0≤Real.log N := by
    dsimp [N]
    rw [sourceTargetScale,Real.log_rpow hn0]
    exact mul_nonneg (lt_of_lt_of_le (by positivity) (sourceScaleProduct_lower B D i hB)).le (Real.log_pos hn1).le
  have hk := sourceHalfMoment_strong B D i hB hn1
  change (10^8:ℝ)*2^(10*B)*A*Real.log n ≤ (k:ℝ)*Real.log N at hk
  have hp : (2:ℝ)^(2*B) ≤ 2^(10*B) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hc : 1000 ≤ sourceGapFloor B/4*((10^8:ℝ)*2^(10*B)) := by
    unfold sourceGapFloor
    calc
      (1000:ℝ) ≤ (10^8*2^(10*B))/(512*2^(2*B)) := by
        apply (le_div_iff₀ (by positivity : (0:ℝ)<512*2^(2*B))).mpr
        nlinarith only [hp,show (0:ℝ) ≤ 2^(2*B) by positivity]
      _ = _ := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ sourceGapFloor B/4 by positivity [sourceGapFloor_pos B])
  have hh' := mul_le_mul_of_nonneg_right hc (show 0≤A*Real.log n by positivity [Real.log_pos hn1])
  have hhg := mul_le_mul_of_nonneg_right hg (show 0≤(k:ℝ)*Real.log N/4 by positivity)
  have hdec : 1000*A*Real.log n ≤ gap*(k:ℝ)/4*Real.log N := by nlinarith only [hh,hh',hhg]
  have h3 : Real.log 3 ≤ A*Real.log n := by
    have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by linarith only [hn])
    exact hl.trans (le_mul_of_one_le_left (Real.log_pos hn1).le hA)
  rw [show (3:ℝ)=Real.exp (Real.log 3) by rw [Real.exp_log (by norm_num)],Real.rpow_def_of_pos hN,←Real.exp_add,
    Real.rpow_def_of_pos hn0]
  exact Real.exp_le_exp.mpr (by nlinarith only [hdec,h3,mul_nonneg (by linarith only [hA] : 0≤A) (Real.log_pos hn1).le])

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceWorkSize (B D : ℕ) : ℝ :=
  totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10

theorem sourceWorkSize_pos (B D : ℕ) (hB : 2≤ B) : 0< sourceWorkSize B D := by
  unfold sourceWorkSize
  have hd := (totalScoreExponent_bounds B D hB).1
  have hr := Nat.cast_nonneg (sourceDegreeCutoff B) (α:=ℝ)
  have hb := Nat.cast_nonneg B (α:=ℝ)
  linarith only [hd,hr,hb]

theorem sourceCancellationOrder_lower (B D : ℕ) :
    100*sourceWorkSize B D ≤ (sourceCancellationOrder B D:ℝ)*sourceEpsilon B D := by
  exact (div_le_iff₀ (sourceEpsilon_pos B D)).mp (Nat.le_ceil _)

theorem source_smoothing_absorb {B D : ℕ} {N K ω : ℝ} {m : ℕ}
    (hB : 2≤ B) (hN : 1≤ N) (hK : 0≤ K)
    (hm : hiddenBinomialCap m ω ≤ K*N^(-sourceEpsilon B D/2))
    (hpref : sourceSmoothingPrefactor (sourceCancellationOrder B D) K ≤ N^(sourceEpsilon B D)) :
    hiddenSmoothingBound m (sourceCancellationOrder B D) ω ≤ N^(-20*sourceWorkSize B D) := by
  have hN0 : 0< N := by linarith only [hN]
  apply (hiddenSmoothingBound_scale hN0 hK hm).trans
  apply (mul_le_mul_of_nonneg_right hpref (by positivity)).trans
  rw [←Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hs := sourceCancellationOrder_lower B D
  have hw := sourceWorkSize_pos B D hB
  have he := sourceEpsilon_pos B D
  have he' : sourceEpsilon B D ≤ 1 := by
    simpa only [pow_zero,one_mul] using sourceEpsilon_power_small B D 0 (by omega)
  have hW : 10≤ sourceWorkSize B D := by
    unfold sourceWorkSize
    have hd := (totalScoreExponent_bounds B D hB).1
    have hr := Nat.cast_nonneg (sourceDegreeCutoff B) (α:=ℝ)
    have hb := Nat.cast_nonneg B (α:=ℝ)
    linarith only [hd,hr,hb]
  nlinarith only [hs,he,he',hW]

/-- The actual sparse count controls both extra forced roles and clipping. -/
theorem sparse_power_absorb {N ε gap W L x : ℝ}
    (hN : 1≤ N) (he : 0≤ε) (hg : 2*ε≤ gap) (hW : 0≤ W) (hL : 1≤ L)
    (hx : x≤ W*L*N^(-gap)) (hfac : 8*W*L^2≤ N^ε) :
    x≤ N^(-gap/2)/8 ∧ x≤1/2 ∧ x*L≤1 := by
  have hN0 : 0< N := by linarith only [hN]
  have hL0 : 0≤ L := by linarith only [hL]
  have hg0 : 0≤ gap := by linarith only [he,hg]
  have hwl : 8*W*L≤ N^ε := by
    have hh : L≤ L^2 := by nlinarith only [hL,sq_nonneg (L-1)]
    exact (mul_le_mul_of_nonneg_left hh (by positivity : 0≤8*W)).trans hfac
  have hx' : x≤ N^(ε-gap)/8 := by
    have hh := mul_le_mul_of_nonneg_right hwl (Real.rpow_pos_of_pos hN0 (-gap)).le
    rw [←Real.rpow_add hN0] at hh
    have heq : ε+-gap=ε-gap := by ring
    rw [heq] at hh
    nlinarith only [hx,hh]
  have hsmall := Real.rpow_le_rpow_of_exponent_le hN (show ε-gap≤-gap/2 by linarith only [hg])
  have hxhalf : x≤ N^(-gap/2)/8 := hx'.trans (div_le_div_of_nonneg_right hsmall (by norm_num))
  have hone : N^(-gap/2)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith only [hg0])
  refine ⟨hxhalf,by linarith only [hxhalf,hone],?_⟩
  have hh := mul_le_mul_of_nonneg_right hfac (Real.rpow_pos_of_pos hN0 (-gap)).le
  rw [←Real.rpow_add hN0] at hh
  have hh' := mul_le_mul_of_nonneg_right hx hL0
  have hr := Real.rpow_le_one_of_one_le_of_nonpos hN (show ε+-gap≤0 by linarith only [hg,he])
  nlinarith only [hh,hh',hr]

theorem source_weight_square {N e d L : ℝ} {k : ℕ} (hN : 0< N)
    (hL : L=N^(-e*d/2)) :
    ((6*(2*k:ℕ):ℝ)*L)^2=144*(k:ℝ)^2*N^(-e*d) := by
  rw [hL,mul_pow]
  have hr : (N^(-e*d/2))^2=N^(-e*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [hr]
  push_cast
  ring

theorem source_high_tail_margin (B : ℕ) {d : ℝ} (_hB : 2≤ B) (hd : 0≤ d) :
    d+blockGain B+1 ≤ ((d+1)*sourceGapFloor B)/2*(sourceDegreeCutoff B:ℝ) := by
  have hp : (2:ℝ)^(2*B+8)*(B+2) ≤ 2^(10*B+40) := by
    have hb : (B:ℝ)+2 ≤ (2:ℝ)^(B+2) := by
      have hh : B+1 < 2^(B+1) := Nat.lt_two_pow_self
      have hh' : B+2≤2^(B+1) := by omega
      have hcast : (B:ℝ)+2≤(2:ℝ)^(B+1) := by exact_mod_cast hh'
      exact hcast.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤2^(2*B+8) by positivity)
    rw [←pow_add] at hh
    exact hh.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hc : (B:ℝ)+2 ≤ sourceGapFloor B/2*(sourceDegreeCutoff B:ℝ) := by
    unfold sourceGapFloor sourceDegreeCutoff
    push_cast
    calc
      (B:ℝ)+2 ≤ 2^(10*B+40)/(256*2^(2*B)) := by
        apply (le_div_iff₀ (by positivity : (0:ℝ)<256*2^(2*B))).mpr
        rw [pow_add] at hp
        norm_num only [show (2:ℝ)^8=256 by norm_num] at hp
        nlinarith only [hp]
      _ = _ := by field_simp; norm_num
  have hh := mul_le_mul_of_nonneg_left hc (show 0≤ d+1 by linarith only [hd])
  unfold blockGain
  have hb : (0:ℝ)≤ B := Nat.cast_nonneg _
  nlinarith only [hh,hd,hb,mul_nonneg hd hb]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem rpow_coefficient_absorb {N ε e d c : ℝ} (hN : 1≤ N)
    (hc : 3*c≤ N^ε) (he : ε+e≤ d) : c*N^e ≤ N^d/3 := by
  have hN0 : 0< N := by linarith only [hN]
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hN0 e).le
  rw [←Real.rpow_add hN0] at hh
  have hr := Real.rpow_le_rpow_of_exponent_le hN he
  linarith only [hh,hr]

/-- Closing the three explicit sharp classes, with the source's fixed
 finite degree cutoff and no hidden dependence on N in their constants. -/
theorem sharp_energy_absorb {N ε d M Fdec gap Cr Cf E : ℝ} {R : ℕ}
    (hN : 1≤ N) (he : ε≤1) (hM : d+(R:ℝ)+1≤ M) (hd : 0≤ d) (_hR : 0≤(R:ℝ))
    (hbad : 384*Cr≤ N^ε) (hforce : 192*Cf≤ N^ε) (htail : 1536≤ N^ε)
    (hfdec : d+ε≤ Fdec) (hgap : d+ε≤ gap*(R:ℝ))
    (hE : E ≤ Cr*N^R*((N^(-20*M))^2+(N^(-20*M))^2)+Cf*N^(-Fdec)+8*N^(-gap*(R:ℝ))) :
    64*E≤ N^(-d) := by
  have hN0 : 0< N := by linarith only [hN]
  have hpow : N^R*(N^(-20*M))^2=N^((R:ℝ)-40*M) := by
    rw [←Real.rpow_natCast (N^(-20*M)) 2,←Real.rpow_mul hN0.le,←Real.rpow_natCast N R,←Real.rpow_add hN0]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hb := rpow_coefficient_absorb hN (c:=128*Cr) (by nlinarith only [hbad])
    (e:=(R:ℝ)-40*M) (d:=-d) (by linarith only [hM,hd,he])
  have hf := rpow_coefficient_absorb hN (c:=64*Cf) (by nlinarith only [hforce])
    (e:=-Fdec) (d:=-d) (by linarith only [hfdec])
  have ht := rpow_coefficient_absorb hN (c:=512) (by norm_num at htail ⊢; exact htail)
    (e:=-gap*(R:ℝ)) (d:=-d) (by linarith only [hgap])
  have hh := mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ)≤64)
  have heq : 64*(Cr*N^R*((N^(-20*M))^2+(N^(-20*M))^2)+Cf*N^(-Fdec)+8*N^(-gap*(R:ℝ))) =
      128*Cr*N^((R:ℝ)-40*M)+64*Cf*N^(-Fdec)+512*N^(-gap*(R:ℝ)) := by
    calc
      _ = 128*Cr*(N^R*(N^(-20*M))^2)+64*Cf*N^(-Fdec)+512*N^(-gap*(R:ℝ)) := by ring
      _ = _ := by rw [hpow]
  rw [heq] at hh
  linarith only [hh,hb,hf,ht]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceDimension_bounds (B i : ℕ) (hB : 2≤ B) :
    2≤ sourceDimension B i ∧ sourceDimension B i≤ B := by
  unfold sourceDimension
  split_ifs <;> omega

theorem totalScoreExponent_mono (B : ℕ) (hB : 2≤ B) : Monotone (totalScoreExponent B) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [totalScoreExponent_step]
  exact le_add_of_nonneg_right (blockGain_pos _ (sourceDimension_bounds B i hB).1).le

theorem sourceTargetScale_bounds (B D i : ℕ) {n : ℝ} (hB : 2≤ B) (hn : 1≤ n) :
    1≤ sourceTargetScale B D n i ∧ sourceTargetScale B D n i≤ n := by
  have hp : 0≤ sourceScaleProduct B D i :=
    (show (0:ℝ)≤1/(2*2^(B*D)) by positivity).trans (sourceScaleProduct_lower B D i hB)
  refine ⟨Real.one_le_rpow hn hp,?_⟩
  simpa only [sourceTargetScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (sourceScaleProduct_le_one B D i hB)

theorem ConcreteLevelPair.error_le {q N Δ d ω F : ℝ} {hq : q∈Set.Icc 0 1} {i k : ℕ}
    (C : ConcreteLevelPair q hq N Δ d ω F i k) (hN : 0< N) (hΔ : 0≤Δ) :
    C.error≤((i:ℝ)+1)*Δ*N := by
  have hl : 0<(C.left.length:ℝ) := lt_of_lt_of_le (by linarith only [hN]) C.length_lower
  exact ((div_le_iff₀ hl).mp C.normalized_error).trans
    (mul_le_mul_of_nonneg_left C.length_upper (by positivity))

theorem source_warmup_score_margin (B D : ℕ) {d : ℝ} (hB : 2≤ B)
    (hd : 11/5≤ d) (hd' : d≤3+(B:ℝ)*D) :
    27/50≤ scaleA 2 0 (sourceEpsilon B D)*d ∧ scaleA 2 1 (sourceEpsilon B D)≤1/2 := by
  have he := sourceEpsilon_pos B D
  have hloss := sourceEpsilon_loss B D 2 d hB (by linarith only [hd]) hd'
  norm_num only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] at hloss
  have hlo := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower 2 (sourceEpsilon B D) he.le)
    (show 0≤ d by linarith only [hd])
  norm_num only [show (2:ℝ)^2=4 by norm_num] at hlo
  constructor
  · nlinarith only [hloss,hlo,hd,he]
  · have hh := scaleA_le_geometric 2 1 (sourceEpsilon B D) he.le (by omega)
    norm_num at hh ⊢
    exact hh

theorem source_main_score_margin (B D : ℕ) {d : ℝ} (hB : 2≤ B)
    (hd : (2:ℝ)^B+2≤ d) (hd' : d≤3+(B:ℝ)*D) :
    1+1/(2:ℝ)^B ≤ scaleA B 0 (sourceEpsilon B D)*d := by
  let X := (2:ℝ)^B
  let ε := sourceEpsilon B D
  have hX : 4≤ X := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hB
    norm_num at hh
    exact hh
  have hX0 : 0< X := by linarith only [hX]
  have he : 0<ε := sourceEpsilon_pos _ _
  have hd0 : 0≤ d := by dsimp [X] at hX; linarith only [hd,hX]
  have hloss := sourceEpsilon_loss B D B d le_rfl hd0 hd'
  change ((X-1)*d+3*B*(X/2))*ε<1/100 at hloss
  have hnonneg : 0≤3*(B:ℝ)*(X/2)*ε := by positivity
  have hde : 0≤ d*ε := mul_nonneg hd0 he.le
  have hmul : X*d*ε≤1/50 := by
    have hxx : 0≤(X-2)*(d*ε) := mul_nonneg (by linarith only [hX]) hde
    nlinarith only [hloss,hnonneg,hxx]
  have hlo := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower B ε he.le) hd0
  change (1/X-ε)*d≤ scaleA B 0 ε*d at hlo
  have hgoal : 1+1/X≤(1/X-ε)*d := by
    apply (mul_le_mul_iff_left₀ hX0).mp
    field_simp
    change X+2 ≤ d at hd
    nlinarith only [hd,hmul]
  exact hgoal.trans hlo

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceSparseCount_ge_one (T : ℕ→ℕ) (s b : ℕ) (hT : ∀j<b,1 ≤ T (j+1)) :
    1 ≤ sourceSparseCount T s b := by
  unfold sourceSparseCount
  apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by omega))
  exact Finset.one_le_prod (fun j hj=>hT j (Finset.mem_range.mp hj))

/-- Scalar closure of the exact sparse/forced block budget. All assumptions
 here are explicit elementary coefficient bounds, not oracle conclusions. -/
theorem source_block_energy_close (T n : ℕ→ℕ) (s b R : ℕ) (ω N ε d dnew K W M gap : ℝ)
    (hN : 1 ≤ N) (he : 0 ≤ ε) (he1 : ε ≤ 1) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hd : 0 ≤ dnew) (hM : dnew+(R:ℝ)+1 ≤ M) (hg : 2*ε ≤ gap)
    (hf : dnew+ε ≤ forcedDecay (b+1) ε d) (hR : dnew+ε ≤ gap/2*(R:ℝ))
    (hfac : 8*W*((2^s:ℕ):ℝ)^2 ≤ N^ε)
    (hbad : 384*sourceBadRoleFactor b R ≤ N^ε)
    (hforce : 192*(sourceForcedRoleFactor b R*W^(2^(b+1))*sourceSkeletonPrefactor s b K) ≤ N^ε)
    (htail : 1536 ≤ N^ε)
    (hleaf : (SourceLeafCount T (b+1):ℝ) ≤ N)
    (hcount : 1 ≤ sourceSparseCount T s b)
    (k : ℕ) (L : ℝ)
    (hw : ((6*(2*k:ℕ):ℝ)*L)^2 ≤ W*N^(-scaleA (b+1) 0 ε*d))
    (hsparse : ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s b:ℝ) ≤
      W*((2^s:ℕ):ℝ)*N^(-gap))
    (hn : ∀j ≤ b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hgcap : ∀j<b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s b:ℝ) ≤ N^(-gap/2)/8 ∧
    ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s b:ℝ) ≤ 1/2 ∧
    64*sourceSharpEnergyBudget T n s b R ω (N^(-20*M)) (N^(-20*M)) ((6*(2*k:ℕ):ℝ)*L) ≤ N^(-dnew) := by
  let w := (6*(2*k:ℕ):ℝ)*L
  have hmot : 1 ≤ ((2^s:ℕ):ℝ) := by exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ (2:ℕ)) : 1 ≤ (2:ℕ)^s)
  have hx := sparse_power_absorb hN he hg hW hmot hsparse hfac
  have hwone : w^2 ≤ 1 := by
    have hc : (1:ℝ) ≤ sourceSparseCount T s b := by exact_mod_cast hcount
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg w)
    dsimp [w] at hh
    nlinarith only [hh,hx.2.1]
  have hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1 := by
    dsimp [w]
    nlinarith only [hx.2.2]
  have hr : w^2*(sourceSparseCount T s b:ℝ) ≤ 1*N^(-(gap/2)) := by
    have hp : 0 ≤ N^(-gap/2) := Real.rpow_nonneg (by linarith only [hN]) _
    dsimp [w]
    rw [←neg_div]
    nlinarith only [hx.1,hp]
  have hnum := source_sharp_numeric T n s b R ω (N^(-20*M)) (N^(-20*M)) w N ε d K W 1 (gap/2)
    hN hK hW (by norm_num) hleaf hwone hw hsmall hx.2.1 hr hn hgcap
  simp only [one_pow,mul_one] at hnum
  refine ⟨hx.1,hx.2.1,?_⟩
  exact sharp_energy_absorb hN he1 hM hd (Nat.cast_nonneg _) hbad hforce htail hf hR hnum

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Instantiation at the manuscript's literal block dimension, integer
 schedules, source cutoff, moment envelope, and full next score exponent. -/
theorem source_level_energy (B D i ell h k : ℕ) (C N F ω K : ℝ)
    (hB : 2 ≤ B) (hi : i<D) (hN : 1 ≤ N) (hC : 1 ≤ C) (hF : 1 ≤ F) (hω : 0<ω)
    (H : SourceArithmeticBounds C N F (sourceEpsilon B D) (sourceCancellationOrder B D)
      (sourceDimension B i) ell h)
    (hk : (k:ℝ) ≤ sourceMomentEnvelope B D)
    (hK : 200*(C^(2*sourceDimension B i)*F)/ω ≤ K)
    (hfac : 8*sourceWeightEnvelope B D*((2^(sourceCancellationOrder B D):ℕ):ℝ)^2 ≤ N^(sourceEpsilon B D))
    (hbad : 384*sourceBadRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B) ≤ N^(sourceEpsilon B D))
    (hforce : 192*(sourceForcedRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B)*
        (sourceWeightEnvelope B D)^(2^(sourceDimension B i))*
        sourceSkeletonPrefactor (sourceCancellationOrder B D) (sourceDimension B i-1) K) ≤ N^(sourceEpsilon B D))
    (htail : 1536 ≤ N^(sourceEpsilon B D))
    (hsmooth : sourceSmoothingPrefactor (sourceCancellationOrder B D) K ≤ N^(sourceEpsilon B D)) :
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials C N b ε ell h
    let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤
        N^(-((totalScoreExponent B i+1)*sourceGapFloor B)/2)/8) ∧
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ 1/2) ∧
    (64*sourceSharpEnergyBudget T t s (b-1) (sourceDegreeCutoff B) ω
       (N^(-20*sourceWorkSize B D)) (N^(-20*sourceWorkSize B D)) ((6*(2*k:ℕ):ℝ)*L) ≤
       N^(-totalScoreExponent B (i+1))) ∧
    (∀j<b,hiddenSmoothingBound (t j) s ω ≤ N^(-20*sourceWorkSize B D)) := by
  let b := sourceDimension B i
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let d := totalScoreExponent B i
  let dnew := totalScoreExponent B (i+1)
  let W := sourceWeightEnvelope B D
  let gap := (d+1)*sourceGapFloor B
  let T := sourceBlockWindows N b ε
  let t := sourceArithmeticTrials C N b ε ell h
  let L := N^(-scaleA b 0 ε*d/2)
  have hb := sourceDimension_bounds B i hB
  have hb1 : b-1+1=b := by dsimp [b]; omega
  have he := sourceEpsilon_pos B D
  have he1 : ε ≤ 1/100 := by
    have hh := sourceEpsilon_gap_small B D
    have hg := sourceGapFloor_le_one B
    dsimp [ε]
    linarith only [hh,hg]
  have hd : 0 ≤ d := le_trans (by norm_num) (totalScoreExponent_bounds B i hB).1
  have hdnew : 0 ≤ dnew := le_trans (by norm_num) (totalScoreExponent_bounds B (i+1) hB).1
  have hdle : d ≤ totalScoreExponent B D := totalScoreExponent_mono B hB (Nat.le_of_lt hi)
  have hdnewle : dnew ≤ totalScoreExponent B D := totalScoreExponent_mono B hB (by omega)
  have hdd : d ≤ 3+(B:ℝ)*D := by
    have hh := (totalScoreExponent_bounds B D hB).2
    nlinarith only [hdle,hh]
  have hN0 : 0<N := by linarith only [hN]
  have hK0 : 0 ≤ K := le_trans (by positivity : 0 ≤ 200*(C^(2*sourceDimension B i)*F)/ω) hK
  have hW : 0 ≤ W := by dsimp [W,sourceWeightEnvelope]; exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hM : dnew+(sourceDegreeCutoff B:ℝ)+1 ≤ sourceWorkSize B D := by
    unfold sourceWorkSize
    linarith only [hdnewle,Nat.cast_nonneg B (α:=ℝ)]
  have hg : 2*ε ≤ gap := by
    have hf := sourceGapFloor_pos B
    have hh := sourceEpsilon_gap_small B D
    dsimp [gap,ε]
    nlinarith only [hh,hd,mul_nonneg hd hf.le,he]
  have hfdec : dnew+ε ≤ forcedDecay b ε d := by
    have hh := forcedDecay_margin B D b d (by dsimp [b]; omega) hb.2 hd hdd
    have heq : dnew=d+blockGain b := totalScoreExponent_step B i
    rw [heq]
    unfold blockGain
    linarith only [hh,he1]
  have hR : dnew+ε ≤ gap/2*(sourceDegreeCutoff B:ℝ) := by
    have hh := source_high_tail_margin B hB hd
    have heq : dnew=d+blockGain b := totalScoreExponent_step B i
    have hbg : blockGain b ≤ blockGain B := by unfold blockGain; exact (by
      have hcast : (b:ℝ) ≤ B := by exact_mod_cast hb.2
      linarith only [hcast])
    dsimp [gap]
    rw [heq]
    linarith only [hh,hbg,he1]
  have hw : ((6*(2*k:ℕ):ℝ)*L)^2 ≤ W*N^(-scaleA b 0 ε*d) := by
    rw [source_weight_square hN0 (show L=N^(-scaleA b 0 ε*d/2) from rfl)]
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2) (by norm_num : (0:ℝ)≤144)
    exact mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hN0 _).le
  have hsparse : ((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ W*((2^s:ℕ):ℝ)*N^(-gap) := by
    apply (source_sparse_weight_bound N ε d W _ b s hN0 hW hw).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hh := source_level_sparse_gap B D i hB
    have heq : (d+1)/(128*(2:ℝ)^(2*B))=gap := by dsimp [gap,sourceGapFloor]; ring
    rw [heq] at hh
    linarith only [hh]
  have hcaps := H.binomial_caps hN0 hC hF hω
  have hncap (j) (hj : j<b) : hiddenBinomialCap (t j) ω ≤ K*N^(-ε/2) :=
    (hcaps.1 j hj).trans (mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos hN0 _).le)
  have hgcap (j) (hj : j<b-1) : hiddenBinomialCap (sourceScheduledTrials T t (j+1)) ω ≤
      K*N^(-(scaleKappa b (j+2) ε+ε)/2) :=
    (hcaps.2 j (by omega)).trans (mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos hN0 _).le)
  have hc : 1 ≤ sourceSparseCount T s (b-1) := sourceSparseCount_ge_one T s (b-1)
    (fun j _=>Nat.succ_le_of_lt (H.window_positive (j+1)))
  have HE := source_block_energy_close T t s (b-1) (sourceDegreeCutoff B) ω N ε d dnew K W
    (sourceWorkSize B D) gap hN he.le (by linarith only [he1]) hK0 hW hdnew hM hg
    (by rw [hb1]; exact hfdec) hR hfac hbad (by rw [hb1]; exact hforce) htail
    (by rw [hb1]; exact H.leaf_bound hN0) hc k L (by rw [hb1]; exact hw) hsparse
    (fun j hj=>hncap j (by omega)) (fun j hj=>by rw [hb1]; exact hgcap j hj)
  refine ⟨HE.1,HE.2.1,HE.2.2,?_⟩
  intro j hj
  exact source_smoothing_absorb hB hN hK0 (hncap j hj) hsmooth

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

structure SourceNumericMargins (B D : ℕ) (q N : ℝ) : Prop where
  geometry : 1200*sourceCapEnvelope B D q ≤ N^(sourceEpsilon B D)
  motif : 48*(2:ℝ)^(sourceCancellationOrder B D) ≤ N^(sourceEpsilon B D)
  sparse : 8*sourceWeightEnvelope B D*((2:ℝ)^(sourceCancellationOrder B D))^2 ≤ N^(sourceEpsilon B D)
  smoothing : sourceSmoothingPrefactor (sourceCancellationOrder B D) (sourceCapEnvelope B D q) ≤ N^(sourceEpsilon B D)
  bad : ∀b ≤ B,384*sourceBadRoleFactor b (sourceDegreeCutoff B) ≤ N^(sourceEpsilon B D)
  force : ∀b ≤ B,192*(sourceForcedRoleFactor b (sourceDegreeCutoff B)*(sourceWeightEnvelope B D)^(2^(b+1))*
    sourceSkeletonPrefactor (sourceCancellationOrder B D) b (sourceCapEnvelope B D q)) ≤ N^(sourceEpsilon B D)
  tail : 1536 ≤ N^(sourceEpsilon B D)
  error : 64*(sourceCapEnvelope B D q+1)*((D:ℝ)+1) ≤ N^(sourceEpsilon B D)
  overlap : 1099511627776*(sourceCapEnvelope B D q+1)*(sourceWeightEnvelope B D+1)^2*
    ((2:ℝ)^(sourceCancellationOrder B D))^(B+2) ≤ N^(sourceEpsilon B D)

theorem sourceWeightEnvelope_nonneg (B D : ℕ) : 0 ≤ sourceWeightEnvelope B D := by
  unfold sourceWeightEnvelope
  exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem sourceForcedRoleFactor_nonneg (b R : ℕ) : 0 ≤ sourceForcedRoleFactor b R := by
  unfold sourceForcedRoleFactor
  exact Finset.sum_nonneg (fun _ _=>by positivity)

theorem source_forced_prefactor_expUpper (B b : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>192*(sourceForcedRoleFactor b (sourceDegreeCutoff B)*
      (sourceWeightEnvelope B D)^(2^(b+1))*
      sourceSkeletonPrefactor (sourceCancellationOrder B D) b (sourceCapEnvelope B D q))) := by
  have H := (((SourceExpUpper.const (sourceForcedRoleFactor b (sourceDegreeCutoff B))).mul
    ((sourceWeightEnvelope_expUpper B).pow (fun _ _ _=>sourceWeightEnvelope_nonneg _ _) (2^(b+1)))
    (fun _ _ _=>sourceForcedRoleFactor_nonneg _ _) (fun _ _ _=>pow_nonneg (sourceWeightEnvelope_nonneg _ _) _)).mul
      (sourceSkeletonPrefactor_expUpper B b hB)
      (fun _ _ _=>mul_nonneg (sourceForcedRoleFactor_nonneg _ _) (pow_nonneg (sourceWeightEnvelope_nonneg _ _) _))
      (fun D q hq=>sourceSkeletonPrefactor_nonneg _ _ (sourceCapEnvelope_pos B D hq.1).le))
  exact (SourceExpUpper.const 192).mul H (fun _ _ _=>by norm_num)
    (fun D q hq=>mul_nonneg (mul_nonneg (sourceForcedRoleFactor_nonneg _ _)
      (pow_nonneg (sourceWeightEnvelope_nonneg _ _) _))
        (sourceSkeletonPrefactor_nonneg _ _ (sourceCapEnvelope_pos B D hq.1).le))

theorem source_overlap_prefactor_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D q=>1099511627776*(sourceCapEnvelope B D q+1)*(sourceWeightEnvelope B D+1)^2*
      ((2:ℝ)^(sourceCancellationOrder B D))^(B+2)) := by
  have hK := (sourceCapEnvelope_expUpper B).add (SourceExpUpper.const 1)
  have hW := (sourceWeightEnvelope_expUpper B).add (SourceExpUpper.const 1)
  have hL := sourceMotif_expUpper B hB
  exact (((SourceExpUpper.const 1099511627776).mul hK (fun _ _ _=>by norm_num)
    (fun D q hq=>by linarith only [sourceCapEnvelope_pos B D hq.1])).mul
      (hW.pow (fun D _ _=>by linarith only [sourceWeightEnvelope_nonneg B D]) 2)
      (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>sq_nonneg _)).mul
        (hL.pow (fun _ _ _=>by positivity) (B+2))
        (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>by positivity)

theorem source_numeric_margins_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,SourceNumericMargins B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i) := by
  have hu (f : ℕ→ℝ→ℝ) (hf : SourceExpUpper f) :=
    SourceExpUpper.uniform f hf B ζ 1 hB hζ (by norm_num) hn hq hH
  have hgeom := hu _ ((SourceExpUpper.const 1200).mul (sourceCapEnvelope_expUpper B)
    (fun _ _ _=>by norm_num) (fun D q hq=>(sourceCapEnvelope_pos B D hq.1).le))
  have hmot := hu _ ((SourceExpUpper.const 48).mul (sourceMotif_expUpper B hB)
    (fun _ _ _=>by norm_num) (fun _ _ _=>by positivity))
  have hsparse := hu _ (((SourceExpUpper.const 8).mul (sourceWeightEnvelope_expUpper B)
    (fun _ _ _=>by norm_num) (fun _ _ _=>sourceWeightEnvelope_nonneg _ _)).mul
      ((sourceMotif_expUpper B hB).pow (fun _ _ _=>by positivity) 2)
      (fun _ _ _=>mul_nonneg (by norm_num) (sourceWeightEnvelope_nonneg _ _)) (fun _ _ _=>sq_nonneg _))
  have hsmooth := hu _ (sourceSmoothingPrefactor_expUpper B hB)
  have hbad : ∀ᶠt in atTop,∀b∈Finset.range (B+1),∀i,
      384*sourceBadRoleFactor b (sourceDegreeCutoff B) ≤
        (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
    apply (Filter.eventually_all_finset _).mpr
    intro b _
    simpa only [one_mul] using hu _ (SourceExpUpper.const (384*sourceBadRoleFactor b (sourceDegreeCutoff B)))
  have hforce : ∀ᶠt in atTop,∀b∈Finset.range (B+1),∀i,
      192*(sourceForcedRoleFactor b (sourceDegreeCutoff B)*
        (sourceWeightEnvelope B (sourceDepth B ζ ((q t)^3*Real.log (n t))))^(2^(b+1))*
        sourceSkeletonPrefactor (sourceCancellationOrder B (sourceDepth B ζ ((q t)^3*Real.log (n t))))
          b (sourceCapEnvelope B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t))) ≤
        (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
    apply (Filter.eventually_all_finset _).mpr
    intro b _
    simpa only [one_mul] using hu _ (source_forced_prefactor_expUpper B b hB)
  have htail := hu _ (SourceExpUpper.const 1536)
  have herr := hu _ (((SourceExpUpper.const 64).mul
    ((sourceCapEnvelope_expUpper B).add (SourceExpUpper.const 1))
    (fun _ _ _=>by norm_num) (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1])).mul
    SourcePolyUpper.depth.expUpper (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1])
      (fun _ _ _=>by positivity))
  have hov := hu _ (source_overlap_prefactor_expUpper B hB)
  filter_upwards [hgeom,hmot,hsparse,hsmooth,hbad,hforce,htail,herr,hov] with t hg hm hs hsm hb hf ht he ho
  intro i
  refine ⟨?_,?_,?_,?_,fun b h=>hb b (Finset.mem_range.mpr (by omega)) i,
    fun b h=>hf b (Finset.mem_range.mpr (by omega)) i,?_,?_,?_⟩ <;>
    first | simpa only [one_mul] using hg i | simpa only [one_mul] using hm i |
      simpa only [one_mul] using hs i | simpa only [one_mul] using hsm i |
      simpa only [one_mul] using ht i | simpa only [one_mul] using he i | simpa only [one_mul] using ho i

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_count_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      (sourceOverlapConstant q)^(2*B*(D+1)+2) := by
  rw [←pow_add]
  apply pow_le_pow_right₀ ((by norm_num : (1:ℝ)≤ 2).trans (sourceOverlapConstant_ge_two hq))
  have hh := Nat.mul_le_mul_left (2*B) hi
  nlinarith only [hh,hb]

theorem source_cap_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    200*((sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2))/initialOverlapLower q ≤
      sourceCapEnvelope B D q := by
  dsimp [sourceCapEnvelope]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (source_count_envelope B D i b hq hi hb)
    (by norm_num)) (inv_pos.mpr (initialOverlapLower_pos q)).le

theorem source_local_envelope (B D i b : ℕ) {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hi : i≤ D) (hb : b≤ B) :
    (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      sourceCapEnvelope B D q := by
  have hω := initialOverlapLower_lt_eighth hq.1
  have hω0 := initialOverlapLower_pos q
  have hG : 0 ≤ (sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) := by
    positivity [sourceOverlapConstant_pos hq.1]
  apply le_trans _ (source_cap_envelope B D i b hq hi hb)
  apply (le_div_iff₀ hω0).mpr
  nlinarith only [hω,hG,mul_nonneg hG (show 0 ≤ 200-initialOverlapLower q by linarith only [hω])]

theorem SourceArithmeticBounds.count_bound {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hC : 1≤ C) (hF : 0≤ F) (hN : 1≤ N)
    (hj : j≤ b) (ha : 0≤ scaleA b j ε) :
    ((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ) ≤
      (C^(2*b)*F+1)*N^(scaleA b j ε) := by
  have hc := (H.counts j hj).2
  have hc' : (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
      (C^(2*b)*F)*N^(scaleA b j ε) := by
    apply hc.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by omega)) hF)
      (H.lengths j hj).2 (by positivity) (by positivity)
  have ho := Real.one_le_rpow hN ha
  push_cast
  nlinarith only [hc',ho]

theorem sourceErrorUnit_small {B D : ℕ} {n : ℝ} (hB : 2≤ B) (hn : 4≤ n) :
    4*n^(-200*(totalScoreExponent B D+B+1)) ≤ n^(-100*(totalScoreExponent B D+B+1)) ∧
    4*n^(-200*(totalScoreExponent B D+B+1)) ≤ 1/2 := by
  let A := totalScoreExponent B D+B+1
  have hA : 1≤ A := by dsimp [A]; linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hn0 : 0<n := by linarith only [hn]
  have hn1 : 1≤ n := by linarith only [hn]
  have hpow : 4≤ n^(100*A) := hn.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (show 1≤ 100*A by linarith only [hA]))
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_pos_of_pos hn0 (-200*A)).le
  rw [←Real.rpow_add hn0] at hh
  have heq : 100*A+(-200*A)=-100*A := by ring
  rw [heq] at hh
  have hsmall : n^(-100*A) ≤ 1/2 := by
    have hh' := Real.rpow_le_rpow_of_exponent_le hn1 (show -100*A≤ (-1:ℝ) by linarith only [hA])
    rw [Real.rpow_neg_one] at hh'
    exact hh'.trans (by apply (inv_le_comm₀ hn0 (by norm_num)).mpr; norm_num; linarith only [hn])
  exact ⟨hh,hh.trans hsmall⟩

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceTailDenominator (B D : ℕ) (q : ℝ) : ℝ :=
  512+9600*sourceCapEnvelope B D q*(initialOverlapLower q)⁻¹^4

def sourceTailExponent (B D : ℕ) : ℝ :=
  300*(totalScoreExponent B D+B+1)+40*sourceWorkSize B D+5

theorem sourceTailDenominator_pos (B D : ℕ) {q : ℝ} (hq : 0<q) :
    0<sourceTailDenominator B D q := by
  unfold sourceTailDenominator
  positivity [sourceCapEnvelope_pos B D hq]

theorem sourceTailDenominator_expUpper (B : ℕ) : SourceExpUpper (sourceTailDenominator B) := by
  have H := ((SourceExpUpper.const 9600).mul (sourceCapEnvelope_expUpper B)
    (fun _ _ _=>by norm_num) (fun D q hq=>(sourceCapEnvelope_pos B D hq.1).le)).mul
      (initialOverlapLower_inverse_expUpper.pow (fun _ q _=>(inv_pos.mpr (initialOverlapLower_pos q)).le) 4)
      (fun D q hq=>by positivity [sourceCapEnvelope_pos B D hq.1]) (fun _ _ _=>by positivity)
  exact (SourceExpUpper.const 512).add H

theorem sourceWorkSize_poly (B : ℕ) (hB : 2 ≤ B) : SourcePolyUpper (sourceWorkSize B) := by
  exact (((totalScoreExponent_poly B hB).add (SourcePolyUpper.const (sourceDegreeCutoff B:ℝ))).add
    (SourcePolyUpper.const (B:ℝ))).add (SourcePolyUpper.const 10)

theorem sourceTailExponent_expUpper (B : ℕ) (hB : 2 ≤ B) :
    SourceExpUpper (fun D _=>sourceTailExponent B D) := by
  have ha := ((totalScoreExponent_poly B hB).add (SourcePolyUpper.const (B:ℝ))).add (SourcePolyUpper.const 1)
  have hu := (SourcePolyUpper.const 300).mul ha (fun _=>by norm_num)
    (fun D=>by linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)])
  have hw := (SourcePolyUpper.const 40).mul (sourceWorkSize_poly B hB) (fun _=>by norm_num)
    (fun D=>(sourceWorkSize_pos B D hB).le)
  exact ((hu.add hw).add (SourcePolyUpper.const 5)).expUpper

theorem source_tails_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i,2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) i)^
        (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t))))/
        sourceTailDenominator B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (q t)) ≤
      (n t)^(-sourceTailExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  apply (sourceTailDenominator_expUpper B).uniform_tail (SourceExpUpper.const (2*(B:ℝ)))
    (sourceTailExponent_expUpper B hB) (fun D q hq=>sourceTailDenominator_pos B D hq.1)
    (fun _ _ _=>by positivity) (fun D _ _=>?_) B ζ hB hζ hn hq hH
  unfold sourceTailExponent
  have ha : 0 ≤ totalScoreExponent B D+B+1 := by
    linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hw := (sourceWorkSize_pos B D hB).le
  linarith only [ha,hw]

/-- Turning the common uniform exponential bound into the two exact
 scheduled-error terms, including the division by the clipping threshold. -/
theorem source_exponential_error_budget {B D b s ell k : ℕ} {C N F ω f n : ℝ}
    (H : SourceArithmeticBounds C N F (sourceEpsilon B D) s b ell k)
    (hB : 2 ≤ B) (hb : b ≤ B) (hC : 0<C) (hF : 0<F) (hω : 0<ω)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n)
    (hf512 : 512 ≤ f) (hfmeta : 9600*(C^(2*b)*F)/ω^4 ≤ f)
    (htail : 2*(B:ℝ)*Real.exp (-(N^(sourceEpsilon B D)/f)) ≤ n^(-sourceTailExponent B D)) :
    sourceEffectiveHiddenTail (sourceBlockWindows N b (sourceEpsilon B D))
      (sourceArithmeticTrials C N b (sourceEpsilon B D) ell k) b ω ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail (sourceBlockWindows N b (sourceEpsilon B D))
      (sourceArithmeticTrials C N b (sourceEpsilon B D) ell k) b /
      N^(-20*sourceWorkSize B D) ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail (sourceBlockWindows N b (sourceEpsilon B D))
      (sourceArithmeticTrials C N b (sourceEpsilon B D) ell k) b ≤ n^(-200*(totalScoreExponent B D+B+1)) := by
  let A := totalScoreExponent B D+B+1
  let M := sourceWorkSize B D
  let ε := sourceEpsilon B D
  have hN0 : 0<N := by linarith only [hN]
  have hn0 : 0<n := by linarith only [hn]
  have hf0 : 0<f := by linarith only [hf512]
  have hA : 0 ≤ A := by dsimp [A]; linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  have hM : 0 ≤ M := (sourceWorkSize_pos B D hB).le
  have hexpfit : Real.exp (-(N^ε/512)) ≤ Real.exp (-(N^ε/f)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN0 ε).le (by norm_num) hf512)
  have hexpmeta : Real.exp (-(N^ε/(600*(C^(2*b)*F)))*ω^4/16) ≤ Real.exp (-(N^ε/f)) := by
    have hden : 0<9600*(C^(2*b)*F)/ω^4 := by positivity
    have hh := div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN0 ε).le hden hfmeta
    have heq : N^ε/(9600*(C^(2*b)*F)/ω^4)=N^ε/(600*(C^(2*b)*F))*ω^4/16 := by field_simp; ring
    rw [heq] at hh
    apply Real.exp_le_exp.mpr
    nlinarith only [hh]
  have hcommon : 2*(b:ℝ)*N*Real.exp (-(N^ε/f)) ≤ n^(1-sourceTailExponent B D) := by
    have hcast : (b:ℝ) ≤ B := by exact_mod_cast hb
    have hh := mul_le_mul_of_nonneg_left htail hn0.le
    have hcoeff : 2*(b:ℝ)*N ≤ n*(2*(B:ℝ)) := by
      have hh' := mul_le_mul hcast hNn (by linarith only [hN]) (Nat.cast_nonneg B (α:=ℝ))
      nlinarith only [hh']
    have hp := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (-(N^ε/f))).le
    have heq : n*(n^(-sourceTailExponent B D))=n^(1-sourceTailExponent B D) := by
      calc
        _ = n^(1:ℝ)*n^(-sourceTailExponent B D) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hn0]; rfl
    nlinarith only [hh,hp,heq]
  have hfit := H.fit_tail hC hF hN (sourceEpsilon_pos B D).le
    (fun v hv=>sourceKappa_three_epsilon B D b (v+1) hb (by omega) (by omega))
  have hm := H.metadata_tail (ω:=ω) hN0
  have hf' := hfit.trans ((mul_le_mul_of_nonneg_left hexpfit (by positivity : 0 ≤ 2*(b:ℝ)*N)).trans hcommon)
  have hm' := hm.trans ((mul_le_mul_of_nonneg_left hexpmeta (by positivity : 0 ≤ 2*(b:ℝ)*N)).trans hcommon)
  have hpow : n^(1-sourceTailExponent B D) ≤ n^(-200*A) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    dsimp [sourceTailExponent]
    dsimp [A,M] at *
    linarith only [hA,hM]
  refine ⟨hm'.trans hpow,?_,hf'.trans hpow⟩
  rw [div_eq_mul_inv,←Real.rpow_neg hN0.le]
  simp only [neg_mul,neg_neg]
  have hr : N^(20*M) ≤ n^(20*M) := Real.rpow_le_rpow hN0.le hNn (by positivity)
  apply (mul_le_mul hf' hr (Real.rpow_pos_of_pos hN0 _).le (Real.rpow_pos_of_pos hn0 _).le).trans
  rw [←Real.rpow_add hn0]
  apply Real.rpow_le_rpow_of_exponent_le hn
  dsimp [sourceTailExponent]
  dsimp [A,M] at *
  linarith only [hA,hM]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem rpow_constant_absorb {N ε e c M : ℝ} (hN : 1 ≤ N) (hM : 0<M)
    (hc : M*c ≤ N^ε) (he : ε+e ≤ 0) : c*N^e ≤ 1/M := by
  have hN0 : 0<N := by linarith only [hN]
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hN0 e).le
  rw [←Real.rpow_add hN0] at hh
  have hr := Real.rpow_le_rpow_of_exponent_le hN he
  rw [Real.rpow_zero] at hr
  apply (le_div_iff₀ hM).mpr
  nlinarith only [hh,hr]

theorem overlap_sqrt_budget {v e : ℝ} (hv : v ≤ 1/4096) (he : e ≤ 1/8) :
    Real.sqrt v+e ≤ 1/4 := by
  have hh : Real.sqrt v ≤ 1/64 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num at hv ⊢; exact hv)
  linarith only [hh,he]

/-- Generic dense-template estimate, used for the first warmup step and
 every step of a post-warmup block. -/
theorem source_dense_variance_budget {N ε e a K L V h : ℝ} {j : ℕ}
    (hN : 1 ≤ N) (_hK : 0 ≤ K) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hcount : h ≤ (K+1)*N^a) (hV : V ≤ N^(-e))
    (hc : 4096*(K+1)*L^j ≤ N^ε) (he : ε+a ≤ e) :
    h*(L^j*V) ≤ 1/4096 := by
  have hN0 : 0<N := by linarith only [hN]
  have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ h*L^j by positivity)
  have ht := mul_le_mul_of_nonneg_right hcount (show 0 ≤ L^j*N^(-e) by positivity)
  have heq : ((K+1)*N^a)*(L^j*N^(-e))=((K+1)*L^j)*N^(a-e) := by
    rw [sub_eq_add_neg,Real.rpow_add hN0]
    ring
  rw [heq] at ht
  have hb := rpow_constant_absorb hN (M:=4096) (by norm_num)
    (c:=(K+1)*L^j) (by nlinarith only [hc]) (e:=a-e) (by linarith only [he])
  nlinarith only [hv,ht,hb]

/-- Exact scalar one-window refinement. Its quadratic sparse term is what
 makes the second warmup overlap possible at old score exponent 11/5. -/
theorem source_warmup_variance_budget {N ε e M K W L w T h E : ℝ}
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hT : 0 ≤ T) (hh : 0 ≤ h) (hcount : h ≤ (K+1)*N)
    (hwindow : T ≤ N) (hw : w^2 ≤ W*N^(-e))
    (henergy : E ≤ 64*(72*T*w^2*(N^(-20*M))^2+8*(w^2*L)^2))
    (hbad : 8192*(4608*(K+1)*L*W) ≤ N^ε)
    (hquad : 8192*(512*(K+1)*W^2*L^3) ≤ N^ε)
    (hebad : ε+2-e-40*M ≤ 0) (hequad : ε+1-2*e ≤ 0) :
    h*(L*E) ≤ 1/4096 := by
  have hN0 : 0<N := by linarith only [hN]
  have ha : 0 ≤ N^(-20*M) := (Real.rpow_pos_of_pos hN0 _).le
  have hw0 : 0 ≤ W*N^(-e) := by positivity
  have hb0 : 0 ≤ 64*(72*T*w^2*(N^(-20*M))^2+8*(w^2*L)^2) := by positivity
  have H := (mul_le_mul_of_nonneg_left henergy (show 0 ≤ h*L by positivity)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hL) hb0)
  have ht := mul_le_mul hwindow hw (sq_nonneg _) hN0.le
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg w) hL) (mul_le_mul_of_nonneg_right hw hL) 2
  have hbd := mul_le_mul_of_nonneg_left ht (sq_nonneg (N^(-20*M)))
  have hm := mul_le_mul_of_nonneg_left (show 64*(72*T*w^2*(N^(-20*M))^2+8*(w^2*L)^2) ≤
      64*(72*(N*(W*N^(-e)))*(N^(-20*M))^2+8*((W*N^(-e))*L)^2) by nlinarith only [hbd,hs])
    (show 0 ≤ ((K+1)*N)*L by positivity)
  have hp1 : N*N^(-e)*(N^(-20*M))^2=N^(1-e-40*M) := by
    rw [←Real.rpow_natCast (N^(-20*M)) 2,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    nth_rw 1 [←Real.rpow_one N]
    rw [←Real.rpow_add hN0,←Real.rpow_add hN0]
    congr 1
    ring
  have hp2 : (N^(-e))^2=N^(-2*e) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hpow1 : N^((1:ℝ))*N^(1-e-40*M)=N^(2-e-40*M) := by rw [←Real.rpow_add hN0]; congr 1; ring
  have hpow2 : N^((1:ℝ))*N^(-2*e)=N^(1-2*e) := by rw [←Real.rpow_add hN0]; congr 1; ring
  rw [Real.rpow_one] at hpow1 hpow2
  have heq : (((K+1)*N)*L)*(64*(72*(N*(W*N^(-e)))*(N^(-20*M))^2+8*((W*N^(-e))*L)^2))=
      (4608*(K+1)*L*W)*N^(2-e-40*M)+(512*(K+1)*W^2*L^3)*N^(1-2*e) := by
    calc
      _ = (4608*(K+1)*L*W)*N*(N*N^(-e)*(N^(-20*M))^2)+
        (512*(K+1)*W^2*L^3)*N*(N^(-e))^2 := by ring
      _ = _ := by rw [hp1,hp2,mul_assoc _ N _,hpow1,mul_assoc _ N _,hpow2]
  rw [heq] at hm
  have hb := rpow_constant_absorb hN (M:=8192) (by norm_num) hbad (e:=2-e-40*M) (by linarith only [hebad])
  have hq := rpow_constant_absorb hN (M:=8192) (by norm_num) hquad (e:=1-2*e) (by linarith only [hequad])
  nlinarith only [H,hm,hb,hq]

theorem sourceBlockLength_factor (P : ℕ→ℕ) (ell j : ℕ) :
    sourceBlockLength P ell j=ell*sourceBlockLength P 1 j := by
  induction j with
  | zero => simp only [sourceBlockLength,mul_one]
  | succ j ih => rw [sourceBlockLength,sourceBlockLength,ih]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_delta_power_budget {B D : ℕ} {n N ε : ℝ} (hB : 2 ≤ B)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    n^(-100*(totalScoreExponent B D+B+1))*N^(2+ε) ≤ 1 := by
  have hn0 : 0<n := by linarith only [hn]
  have hN0 : 0<N := by linarith only [hN]
  have hA : 1 ≤ totalScoreExponent B D+B+1 := by
    linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg B (α:=ℝ)]
  apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0.le hNn (by linarith only [he]))
    (Real.rpow_pos_of_pos hn0 (-100*(totalScoreExponent B D+B+1))).le).trans
  rw [←Real.rpow_add hn0]
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn
    (show -100*(totalScoreExponent B D+B+1)+(2+ε) ≤ 0 by linarith only [hA,he1])

/-- Uniform repeated old simulation error; this is the error term in every
 dense nested-overlap estimate. -/
theorem source_repeated_error_budget {n N ε K E t h : ℝ} {B D : ℕ}
    (hB : 2 ≤ B) (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n)
    (he : 0 ≤ ε) (he1 : ε ≤ 1) (hh : 0 ≤ h) (_hK : 0 ≤ K)
    (hcount : h ≤ (K+1)*N)
    (hcost : t*E ≤ ((D:ℝ)+1)*n^(-100*(totalScoreExponent B D+B+1))*N)
    (hmargin : 64*(K+1)*((D:ℝ)+1) ≤ N^ε) : 2*h*(t*E) ≤ 1/32 := by
  let Δ := n^(-100*(totalScoreExponent B D+B+1))
  have hn0 : 0<n := by linarith only [hn]
  have hΔ : 0 ≤ Δ := (Real.rpow_pos_of_pos hn0 _).le
  have hc := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 2*h by positivity)
  have ht := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 2*((D:ℝ)+1)*Δ*N by positivity)
  have hm := mul_le_mul_of_nonneg_right hmargin (show 0 ≤ Δ*N^2 by positivity)
  have hp := source_delta_power_budget (D:=D) hB hn hN hNn he he1
  have hl : N^ε*N^2=N^(2+ε) := by
    rw [←Real.rpow_natCast,←Real.rpow_add (by linarith only [hN] : 0<N)]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hm' : 64*(K+1)*((D:ℝ)+1)*Δ*N^2 ≤ Δ*N^(2+ε) := by
    calc
      _ = (64*(K+1)*((D:ℝ)+1))*(Δ*N^2) := by ring
      _ ≤ N^ε*(Δ*N^2) := hm
      _ = _ := by rw [show N^ε*(Δ*N^2)=Δ*(N^ε*N^2) by ring,hl]
  change Δ*N^(2+ε) ≤ 1 at hp
  nlinarith only [hc,ht,hm',hp]

theorem source_old_error_cost {C N F ε E Δ : ℝ} {s b ell k j i D : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 1 ≤ N)
    (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hΔ : 0 ≤ Δ) (hi : i ≤ D) (hj : j ≤ b)
    (ha : scaleA b j ε ≤ 1) :
    (sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j:ℝ)*E ≤
      ((D:ℝ)+1)*Δ*N := by
  let t := sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j
  have hh := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg t (α:=ℝ))
  have hl : (ell:ℝ)*t ≤ N := by
    have hl' := (H.lengths j hj).2
    rw [sourceArithmeticLength_eq_block,sourceBlockLength_factor] at hl'
    push_cast at hl'
    exact hl'.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN ha)
  have hi' : (i:ℝ) ≤ D := by exact_mod_cast hi
  have hh' := mul_le_mul_of_nonneg_left hl (show 0 ≤ ((D:ℝ)+1)*Δ by positivity)
  have hcoef := mul_le_mul_of_nonneg_right hi' (show 0 ≤ Δ*(ell:ℝ)*t by positivity)
  dsimp [t] at *
  nlinarith only [hh,hh',hcoef]

/-- The normalized error invariant propagates through actual leaf products,
 with one fresh delta paid by clipping and fitting. -/
theorem normalized_block_error {E Δ clip fit : ℝ} {ell newell leaves i : ℕ}
    (hell : 1 ≤ newell) (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hΔ : 0 ≤ Δ)
    (hleaf : leaves*ell ≤ newell) (hnew : clip+fit ≤ Δ) :
    (clip+(leaves:ℝ)*E+fit)/(newell:ℝ) ≤ ((i:ℝ)+2)*Δ := by
  have hl0 : (0:ℝ)<newell := by exact_mod_cast (show 0<newell by omega)
  apply (div_le_iff₀ hl0).mpr
  have hleaf' : (leaves:ℝ)*ell ≤ newell := by exact_mod_cast hleaf
  have h1 := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg leaves (α:=ℝ))
  have h2 := mul_le_mul_of_nonneg_left hleaf' (show 0 ≤ ((i:ℝ)+1)*Δ by positivity)
  have h3 : Δ ≤ Δ*newell := le_mul_of_one_le_right hΔ (by exact_mod_cast hell)
  nlinarith only [h1,h2,h3,hnew]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- All three genuine clipping losses, and fitting, share the same global
 error unit. The reference power is the actual half-moment at this scale. -/
theorem source_level_clipping (B D j s b : ℕ) (T t : ℕ→ℕ) (n ω a gap L : ℝ)
    (hB : 2 ≤ B) (hn : 4 ≤ n) (hg : sourceGapFloor B ≤ gap)
    (hmeta : sourceEffectiveHiddenTail T t (b+1) ω ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hfit : sourceFitTail T t (b+1)/a ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hfit' : sourceFitTail T t (b+1) ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hhalf : ((6*(2*sourceHalfMoment B D n j:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hscale : ((6*(2*sourceHalfMoment B D n j:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤
      (sourceTargetScale B D n j)^(-gap/2)/8) :
    sourceClippingCost T t s b (sourceHalfMoment B D n j) ω a L ≤ 1/2 ∧
    sourceClippingCost T t s b (sourceHalfMoment B D n j) ω a L+sourceFitTail T t (b+1) ≤
      n^(-100*(totalScoreExponent B D+B+1)) := by
  have hN : 0<sourceTargetScale B D n j := Real.rpow_pos_of_pos (by linarith only [hn]) _
  have hc := (source_clipping_moment_power T s b (sourceHalfMoment B D n j)
    (sourceTargetScale B D n j) gap L hN hhalf hscale).trans (source_clipping_power_delta B D j hB hn hg)
  have hu := sourceErrorUnit_small (D:=D) hB hn
  have hunit : 0 ≤ n^(-200*(totalScoreExponent B D+B+1)) := (Real.rpow_pos_of_pos (by linarith only [hn]) _).le
  unfold sourceClippingCost
  constructor <;> linarith only [hmeta,hfit,hfit',hc,hu.1,hu.2,hunit]

/-- At one window the root metadata can still fail; only the fitting loss
 vanishes. We charge the root metadata rather than discard it. -/
theorem source_one_window_clipping (B D j s : ℕ) (T t : ℕ) (n ω a gap L : ℝ)
    (hB : 2 ≤ B) (hn : 4 ≤ n) (hg : sourceGapFloor B ≤ gap)
    (hmeta : sourceEffectiveHiddenTail (fun _=>T) (fun _=>t) 1 ω ≤ n^(-200*(totalScoreExponent B D+B+1)))
    (hhalf : ((6*(2*sourceHalfMoment B D n j:ℕ):ℝ)*L)^2*(2:ℝ)^s ≤ 1/2)
    (hscale : ((6*(2*sourceHalfMoment B D n j:ℕ):ℝ)*L)^2*(2:ℝ)^s ≤
      (sourceTargetScale B D n j)^(-gap/2)/8) :
    sourceClippingCost (fun _=>T) (fun _=>t) s 0 (sourceHalfMoment B D n j) ω a L ≤ 1/2 ∧
    sourceClippingCost (fun _=>T) (fun _=>t) s 0 (sourceHalfMoment B D n j) ω a L ≤
      n^(-100*(totalScoreExponent B D+B+1)) := by
  have hu : 0 ≤ n^(-200*(totalScoreExponent B D+B+1)) :=
    (Real.rpow_pos_of_pos (by linarith only [hn]) _).le
  simpa only [sourceFitTail,add_zero] using source_level_clipping B D j s 0
    (fun _=>T) (fun _=>t) n ω a gap L hB hn hg hmeta
    (by simpa only [sourceFitTail,zero_div] using hu) (by simpa only [sourceFitTail] using hu)
    (by simpa only [sourceSparseCount,Finset.range_zero,Finset.prod_empty,Nat.mul_one,Nat.cast_pow,Nat.cast_ofNat] using hhalf)
    (by simpa only [sourceSparseCount,Finset.range_zero,Finset.prod_empty,Nat.mul_one,Nat.cast_pow,Nat.cast_ofNat] using hscale)

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_overlap_prefactors {K W L X : ℝ} {B j : ℕ}
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hL : 1 ≤ L) (hB : 2 ≤ B) (hj : j ≤ B+2)
    (hX : 1099511627776*(K+1)*(W+1)^2*L^(B+2) ≤ X) :
    4096*(K+1)*L^j ≤ X ∧
    8192*(4608*(K+1)*L*W) ≤ X ∧
    8192*(512*(K+1)*W^2*L^3) ≤ X := by
  have hK1 : 0 ≤ K+1 := by linarith only [hK]
  have hw1 : 1 ≤ (W+1)^2 := by nlinarith only [hW,sq_nonneg W]
  have hww : W ≤ (W+1)^2 := by nlinarith only [hW,sq_nonneg W]
  have hw2 : W^2 ≤ (W+1)^2 := by nlinarith only [hW]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hjpow := pow_le_pow_right₀ hL hj
  have hlpow : L ≤ L^(B+2) := by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ B+2 by omega)
  have h3pow := pow_le_pow_right₀ hL (show 3 ≤ B+2 by omega)
  have hb0 : 0 ≤ (K+1)*(W+1)^2*L^(B+2) := by positivity
  have hfirst : (K+1)*L^j ≤ (K+1)*(W+1)^2*L^(B+2) := by
    have hp := mul_le_mul_of_nonneg_left hjpow hK1
    have hp' := mul_le_mul_of_nonneg_right hw1 (show 0 ≤ (K+1)*L^(B+2) by positivity)
    nlinarith only [hp,hp']
  have hsecond : (K+1)*L*W ≤ (K+1)*(W+1)^2*L^(B+2) := by
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul hlpow hww hW (by positivity)) hK1
    nlinarith only [hp]
  have hthird : (K+1)*W^2*L^3 ≤ (K+1)*(W+1)^2*L^(B+2) := by
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul hw2 h3pow (by positivity) (by positivity)) hK1
    nlinarith only [hp]
  constructor
  · nlinarith only [hfirst,hX,hb0]
  constructor <;> nlinarith only [hsecond,hthird,hX,hb0]

/-- Complete dense-overlap numerical criterion for the literal schedules,
 including the error carried by the old exact simulator. -/
theorem source_literal_dense_overlap {C N F ε E Δ V K W L n e : ℝ}
    {s b ell k j i D B : ℕ} (H : SourceArithmeticBounds C N F ε s b ell k)
    (hB : 2 ≤ B) (hb : b ≤ B) (hC : 1 ≤ C) (hF : 0 ≤ F)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (he : 0 ≤ ε) (he1 : ε ≤ 1)
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hL : 1 ≤ L) (hLdef : L=(2:ℝ)^s)
    (hG : C^(2*b)*F ≤ K) (hi : i ≤ D) (hj : j ≤ b)
    (ha : 0 ≤ scaleA b j ε) (ha1 : scaleA b j ε ≤ 1)
    (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hΔ : Δ=n^(-100*(totalScoreExponent B D+B+1)))
    (hV : V ≤ N^(-e)) (hgap : ε+scaleA b j ε ≤ e)
    (hmargin : 64*(K+1)*((D:ℝ)+1) ≤ N^ε)
    (hoverlap : 1099511627776*(K+1)*(W+1)^2*L^(B+2) ≤ N^ε) :
    Real.sqrt (((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ)*
      (((2^s:ℕ):ℝ)^j*V))+
      2*((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ)*
      ((sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j:ℝ)*E) ≤ 1/4 := by
  let h := ((sourceArithmeticCount C N b ε ell k j+1:ℕ):ℝ)
  have hn0 : 0<n := by linarith only [hn]
  have hN0 : 0<N := by linarith only [hN]
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  have hc : h ≤ (K+1)*N^(scaleA b j ε) := by
    exact (H.count_bound hC hF hN hj ha).trans
      (mul_le_mul_of_nonneg_right (add_le_add hG le_rfl) (Real.rpow_pos_of_pos hN0 _).le)
  have hc' : h ≤ (K+1)*N := hc.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN ha1)
    (by linarith only [hK]))
  have hpref := (source_overlap_prefactors hK hW hL hB (show j ≤ B+2 by omega) hoverlap).1
  have hv := source_dense_variance_budget hN hK (show 0 ≤ L by linarith only [hL]) hh0 hc hV hpref hgap
  have hcost := source_old_error_cost H hN hE (by rw [hΔ]; exact (Real.rpow_pos_of_pos hn0 _).le) hi hj ha1
  rw [hΔ] at hcost
  have herr := source_repeated_error_budget hB hn hN hNn he he1 hh0 hK hc' hcost hmargin
  have hres := overlap_sqrt_budget hv (show 2*h*((sourceBlockLength (sourceArithmeticP C N b ε ell k) 1 j:ℝ)*E) ≤ 1/8 by linarith only [herr])
  simpa only [hLdef,Nat.cast_pow,Nat.cast_ofNat] using hres

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SourceArithmeticBounds.length_positive {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) (hj : j ≤ b) :
    1 ≤ sourceArithmeticLength C N b ε ell k j := by
  have hp : (0:ℝ)<sourceArithmeticLength C N b ε ell k j :=
    (show 0<N^(scaleA b j ε)/2 by positivity).trans_le (H.lengths j hj).1
  have hh : 0<sourceArithmeticLength C N b ε ell k j := by exact_mod_cast hp
  omega

theorem SourceArithmeticBounds.copies_le_target {C N F ε : ℝ} {s b ell k j : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 1 ≤ N) (hj : j<b)
    (ha : scaleA b (j+1) ε ≤ 1) : (sourceArithmeticP C N b ε ell k j:ℝ) ≤ N := by
  have hL := H.length_positive (by linarith only [hN]) (j:=j) (by omega)
  have hp : sourceArithmeticP C N b ε ell k j ≤ sourceArithmeticLength C N b ε ell k (j+1) := by
    rw [sourceArithmeticLength_step]
    simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right (sourceArithmeticP C N b ε ell k j) hL
  exact (show (sourceArithmeticP C N b ε ell k j:ℝ) ≤ sourceArithmeticLength C N b ε ell k (j+1) by exact_mod_cast hp).trans
    ((H.lengths (j+1) (by omega)).2.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN ha))

/-- Both contributions to the error in the second warmup overlap are paid
 by the common delta margin. The old term uses T₀ ≤ P₀, not an independent
 full-block overlap hypothesis. -/
theorem source_warmup_error_budget {C N F ε E Δ clip K n : ℝ} {s ell k i D B : ℕ}
    (H : SourceArithmeticBounds C N F ε s 2 ell k)
    (hB : 2 ≤ B) (hC : 1 ≤ C) (hF : 0 ≤ F) (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n)
    (he : 0 ≤ ε) (he1 : ε ≤ 1) (hK : 0 ≤ K) (hG : C^4*F ≤ K) (hi : i ≤ D)
    (hE : E ≤ ((i:ℝ)+1)*Δ*ell) (hE0 : 0 ≤ E) (hΔ : Δ=n^(-100*(totalScoreExponent B D+B+1)))
    (hclip : clip ≤ Δ) (hmargin : 64*(K+1)*((D:ℝ)+1) ≤ N^ε) :
    2*((sourceArithmeticCount C N 2 ε ell k 2+1:ℕ):ℝ)*
      ((sourceArithmeticP C N 2 ε ell k 1:ℝ)*
        (clip+(sourceBlockWindows N 2 ε 0:ℝ)*E)) ≤ 1/8 := by
  let P := sourceArithmeticP C N 2 ε ell k
  let T := sourceBlockWindows N 2 ε
  let h := ((sourceArithmeticCount C N 2 ε ell k 2+1:ℕ):ℝ)
  have hn0 : 0<n := by linarith only [hn]
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; exact (Real.rpow_pos_of_pos hn0 _).le
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  have hc : h ≤ (K+1)*N := by
    have hh := H.count_bound hC hF hN (j:=2) le_rfl (by rw [scaleA_top]; norm_num)
    simpa only [scaleA_top,Real.rpow_one] using hh.trans
      (mul_le_mul_of_nonneg_right (by simpa only [show (2:ℕ)*2=4 by rfl] using add_le_add hG (show (1:ℝ) ≤ 1 from le_rfl)) (Real.rpow_pos_of_pos (by linarith only [hN]) _).le)
  have hcost := source_old_error_cost H hN hE hΔ0 hi (j:=2) le_rfl (by rw [scaleA_top])
  rw [hΔ] at hcost
  have herr := source_repeated_error_budget hB hn hN hNn he he1 hh0 hK hc hcost hmargin
  have hp1 : (P 1:ℝ) ≤ N := H.copies_le_target hN (by omega) (by rw [show (1:ℕ)+1=2 by rfl,scaleA_top])
  have hclipcost : (P 1:ℝ)*clip ≤ ((D:ℝ)+1)*Δ*N := by
    have h1 := mul_le_mul_of_nonneg_left hclip (Nat.cast_nonneg (P 1) (α:=ℝ))
    have h2 := mul_le_mul_of_nonneg_right hp1 hΔ0
    have h3 := le_mul_of_one_le_left (show 0 ≤ Δ*N by positivity) (show (1:ℝ) ≤ D+1 by linarith only [Nat.cast_nonneg D (α:=ℝ)])
    nlinarith only [h1,h2,h3]
  rw [hΔ] at hclipcost
  have hcliperr := source_repeated_error_budget hB hn hN hNn he he1 hh0 hK hc hclipcost hmargin
  have hT : (T 0:ℝ) ≤ P 0 := by
    exact_mod_cast (show T 0 ≤ P 0 from (by have h := (H.windows 0 (by omega)).2.2.1; change 2*T 0 ≤ P 0 at h; omega))
  have hold := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hE0)
    (show 0 ≤ 2*h*(P 1:ℝ) by positivity)
  have hfactor : (sourceBlockLength P 1 2:ℝ)=(P 1:ℝ)*(P 0:ℝ) := by
    simp only [sourceBlockLength,Nat.cast_mul,mul_one]
  change 2*h*((sourceBlockLength P 1 2:ℝ)*E) ≤ 1/32 at herr
  rw [hfactor] at herr
  nlinarith only [herr,hcliperr,hold]

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
