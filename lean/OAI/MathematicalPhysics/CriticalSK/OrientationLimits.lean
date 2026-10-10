import OAI.MathematicalPhysics.CriticalSK.OrientationBounds

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK


lemma naturalEdgeScale_le_rpow (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    naturalEdgeScale n L ≤ L*(n+1:ℝ)^(-2/3:ℝ) := by
  have hd := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  have hp := Real.rpow_le_rpow hN.le (edgeLength_cube n).1 (by norm_num : (0:ℝ) ≤ 2/3)
  have he : ((edgeLength n:ℝ)^3)^(2/3:ℝ) = (edgeLength n:ℝ)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    norm_num
  rw [he] at hp
  have hi := inv_anti₀ (Real.rpow_pos_of_pos hN (2/3:ℝ)) hp
  have ht := mul_le_mul_of_nonneg_left hi hL
  rw [show (-2/3:ℝ) = -(2/3) by ring,Real.rpow_neg hN.le]
  simpa only [naturalEdgeScale,div_eq_mul_inv] using ht

lemma naturalEdgeScale_cutoff_tendsto (L : ℝ) :
    Tendsto (fun n : ℕ => 216*L*(n+1:ℝ)^(-1/12:ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  simpa only [mul_zero,neg_div,Function.comp_def] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/12)).comp hn).const_mul (216*L)

lemma naturalEdgeScale_cutoff_eventually {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, 216*naturalEdgeScale n L ≤ overlapCentralCutoff (n+1)^2 := by
  filter_upwards [(naturalEdgeScale_cutoff_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
  have hN : (0:ℝ) < n+1 := by positivity
  have hid : overlapCentralCutoff (n+1)^2 = (n+1:ℝ)^(-7/12:ℝ) := by
    unfold overlapCentralCutoff
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    norm_num
  have he : (216*L*(n+1:ℝ)^(-1/12:ℝ))*(n+1:ℝ)^(-7/12:ℝ) =
      216*(L*(n+1:ℝ)^(-2/3:ℝ)) := by
    rw [mul_assoc (216*L),← Real.rpow_add hN]
    norm_num
    ring
  rw [hid]
  calc
    _ ≤ 216*(L*(n+1:ℝ)^(-2/3:ℝ)) := mul_le_mul_of_nonneg_left (naturalEdgeScale_le_rpow n hL) (by norm_num)
    _ = _ := he.symm
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg hN.le _) hn.le

lemma cutoff_cubic_identity {x : ℝ} (hx : 0 < x) :
    x*(x^(-(7/24:ℝ)))^3 = x^(1/8:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  conv_lhs => lhs; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  norm_num

lemma rpow_exp_small_tendsto (p : ℝ) :
    Tendsto (fun n : ℕ => (n+1:ℝ)^p*Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hx := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp hn
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (8*p) (1/24) (by norm_num)).comp hx
  apply hh.congr
  intro n
  change ((n+1:ℝ)^(1/8:ℝ))^(8*p)*_ = _
  rw [← Real.rpow_mul (by positivity)]
  congr 2
  ring

lemma edgeLength_sq_le_linear (n : ℕ) : (edgeLength n:ℝ)^2 ≤ 8*(n+1) := by
  have hd : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hcube := (edgeLength_cube n).2
  have hh : (edgeLength n:ℝ)^2 ≤ (edgeLength n:ℝ)^3 := by nlinarith [sq_nonneg ((edgeLength n:ℝ)-1)]
  exact hh.trans hcube

def naturalPartitionConstant (n : ℕ) (L : ℝ) : ℝ :=
  (naturalEdgeScale n L/4)*Real.exp (-6*(L*Real.sqrt L))

def naturalPartitionBase (L : ℝ) : ℝ := (L/32)*Real.exp (-6*(L*Real.sqrt L))

lemma naturalPartitionBase_pos {L : ℝ} (hL : 0 < L) : 0 < naturalPartitionBase L := by
  unfold naturalPartitionBase
  positivity

lemma naturalPartitionConstant_lower (n : ℕ) {L : ℝ} (hL : 0 < L) :
    naturalPartitionBase L/(n+1) ≤ naturalPartitionConstant n L := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hd := edgeLength_cast_pos n
  have hh := div_le_div_of_nonneg_left hL.le (pow_pos hd 2) (edgeLength_sq_le_linear n)
  have ht := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 4))
    (Real.exp_pos (-6*(L*Real.sqrt L))).le
  unfold naturalPartitionBase naturalPartitionConstant naturalEdgeScale
  calc
    _ = L/(8*(n+1))/4*Real.exp (-6*(L*Real.sqrt L)) := by
      field_simp
      ring
    _ ≤ _ := ht

lemma naturalPartitionConstant_pos (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < naturalPartitionConstant n L :=
  (div_pos (naturalPartitionBase_pos hL) (by positivity)).trans_le (naturalPartitionConstant_lower n hL)

def naturalOrientationTail (n : ℕ) (L : ℝ) : ℝ :=
  (n+2:ℝ)*((26*Real.exp 1*(n+1)/naturalPartitionConstant n L)^2*
    Real.exp (-(n+1:ℝ)/24*overlapCentralCutoff (n+1)^3))

lemma naturalOrientationTail_bound (n : ℕ) {L : ℝ} (hL : 0 < L) :
    naturalOrientationTail n L ≤ 2*(26*Real.exp 1/naturalPartitionBase L)^2*(n+1:ℝ)^5*
      Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ)) := by
  have hN : (0:ℝ) < n+1 := by positivity
  have hK := naturalPartitionConstant_pos n hL
  have hB := naturalPartitionBase_pos hL
  have he : -(n+1:ℝ)/24*overlapCentralCutoff (n+1)^3 = -(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ) := by
    have hi := cutoff_cubic_identity hN
    unfold overlapCentralCutoff
    push_cast
    linear_combination -(1/24:ℝ)*hi
  have hratio : 26*Real.exp 1*(n+1)/naturalPartitionConstant n L ≤
      (26*Real.exp 1/naturalPartitionBase L)*(n+1)^2 := by
    apply (div_le_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left (naturalPartitionConstant_lower n hL)
      (show 0 ≤ (26*Real.exp 1/naturalPartitionBase L)*(n+1:ℝ)^2 by positivity)
    apply le_trans _ hh
    apply le_of_eq
    field_simp
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 26*Real.exp 1*(n+1:ℝ)/naturalPartitionConstant n L) hratio 2
  have hfac : (n+2:ℝ) ≤ 2*(n+1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold naturalOrientationTail
  rw [he]
  have hh := mul_le_mul hfac (mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))).le)
    (by positivity) (by positivity : (0:ℝ) ≤ 2*(n+1))
  apply hh.trans_eq
  ring

lemma naturalOrientationTail_scaled_tendsto {L : ℝ} (hL : 0 < L) (p : ℝ) :
    Tendsto (fun n : ℕ => (n+1:ℝ)^p*naturalOrientationTail n L) atTop (𝓝 0) := by
  have ht := (rpow_exp_small_tendsto (p+5)).const_mul (2*(26*Real.exp 1/naturalPartitionBase L)^2)
  have hz : Tendsto (fun n : ℕ => (n+1:ℝ)^p*
      (2*(26*Real.exp 1/naturalPartitionBase L)^2*(n+1:ℝ)^5*Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.congr (fun n => by
      rw [Real.rpow_add (by positivity),show (5:ℝ) = (5:ℕ) by norm_num, Real.rpow_natCast]
      ring)
  apply squeeze_zero (fun n => by unfold naturalOrientationTail; positivity) (fun n =>
    mul_le_mul_of_nonneg_left (naturalOrientationTail_bound n hL) (Real.rpow_nonneg (by positivity) _)) hz

open Set MeasureTheory Filter

structure OrientationInputs {n : ℕ} [Nonempty (Fin n)]
    (lam : Fin n → ℝ) (K s : ℝ) : Prop where
  bounded : ∀ i, |lam i| ≤ 3
  Kpos : 0 < K
  partitionLower : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)
  scaleNonneg : 0 ≤ s
  topUpper : spectralTop lam < 2+s
  topLower : 2-s ≤ spectralTop lam
  trace : spectralStieltjes lam (2+s) ≤ 1
  traceUniform : ∀ t ∈ Icc s 1, |spectralStieltjes lam (2+t)-semicircleResolvent t| ≤ (1/100)*Real.sqrt t
  cutoff : 216*s ≤ overlapCentralCutoff n^2
  saddle : saddleSubcriticalError lam+s/2 ≤ 1/1536

lemma orthogonal_equal_norm_pair (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ u v : EuclideanSpace ℝ (Fin (n+2)), ‖u‖ = r ∧ ‖v‖ = r ∧ inner ℝ u v = 0 := by
  let b := EuclideanSpace.basisFun (Fin (n+2)) ℝ
  refine ⟨r • b 0,r • b 1,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,b.norm_eq_one,mul_one]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,b.norm_eq_one,mul_one]
  · rw [real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
    norm_num

lemma largeL_space {L : ℝ} (hL : 262144 ≤ L) : 262144 ≤ L*Real.sqrt L := by
  have hL1 : 1 ≤ L := by linarith
  have hr : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  nlinarith

lemma naturalOrientationInputs {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      OrientationInputs lam (naturalPartitionConstant (n+3) L) (naturalEdgeScale (n+3) L) := by
  have hLp : 0 < L := by linarith
  have hLa : 1696 ≤ L := by linarith
  have hspaceL := largeL_space hL
  have hc := (tendsto_add_atTop_nat 3).eventually (traceCost_natural_eventually hh hLp hcost)
  have hs := (tendsto_add_atTop_nat 3).eventually
    ((naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))
  have hf := (tendsto_add_atTop_nat 3).eventually edgeLength_tents_eventually
  have hcut := (tendsto_add_atTop_nat 3).eventually (naturalEdgeScale_cutoff_eventually hLp.le)
  have herr := (tendsto_add_atTop_nat 3).eventually
    (spectralGood_saddle_uniform hh hLa hcost (by linarith : 16 ≤ L*Real.sqrt L)
      (by norm_num : (0:ℝ) < 1/1536))
  filter_upwards [hc,hs,hf,hcut,herr] with n hnc hns hnf hncut hnerr
  intro lam hlam
  let s := naturalEdgeScale (n+3) L
  have hsp : 0 < s := naturalEdgeScale_pos (n+3) hLp
  have hsm : s ≤ 1 := hns.le
  have hsc : 32768 ≤ (n+4:ℝ)*s*Real.sqrt s := by
    have hs' := (naturalEdgeScale_space (n+3) hLp).1
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hs'
    have he : (n:ℝ)+3+1 = n+4 := by ring
    rw [he] at hs'
    linarith
  have hclose (i : Fin (n+4)) (hi : i.val < 3) : |lam i-2| ≤ s/4 :=
    spectralGood_top_close hh hLa hsm hnf hnc hlam i hi
  have hb := spectralGood_bounded (n+3) hh hsp hsm (by norm_num : (1/100:ℝ) ≤ 1/5) hnc hlam
  have hlo := spectralGood_sphere_partition_lower (n := n+2) hh hsp hsm hnc hlam
    (by norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc]; exact hsc)
    (hclose 0 (by simp)) (hclose 1 (by simp))
  norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc] at hlo
  have hsup := (naturalEdgeScale_space (n+3) hLp).2
  norm_num only [Nat.cast_add,Nat.cast_ofNat] at hsup
  rw [show (n:ℝ)+3+1=n+4 by ring] at hsup
  have hpart : naturalPartitionConstant (n+3) L*Real.exp ((n+4:ℝ)*sphericalVariational lam 1) ≤
      spherePartition lam 1 (Real.sqrt (n+4)) := by
    apply le_trans _ hlo
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    unfold naturalPartitionConstant
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity : 0 ≤ s/4)
  have hsmall := (traceCost_small (n+3) hh hsp hsm hnc).trans (by norm_num : (1/100:ℝ) ≤ 1/2)
  have hsc' : 2 ≤ ((n+3:ℕ)+1:ℝ)*s*Real.sqrt s := by
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    linarith
  have htrace (t : ℝ) (ht : s ≤ t) :
      |spectralStieltjes lam (2+t)-semicircleResolvent t| ≤ (1/100)*Real.sqrt t := by
    have ht' := spectralGood_relative_trace (n+3) hh hsp ht hsmall hsc' hlam hnc
    simpa only [spectralStieltjes,Fintype.card_fin,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_comm] using ht'
  have htmax : spectralTop lam < 2+s := by
    obtain ⟨i,hi⟩ := spectralTop_attained lam
    have hu := spectralGood_top_upper (n+3) hh hsp hsm (by norm_num : (1/100:ℝ) ≤ 1) hnc hlam i
    rw [hi] at hu
    linarith
  have htmin : 2-s ≤ spectralTop lam := by
    have hh0 := (abs_le.mp (hclose 0 (by simp))).1
    have hh1 := le_spectralTop lam 0
    linarith
  have htr : spectralStieltjes lam (2+s) ≤ 1 := by
    have he := (abs_le.mp (htrace s le_rfl)).2
    have hd := semicircleResolvent_deficit_lower hsp.le hsm
    linarith [Real.sqrt_nonneg s]
  refine ⟨hb,naturalPartitionConstant_pos (n+3) hLp,?_,hsp.le,htmax,htmin,htr,
    fun t ht => htrace t ht.1,hncut,(hnerr lam hlam).le⟩
  norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc] at hpart ⊢
  exact hpart

lemma spectralGood_orientation_variance {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      (∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt (n+4))-1)^2
        ∂orthogonalHaar (Fin (n+4))) ≤ ε+naturalOrientationTail (n+3) L := by
  have ho := (tendsto_add_atTop_nat 4).eventually (orientation_normalized_variance_bound ε hε)
  filter_upwards [naturalOrientationInputs hh hL hcost,ho] with n hn hv
  intro lam hlam
  have hi := hn lam hlam
  obtain ⟨u,v,hu,hv',huv⟩ := orthogonal_equal_norm_pair (n+2) (Real.sqrt (n+4)) (Real.sqrt_nonneg _)
  have hh := hv lam u v _ _
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hu)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hv') huv hi.bounded hi.Kpos hi.partitionLower hi.scaleNonneg
    hi.topUpper hi.topLower hi.trace hi.traceUniform hi.cutoff hi.saddle
  simpa only [naturalOrientationTail,Nat.cast_add,Nat.cast_ofNat,show (n:ℝ)+3+1=n+4 by ring,
    show (n:ℝ)+3+2=n+4+1 by ring] using hh


lemma edgeLength_rpow_lower (n : ℕ) : (n+1:ℝ)^(1/3:ℝ) ≤ edgeLength n := by
  have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ n+1) (edgeLength_cube n).1
    (by norm_num : (0:ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast,← Real.rpow_mul (edgeLength_cast_pos n).le] at hh
  norm_num at hh
  exact hh

lemma edgeLength_rpow_upper (n : ℕ) : (edgeLength n:ℝ) ≤ 2*(n+1:ℝ)^(1/3:ℝ) := by
  have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (edgeLength n:ℝ)^3)
    (edgeLength_cube n).2 (by norm_num : (0:ℝ) ≤ 1/3)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (by positivity)] at hh
  have hc : (8:ℝ)^(1/3:ℝ) = 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hc,← Real.rpow_natCast,← Real.rpow_mul (edgeLength_cast_pos n).le] at hh
  norm_num at hh
  exact hh

lemma naturalEdgeScale_sqrt (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (naturalEdgeScale n L) = Real.sqrt L/(edgeLength n) := by
  rw [naturalEdgeScale,Real.sqrt_div hL,Real.sqrt_sq (edgeLength_cast_pos n).le]

lemma natural_smallBall_rate (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (n+1:ℝ)^(1/3:ℝ)*Real.sqrt (naturalEdgeScale n L) ≤ Real.sqrt L := by
  rw [naturalEdgeScale_sqrt n hL,← mul_div_assoc,div_le_iff₀ (edgeLength_cast_pos n)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (edgeLength_rpow_lower n) (Real.sqrt_nonneg L)

def naturalOverlapRate (n : ℕ) (L : ℝ) : ℝ :=
  (16*Real.exp (6*(L*Real.sqrt L)))^2*16/((n+1)*Real.sqrt (naturalEdgeScale n L))

def naturalOverlapConstant (L : ℝ) : ℝ :=
  32*(16*Real.exp (6*(L*Real.sqrt L)))^2/Real.sqrt L

lemma naturalOverlapRate_nonneg (n : ℕ) (L : ℝ) : 0 ≤ naturalOverlapRate n L := by
  unfold naturalOverlapRate
  positivity

lemma naturalOverlapRate_scaled_bound (n : ℕ) {L : ℝ} (hL : 0 < L) :
    (n+1:ℝ)^(2/3:ℝ)*naturalOverlapRate n L ≤ naturalOverlapConstant L := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hr := Real.sqrt_pos.mpr hL
  have hd := edgeLength_cast_pos n
  have he : (n+1:ℝ)^(2/3:ℝ)*(n+1:ℝ)^(1/3:ℝ) = n+1 := by
    rw [← Real.rpow_add hn]
    norm_num
  have hh := mul_le_mul_of_nonneg_left (edgeLength_rpow_upper n)
    (show 0 ≤ (n+1:ℝ)^(2/3:ℝ) by positivity)
  have hb : (n+1:ℝ)^(2/3:ℝ)*(edgeLength n:ℝ) ≤ 2*(n+1) := by
    nlinarith [he]
  unfold naturalOverlapRate naturalOverlapConstant
  rw [naturalEdgeScale_sqrt n hL.le]
  have ht := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 16*(16*Real.exp (6*(L*Real.sqrt L)))^2/((n+1:ℝ)*Real.sqrt L) by positivity)
  calc
    _ = (16*(16*Real.exp (6*(L*Real.sqrt L)))^2/((n+1:ℝ)*Real.sqrt L))*
        ((n+1:ℝ)^(2/3:ℝ)*(edgeLength n:ℝ)) := by field_simp
    _ ≤ (16*(16*Real.exp (6*(L*Real.sqrt L)))^2/((n+1:ℝ)*Real.sqrt L))*(2*(n+1)) := ht
    _ = _ := by field_simp; ring

end CriticalSK

end

end OAI
