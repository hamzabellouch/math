import OAI.Probability.TraceReconstruction.Amplification
import OAI.Probability.TraceReconstruction.Propagation

namespace OAI

/-!
# Induction

Concrete level invariants, metadata prefixes, score/error budgets, overlap, the induction step, and the complete construction.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal induction invariant, including the depth-dependent moment,
 actual complete-trace simulator, distinct words, length, and power overlap. -/
abbrev SourceLevelPair (B D : ℕ) (n q : ℝ) (hq : q∈Set.Icc 0 1) (i : ℕ) :=
  ConcreteLevelPair q hq (sourceTargetScale B D n i)
    (n^(-100*(totalScoreExponent B D+B+1))) (totalScoreExponent B i)
    (initialOverlapLower q) ((sourceOverlapConstant q)^(2*B*i+2)) i (sourceHalfMoment B D n i)

theorem source_level_geometry {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D)
    (hn : 1 ≤ n) (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1))) :
    SourceArithmeticBounds (sourceOverlapConstant q) (sourceTargetScale B D n (i+1))
      ((sourceOverlapConstant q)^(2*B*i+2)) (sourceEpsilon B D)
      (sourceCancellationOrder B D) (sourceDimension B i) U.left.length U.overlapCount := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let C := sourceOverlapConstant q
  have hC : 2 ≤ C := sourceOverlapConstant_ge_two hq'
  have hb := sourceDimension_bounds B i hB
  have hN := (sourceTargetScale_bounds B D (i+1) hB hn).1
  have he := sourceEpsilon_pos B D
  have hG := source_local_envelope B D i b hq' (Nat.le_of_lt hi) hb.2
  apply source_arithmetic_geometry hC hN (one_le_pow₀ (by linarith only [hC])) he.le
    (fun j _=>sourceA_nonneg B D b j hb.2 (by omega))
    (fun j hj=>sourceKappa_three_epsilon B D b (j+1) hb.2 (by omega) (by omega))
  · have hh := mul_le_mul_of_nonneg_left hG (show (0:ℝ) ≤ 1200 by norm_num)
    exact (by nlinarith only [hh] : 1200*C^(2*b)*C^(2*B*i+2) ≤ 1200*sourceCapEnvelope B D q).trans H.geometry
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using H.motif
  · simpa only [sourceTargetScale_step B D i n (by linarith only [hn]) hi] using U.length_lower
  · simpa only [sourceTargetScale_step B D i n (by linarith only [hn]) hi] using U.length_upper
  · exact U.overlapCount_lower
  · exact U.overlapCount_upper

theorem SourceArithmeticBounds.copies_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) {j : ℕ} (hj : j<b) :
    1 ≤ sourceArithmeticP C N b ε ell k j := by
  have hh := (H.copies j hj).1
  have hp : (0:ℝ)<N^(scaleA b j ε)*N^ε/2 := by positivity
  have hp' : (0:ℝ)<sourceArithmeticP C N b ε ell k j := hp.trans_le hh
  have hp'' : 0<sourceArithmeticP C N b ε ell k j := by exact_mod_cast hp'
  omega

theorem SourceArithmeticBounds.trials_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (hN : 0<N) (hC : 0<C) (hF : 0<F)
    {j : ℕ} (hj : j<b) : 0<sourceArithmeticTrials C N b ε ell k j := by
  have hh := (H.trials j hj).1
  have hp : (0:ℝ)<N^ε/(600*(C^(2*b)*F)) := by positivity
  exact_mod_cast hp.trans_le hh

theorem source_level_exponent_margins (B D i : ℕ) (hB : 2 ≤ B) (hi : i ≤ D) :
    let ε := sourceEpsilon B D
    let b := sourceDimension B i
    let e := scaleA b 0 ε*totalScoreExponent B i
    (i<warmupBlocks B → b=2 ∧ 27/50 ≤ e ∧ ε+scaleA b 1 ε ≤ e ∧ ε+1-2*e ≤ 0) ∧
    (warmupBlocks B ≤ i → ∀j ≤ b,ε+scaleA b j ε ≤ e) := by
  let ε := sourceEpsilon B D
  have he := sourceEpsilon_pos B D
  have he1 : ε ≤ 1/100 := by
    have hh := sourceEpsilon_gap_small B D
    have hg := sourceGapFloor_le_one B
    dsimp [ε]
    linarith only [hh,hg]
  have hd := (totalScoreExponent_bounds B i hB).1
  have hd' : totalScoreExponent B i ≤ 3+(B:ℝ)*D := by
    simpa only [mul_comm] using (totalScoreExponent_mono B hB hi).trans (totalScoreExponent_bounds B D hB).2
  constructor
  · intro hw
    have hb : sourceDimension B i=2 := ite_eq_left hw
    have hh := source_warmup_score_margin B D hB hd hd'
    simp only [hb]
    exact ⟨True.intro,hh.1,by linarith only [hh.1,hh.2,he1],by linarith only [hh.1,he1]⟩
  · intro hw j hj
    have hb : sourceDimension B i=B := ite_eq_right (by omega)
    rw [hb] at hj ⊢
    have hlarge := totalScoreExponent_after_warmup B i hB hw
    have hh := source_main_score_margin B D hB (by linarith only [hlarge]) hd'
    have ha : scaleA B j ε ≤ 1 := by
      exact (scaleA_mono_index B j B ε he.le hj).trans (by rw [scaleA_top])
    have heps : ε ≤ 1/(2:ℝ)^B := by
      have hs := sourceEpsilon_small B D
      have hm := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ D+1 by have : 0 ≤ (D:ℝ) := Nat.cast_nonneg D; linarith only [this]) (show 0 ≤ (2:ℝ)^B*ε by positivity)
      apply (le_div_iff₀ (by positivity)).mpr
      dsimp [ε] at *
      nlinarith only [hs,hm]
    linarith only [hh,ha,heps]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceEffectiveHiddenTail_one (T n : ℕ→ℕ) (ω : ℝ) :
    sourceEffectiveHiddenTail T n 1 ω = if n 0=0 then 0 else Real.exp (-(n 0:ℝ)*ω^4/16) := by
  unfold sourceEffectiveHiddenTail
  change (∑v : Bool ⊕ (Fin (T 0) × PEmpty),_)=_
  simp only [Fintype.sum_sum_type,Finset.univ_eq_empty,Finset.sum_empty,
    add_zero,Fintype.sum_bool,collectionCount,sourceScheduledTrials,
    ite_true,zero_add]
  rfl

theorem sourceEffectiveHiddenTail_step (T n : ℕ→ℕ) (b : ℕ) (ω : ℝ) :
    sourceEffectiveHiddenTail T n (b+1) ω =
      (if n b=0 then 0 else Real.exp (-(n b:ℝ)*ω^4/16))+
      (if sourceScheduledTrials T n b=0 then 0 else Real.exp (-(sourceScheduledTrials T n b:ℝ)*ω^4/16))+
      (T b:ℝ)*sourceEffectiveHiddenTail T n b ω := by
  unfold sourceEffectiveHiddenTail
  change (∑v : Bool ⊕ (Fin (T b) × WindowCollection T b),_)=_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,collectionCount]
  let f := fun v : ℕ => if v=0 then (0:ℝ) else Real.exp (-(v:ℝ)*ω^4/16)
  change (f (sourceScheduledTrials T n b)+f (n b)+(∑ _ : Fin (T b),
    ∑ v : WindowCollection T b,f (collectionCount T n (sourceScheduledTrials T n) b v))) =
    f (n b)+f (sourceScheduledTrials T n b)+(T b:ℝ)*
    (∑ v : WindowCollection T b,f (collectionCount T n (sourceScheduledTrials T n) b v))
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem sourceEffectiveHiddenTail_two_ge_one (T n : ℕ→ℕ) (ω : ℝ) (hT : 1 ≤ T 1) :
    sourceEffectiveHiddenTail (fun _=>T 0) (fun _=>n 0) 1 ω ≤ sourceEffectiveHiddenTail T n 2 ω := by
  rw [sourceEffectiveHiddenTail_step T n 1 ω,sourceEffectiveHiddenTail_one,
    sourceEffectiveHiddenTail_one]
  have hnonneg (v : ℕ) : 0 ≤ (if v=0 then 0 else Real.exp (-(v:ℝ)*ω^4/16)) := by
    split_ifs <;> positivity
  have ht : (1:ℝ) ≤ T 1 := by exact_mod_cast hT
  have hh := le_mul_of_one_le_left (hnonneg (n 0)) ht
  linarith only [hh,hnonneg (n 1),hnonneg (sourceScheduledTrials T n 1)]

theorem sourceSparseCount_motif_le (T : ℕ→ℕ) (s b : ℕ) (hT : ∀j<b,1 ≤ T (j+1)) :
    (2:ℝ)^s ≤ (sourceSparseCount T s b:ℝ) := by
  have hp : 1 ≤ ∏j∈Finset.range b,T (j+1) := Finset.one_le_prod (fun j hj=>hT j (Finset.mem_range.mp hj))
  have hh : 2^s ≤ sourceSparseCount T s b := by
    unfold sourceSparseCount
    exact Nat.le_mul_of_pos_right _ hp
  exact_mod_cast hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_tail_budget {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    sourceEffectiveHiddenTail T t b (initialOverlapLower q) ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail T t b/N^(-20*sourceWorkSize B D) ≤ n^(-200*(totalScoreExponent B D+B+1)) ∧
    sourceFitTail T t b ≤ n^(-200*(totalScoreExponent B D+B+1)) := by
  have hn1 : 1 ≤ n := by linarith only [hn]
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have hC := sourceOverlapConstant_pos hq'.1
  have hω := initialOverlapLower_pos q
  have hG := source_local_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) hb.2
  have hf : 9600*((sourceOverlapConstant q)^(2*sourceDimension B i)*
      (sourceOverlapConstant q)^(2*B*i+2))/(initialOverlapLower q)^4 ≤ sourceTailDenominator B D q := by
    have hh := mul_le_mul_of_nonneg_right hG (show 0 ≤ 9600*(initialOverlapLower q)⁻¹^4 by positivity)
    unfold sourceTailDenominator
    rw [div_eq_mul_inv,←inv_pow]
    nlinarith only [hh]
  exact source_exponential_error_budget H' hB hb.2 hC (by positivity) hω hn1 hN.1 hN.2
    (by
      have hh : 0 ≤ 9600*sourceCapEnvelope B D q*(initialOverlapLower q)⁻¹^4 := by positivity [sourceCapEnvelope_pos B D hq'.1]
      unfold sourceTailDenominator
      linarith only [hh]) hf
    (by simpa only [neg_div] using htail)

theorem source_level_all_budgets {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let k := sourceHalfMoment B D n (i+1)
    let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
    let a := N^(-20*sourceWorkSize B D)
    let ω := initialOverlapLower q
    let gap := (totalScoreExponent B i+1)*sourceGapFloor B
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ N^(-gap/2)/8) ∧
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ 1/2) ∧
    (64*sourceSharpEnergyBudget T t s (b-1) (sourceDegreeCutoff B) ω a a ((6*(2*k:ℕ):ℝ)*L) ≤
       N^(-totalScoreExponent B (i+1))) ∧
    (∀j<b,hiddenSmoothingBound (t j) s ω ≤ a) ∧
    sourceClippingCost T t s (b-1) k ω a L ≤ 1/2 ∧
    sourceClippingCost T t s (b-1) k ω a L+sourceFitTail T t b ≤
      n^(-100*(totalScoreExponent B D+B+1)) := by
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn2 : 1<n := by linarith only [hn]
  have hC : 1 ≤ sourceOverlapConstant q := (by norm_num : (1:ℝ) ≤ 2).trans (sourceOverlapConstant_ge_two hq')
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hb1 : sourceDimension B i-1+1=sourceDimension B i := by omega
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have he := source_level_energy B D i U.left.length U.overlapCount (sourceHalfMoment B D n (i+1))
    (sourceOverlapConstant q) (sourceTargetScale B D n (i+1)) ((sourceOverlapConstant q)^(2*B*i+2))
    (initialOverlapLower q) (sourceCapEnvelope B D q) hB hi hN.1 hC (one_le_pow₀ hC) (initialOverlapLower_pos q)
    H' (sourceHalfMoment_bounds B D (i+1) hB hn2).2
    (source_cap_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) hb.2)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using H.sparse)
    (H.bad _ (by omega)) (by simpa only [hb1] using H.force (sourceDimension B i-1) (by omega)) H.tail H.smoothing
  have ht := source_level_tail_budget U hB hi hn hq' H htail
  have hg : sourceGapFloor B ≤ (totalScoreExponent B i+1)*sourceGapFloor B := by
    exact le_mul_of_one_le_left (sourceGapFloor_pos B).le
      (by linarith only [(totalScoreExponent_bounds B i hB).1])
  have hc := source_level_clipping B D (i+1) (sourceCancellationOrder B D) (sourceDimension B i-1)
    (sourceBlockWindows (sourceTargetScale B D n (i+1)) (sourceDimension B i) (sourceEpsilon B D))
    (sourceArithmeticTrials (sourceOverlapConstant q) (sourceTargetScale B D n (i+1))
      (sourceDimension B i) (sourceEpsilon B D) U.left.length U.overlapCount)
    n (initialOverlapLower q) ((sourceTargetScale B D n (i+1))^(-20*sourceWorkSize B D))
    ((totalScoreExponent B i+1)*sourceGapFloor B)
    ((sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i/2))
    hB hn hg (by simpa only [hb1] using ht.1) (by simpa only [hb1] using ht.2.1)
    (by simpa only [hb1] using ht.2.2) he.2.1 he.1
  exact ⟨he.1,he.2.1,he.2.2.1,he.2.2.2,hc.1,by simpa only [hb1] using hc.2⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_old_variance_scale (B D i : ℕ) {n : ℝ} (hn : 0<n) (hi : i<D) :
    (sourceTargetScale B D n i)^(-totalScoreExponent B i)=
      (sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) := by
  rw [sourceTargetScale_step B D i n hn.le hi,←Real.rpow_mul (show 0 ≤ sourceTargetScale B D n (i+1) from (Real.rpow_pos_of_pos hn _).le)]
  congr 1
  ring

theorem source_old_variance_square (B D i : ℕ) {n : ℝ} (hn : 0<n) (hi : i<D) :
    (sourceTargetScale B D n i)^(-totalScoreExponent B i)=
      ((sourceTargetScale B D n (i+1))^(-scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i/2))^2 := by
  rw [source_old_variance_scale B D i hn hi,←Real.rpow_natCast,←Real.rpow_mul (show 0 ≤ sourceTargetScale B D n (i+1) from (Real.rpow_pos_of_pos hn _).le)]
  congr 1
  norm_num

theorem source_level_dense_overlap {B D i j : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (hj : j ≤ sourceDimension B i)
    (hgap : sourceEpsilon B D+scaleA (sourceDimension B i) j (sourceEpsilon B D) ≤
      scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    Real.sqrt (((h j+1:ℕ):ℝ)*(((2^s:ℕ):ℝ)^j*(sourceTargetScale B D n i)^(-totalScoreExponent B i)))+
      2*((h j+1:ℕ):ℝ)*((sourceBlockLength P 1 j:ℝ)*U.error) ≤ 1/4 := by
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have he := sourceEpsilon_pos B D
  have he1 : sourceEpsilon B D ≤ 1 := by
    linarith only [sourceEpsilon_gap_small B D,sourceGapFloor_le_one B]
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have hC : 1 ≤ sourceOverlapConstant q := (by norm_num : (1:ℝ) ≤ 2).trans (sourceOverlapConstant_ge_two hq')
  have hE : U.error ≤ ((i:ℝ)+1)*n^(-100*(totalScoreExponent B D+B+1))*U.left.length := by
    apply (div_le_iff₀ ?_).mp U.normalized_error
    exact (show 0<sourceTargetScale B D n i/2 by positivity [Real.rpow_pos_of_pos hn0 (sourceScaleProduct B D i)]).trans_le U.length_lower
  apply source_literal_dense_overlap (V:=(sourceTargetScale B D n i)^(-totalScoreExponent B i)) (e:=scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i) (W:=sourceWeightEnvelope B D) (L:=(2:ℝ)^(sourceCancellationOrder B D))
    H' hB hb.2 hC (pow_nonneg (by linarith only [hC]) _) hn1 hN.1 hN.2 he.le he1
    (sourceCapEnvelope_pos B D hq'.1).le (sourceWeightEnvelope_nonneg B D) (one_le_pow₀ (by norm_num)) rfl
    (source_local_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) hb.2) (Nat.le_of_lt hi) hj
    (sourceA_nonneg B D _ j hb.2 (by omega))
    ((scaleA_mono_index _ j _ _ he.le hj).trans (by rw [scaleA_top])) hE rfl
    (by simpa only [neg_mul] using (source_old_variance_scale B D i hn0 hi).le) hgap H.error H.overlap

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The second warmup lift is produced from the one-window oracle, whose
 quadratic energy gain is essential before the main-block regime. -/
theorem source_level_warmup_second {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ)) (hiw : i<warmupBlocks B)
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N 2 ε
    let t := sourceArithmeticTrials (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
    let P := sourceArithmeticP (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
    let k := sourceHalfMoment B D n (i+1)
    let L := N^(-scaleA 2 0 ε*totalScoreExponent B i/2)
    let a := N^(-20*sourceWorkSize B D)
    let ω := initialOverlapLower q
    let cost := sourceClippingCost (fun _=>T 0) (fun _=>t 0) s 0 k ω a L
    (((6*(2*k:ℕ):ℝ)*L)^2*(2:ℝ)^s ≤ 1/2) ∧ cost ≤ 1/2 ∧
    Real.sqrt (((h 2+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*
      (64*sourceSharpEnergyBudget (fun _=>T 0) (fun _=>t 0) s 0 2 ω a a ((6*(2*k:ℕ):ℝ)*L)))+
      2*((h 2+1:ℕ):ℝ)*((P 1:ℝ)*(cost+(T 0:ℝ)*U.error)) ≤ 1/4 := by
  let N := sourceTargetScale B D n (i+1)
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let C := sourceOverlapConstant q
  let F := C^(2*B*i+2)
  let K := sourceCapEnvelope B D q
  let W := sourceWeightEnvelope B D
  let T := sourceBlockWindows N 2 ε
  let t := sourceArithmeticTrials C N 2 ε U.left.length U.overlapCount
  let P := sourceArithmeticP C N 2 ε U.left.length U.overlapCount
  let h := sourceArithmeticCount C N 2 ε U.left.length U.overlapCount
  let k := sourceHalfMoment B D n (i+1)
  let e := scaleA 2 0 ε*totalScoreExponent B i
  let L := N^(-scaleA 2 0 ε*totalScoreExponent B i/2)
  let a := N^(-20*sourceWorkSize B D)
  let ω := initialOverlapLower q
  let w := (6*(2*k:ℕ):ℝ)*L
  let gap := (totalScoreExponent B i+1)*sourceGapFloor B
  let Δ := n^(-100*(totalScoreExponent B D+B+1))
  have hb : sourceDimension B i=2 := ite_eq_left hiw
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have hN := sourceTargetScale_bounds B D (i+1) hB hn1
  have hN0 : 0<N := by dsimp [N]; linarith only [hN.1]
  have hC : 1 ≤ C := (by norm_num : (1:ℝ) ≤ 2).trans (sourceOverlapConstant_ge_two hq')
  have hC0 : 0<C := by linarith only [hC]
  have hF : 0<F := by positivity
  have hK : 0 ≤ K := (sourceCapEnvelope_pos B D hq'.1).le
  have hW : 0 ≤ W := sourceWeightEnvelope_nonneg B D
  have he := sourceEpsilon_pos B D
  have he1 : ε ≤ 1 := by
    dsimp [ε]
    linarith only [sourceEpsilon_gap_small B D,sourceGapFloor_le_one B]
  have H' := source_level_geometry U hB hi hn1 hq' H
  rw [hb] at H'
  have Hnum := source_level_all_budgets U hB hi hn hq' H htail
  simp only [hb,show (2:ℕ)-1=1 by rfl] at Hnum
  have ht := source_level_tail_budget U hB hi hn hq' H htail
  simp only [hb] at ht
  have hmot : (2:ℝ)^s ≤ (sourceSparseCount T s 1:ℝ) :=
    sourceSparseCount_motif_le T s 1 (fun j _=>Nat.succ_le_of_lt (H'.window_positive (j+1)))
  have hs := mul_le_mul_of_nonneg_left hmot (sq_nonneg w)
  have hs1 : w^2*(2:ℝ)^s ≤ 1/2 := hs.trans Hnum.2.1
  have hs2 : w^2*(2:ℝ)^s ≤ N^(-gap/2)/8 := hs.trans Hnum.1
  have hm : sourceEffectiveHiddenTail (fun _=>T 0) (fun _=>t 0) 1 ω ≤
      n^(-200*(totalScoreExponent B D+B+1)) :=
    (sourceEffectiveHiddenTail_two_ge_one T t ω (Nat.succ_le_of_lt (H'.window_positive 1))).trans ht.1
  have hg : sourceGapFloor B ≤ gap := le_mul_of_one_le_left (sourceGapFloor_pos B).le
    (by linarith only [(totalScoreExponent_bounds B i hB).1])
  have hc := source_one_window_clipping B D (i+1) s (T 0) (t 0) n ω a gap L hB hn hg hm hs1 hs2
  have hG : C^4*F ≤ K := by
    simpa only [hb,show (2:ℕ)*2=4 by rfl] using
      source_local_envelope B D i (sourceDimension B i) hq' (Nat.le_of_lt hi) (sourceDimension_bounds B i hB).2
  have hE : U.error ≤ ((i:ℝ)+1)*Δ*U.left.length := by
    apply (div_le_iff₀ ?_).mp U.normalized_error
    exact (show 0<sourceTargetScale B D n i/2 by positivity [Real.rpow_pos_of_pos hn0 (sourceScaleProduct B D i)]).trans_le U.length_lower
  have herr := source_warmup_error_budget H' hB hC hF.le hn1 hN.1 hN.2 he.le he1 hK hG
    (Nat.le_of_lt hi) hE U.error_nonneg rfl hc.2 H.error
  have hcount : ((h 2+1:ℕ):ℝ) ≤ (K+1)*N := by
    have hh := H'.count_bound hC hF.le hN.1 (j:=2) le_rfl (by rw [scaleA_top]; norm_num)
    have hh' := mul_le_mul_of_nonneg_right (add_le_add hG (show (1:ℝ) ≤ 1 from le_rfl)) hN0.le
    simp only [scaleA_top,Real.rpow_one,show (2:ℕ)*2=4 by rfl] at hh
    exact hh.trans hh'
  have hwindow : (T 0:ℝ) ≤ N := by
    have hp : T 0 ≤ P 0 := by have hh := (H'.windows 0 (by omega)).2.2.1; change 2*T 0 ≤ P 0 at hh; omega
    exact (show (T 0:ℝ) ≤ P 0 by exact_mod_cast hp).trans
      (H'.copies_le_target hN.1 (by omega) ((scaleA_mono_index 2 1 2 ε he.le (by omega)).trans (by rw [scaleA_top])))
  have hw : w^2 ≤ W*N^(-e) := by
    rw [source_weight_square hN0 (show L=N^(-scaleA 2 0 ε*totalScoreExponent B i/2) from rfl)]
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k)
      (sourceHalfMoment_bounds B D (i+1) hB (by linarith only [hn])).2 2) (by norm_num : (0:ℝ) ≤ 144)
    simpa only [W,sourceWeightEnvelope,sourceMomentEnvelope,e,neg_mul] using
      mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hN0 (-e)).le
  have henergy := mul_le_mul_of_nonneg_left
    (sourceSharpEnergyBudget_warmup (fun _=>T 0) (fun _=>t 0) s ω a w hs1) (by norm_num : (0:ℝ) ≤ 64)
  have hpref := source_overlap_prefactors hK hW (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hB (j:=0) (by omega) H.overlap
  have hexp := (source_level_exponent_margins B D i hB (Nat.le_of_lt hi)).1 hiw
  rw [hb] at hexp
  have hM : 1 ≤ sourceWorkSize B D := by
    unfold sourceWorkSize
    linarith only [(totalScoreExponent_bounds B D hB).1,Nat.cast_nonneg (sourceDegreeCutoff B) (α:=ℝ),Nat.cast_nonneg B (α:=ℝ)]
  have hv := source_warmup_variance_budget hN.1 hK hW (show 0 ≤ (2:ℝ)^s by positivity)
    (Nat.cast_nonneg (T 0)) (Nat.cast_nonneg (h 2+1)) hcount hwindow hw henergy hpref.2.1 hpref.2.2
    (by change ε+2-e-40*sourceWorkSize B D ≤ 0; have hloe : 27/50 ≤ e := hexp.2.1; linarith only [he1,hloe,hM])
    hexp.2.2.2
  refine ⟨hs1,hc.1,?_⟩
  have hh := overlap_sqrt_budget hv herr
  simpa only [N,ε,s,C,F,K,W,T,t,P,h,k,e,L,a,ω,w,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_overlap {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let atom := fun (τ : Bool)=>if τ then U.right else U.left
    ∀j ≤ b, initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
  let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
  let T := sourceBlockWindows N b ε
  let t := sourceArithmeticTrials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
  let atom := fun (τ : Bool)=>if τ then U.right else U.left
  let k := sourceHalfMoment B D n (i+1)
  let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
  let a := N^(-20*sourceWorkSize B D)
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn2 : 1 < n := by linarith only [hn]
  have hN : 0<N := (by norm_num : (0:ℝ)<1).trans_le (sourceTargetScale_bounds B D (i+1) hB hn1).1
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hk : 1 ≤ k := (sourceHalfMoment_bounds B D (i+1) hB hn2).1
  let O := U.oracle.restrict hk (sourceHalfMoment_step B D i hB hi hn2)
  have hC := sourceOverlapConstant_large hq'
  have hp : initialOverlapLower q∈Set.Ioc 0 (1/8:ℝ) :=
    ⟨initialOverlapLower_pos q,(initialOverlapLower_lt_eighth hq'.1).le⟩
  have hc (j : ℕ) (hj : j ≤ b) : 1 ≤ h j :=
    (H'.length_positive hN hj).trans (H'.counts j hj).1
  have hP (j : ℕ) (hj : j<b) : 1 ≤ P j := H'.copies_positive hN hj
  have hlift (j : ℕ) (_hj : j<b) : sourceOverlapConstant q*h j*P j ≤ h (j+1) :=
    sourceArithmetic_count_lift _ _ _ _ _ _ _
  have hbase : initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (atom false) (h 0)) (pureAtomRun (atom false) (h 0+1)) := U.power_overlap
  by_cases hiw : i<warmupBlocks B
  · have hb2 : sourceDimension B i=2 := ite_eq_left hiw
    have hb' : b=2 := hb2
    have hw := source_level_warmup_second U hB hi hn hq' hiw H htail
    have hnum := source_level_all_budgets U hB hi hn hq' H htail
    have hexp := (source_level_exponent_margins B D i hB (Nat.le_of_lt hi)).1 hiw
    have hfirst := source_level_dense_overlap U hB hi hn hq' H (j:=1) (by omega) hexp.2.2.1
    have hfirst' : Real.sqrt (((h 1+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*(sourceTargetScale B D n i)^(-totalScoreExponent B i))+
        2*((h 1+1:ℕ):ℝ)*((P 0:ℝ)*U.error) ≤ 1/4 := by
      simpa only [pow_one,sourceBlockLength,mul_one,mul_assoc] using hfirst
    have hev : Even (T 0) := by
      change Even (sourceBlockWindows N b ε 0)
      rw [sourceBlockWindows,ite_eq_left (by omega : 0<b)]
      exact sourceWindowSize_even _ _ _ _
    have hfit : t 0*(2*h 0+1)+T 0 ≤ P 0 := by
      dsimp only [t]
      rw [sourceArithmetic_inner_trials (sourceOverlapConstant q) N b ε U.left.length U.overlapCount 0 (by omega : 0+1≠b)]
      have hh := sourceLocalTrials_budget (P 0) (h 0)
      have ht := (H'.windows 0 (by omega)).2.2.1
      change 2*T 0 ≤ P 0 at ht
      rw [mul_assoc] at hh
      change sourceLocalTrials (P 0) (h 0)*(2*h 0+1)+T 0 ≤ P 0
      omega
    have hs : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _=>T 0) s 0 ≤ 1/2 := by
      simpa only [L,N,b,ε,k,s,T,t,a,hb2,sourceSparseCount,Finset.range_zero,Finset.prod_empty,Nat.mul_one,Nat.cast_pow,Nat.cast_ofNat] using hw.1
    have hclip : sourceClippingCost (fun _=>T 0) (fun _=>t 0) s 0 k (initialOverlapLower q) a L ≤ 1/2 := by
      simpa only [L,N,b,ε,k,s,T,t,a,P,h,hb2] using hw.2.1
    have hv : (sourceTargetScale B D n i)^(-totalScoreExponent B i) ≤ L^2 := by
      rw [source_old_variance_square B D i (by linarith only [hn]) hi]
    have hh := source_warmup_nested_overlap hq U.error_nonneg s k P h atom O hp hC
      (fun j hj=>hc j (by omega)) (fun j hj=>hP j (by omega)) (fun j hj=>hlift j (by omega))
      hfirst' hbase (T 0) (t 0) (H'.windows 0 (by omega)).1 hev (H'.windows 0 (by omega)).2.1
      (H'.windows 0 (by omega)).2.2.2 hfit a a L (by positivity) (by positivity) hk hv hs
      (hnum.2.2.2.1 0 (by omega)) hclip (by simpa only [L,N,b,ε,k,s,T,t,a,P,h,hb2] using hw.2.2)
    change ∀j : ℕ,j≤b → initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1))
    intro j hj
    exact hh j (by change j≤b at hj; omega)
  · apply source_nested_overlap hq U.error_nonneg s P h atom (O.hellinger hk) b hp hC hc hP hlift _ hbase
    intro j hj
    exact source_level_dense_overlap U hB hi hn hq' H (by omega)
      ((source_level_exponent_margins B D i hB (Nat.le_of_lt hi)).2 (by omega) (j+1) (by omega))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The exact manuscript block is now a producer: no new level invariant or
 overlap is assumed. All hypotheses besides the old actual pair are literal
 scalar schedule margins. -/
theorem source_level_step {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    Nonempty (SourceLevelPair B D n q hq (i+1)) := by
  let N := sourceTargetScale B D n (i+1)
  let b := sourceDimension B i
  let ε := sourceEpsilon B D
  let s := sourceCancellationOrder B D
  let C := sourceOverlapConstant q
  let P := sourceArithmeticP C N b ε U.left.length U.overlapCount
  let h := sourceArithmeticCount C N b ε U.left.length U.overlapCount
  let T := sourceBlockWindows N b ε
  let t := sourceArithmeticTrials C N b ε U.left.length U.overlapCount
  let atom := fun (τ : Bool)=>if τ then U.right else U.left
  let k := sourceHalfMoment B D n (i+1)
  let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
  let a := N^(-20*sourceWorkSize B D)
  let ω := initialOverlapLower q
  let Δ := n^(-100*(totalScoreExponent B D+B+1))
  have hn1 : 1 ≤ n := by linarith only [hn]
  have hn2 : 1 < n := by linarith only [hn]
  have hn0 : 0<n := by linarith only [hn]
  have hN : 0<N := (by norm_num : (0:ℝ)<1).trans_le (sourceTargetScale_bounds B D (i+1) hB hn1).1
  have hC : 1 ≤ C := (by norm_num : (1:ℝ)≤2).trans (sourceOverlapConstant_ge_two hq')
  have H' := source_level_geometry U hB hi hn1 hq' H
  have hb := sourceDimension_bounds B i hB
  have hb1 : b-1+1=b := by dsimp [b]; omega
  have hk : 1 ≤ k := (sourceHalfMoment_bounds B D (i+1) hB hn2).1
  let O := U.oracle.restrict hk (sourceHalfMoment_step B D i hB hi hn2)
  let := O.finiteOutcome
  have hnum := source_level_all_budgets U hB hi hn hq' H htail
  have hov := source_level_overlap U hB hi hn hq' H htail
  have hv : (sourceTargetScale B D n i)^(-totalScoreExponent B i) ≤ L^2 := by
    rw [source_old_variance_square B D i hn0 hi]
  have hm : O.first.expect (fun z=>|O.score z|^(2*k)) ≤ L^(2*k) := by
    have hh := O.first.expect_even_pow_le_of_moment O.score k hk (O.moment.trans hv)
    simpa only [pow_mul] using hh
  have he (j : ℕ) (hj : j ≤ b-1) : Even (T j) := by
    change Even (sourceBlockWindows N b ε j)
    rw [sourceBlockWindows,ite_eq_left (by omega : j<b)]
    exact sourceWindowSize_even _ _ _ _
  obtain ⟨W⟩ := actual_source_oracle hq U.error_nonneg s P T t h atom (b-1) (sourceDegreeCutoff B) k
    H'.layout H'.window_positive (by
      simpa only [P,t,h,T,sourceBlockWindows,ite_eq_left (show b-1<b by omega)] using
        sourceArithmetic_root_copies C N b ε U.left.length U.overlapCount (by omega))
    (fun j hj=>H'.trials_positive hN (by linarith only [hC]) (by positivity) (by omega))
    (fun j hj=>(H'.windows j (by omega)).1) he (fun j hj=>(H'.windows j (by omega)).2.1)
    (H'.windows (b-1) (by omega)).2.2.2 O.first O.second O.decode O.score O.density O.likelihood_nonneg
    O.first_simulation O.second_simulation ω a a L (by positivity) (by positivity)
    ⟨initialOverlapLower_pos q,lt_of_lt_of_le (initialOverlapLower_lt_eighth hq'.1) (by norm_num)⟩
    (fun j hj=>hov j (by omega)) hk hm hnum.2.1
    (fun j hj=>hnum.2.2.2.1 j (by omega)) hnum.2.2.2.2.1
  rw [hb1] at W
  have hlen (τ : Bool) : (sourceBlockWord s P atom b τ).length=sourceArithmeticLength C N b ε U.left.length U.overlapCount b := by
    rw [sourceArithmeticLength_eq_block]
    apply sourceBlockWord_length
    intro σ
    cases σ
    · rfl
    · exact U.equalLength.symm
  have hinj : Function.Injective atom := by
    intro τ σ hτσ
    cases τ <;> cases σ
    · rfl
    · exact False.elim (U.different hτσ)
    · exact False.elim (U.different hτσ.symm)
    · rfl
  have hne : sourceBlockWord s P atom b false≠sourceBlockWord s P atom b true := by
    intro hh
    have hh' := sourceBlockWord_injective s P atom U.left.length (by
      intro τ; cases τ; rfl; exact U.equalLength.symm) hinj b
      (fun j hj=>Nat.lt_of_lt_of_le (by omega : 0<1) (H'.copies_positive hN hj)) hh
    contradiction
  have hlength := H'.lengths b le_rfl
  change N^(scaleA b b ε)/2 ≤ (sourceArithmeticLength C N b ε U.left.length U.overlapCount b:ℝ) ∧
    (sourceArithmeticLength C N b ε U.left.length U.overlapCount b:ℝ) ≤ N^(scaleA b b ε) at hlength
  simp only [scaleA_top,Real.rpow_one] at hlength
  have hE : U.error ≤ ((i:ℝ)+1)*Δ*U.left.length := by
    apply (div_le_iff₀ ?_).mp U.normalized_error
    exact (show 0<sourceTargetScale B D n i/2 by positivity [Real.rpow_pos_of_pos hn0 (sourceScaleProduct B D i)]).trans_le U.length_lower
  have hleaf : SourceLeafCount T b*U.left.length ≤ sourceArithmeticLength C N b ε U.left.length U.overlapCount b := by
    rw [sourceArithmeticLength_eq_block,sourceBlockLength_factor]
    rw [Nat.mul_comm]
    apply Nat.mul_le_mul_left
    apply sourceLeafCount_le_length (by omega : 1≤1)
    intro j hj
    have hh := (H'.windows j hj).2.2.1
    change 2*T j ≤ P j at hh
    change T j ≤ P j
    omega
  have herror := normalized_block_error (H'.length_positive hN le_rfl) hE
    (show 0≤Δ by positivity) hleaf hnum.2.2.2.2.2
  have hfac : C^(2*b)*C^(2*B*i+2) ≤ C^(2*B*(i+1)+2) := by
    rw [←pow_add]
    apply pow_le_pow_right₀ hC
    dsimp [b]
    nlinarith only [hb.2]
  refine ⟨W.toConcrete hq ((hlen false).trans (hlen true).symm) hne ?_ ?_ ?_ hnum.2.2.1 ?_ ?_ (hov b le_rfl)⟩
  · rw [hlen]; exact hlength.1
  · rw [hlen]; exact hlength.2
  · rw [hlen]
    simpa only [Δ,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using herror
  · rw [hlen]; exact (H'.counts b le_rfl).1
  · rw [hlen]
    exact (H'.counts b le_rfl).2.trans (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Full source construction at every scheduled level, uniformly in the
 joint deletion regime. No level witnesses are assumed. -/
theorem source_all_levels_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i ≤ sourceDepth B ζ ((q t)^3*Real.log (n t)),
      Nonempty (SourceLevelPair B (sourceDepth B ζ ((q t)^3*Real.log (n t)))
        (n t) (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ i) := by
  filter_upwards [source_initial_at_smallest_scale B ζ hB hζ hn hq hH,
    source_numeric_margins_eventually B ζ hB hζ hn hq hH,
    source_tails_eventually B ζ hB hζ hn hq hH,hn.eventually_ge_atTop 4] with t h0 hm ht hn4
  intro i hi
  induction i with
  | zero => simpa only [SourceLevelPair,totalScoreExponent,Finset.range_zero,
      Finset.sum_empty,add_zero,Nat.mul_zero,Nat.zero_add] using h0
  | succ i ih =>
    obtain ⟨U⟩ := ih (by omega)
    exact source_level_step U hB (by omega) hn4 (hq t) (hm (i+1)) (ht (i+1))

/-- The final source pair has actual length in [n/2,n], an exact common
 complete-trace simulator, prescribed high moment and inductively obtained
 power overlap. This is the construction theorem, before statistical transfer. -/
theorem source_final_pair_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ (n t)
      ((n t)^(-100*(totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))+B+1)))
      (totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t))))
      (initialOverlapLower (q t))
      ((sourceOverlapConstant (q t))^(2*B*sourceDepth B ζ ((q t)^3*Real.log (n t))+2))
      (sourceDepth B ζ ((q t)^3*Real.log (n t)))
      (sourceHalfMoment B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t)
        (sourceDepth B ζ ((q t)^3*Real.log (n t))))) := by
  filter_upwards [source_all_levels_eventually B ζ hB hζ hn hq hH] with t ht
  simpa only [SourceLevelPair,sourceTargetScale_top] using ht _ le_rfl

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

end OAI
