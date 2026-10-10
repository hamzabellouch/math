import OAI.Analysis.C0Absorption.FiniteShift

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem mixed_vector_tendsto (s : C0Ball) (lev : Level) (b : Block lev) :
    Tendsto (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).vector lev b)
      (nhds (s,s)) (nhds ((stateWeights s).vector lev b)) := by
  classical
  have h1 : Tendsto (fun p : C0Ball × C0Ball => blockVector lev p.1 b) (nhds (s,s)) (nhds (blockVector lev s b)) :=
    ((blockVector_continuous lev b).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : C0Ball × C0Ball => blockVector lev p.2 b) (nhds (s,s)) (nhds (blockVector lev s b)) :=
    ((blockVector_continuous lev b).comp continuous_snd).continuousAt
  have he : (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).vector lev b)=
      (fun p : C0Ball × C0Ball => if localRadius lev p.2.val≤localRadius lev p.1.val then blockVector lev p.1 b else blockVector lev p.2 b) := by
    funext p
    dsimp only [mixedWeights,mixedState]
    split_ifs <;> rfl
  rw [he]
  exact h1.if' h2

theorem mixed_row_tendsto (s : C0Ball) (lev : Level) (b : Block lev) :
    Tendsto (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).row lev b)
      (nhds (s,s)) (nhds ((stateWeights s).row lev b)) := by
  classical
  have h1 : Tendsto (fun p : C0Ball × C0Ball => blockRow lev p.1 b) (nhds (s,s)) (nhds (blockRow lev s b)) :=
    ((blockRow_continuous lev b).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : C0Ball × C0Ball => blockRow lev p.2 b) (nhds (s,s)) (nhds (blockRow lev s b)) :=
    ((blockRow_continuous lev b).comp continuous_snd).continuousAt
  have he : (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).row lev b)=
      (fun p : C0Ball × C0Ball => if localRadius lev p.2.val≤localRadius lev p.1.val then blockRow lev p.1 b else blockRow lev p.2 b) := by
    funext p
    dsimp only [mixedWeights,mixedState]
    split_ifs <;> rfl
  rw [he]
  exact h1.if' h2

variable {N : ℕ}

theorem finiteRow_mixed_tendsto (s : C0Ball) (l : FLevel N) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finiteRow (mixedWeights p.1 p.2) l x)
      (nhds (s,s)) (nhds (finiteRow (stateWeights s) l x)) := by
  exact tendsto_finsetSum _ (fun b _ => (mixed_row_tendsto s _ b).mul_const _)

theorem finitePrev_mixed_tendsto (s : C0Ball) (l : FLevel N) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finitePrev (mixedWeights p.1 p.2) l x)
      (nhds (s,s)) (nhds (finitePrev (stateWeights s) l x)) := by
  unfold finitePrev
  split_ifs
  · exact tendsto_const_nhds
  · exact finiteRow_mixed_tendsto s _ x

theorem finiteFrozen_mixed_apply_tendsto (s : C0Ball) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finiteFrozen N (mixedWeights p.1 p.2) x)
      (nhds (s,s)) (nhds (finiteFrozen N (stateWeights s) x)) := by
  apply tendsto_pi_nhds.mpr
  rintro (i|⟨l,b⟩)
  · exact finiteRow_mixed_tendsto s (i,Fin.last N) x
  · exact tendsto_const_nhds.add ((mixed_vector_tendsto s _ b).mul
      ((finitePrev_mixed_tendsto s l x).sub (finiteRow_mixed_tendsto s l x)))

theorem finiteFrozen_mixed_tendsto (N : ℕ) (s : C0Ball) :
    Tendsto (fun p : C0Ball × C0Ball => finiteFrozen N (mixedWeights p.1 p.2))
      (nhds (s,s)) (nhds (finiteFrozen N (stateWeights s))) := by
  classical
  exact tendsto_finiteOperator_of_columns _ _ (fun a => finiteFrozen_mixed_apply_tendsto s _)

theorem normalizedBall_continuousAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x≠0) : ContinuousAt (@normalizedBall E _ _ ) x := by
  apply tendsto_subtype_rng.mpr
  exact (continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

theorem finite_normalized_continuousAt {x : FInput N} (hx : x≠0) :
    ContinuousAt (fun y => normalizedBall (finiteEmbed N y)) x := by
  have he : finiteEmbed N x≠0 := fun he => hx ((finiteEmbed N).injective (he.trans (map_zero _).symm))
  exact (normalizedBall_continuousAt he).comp (finiteEmbed N).continuous.continuousAt

theorem finite_mixed_operator_near {x : FInput N} (hx : x≠0) :
    ∃ s : Set (FInput N), s∈nhds x ∧ ∀ y∈s, ∀ z∈s,
      ‖finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N y)) (normalizedBall (finiteEmbed N z)))-
        finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x)))‖ < 1/20 := by
  exact diagonal_neighborhood (fun y => normalizedBall (finiteEmbed N y))
    (finite_normalized_continuousAt hx) (fun p => finiteFrozen N (mixedWeights p.1 p.2))
    (finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x))))
    (finiteFrozen_mixed_tendsto N _) (by norm_num)

theorem finiteRecomputed_local_onto {x : FInput N} (hx : x≠0) :
    Set.range (finiteRecomputed N)∈nhds (finiteRecomputed N x) := by
  let W := stateWeights (normalizedBall (finiteEmbed N x))
  let S := finiteEquiv N W
  obtain ⟨s,hs,hclose⟩ := finite_mixed_operator_near hx
  apply range_mem_nhds_of_approx S s hs (1/10)
  · have hh : ‖(S.symm : FInput N →L[ℝ] FInput N)‖₊≤5 := by
      exact_mod_cast finiteEquiv_symm_norm N W
    have hpos : 0<‖(S.symm : FInput N →L[ℝ] FInput N)‖₊ := by
      exact S.nnnorm_symm_pos
    rw [inv_eq_one_div,lt_div_iff₀ hpos]
    calc (1/10 : ℝ≥0)*‖(S.symm : FInput N →L[ℝ] FInput N)‖₊ ≤ (1/10)*5 := mul_le_mul_of_nonneg_left hh (by positivity)
         _ < 1 := by norm_num
  · intro y hy z hz
    let V := mixedWeights (normalizedBall (finiteEmbed N y)) (normalizedBall (finiteEmbed N z))
    have he : ‖finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N V (y-z)‖≤24*eta*dist y z :=
      finiteRecomputed_mixed_approx y z
    have hd : ‖(finiteFrozen N V-finiteFrozen N W) (y-z)‖≤(1/20)*dist y z := by
      apply ((finiteFrozen N V-finiteFrozen N W).le_opNorm (y-z)).trans
      rw [← dist_eq_norm y z]
      exact mul_le_mul_of_nonneg_right (hclose y hy z hz).le dist_nonneg
    have hid : finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N W (y-z)=
      (finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N V (y-z))+
        (finiteFrozen N V-finiteFrozen N W) (y-z) := by
      rw [sub_apply]
      abel
    change ‖finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N W (y-z)‖≤(1/10 : ℝ≥0)*‖y-z‖
    rw [hid]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ 24*eta*dist y z+(1/20)*dist y z := add_le_add he hd
      _ = (24*eta+1/20)*dist y z := by ring
      _ ≤ (1/10)*dist y z := mul_le_mul_of_nonneg_right (by norm_num [eta]) dist_nonneg
      _ = _ := by norm_num only [NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]; rw [dist_eq_norm]

end
end C0Absorption

end OAI
