import OAI.Analysis.C0Absorption.Continuity

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem finiteRecomputed_surjective (N : ℕ) (hN : 0 < N) : Function.Surjective (finiteRecomputed N) := by
  apply surjective_of_punctured_local_onto (finiteRecomputed N)
    (finiteRecomputed_antilipschitz N) (finiteRecomputed_lipschitz N) (finiteRecomputed_zero N)
  · apply (isConnected_compl_singleton_of_one_lt_rank (E := FInput N) _ 0).isPreconnected
    change 1 < Module.rank ℝ (FCoord N → ℝ)
    rw [rank_fun']
    have hh : 1 < Fintype.card (FCoord N) := by
      change 1 < Fintype.card (Sum (Fin (N+1)) (FLabel N))
      rw [Fintype.card_sum,Fintype.card_fin]
      omega
    exact_mod_cast hh
  · exact fun x hx => finiteRecomputed_local_onto hx

variable {N : ℕ}

def finiteTarget (N : ℕ) (y : BlockC0) : FInput N := Sum.elim (fun _ => 0) (fun γ => y (fLabel γ))

theorem finiteRecomputed_block (x : FInput N) (γ : FLabel N) :
    finiteRecomputed N x (.inr γ)=recomputedShift (finiteEmbed N x) (fLabel γ) :=
  finiteFrozen_block _ x γ

theorem finiteRecomputed_row (x : FInput N) (i : Fin (N+1)) :
    finiteRecomputed N x (.inl i)=
      rowScalar (stateWeights (normalizedBall (finiteEmbed N x))) (i.val,N) (finiteEmbed N x) :=
  finiteRow_eq _ (i,Fin.last N) x

theorem finiteEmbed_rowScalar_outside (W : FrozenWeights) (x : FInput N) (lev : Level)
    (hl : N < lev.1 ∨ N < lev.2) : rowScalar W lev (finiteEmbed N x)=0 := by
  classical
  rw [rowScalar_apply]
  apply Finset.sum_eq_zero
  intro b hb
  change W.row lev b*finiteEmbed N x (labelIndex (blockLabel lev b))=0
  rw [finiteEmbed_block_outside x (blockLabel lev b) hl,mul_zero]

theorem finite_solution_gives_infinite (y : BlockC0) (x : FInput N)
    (hy : ∀ γ : Label, N < γ.level.1 ∨ N < γ.level.2 → y γ=0)
    (hx : finiteRecomputed N x=finiteTarget N y) : recomputedShift (finiteEmbed N x)=y := by
  let W := stateWeights (normalizedBall (finiteEmbed N x))
  have hterminal (i : ℕ) (hi : i≤N) : rowScalar W (i,N) (finiteEmbed N x)=0 := by
    have hh := congrFun hx (.inl ⟨i,by omega⟩)
    rw [finiteRecomputed_row] at hh
    exact hh
  ext γ
  by_cases hγ : γ.level.1≤N ∧ γ.level.2≤N
  · let l : FLevel N := (⟨γ.level.1,by omega⟩,⟨γ.level.2,by omega⟩)
    let b : Block (l.1.val,l.2.val) := ⟨γ.band,γ.tag⟩
    let δ : FLabel N := ⟨l,b⟩
    have he : fLabel δ=γ := by cases γ; rfl
    have hh := congrFun hx (.inr δ)
    rw [finiteRecomputed_block] at hh
    change recomputedShift (finiteEmbed N x) (fLabel δ)=y (fLabel δ) at hh
    simpa only [he] using hh
  · have hout : N < γ.level.1 ∨ N < γ.level.2 := by omega
    rw [hy γ hout]
    change frozenShift W (finiteEmbed N x) γ=0
    rw [frozenShift_apply,finiteEmbed_block_outside x γ hout,frozenCorrection_apply,
      finiteEmbed_rowScalar_outside W x γ.level hout]
    have hp : previousScalar W γ.level (finiteEmbed N x)=0 := by
      rcases hl : γ.level with ⟨i,n⟩
      rw [hl] at hout
      change N < i ∨ N < n at hout
      cases n with
      | zero =>
        change finiteEmbed N x (rowIndex i)=0
        exact finiteEmbed_row_outside x i (by omega)
      | succ n =>
        change rowScalar W (i,n) (finiteEmbed N x)=0
        by_cases hi : N < i
        · exact finiteEmbed_rowScalar_outside W x _ (Or.inl hi)
        · by_cases hn : n=N
          · subst n
            exact hterminal i (by omega)
          · exact finiteEmbed_rowScalar_outside W x _ (Or.inr (by omega))
    rw [hp]
    ring

theorem finite_target_mem_range (N : ℕ) (hN : 0 < N) (y : BlockC0)
    (hy : ∀ γ : Label, N < γ.level.1 ∨ N < γ.level.2 → y γ=0) : y∈Set.range recomputedShift := by
  obtain ⟨x,hx⟩ := finiteRecomputed_surjective N hN (finiteTarget N y)
  exact ⟨finiteEmbed N x,finite_solution_gives_infinite y x hy hx⟩

def blockSquare (N : ℕ) (y : BlockC0) : BlockC0 :=
  cfunOfTendsto (fun γ => if γ.level.1≤N ∧ γ.level.2≤N then y γ else 0)
    ((cfun_tendsto y).if' tendsto_const_nhds)

@[simp] theorem blockSquare_apply (N : ℕ) (y : BlockC0) (γ : Label) :
    blockSquare N y γ=if γ.level.1≤N ∧ γ.level.2≤N then y γ else 0 := rfl

theorem blockSquare_outside (N : ℕ) (y : BlockC0) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : blockSquare N y γ=0 := by
  rw [blockSquare_apply,ite_eq_right (by omega)]

theorem blockSquare_tendsto (y : BlockC0) : Tendsto (fun N => blockSquare N y) atTop (nhds y) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : ∀ᶠ γ in cofinite, |y γ|<ε/2 := by
    have hh := Metric.tendsto_nhds.mp (cfun_tendsto y) (ε/2) (half_pos hε)
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hh
  have hfin : {γ : Label | ε/2≤|y γ|}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp hsmall
  let S := hfin.toFinset
  let M := S.sup (fun γ => max γ.level.1 γ.level.2)
  refine ⟨M,fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply cfun_norm_le _ (half_pos hε).le
  intro γ
  change |blockSquare n y γ-y γ|≤ε/2
  rw [blockSquare_apply]
  split_ifs with hγ
  · simpa only [sub_self,abs_zero] using (half_pos hε).le
  · simp only [zero_sub,abs_neg]
    apply le_of_lt
    by_contra hbad
    have hmem : γ∈S := hfin.mem_toFinset.mpr (le_of_not_gt hbad)
    have hb : max γ.level.1 γ.level.2≤M := Finset.le_sup (f := fun γ : Label => max γ.level.1 γ.level.2) hmem
    have h1 := (le_max_left γ.level.1 γ.level.2).trans (hb.trans hn)
    have h2 := (le_max_right γ.level.1 γ.level.2).trans (hb.trans hn)
    exact hγ ⟨h1,h2⟩

theorem recomputedShift_surjective : Function.Surjective recomputedShift := by
  have hclosed : IsClosed (Set.range recomputedShift) :=
    recomputed_antilipschitz.isClosed_range recomputed_lipschitz.uniformContinuous
  intro y
  apply hclosed.mem_of_tendsto (blockSquare_tendsto y)
  apply Filter.eventually_atTop.mpr
  refine ⟨1,fun N hN => finite_target_mem_range N (by omega) (blockSquare N y) ?_⟩
  exact blockSquare_outside N y

end
end C0Absorption

end OAI
