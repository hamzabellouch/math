import OAI.Dynamics.StandardMap.MatchingAssembly

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma matching_of_shortfalls (M : ℝ) (vp vm : ℕ → ℝ) (bp bm : ℝ)
    (n Np Nm : ℕ) (hn : 1000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1)
    (hNm : n ≤ Nm ∧ Nm ≤ n+1) (hM : 1 < M)
    (hvp : ∀ j, 1 ≤ j → j < Np → |vp j|+1 ≤ M)
    (hvm : ∀ j, 1 ≤ j → j < Nm → |vm j|+1 ≤ M)
    (hshortp : (Np:ℝ)-1-pairLog M (tSolution vp) Np ≤ (n:ℝ)/1000)
    (hshortm : (Nm:ℝ)-1-pairLog M (tSolution vm) Nm ≤ (n:ℝ)/1000)
    (hbadp : (badIndices M vp bp Np).card ≤ n/1000)
    (hbadm : (badIndices M vm bm Nm).card ≤ n/1000) :
    ∃ (T : Finset ℕ) (f : ℕ → ℕ), n/100 ≤ T.card ∧
      (∀ j ∈ T, 2 ≤ j ∧ j ≤ Np-2 ∧ GoodIndex M vp bp j ∧
        2 ≤ f j ∧ f j ≤ Nm-2 ∧ GoodIndex M vm bm (f j) ∧
        |pairLog M (tSolution vp) j-pairLog M (tSolution vm) (f j)| ≤ 1/2) ∧
      (∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) := by
  classical
  let τ:=pairLog M (tSolution vp)
  let ρ:=pairLog M (tSolution vm)
  have hτstep (j : ℕ) (hj : 1 ≤ j) (hjN : j < Np) : τ (j+1)-τ j ≤ 1 :=
    (abs_le.mp (pairLog_step_abs M vp 0 1 j hM hj (hvp j hj hjN)
      (pairMagnitude_t_pos vp j hj) (pairMagnitude_t_pos vp (j+1) (by omega)))).2
  have hρstep (j : ℕ) (hj : 1 ≤ j) (hjN : j < Nm) : ρ (j+1)-ρ j ≤ 1 :=
    (abs_le.mp (pairLog_step_abs M vm 0 1 j hM hj (hvm j hj hjN)
      (pairMagnitude_t_pos vm j hj) (pairMagnitude_t_pos vm (j+1) (by omega)))).2
  have hτ1 : τ 1=0 := pairLog_t_one vp M
  have hρ1 : ρ 1=0 := pairLog_t_one vm M
  let I:=Finset.Icc (n/3) (n/2)
  let S:=I.filter fun j => GoodIndex M vp bp j
  let B:=badIndices M vm bm Nm
  have hI (j : ℕ) (hj : j ∈ I) : 2 ≤ j ∧ j ≤ Np-2 := by
    have hh:=Finset.mem_Icc.mp hj
    omega
  have hS (j : ℕ) (hj : j ∈ S) : j ∈ I ∧ GoodIndex M vp bp j := Finset.mem_filter.mp hj
  have hcard : n/2+1-n/3 ≤ S.card+n/1000 := by
    have hbad : (I.filter fun j => ¬GoodIndex M vp bp j).card ≤ (badIndices M vp bp Np).card := by
      apply Finset.card_le_card
      intro j hj
      obtain ⟨hj,hg⟩:=Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hI j hj),hg⟩
    have hh:=Finset.card_filter_add_card_filter_not (s := I) (fun j => GoodIndex M vp bp j)
    have hIc : I.card=n/2+1-n/3 := by simp [I,Nat.card_Icc]
    dsimp [S]
    omega
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hrange : ∀ j ∈ S, 1 < τ j ∧ τ j ≤ ρ (Nm-2) := by
    intro j hj
    have hjI:=Finset.mem_Icc.mp (hS j hj).1
    have hjbd:=hI j (hS j hj).1
    have hh:=log_path_bounds τ Np hτstep hτ1 j (by omega) (by omega)
    have hm:=log_path_bounds ρ Nm hρstep hρ1 (Nm-2) (by omega) (by omega)
    have hjlo : (n:ℝ)/3-1 ≤ j := by
      have hnat : n ≤ 3*j+2 := by omega
      have hreal : (n:ℝ) ≤ 3*(j:ℝ)+2 := by exact_mod_cast hnat
      linarith
    have hjhi : (j:ℝ) ≤ (n:ℝ)/2 := by
      have hnat : 2*j ≤ n := by omega
      have hreal : 2*(j:ℝ) ≤ n := by exact_mod_cast hnat
      linarith
    have hNmR : (n:ℝ) ≤ Nm := by exact_mod_cast hNm.1
    have he : ((Nm-2:ℕ):ℝ)=(Nm:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [he] at hm
    dsimp [τ,ρ] at *
    exact ⟨by linarith,by linarith⟩
  obtain ⟨T,f,hTS,hct,hmatch,hord⟩:=matching_subset S B τ ρ (Nm-2) goodExponent
    (by norm_num [goodExponent]) (by omega)
    (fun j hj hjN => hρstep j hj (by omega)) hρ1 hrange
    (by
      intro i hi j hj hij
      exact (hS j hj).2.2.1 i (by have := (hS i hi).2.1; omega) hij)
    (by
      intro i hi hiN hinB j hj hji
      have hgood : GoodIndex M vm bm i := by
        by_contra hnot
        exact hinB (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi,hiN⟩,hnot⟩)
      exact hgood.2.1 j (by omega) hji)
  refine ⟨T,f,?_,?_,hord⟩
  · dsimp [B] at hct
    omega
  · intro j hj
    have hp:=hS j (hTS hj)
    have hb:=hI j hp.1
    have hm:=hmatch j hj
    refine ⟨hb.1,hb.2,hp.2,hm.1,hm.2.1,?_,hm.2.2.2⟩
    by_contra hnot
    exact hm.2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm.1,hm.2.1⟩,hnot⟩)
end StandardMapEntropy

end OAI
