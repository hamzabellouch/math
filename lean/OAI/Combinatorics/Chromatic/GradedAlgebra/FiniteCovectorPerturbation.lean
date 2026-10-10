import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ChartRefinement

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]

lemma real_lex_epsilon (a b : ℝ) : ∃ε>0,∀δ:ℝ,0<δ→δ<ε→
    (0<a→0<a+δ*b) ∧ (a<0→a+δ*b<0) ∧
      (a=0→(0<b→0<a+δ*b) ∧ (b=0→a+δ*b=0) ∧ (b<0→a+δ*b<0)) :=by
  by_cases ha : a=0
  · refine ⟨1,one_pos,?_⟩
    intro δ hδ hδ1
    subst a
    constructor
    · intro h; exact False.elim (lt_irrefl 0 h)
    constructor
    · intro h; exact False.elim (lt_irrefl 0 h)
    · intro h
      exact ⟨fun hb=>by nlinarith,fun hb=>by simp [hb],fun hb=>by nlinarith⟩
  · have hden : 0 < |b|+1:=by positivity
    refine ⟨|a|/(|b|+1),div_pos (abs_pos.mpr ha) hden,?_⟩
    intro δ hδ hδε
    have he:= (lt_div_iff₀ hden).mp hδε
    have hbound : δ*|b| < |a|:=by nlinarith
    have hlo:=mul_le_mul_of_nonneg_left (neg_abs_le b) hδ.le
    have hhi:=mul_le_mul_of_nonneg_left (le_abs_self b) hδ.le
    constructor
    · intro h
      rw [abs_of_pos h] at hbound
      nlinarith
    constructor
    · intro h
      rw [abs_of_neg h] at hbound
      nlinarith
    · exact fun h=>False.elim (ha h)

lemma finite_lex_epsilon (S : Finset M) (h k : M→+ℝ) :
    ∃ε>0,∀δ:ℝ,0<δ→δ<ε→∀m∈S,LexSigns h k (h+δ • k) m :=by
  classical
  induction S using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,fun _ _ _ _ hm=>False.elim (Finset.notMem_empty _ hm)⟩
  | @insert m S hm ih=>
    obtain ⟨ε,hε,Hε⟩:=ih
    obtain ⟨η,hη,Hη⟩:=real_lex_epsilon (h m) (k m)
    refine ⟨min ε η,lt_min hε hη,?_⟩
    intro δ hδ hd x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Hη δ hδ (lt_of_lt_of_le hd (min_le_right _ _))
    · exact Hε δ hδ (lt_of_lt_of_le hd (min_le_left _ _)) x hx

def rootsThrough (C : (I→ℤ)→+M) (N : ℕ) : Finset M :=
  by
  classical
  exact (Finset.range (N+1)).biUnion (fun n=>(rootDegree_finite C n).toFinset)

lemma mem_rootsThrough (C : (I→ℤ)→+M) (N n : ℕ) (hn : n≤N) (m : M)
    (hm : HasRootDegree C n m) : m∈rootsThrough C N :=by
  classical
  unfold rootsThrough
  apply Finset.mem_biUnion.mpr
  exact ⟨n,Finset.mem_range.mpr (by omega),by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hm⟩

lemma root_lex_epsilon (C : (I→ℤ)→+M) (N : ℕ) (h k : M→+ℝ) :
    ∃ε>0,∀δ:ℝ,0<δ→δ<ε→∀n≤N,∀m,HasRootDegree C n m→LexSigns h k (h+δ • k) m :=by
  obtain ⟨ε,hε,Hε⟩:=finite_lex_epsilon (rootsThrough C N) h k
  exact ⟨ε,hε,fun δ hδ hd n hn m hm=>Hε δ hδ hd m (mem_rootsThrough C N n hn m hm)⟩

open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

theorem incoming_nearby_log (hΩ : ∀m,Ω m m=0) (r : M) (k : M→+ℝ) (hk : k r=0)
    (F : CompletedPositive v Ω C) (N : ℕ) :
    ∃ε>0,∀δ:ℝ,0<δ→δ<ε→∀n≤N,
      coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω r+δ • k) F).val) r=
      coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω r) F).val) r :=by
  obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N (incomingCovector Ω r) k
  refine ⟨ε,hε,?_⟩
  intro δ hδ hd n hn
  have H:=chart_zero_refinement v Ω C (incomingCovector Ω r) k
    (incomingCovector Ω r+δ • k) F N (Hε δ hδ hd)
  have Hlog:=FormalLog.log_coeff_congr
    (chartZero v Ω C (incomingCovector Ω r+δ • k) F).val
    (chartZero v Ω C k (chartZero v Ω C (incomingCovector Ω r) F)).val n
    (fun j hj=>H j (hj.trans hn))
  rw [Hlog]
  exact incoming_displacement_log v Ω C hΩ r k hk F n
end
end ElementaryPositivity.QuantumTorus

end

end OAI
