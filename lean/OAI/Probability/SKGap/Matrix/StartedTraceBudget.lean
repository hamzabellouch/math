import Mathlib
import OAI.Probability.SKGap.Localization.LocalStartedDiagonal

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ}

def startedTraceBudget (c k : ℝ) (W : ℕ→ℝ) (B : ℝ) (a : ℕ) : ℝ :=
  c*W a+k*∑b:Fin a,startedTraceBudget c k W B b+B
termination_by a
lemma startedTraceBudget_nonneg {c k B : ℝ} {W : ℕ→ℝ}
    (hc : 0≤c) (hk : 0≤k) (hW : ∀a,0≤W a) (hB : 0≤B) (a : ℕ) :
    0≤ startedTraceBudget c k W B a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [startedTraceBudget]
    exact add_nonneg (add_nonneg (mul_nonneg hc (hW a))
      (mul_nonneg hk (Finset.sum_nonneg fun b _=>ih b b.isLt))) hB
lemma startedTraceBudget_ge {c k B : ℝ} {W : ℕ→ℝ}
    (hc : 0≤c) (hk : 0≤k) (hW : ∀a,0≤W a) (hB : 0≤B) (a : ℕ) :
    B≤ startedTraceBudget c k W B a := by
  rw [startedTraceBudget]
  exact le_add_of_nonneg_left (add_nonneg (mul_nonneg hc (hW a))
      (mul_nonneg hk (Finset.sum_nonneg fun b _=>startedTraceBudget_nonneg hc hk hW hB b)))

namespace OrdinaryData
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

theorem startedMarked_budget (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ))
    (t₀ : SmallTree n) (a₀ : Fin n→ℝ) (x : Spin n) (N : ℕ)
    (W : ℕ→ℝ) {A Q B : ℝ} (hA : 0≤A) (hQ : 0≤Q) (hB : 0≤B) (hW : ∀a,0≤W a)
    (hinit : pairBudget (t₀.marked D.j a₀)≤B)
    (hp : ∀a≤N,∀l,vectorNorm (D.startedPartial w y a l x)≤W a)
    (hm : ∀l,Marked.mass (GradedWords.ordinaryWords D.j (T l)).1≤Q ∧
      Marked.mass (GradedWords.ordinaryWords D.j (T l)).2≤Q)
    (ha : ∀a≤N,∀b:Fin a,|siteMean (D.auxCoefficient a b) x|≤A) :
    ∀a≤N,pairBudget ((D.startedSmallTree w y T t₀ x a).marked D.j a₀)≤
      startedTraceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *A) W B a := by
  let L : ℝ:=(2+|D.j|)*Q
  let K : ℝ:=2+|D.j| *A
  have hL : 0≤L:=by dsimp [L];positivity
  have hK : 0≤K:=by dsimp [K];positivity
  have hc : 0≤(Fintype.card ι:ℝ)*L:=mul_nonneg (Nat.cast_nonneg _) hL
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    rcases a with _|r
    · simpa only [startedSmallTree] using hinit.trans (startedTraceBudget_ge hc hK hW hB 0)
    · rw [startedSmallTree,SmallTree.smallBranches_budget]
      have hsmall : (List.map (fun t : (Fin n→ℝ)×ClosedTree (Fin n→ℝ)=>vectorNorm t.1*
          (2*Marked.mass (t.2.words D.j a₀).2+|D.j| *Marked.mass (t.2.words D.j a₀).1))
            (Finset.univ.toList.map (fun l=>(D.startedPartial w y (r+1) l x,ClosedTree.ofOrdinary (T l))))).sum≤
          (Fintype.card ι:ℝ)*(L*W (r+1)) := by
        simp only [List.map_map,Function.comp_def,ClosedTree.words_ofOrdinary]
        simp only [Finset.sum_map_toList]
        have hs : (∑l:ι,vectorNorm (D.startedPartial w y (r+1) l x)*
            (2*Marked.mass (GradedWords.ordinaryWords D.j (T l)).2+|D.j| *Marked.mass (GradedWords.ordinaryWords D.j (T l)).1))≤∑_l:ι,L*W (r+1) := by
          apply Finset.sum_le_sum
          intro l _
          have hc' : 2*Marked.mass (GradedWords.ordinaryWords D.j (T l)).2+
              |D.j| *Marked.mass (GradedWords.ordinaryWords D.j (T l)).1≤L := by
            nlinarith [(hm l).2,mul_le_mul_of_nonneg_left (hm l).1 (abs_nonneg D.j)]
          exact (mul_le_mul_of_nonneg_left hc' (vectorNorm_nonneg _)).trans
            (by simpa [mul_comm] using mul_le_mul_of_nonneg_right (hp (r+1) haN l) hL)
        simpa using hs
      have H:=SmallTree.boundedBranches_budget D.j a₀
        (Finset.univ.toList.map (fun b:Fin (r+1)=>(D.auxCoefficient (r+1) b x,D.startedSmallTree w y T t₀ x b))) .zero
        (A:=A) (by
          intro t ht
          obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
          simpa only [siteMean,Diagram.mean,Fintype.card_fin] using ha (r+1) haN b)
      have hzero : pairBudget ((SmallTree.zero (n:=n)).marked D.j a₀)=0 := by
        simp [SmallTree.marked,zeroPair,pairBudget,Marked.budget,Mark.vector]
      rw [hzero,add_zero] at H
      simp only [List.map_map,Function.comp_def] at H
      have hs : (List.map (fun b:Fin (r+1)=>K*pairBudget ((D.startedSmallTree w y T t₀ x b).marked D.j a₀))
          Finset.univ.toList).sum≤K*∑b:Fin (r+1),startedTraceBudget ((Fintype.card ι:ℝ)*L) K W B b := by
        simp only [Finset.sum_map_toList]
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun b _=>mul_le_mul_of_nonneg_left (ih b b.isLt (b.isLt.le.trans haN)) hK
      have H' := H.trans hs
      apply (add_le_add hsmall H').trans
      rw [startedTraceBudget]
      change (Fintype.card ι:ℝ)*(L*W (r+1))+K*∑b:Fin (r+1),startedTraceBudget ((Fintype.card ι:ℝ)*L) K W B b≤_
      nlinarith only [hB]

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
