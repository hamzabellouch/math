import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.StageState
import OAI.Combinatorics.RamseyFive.Trees.Windows

namespace OAI

noncomputable section

namespace SharpRamseyFive.SelectedTuple.SelectedStream
open FiniteEntropy
open scoped Classical
variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]

def reindex {N n l : ℕ} {admissible : (Fin N→α)→Prop}
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) (e : Fin l↪o Fin n) :
    SelectedStream (Ω:=Ω) (β:=β) N l admissible where
  law:=S.law
  stream:=S.stream
  tuple:=fun a i=>S.tuple a (e i)
  reverse:=S.reverse
  view:=S.view
  selected:=by
    intro a ha
    apply occurrences_trans _ _ _ (S.selected a ha)
    apply sourceSequence_occurs
    exact (mem_occurrences_iff _ _).mpr ⟨e,fun _=>rfl⟩
  good:=S.good
  density:=S.density
  density_nonneg:=S.density_nonneg
  density_bound:=S.density_bound
end SharpRamseyFive.SelectedTuple.SelectedStream
namespace SharpRamseyFive.Windows
open scoped Classical

def middleEmbedding (w r : ℕ) : Fin (w*(2*r))↪o Fin (w*(4*r)) :=
  OrderEmbedding.ofStrictMono
    (fun i=>slotEmbedding (Sum.inr (finProdFinEquiv.symm i))) (by
      intro i j hij
      let a := finProdFinEquiv.symm i
      let b := finProdFinEquiv.symm j
      have hi : i.val=a.1.val*(2*r)+a.2.val := by
        calc
          _ = (finProdFinEquiv a).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i).symm
          _ = _ := by change a.2.val+(2*r)*a.1.val=_;ring
      have hj : j.val=b.1.val*(2*r)+b.2.val := by
        calc
          _ = (finProdFinEquiv b).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j).symm
          _ = _ := by change b.2.val+(2*r)*b.1.val=_;ring
      by_cases hab : a.1<b.1
      · exact ordered_windows _ _ hab
      · have hea : a.1=b.1 := by
          apply Fin.ext
          have ha:=a.2.isLt
          have hb:=b.2.isLt
          have hij' : a.1.val*(2*r)+a.2.val<b.1.val*(2*r)+b.2.val := by
            simpa only [Fin.lt_def,hi,hj] using hij
          have hle : b.1.val≤a.1.val := Nat.le_of_not_gt hab
          by_contra hn
          have hg : (b.1.val+1)*(2*r)≤a.1.val*(2*r) := by
            apply Nat.mul_le_mul_right
            omega
          nlinarith
        change slotEmbedding (Sum.inr a)<slotEmbedding (Sum.inr b)
        have hab' : a.2<b.2 := by
          have hh := hij
          simp only [Fin.lt_def,hi,hj,hea] at hh ⊢
          omega
        change slotEmbedding (Sum.inr (a.1,a.2))<slotEmbedding (Sum.inr (b.1,b.2))
        rw [←hea]
        exact middle_order _ _ _ hab')

lemma middleEmbedding_apply (w r : ℕ) (v : Fin w) (t : Fin (2*r)) :
    middleEmbedding w r (finProdFinEquiv (v,t))=slotEmbedding (Sum.inr (v,t)) := by
  change slotEmbedding (Sum.inr (finProdFinEquiv.symm (finProdFinEquiv (v,t))))=_
  rw [Equiv.symm_apply_apply]
end SharpRamseyFive.Windows

end

end OAI
