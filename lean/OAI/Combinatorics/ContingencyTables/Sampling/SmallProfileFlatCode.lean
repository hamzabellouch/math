import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileCode
import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeCandidates

namespace OAI

/-! # Flattening the two stored views for coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def flattenViews (z : List ℕ×List ℕ) : List ℕ := z.1++z.2

def flattenViewsRealizer : Realizer flattenViews := append

theorem polynomial_flattenViews : PolynomialTime flattenViewsRealizer := polynomial_append

def splitViews (z : ℕ×List ℕ) : List ℕ×List ℕ := (z.2.take z.1,z.2.drop z.1)

def splitViewsRealizer : Realizer splitViews :=
  pair (composition (pair second first) takeFast) (composition (pair second first) dropFast)

theorem polynomial_splitViews : PolynomialTime splitViewsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_dropFast)

lemma split_flattenViews (v : List ℕ×List ℕ) :
    splitViews (v.1.length,flattenViews v)=v := by
  simp only [splitViews,flattenViews,List.take_left,List.drop_left,Prod.mk.eta]

def codeExchange (z : (List ℕ×List ℕ)×(ℕ×ℕ)) : List ℕ×List ℕ :=
  splitViews (z.1.1.length,listExchange (flattenViews z.1,z.2))

def codeExchangeRealizer : Realizer codeExchange :=
  composition (pair (composition (composition first first) listLength)
    (composition (pair (composition first flattenViewsRealizer) second) listExchangeRealizer))
      splitViewsRealizer

theorem polynomial_codeExchange : PolynomialTime codeExchangeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_flattenViews) polynomial_second)
      polynomial_listExchange)) polynomial_splitViews

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms
open IntegerWeightedTransport

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def sumViewEquiv : (Fin q⊕Fin q) ≃ Cells small×Bool where
  toFun
    | .inl i => (e i,false)
    | .inr i => (e i,true)
  invFun a := if a.2 then .inr (e.symm a.1) else .inl (e.symm a.1)
  left_inv a := by cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,Equiv.symm_apply_apply]
  right_inv a := by rcases a with ⟨a,b⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,
    ite_true,Equiv.apply_symm_apply]

def flatViewEquiv : Fin (q+q) ≃ Cells small×Bool :=
  finSumFinEquiv.symm.trans (sumViewEquiv small e)

lemma flatten_profileCode (z : SmallProfile small) :
    flattenViews (profileCode small e z)=List.ofFn (fun i => z (flatViewEquiv small e i)) := by
  rw [List.ofFn_add]
  unfold flattenViews profileCode viewList
  congr 1
  · apply congrArg List.ofFn
    funext i
    change z (e i,false)=z (sumViewEquiv small e (finSumFinEquiv.symm (Fin.castAdd q i)))
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  · apply congrArg List.ofFn
    funext i
    change z (e i,true)=z (sumViewEquiv small e (finSumFinEquiv.symm (Fin.natAdd q i)))
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

theorem codeExchange_eq (z : SmallProfile small) (i j : Fin (q+q)) :
    codeExchange (profileCode small e z,(i.val,j.val))=
      profileCode small e (exchangeTarget z (flatViewEquiv small e i) (flatViewEquiv small e j)) := by
  have he : exchangeTarget (fun a => z (flatViewEquiv small e a)) i j=
      fun a => exchangeTarget z (flatViewEquiv small e i) (flatViewEquiv small e j)
        (flatViewEquiv small e a) := by
    funext a
    simp only [exchangeTarget,(flatViewEquiv small e).injective.eq_iff]
  unfold codeExchange
  rw [flatten_profileCode,listExchange_ofFn,he,←flatten_profileCode]
  simpa only [profileCode,viewList,List.length_ofFn] using
    split_flattenViews (profileCode small e
      (exchangeTarget z (flatViewEquiv small e i) (flatViewEquiv small e j)))

end
end ContingencyTables.SmallGraphProfiles

end OAI
