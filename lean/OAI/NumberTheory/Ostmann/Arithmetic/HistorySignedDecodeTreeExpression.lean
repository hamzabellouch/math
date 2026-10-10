import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeRebuild
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeTreeExpressionBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPositiveSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicEncoding
open HistoryOccurrenceVariables
variable {ι : Type*}

def TreeGiantsAgree (x : ι → ℝ) : {l : ℕ} → (h : History l) →
    TreeExpr ι h → SignedHistory l → Prop
  | _, .leaf _, e, .leaf b =>
    e.plus.realEval x = (b.giantPlus : ℝ) ∧ e.minus.realEval x = (b.giantMinus : ℝ)
  | _, .node _ _ _ _ _ left right, e, .node b _ _ _ _ left' right' =>
    e.1.plus.realEval x = (b.giantPlus : ℝ) ∧ e.1.minus.realEval x = (b.giantMinus : ℝ) ∧
      TreeGiantsAgree x left e.2.1 left' ∧ TreeGiantsAgree x right e.2.2 right'

theorem TreeGiantsAgree.root {x : ι → ℝ} {l : ℕ} {h : History l}
    {e : TreeExpr ι h} {h' : SignedHistory l} (he : TreeGiantsAgree x h e h') :
    (treeRoot h e).plus.realEval x = (h'.root.giantPlus : ℝ) ∧
      (treeRoot h e).minus.realEval x = (h'.root.giantMinus : ℝ) := by
  cases h <;> cases h'
  · exact he
  · exact ⟨he.1, he.2.1⟩

theorem encode_rebuild_giantsAgree {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp : ℝ)) (heminus : e.minus.realEval x = (Xm : ℝ))
    (he : SmallRealValues x h.root.small e.small)
    (hc : ∀ i, (comp i).realEval x = ((internalSlot h i).value : ℝ))
    (hi : (rebuild h Xp Xm).IntegralGuard) :
    TreeGiantsAgree x h (encode V outside h hs e comp) (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a => exact ⟨heplus, heminus⟩
  | @node l a p u hp hm left right ihl ihr =>
    have hu : SmallRealValues x u (fun i => comp (Sum.inl i)) := by
      intro i
      simpa only [internalSlot, Sum.elim_inl] using hc (Sum.inl i)
    have hguard := hi
    simp only [rebuild, SignedHistory.IntegralGuard, rebuild_root] at hguard
    have hpiv := pivotExpr_realEval_eq_signedPivot hs e (fun i => comp (Sum.inl i))
      x Xp Xm heplus heminus he hu hguard.1 hguard.2.1
    have hsmall := children_smallRealValues hs e (fun i => comp (Sum.inl i)) x he hu
    refine ⟨heplus, heminus, ?_, ?_⟩
    · exact ihl (History.supported_left hs) _ _ _ _ hpiv heplus hsmall.1
        (fun i => by
          simpa only [internalSlot, Sum.elim_inr, Sum.elim_inl] using hc (Sum.inr (Sum.inl i))) hguard.2.2.1
    · exact ihr (History.supported_right hs) _ _ _ _ hpiv heminus hsmall.2
        (fun i => by
          simpa only [internalSlot, Sum.elim_inr] using hc (Sum.inr (Sum.inr i))) hguard.2.2.2

theorem TreeGiantsAgree.allPivotsPositive_iff {x : ι → ℝ} {l : ℕ}
    (h : History l) (e : TreeExpr ι h) (Xp Xm : ℤ)
    (he : TreeGiantsAgree x h e (rebuild h Xp Xm)) :
    AllPivotsPositive x h e ↔ (rebuild h Xp Xm).PivotsPositive := by
  induction h generalizing Xp Xm with
  | leaf a => rfl
  | @node l a p u hp hm left right ihl ihr =>
    have hl := he.2.2.1
    have hr := he.2.2.2
    have hpiv := hl.root.1
    rw [rebuild_root] at hpiv
    simp only [AllPivotsPositive, AllPivots, rebuild, SignedHistory.PivotsPositive]
    rw [hpiv]
    have hleft := ihl e.2.1 _ _ hl
    have hright := ihr e.2.2 _ _ hr
    simpa only [AllPivotsPositive, Int.cast_pos] using
      and_congr Iff.rfl (and_congr hleft hright)

theorem encode_allPivotsPositive_iff_rebuild {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp : ℝ)) (heminus : e.minus.realEval x = (Xm : ℝ))
    (he : SmallRealValues x h.root.small e.small)
    (hc : ∀ i, (comp i).realEval x = ((internalSlot h i).value : ℝ))
    (hi : (rebuild h Xp Xm).IntegralGuard) :
    AllPivotsPositive x h (encode V outside h hs e comp) ↔
      (rebuild h Xp Xm).PivotsPositive :=
  TreeGiantsAgree.allPivotsPositive_iff h _ Xp Xm
    (encode_rebuild_giantsAgree h hs e comp x Xp Xm heplus heminus he hc hi)

theorem encode_rebuild_nonnegative {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp : ℝ)) (heminus : e.minus.realEval x = (Xm : ℝ))
    (he : SmallRealValues x h.root.small e.small)
    (hc : ∀ i, (comp i).realEval x = ((internalSlot h i).value : ℝ))
    (hi : (rebuild h Xp Xm).IntegralGuard) (hp : 0 ≤ Xp) (hm : 0 ≤ Xm)
    (hpos : AllPivotsPositive x h (encode V outside h hs e comp)) :
    (rebuild h Xp Xm).Nonnegative :=
  rebuild_nonnegative_of_pivotsPositive h Xp Xm hp hm
    ((TreeGiantsAgree.allPivotsPositive_iff h _ Xp Xm
      (encode_rebuild_giantsAgree h hs e comp x Xp Xm heplus heminus he hc hi)).mp hpos)

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
