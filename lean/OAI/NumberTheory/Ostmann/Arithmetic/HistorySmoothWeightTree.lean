import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightState

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
open scoped FourierTransform SchwartzMap
variable {ι : Type*}

def treeRoot : {l : ℕ} → (h : History l) → TreeExpr ι h → StateExpr h.root ι
  | _, .leaf _, e => e
  | _, .node _ _ _ _ _ _ _, e => e.1

theorem treeCorrect_root (x : ι → ℚ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (he : TreeCorrect x h e) : (treeRoot h e).Correct x := by
  cases h with
  | leaf a => exact he
  | node a p u hp hm left right => exact he.1

def realHistoryScalar (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ) (x : ι → ℝ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → ℂ
  | _, .leaf _, e => e.realScalar b s X tb td outside x
  | _, .node _ _ _ _ _ left right, e =>
      (giantCell G ((treeRoot left e.2.1).plus.realEval x):ℂ) *
        realHistoryScalar b s X tb td G outside x left e.2.1 *
        star (realHistoryScalar b s X tb td G outside x right e.2.2)

theorem smoothHistoryScalar_node (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} (a : State) (p : ℕ) (u hp hm : List SmallSlot) (left right : History l) :
    smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
      outside smoothPartition G (.node a p u hp hm left right) =
      (smoothPartition (Real.log p-G):ℂ) *
        smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
          outside smoothPartition G left *
        star (smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
          outside smoothPartition G right) := by
  simp only [smoothHistoryScalar,History.cellWeight,History.leafProduct,Complex.ofReal_mul,
    star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

theorem realHistoryScalar_correct (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (e : TreeExpr ι h) (x : ι → ℚ) (he : TreeCorrect x h e) :
    realHistoryScalar b s X tb td G outside (fun i => (x i:ℝ)) h e =
      smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
        outside smoothPartition G h := by
  induction h with
  | leaf a =>
    simpa only [realHistoryScalar,smoothHistoryScalar,History.cellWeight,History.leafProduct,
      Complex.ofReal_one,one_mul] using e.realScalar_correct b s X tb td outside x he
  | @node l a p u hp hm left right ihl ihr =>
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast History.supported_pivot_pos hs
    have hpiv : (treeRoot left e.2.1).plus.realEval (fun i => (x i:ℝ)) = (p:ℝ) := by
      rw [Expr.realEval_cast_rational,(treeCorrect_root x left e.2.1 he.2.1).2.1,
        (History.supported_child_giants hs).1,Rat.cast_natCast]
    rw [realHistoryScalar,hpiv,giantCell,ite_eq_left hp0,
      ihl (History.supported_left hs) e.2.1 he.2.1,
      ihr (History.supported_right hs) e.2.2 he.2.2]
    exact (smoothHistoryScalar_node b s X tb td G outside a p u hp hm left right).symm

def actualRealHistoryScalar (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) (x : Key h → ℝ) : ℂ :=
  realHistoryScalar b s X tb td G outside x h (symbolicHistory h hs)

theorem actualRealHistoryScalar_integer_sample (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) :
    actualRealHistoryScalar b s X tb td G outside h hs (fun i => (rationalSample h i:ℝ)) =
      smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
        outside smoothPartition G h :=
  realHistoryScalar_correct b s X tb td G outside h hs (symbolicHistory h hs) _
    (symbolicHistory_correct h hs)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
