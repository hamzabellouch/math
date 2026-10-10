import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.Spectra
import OAI.Analysis.JiangSu.DimensionDrop.IteratedSpectrum
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixDiagonalComposition

namespace OAI


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction

def stageMultiplicities (n : ℕ) := multiplicities (pair n)
def IteratedIndex (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | k+1 => IteratedIndex n k × Index (stageMultiplicities (n+k))
instance iteratedFintype (n : ℕ) : (k : ℕ) → Fintype (IteratedIndex n k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k+1 => letI := iteratedFintype n k
    inferInstanceAs (Fintype (IteratedIndex n k × Index (stageMultiplicities (n+k))))
instance iteratedDecEq (n : ℕ) : (k : ℕ) → DecidableEq (IteratedIndex n k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => letI := iteratedDecEq n k
    inferInstanceAs (DecidableEq (IteratedIndex n k × Index (stageMultiplicities (n+k))))
instance iteratedNonempty (n : ℕ) : (k : ℕ) → Nonempty (IteratedIndex n k)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | k+1 =>
    letI := iteratedNonempty n k
    letI : Nonempty (Index (stageMultiplicities (n+k))) :=
      ⟨Sum.inl ⟨0,(stageMultiplicities (n+k)).lower_pos⟩⟩
    inferInstanceAs (Nonempty (IteratedIndex n k × Index (stageMultiplicities (n+k))))

def iteratedFamily (n : ℕ) : (k : ℕ) → IteratedIndex n k → C(Interval,Interval)
  | 0,_ => ContinuousMap.id _
  | k+1,z => (iteratedFamily n k z.1).comp (family (stageMultiplicities (n+k)) z.2)

lemma iterated_contract (n k : ℕ) (j : IteratedIndex n k) (s t : Interval) :
    |(iteratedFamily n k j s).1-(iteratedFamily n k j t).1|≤(1/2:ℝ)^k*|s.1-t.1| := by
  induction k generalizing s t with
  | zero => simp [iteratedFamily]
  | succ k ih =>
    change |(iteratedFamily n k j.1 (family (stageMultiplicities (n+k)) j.2 s)).1-
      (iteratedFamily n k j.1 (family (stageMultiplicities (n+k)) j.2 t)).1|≤_
    calc
      _≤(1/2:ℝ)^k*|(family (stageMultiplicities (n+k)) j.2 s).1-
        (family (stageMultiplicities (n+k)) j.2 t).1| := ih j.1 _ _
      _≤(1/2:ℝ)^k*(|s.1-t.1|/2) := mul_le_mul_of_nonneg_left (family_contract _ _ _ _) (by positivity)
      _=(1/2:ℝ)^(k+1)*|s.1-t.1| := by rw [pow_succ]; ring

lemma iterated_variation (n k : ℕ) (j : IteratedIndex n k) (s t : Interval) :
    dist (iteratedFamily n k j s) (iteratedFamily n k j t) ≤ (1/2:ℝ)^k := by
  have habs : |s.1-t.1|≤1 := by rw [abs_le]; constructor <;> linarith [s.2.1,s.2.2,t.2.1,t.2.2]
  exact (iterated_contract n k j s t).trans
    (mul_le_of_le_one_right (by positivity) habs)

open scoped CStarAlgebra ComplexOrder

local instance diagIteratedDecEq (n : ℕ) : (k : ℕ) → DecidableEq (IteratedIndex n k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => letI := diagIteratedDecEq n k
    inferInstanceAs (DecidableEq (IteratedIndex n k × Index (stageMultiplicities (n+k))))

def stepUnitary (n : ℕ) : C(Interval,unitary (TensorMat (pair (n+1)).p (pair (n+1)).q)) :=
  (finiteMatrixUnitaryPath
    (permutationUnitary ((zeroIndexEquiv (stageMultiplicities n)).symm.trans
      (zeroIndexEquiv (stageMultiplicities n))))
    (permutationUnitary ((zeroIndexEquiv (stageMultiplicities n)).symm.trans
      (oneIndexEquiv (stageMultiplicities n))))).toContinuousMap

lemma stageStep_eval (n : ℕ) (f : Stage n) (t : Interval) :
    (stageStep n f).val t=unitaryConjugation (stepUnitary n t)
      (CStarMatrix.reindexₐ ℂ ℂ (zeroIndexEquiv (stageMultiplicities n))
        (blockDiagonalHom (fun z => f.val (family (stageMultiplicities n) z t)))) := rfl

theorem iterate_diagonalization (n k : ℕ) :
    ∃ e : ((Fin (pair n).p×Fin (pair n).q)×IteratedIndex n k) ≃
        (Fin (pair (n+k)).p×Fin (pair (n+k)).q),
    ∃ V : C(Interval,unitary (TensorMat (pair (n+k)).p (pair (n+k)).q)),
    ∀ f : Stage n,∀ t : Interval,
      (system.map (Nat.le_add_right n k) f).val t=
        unitaryConjugation (V t) (CStarMatrix.reindexₐ ℂ ℂ e
          (blockDiagonalHom (fun i => f.val (iteratedFamily n k i t)))) := by
  classical
  induction k with
  | zero =>
    refine ⟨Equiv.prodPUnit _,1,?_⟩
    intro f t
    change (SequentialCStar.sequenceHom stageStep (le_refl n) f).val t=
      unitaryConjugation 1 (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodPUnit _)
        (blockDiagonalHom (fun _ : PUnit.{1} => f.val t)))
    rw [SequentialCStar.sequenceHom_self,unitaryConjugation_one,block_punit]
  | succ k ih =>
    obtain ⟨e,V,hV⟩ := ih
    let ξ := family (stageMultiplicities (n+k))
    let E := zeroIndexEquiv (stageMultiplicities (n+k))
    let R := (CStarMatrix.reindexₐ ℂ ℂ E).toStarAlgHom
    let e' := ((Equiv.prodAssoc (Fin (pair n).p×Fin (pair n).q)
      (IteratedIndex n k) (Index (stageMultiplicities (n+k)))).symm.trans
      (Equiv.prodCongr e (Equiv.refl _))).trans E
    let T := Fin (pair (n+k)).p×Fin (pair (n+k)).q
    let K := Index (stageMultiplicities (n+k))
    let B : C(Interval,unitary (CStarMatrix (T×K) (T×K) ℂ)) :=
      ⟨fun t => blockUnitary (fun z => V (ξ z t)),
        blockUnitary_continuous.comp (continuous_pi fun z => V.continuous.comp (ξ z).continuous)⟩
    let V' := stepUnitary (n+k) *
      (⟨fun t => homUnitary R (B t), (homUnitary_continuous R).comp B.continuous⟩ :
        C(Interval,unitary (TensorMat (pair (n+k+1)).p (pair (n+k+1)).q)))
    refine ⟨e',V',?_⟩
    intro f t
    change (SequentialCStar.sequenceHom stageStep
      ((Nat.le_add_right n k).trans (Nat.le_succ (n+k))) f).val t=_
    rw [SequentialCStar.sequenceHom_succ,stageStep_eval]
    change unitaryConjugation (stepUnitary (n+k) t)
      (R (blockDiagonalHom (fun z => (system.map (Nat.le_add_right n k) f).val (ξ z t))))=_
    have hfun : (fun z => (system.map (Nat.le_add_right n k) f).val (ξ z t))=
        (fun z => unitaryConjugation (V (ξ z t)) (CStarMatrix.reindexₐ ℂ ℂ e
          (blockDiagonalHom (fun i => f.val (iteratedFamily n k i (ξ z t)))))) := by
      funext z
      exact hV f (ξ z t)
    rw [hfun]
    exact diagonalization_comp (stepUnitary (n+k) t) (fun z => V (ξ z t)) e E
      (fun i : IteratedIndex n k×Index (stageMultiplicities (n+k)) =>
        f.val (iteratedFamily n k i.1 (ξ i.2 t)))

end OriginalJiangSu

end

end OAI
