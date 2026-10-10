import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.ActualNormalizedMatching
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixDiagonalComposition

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

local instance iteratedIndexDecEq (n : ℕ) : (k : ℕ) → DecidableEq (IteratedIndex n k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => letI := iteratedIndexDecEq n k
    inferInstanceAs (DecidableEq (IteratedIndex n k × SpectralIndex (stageMultiplicities (n+k))))

def stepUnitary (n : ℕ) : C(Interval,unitary (TensorMat (stagePair (n+1)).p (stagePair (n+1)).q)) :=
  (finiteMatrixUnitaryPath
    (permutationUnitary ((zeroIndexEquiv (stageMultiplicities n)).symm.trans
      (zeroIndexEquiv (stageMultiplicities n))))
    (permutationUnitary ((zeroIndexEquiv (stageMultiplicities n)).symm.trans
      (oneIndexEquiv (stageMultiplicities n))))).toContinuousMap

lemma stageStep_eval (n : ℕ) (f : StageAlgebra n) (t : Interval) :
    (stageStep n f).val t=unitaryConjugation (stepUnitary n t)
      (CStarMatrix.reindexₐ ℂ ℂ (zeroIndexEquiv (stageMultiplicities n))
        (blockDiagonalHom (fun z => f.val (spectralFamily (stageMultiplicities n) z t)))) := rfl

theorem concrete_iterate_diagonalization (n k : ℕ) :
    ∃ e : ((Fin (stagePair n).p×Fin (stagePair n).q)×IteratedIndex n k) ≃
        (Fin (stagePair (n+k)).p×Fin (stagePair (n+k)).q),
    ∃ V : C(Interval,unitary (TensorMat (stagePair (n+k)).p (stagePair (n+k)).q)),
    ∀ f : StageAlgebra n,∀ t : Interval,
      (concreteSystem.map (Nat.le_add_right n k) f).val t=
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
    let ξ := spectralFamily (stageMultiplicities (n+k))
    let E := zeroIndexEquiv (stageMultiplicities (n+k))
    let R := (CStarMatrix.reindexₐ ℂ ℂ E).toStarAlgHom
    let e' := ((Equiv.prodAssoc (Fin (stagePair n).p×Fin (stagePair n).q)
      (IteratedIndex n k) (SpectralIndex (stageMultiplicities (n+k)))).symm.trans
      (Equiv.prodCongr e (Equiv.refl _))).trans E
    let T := Fin (stagePair (n+k)).p×Fin (stagePair (n+k)).q
    let K := SpectralIndex (stageMultiplicities (n+k))
    let B : C(Interval,unitary (CStarMatrix (T×K) (T×K) ℂ)) :=
      ⟨fun t => blockUnitary (fun z => V (ξ z t)),
        blockUnitary_continuous.comp (continuous_pi fun z => V.continuous.comp (ξ z).continuous)⟩
    let V' := stepUnitary (n+k) *
      (⟨fun t => homUnitary R (B t), (homUnitary_continuous R).comp B.continuous⟩ :
        C(Interval,unitary (TensorMat (stagePair (n+k+1)).p (stagePair (n+k+1)).q)))
    refine ⟨e',V',?_⟩
    intro f t
    change (SequentialCStar.sequenceHom stageStep
      ((Nat.le_add_right n k).trans (Nat.le_succ (n+k))) f).val t=_
    rw [SequentialCStar.sequenceHom_succ,stageStep_eval]
    change unitaryConjugation (stepUnitary (n+k) t)
      (R (blockDiagonalHom (fun z => (concreteSystem.map (Nat.le_add_right n k) f).val (ξ z t))))=_
    have hfun : (fun z => (concreteSystem.map (Nat.le_add_right n k) f).val (ξ z t))=
        (fun z => unitaryConjugation (V (ξ z t)) (CStarMatrix.reindexₐ ℂ ℂ e
          (blockDiagonalHom (fun i => f.val (iteratedFamily n k i (ξ z t)))))) := by
      funext z
      exact hV f (ξ z t)
    rw [hfun]
    exact diagonalization_comp (stepUnitary (n+k) t) (fun z => V (ξ z t)) e E
      (fun i : IteratedIndex n k×SpectralIndex (stageMultiplicities (n+k)) =>
        f.val (iteratedFamily n k i.1 (ξ i.2 t)))

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

local instance iteratedIndexDecEq' (n k : ℕ) : DecidableEq (IteratedIndex n k) :=
  iteratedIndexDecEq n k

variable {I J H K : Type*} [Fintype I] [Fintype J] [Fintype H] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq H] [DecidableEq K]

lemma block_reindex_both (e : I≃H) (d : J≃K) (x : J → CStarMatrix I I ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e d) (blockDiagonalHom x)=
      blockDiagonalHom (fun k => CStarMatrix.reindexₐ ℂ ℂ e (x (d.symm k))) := by
  ext ⟨i,j⟩ ⟨a,b⟩
  change Matrix.blockDiagonal (fun j => CStarMatrix.ofMatrix.symm (x j))
    (e.symm i,d.symm j) (e.symm a,d.symm b)=
    Matrix.blockDiagonal (fun k => Matrix.reindex e e (CStarMatrix.ofMatrix.symm (x (d.symm k)) )) (i,j) (a,b)
  simp only [Matrix.blockDiagonal_apply,Matrix.reindex_apply]
  by_cases h : j=b
  · subst b; simp
  · have h' : d.symm j≠d.symm b := fun he => h (d.symm.injective he)
    simp [h,h']

theorem actual_index_normalized_matching (n : ℕ)
    (F : Finset C(Interval,CStarMatrix I I ℂ)) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∀ l,k≤l → ∃ U : C(Interval×Interval,
      unitary (CStarMatrix (I×IteratedIndex n l) (I×IteratedIndex n l) ℂ)),
      (∀ s : Interval,U (s,s)=1) ∧ ∀ f∈F,∀ s t : Interval,
        ‖unitaryConjugation (U (s,t)) (blockDiagonalHom (fun i => f (iteratedFamily n l i s)))-
          blockDiagonalHom (fun i => f (iteratedFamily n l i t))‖<ε := by
  classical
  let e := Fintype.equivFin I
  let R := CStarMatrix.reindexₐ ℂ ℂ e
  let toFin (f : C(Interval,CStarMatrix I I ℂ)) : C(Interval,Mat (Fintype.card I)) :=
    ⟨fun s => R (f s), (map_continuous R).comp f.continuous⟩
  obtain ⟨k,hk⟩ := actual_iterated_normalized_matching n (Fintype.card I) (F.image toFin) hε
  refine ⟨k,?_⟩
  intro l hl
  obtain ⟨V,hVd,hV⟩ := hk l hl
  let d := Fintype.equivFin (IteratedIndex n l)
  let Q := (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e.symm d.symm)).toStarAlgHom
  let U := (⟨fun z => homUnitary Q (V z), (homUnitary_continuous Q).comp V.continuous⟩ :
    C(Interval×Interval,unitary (CStarMatrix (I×IteratedIndex n l) (I×IteratedIndex n l) ℂ)))
  have hb (f : C(Interval,CStarMatrix I I ℂ)) (s : Interval) :
      Q (blockDiagonalHom (toFin f ∘ iteratedTuple n l s))=
        blockDiagonalHom (fun i => f (iteratedFamily n l i s)) := by
    change CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e.symm d.symm) _=_
    rw [block_reindex_both]
    congr 1
    funext i
    change R.symm (R (f (iteratedFamily n l (d.symm (d i)) s)))=_
    rw [d.symm_apply_apply,R.symm_apply_apply]
  refine ⟨U,?_,?_⟩
  · intro s
    change homUnitary Q (V (s,s))=1
    rw [hVd,homUnitary_one]
  · intro f hf s t
    have hh := hV (toFin f) (Finset.mem_image.mpr ⟨f,hf,rfl⟩) s t
    have hn := NonUnitalStarAlgHom.norm_apply_le Q
      (unitaryConjugation (V (s,t)) (blockDiagonalHom (toFin f ∘ iteratedTuple n l s))-
        blockDiagonalHom (toFin f ∘ iteratedTuple n l t))
    rw [map_sub,←homUnitary_conjugation,hb,hb] at hn
    exact hn.trans_lt hh

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

local instance iteratedDecEqMatching (n k : ℕ) : DecidableEq (IteratedIndex n k) :=
  iteratedIndexDecEq' n k

lemma unitary_conjugating_matching {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (R : A →⋆ₐ[ℂ] B) (u : unitary A) (v w : unitary B) (x y : A) :
    ‖unitaryConjugation (w*homUnitary R u*v⁻¹) (unitaryConjugation v (R x))-
      unitaryConjugation w (R y)‖≤‖unitaryConjugation u x-y‖ := by
  rw [←unitaryConjugation_mul]
  have hc : (w*homUnitary R u*v⁻¹)*v=w*homUnitary R u := by group
  rw [hc,unitaryConjugation_mul,homUnitary_conjugation,←map_sub,←map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation w) _).trans
    (NonUnitalStarAlgHom.norm_apply_le R _)

theorem concrete_stage_matching (n : ℕ) (F : Finset (StageAlgebra n))
    {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∀ l,k≤l → ∃ W : C(Interval×Interval,
      unitary (TensorMat (stagePair (n+l)).p (stagePair (n+l)).q)),
      (∀ s : Interval,W (s,s)=1) ∧ ∀ f∈F,∀ s t : Interval,
        ‖unitaryConjugation (W (s,t)) ((concreteSystem.map (Nat.le_add_right n l) f).val s)-
          (concreteSystem.map (Nat.le_add_right n l) f).val t‖<ε := by
  classical
  obtain ⟨k,hk⟩ := actual_index_normalized_matching (I := Fin (stagePair n).p×Fin (stagePair n).q) n (F.image Subtype.val) hε
  refine ⟨k,?_⟩
  intro l hl
  obtain ⟨U,hUd,hU⟩ := hk l hl
  obtain ⟨e,V,hV⟩ := concrete_iterate_diagonalization n l
  let R := (CStarMatrix.reindexₐ ℂ ℂ e).toStarAlgHom
  let W : C(Interval×Interval,unitary (TensorMat (stagePair (n+l)).p (stagePair (n+l)).q)) :=
    ⟨fun z => V z.2*homUnitary R (U z)*(V z.1)⁻¹,
      ((V.continuous.comp continuous_snd).mul ((homUnitary_continuous R).comp U.continuous)).mul
        ((V.continuous.comp continuous_fst).inv)⟩
  refine ⟨W,?_,?_⟩
  · intro s
    change V s*homUnitary R (U (s,s))*(V s)⁻¹=1
    rw [hUd,homUnitary_one,mul_one,mul_inv_cancel]
  · intro f hf s t
    rw [hV,hV]
    exact (unitary_conjugating_matching R (U (s,t)) (V s) (V t) _ _).trans_lt
      (hU f.val (Finset.mem_image.mpr ⟨f,hf,rfl⟩) s t)

end JiangSuConstruction

end

end OAI
