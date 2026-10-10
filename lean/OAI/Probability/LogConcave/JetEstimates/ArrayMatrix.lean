import Mathlib
import OAI.Probability.LogConcave.Sampling.TransportMajorant
import OAI.Probability.LogConcave.JetEstimates.ArrayRelabel
import OAI.Probability.LogConcave.Sampling.TerminalJacobianInverse

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy

def arrayMatrix {d : ℕ} (a : (Unit ⊕ Unit → Fin d) → ℝ) : Point d →L[ℝ] Point d :=
  ∑i, ∑j, a (Sum.elim (fun _ => i) (fun _ => j)) • coordinateRankOne d i j

lemma matrixArray_arrayMatrix {d : ℕ} (a : (Unit ⊕ Unit → Fin d) → ℝ) :
    matrixArray d (arrayMatrix a) = a := by
  funext c
  simp only [matrixArray_apply,arrayMatrix,sum_apply,
    smul_apply,coordinateRankOne,ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right,inner_sum,innerSL_apply_apply]
  simp only [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal,
    mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  congr 1
  funext s
  cases s with
  | inl u => cases u; rfl
  | inr u => cases u; rfl

lemma matrixArray_injective (d : ℕ) : Function.Injective (matrixArray d) := by
  intro A B h
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  change (A (EuclideanSpace.basisFun (Fin d) ℝ j)).ofLp i =
    (B (EuclideanSpace.basisFun (Fin d) ℝ j)).ofLp i
  have hh := congrFun h (Sum.elim (fun _ => i) (fun _ => j))
  simpa only [matrixArray_apply,Sum.elim_inl,Sum.elim_inr,
    EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,map_one,one_mul] using hh

lemma arrayMatrix_matrixArray {d : ℕ} (A : Point d →L[ℝ] Point d) :
    arrayMatrix (matrixArray d A) = A :=
  matrixArray_injective d (matrixArray_arrayMatrix _)

lemma arrayMatrix_add {d : ℕ} (a b : (Unit ⊕ Unit → Fin d) → ℝ) :
    arrayMatrix (a+b)=arrayMatrix a+arrayMatrix b := by
  apply matrixArray_injective d
  simp only [matrixArray_arrayMatrix,map_add]

lemma arrayMatrix_smul {d : ℕ} (c : ℝ) (a : (Unit ⊕ Unit → Fin d) → ℝ) :
    arrayMatrix (c • a)=c • arrayMatrix a := by
  apply matrixArray_injective d
  simp only [matrixArray_arrayMatrix,map_smul]
end TensorEnergy

namespace TensorSum

def matrixEval {d : ℕ} (A : TensorSum (Unit ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  TensorEnergy.arrayMatrix (fun c => A.eval F x r L c p)

lemma matrixEval_add {d : ℕ} (A B : TensorSum (Unit ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (p : ℝ × Point d) :
    (A.add B).matrixEval F x r L p=A.matrixEval F x r L p+B.matrixEval F x r L p := by
  simp only [matrixEval,add_eval]
  exact TensorEnergy.arrayMatrix_add _ _

lemma matrixEval_scale {d : ℕ} (A : TensorSum (Unit ⊕ Unit)) (n : ℕ) (P : Polynomial ℝ)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (p : ℝ × Point d) :
    (A.scale n P).matrixEval F x r L p=
      ((r*L)^n*P.eval p.1) • A.matrixEval F x r L p := by
  simp only [matrixEval,scale_eval]
  exact TensorEnergy.arrayMatrix_smul _ _

def matrixComp (A B : TensorSum (Unit ⊕ Unit)) : TensorSum (Unit ⊕ Unit) :=
  A.contract (B.relabel (Equiv.sumComm Unit Unit))

lemma matrixComp_weight {A B : TensorSum (Unit ⊕ Unit)} {u v : ℕ}
    (hA : A.weightLE u) (hB : B.weightLE v) : (A.matrixComp B).weightLE (u+v) :=
  weightLE_contract hA (weightLE_relabel hB _)

lemma matrixEval_comp {d : ℕ} (A B : TensorSum (Unit ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (p : ℝ × Point d) :
    (A.matrixComp B).matrixEval F x r L p=
      (A.matrixEval F x r L p).comp (B.matrixEval F x r L p) := by
  apply TensorEnergy.matrixArray_injective d
  funext c
  rw [matrixEval,TensorEnergy.matrixArray_arrayMatrix]
  rw [TensorEnergy.matrixArray_comp]
  simp only [matrixComp,contract_eval,relabel_eval,matrixEval,
    TensorEnergy.matrixArray_arrayMatrix]
  rfl

lemma matrixEval_smoothAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : -1<ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (y : Point d) :
    ContDiffAt ℝ (⊤:ℕ∞) (A.matrixEval F x r ((lam:ℝ)*r)) (ρ,y) := by
  unfold matrixEval TensorEnergy.arrayMatrix
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (A.timeSmooth hF x hr hlam hl _ (ρ,y) h0 h1).smul contDiffAt_const

lemma HasMaterial.matrixEval_path {A D : TensorSum (Unit ⊕ Unit)} (hA : A.HasMaterial D)
    {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam) (x : Point d)
    {r T ρ : ℝ} (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hT0 : 0≤T) (hT1 : T<1) (h0 : 0<ρ) (hT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => A.matrixEval F x r ((lam:ℝ)*r)
      (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y)))
      (D.matrixEval F x r ((lam:ℝ)*r)
        (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) ρ := by
  unfold matrixEval TensorEnergy.arrayMatrix
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have hS := (A.timeSmooth hF x hr hlam hl
    (Sum.elim (fun _ => i) (fun _ => j))
    (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) (by dsimp; linarith)
    (hT.trans hT1)).differentiableAt (by simp)
  have hd := hS.hasFDerivAt.comp_hasDerivAt ρ ((hasDerivAt_id ρ).prodMk
    (terminalBackward_deriv hF x hr hl hT0 hT1 h0 hT y))
  rw [joint_material_direction F x r hS,hA hF x hr hlam hl h0.le (hT.trans hT1)] at hd
  exact hd.smul_const (coordinateRankOne d i j)

def firstMatrix : TensorSum (Unit ⊕ Unit) :=
  (pure (TensorAtom.jetList [()] (by simp) (by intro u; cases u; simp) (by simp))).relabel
    (Equiv.sumComm Unit Unit)

lemma firstMatrix_weight : firstMatrix.weightLE 0 := by
  apply weightLE_relabel
  apply weightLE_pure
  simp only [TensorAtom.jetList_weight,List.length_singleton,Nat.sub_self,le_refl]

lemma firstMatrix_eval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) :
    firstMatrix.matrixEval F x r L p=L⁻¹ • conditionalFirstJet F x r L p := by
  apply TensorEnergy.matrixArray_injective d
  funext c
  rw [matrixEval,TensorEnergy.matrixArray_arrayMatrix,map_smul]
  simp only [firstMatrix,relabel_eval,pure_eval,TensorAtom.jetList_eval,
    Equiv.sumComm_apply,Function.comp_apply,Sum.swap_inl,Sum.swap_inr,Pi.smul_apply,
    smul_eq_mul]
  rw [matrixArray_firstJet]
  rfl
end TensorSum

namespace TensorSum

def material {S : Type} (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) : TensorSum S :=
  Classical.choose (A.hasMaterial hw)
lemma material_weight {S : Type} (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) :
    (A.material hw).weightLE (w+2) := (Classical.choose_spec (A.hasMaterial hw)).1
lemma material_spec {S : Type} (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) :
    A.HasMaterial (A.material hw) := (Classical.choose_spec (A.hasMaterial hw)).2

def terminalQ : (n : ℕ) → {A : TensorSum (Unit ⊕ Unit) // A.weightLE (2*n)}
  | 0 => ⟨firstMatrix.scale 0 Polynomial.X,weightLE_scale firstMatrix_weight _ _⟩
  | n+1 =>
    let Q := terminalQ n
    ⟨((firstMatrix.matrixComp Q.val).scale 1 Polynomial.X).add (Q.val.material Q.property),
      weightLE_add
        (weightLE_mono (weightLE_scale (matrixComp_weight firstMatrix_weight Q.property) _ _)
          (by omega))
        (weightLE_mono (Q.val.material_weight Q.property) (by omega))⟩

lemma terminalQ_zero_eval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) :
    (terminalQ 0).val.matrixEval F x r L p = (p.1*L⁻¹) • conditionalFirstJet F x r L p := by
  rw [terminalQ,matrixEval_scale,firstMatrix_eval]
  simp only [pow_zero,one_mul,Polynomial.eval_X,smul_smul]

lemma terminalQ_succ_eval {d : ℕ} (n : ℕ) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) :
    (terminalQ (n+1)).val.matrixEval F x r L p =
      ((r*L)*p.1) • ((firstMatrix.matrixEval F x r L p).comp
        ((terminalQ n).val.matrixEval F x r L p)) +
      ((terminalQ n).val.material (terminalQ n).property).matrixEval F x r L p := by
  conv_lhs => unfold terminalQ
  rw [matrixEval_add,matrixEval_scale,matrixEval_comp]
  simp only [pow_one,Polynomial.eval_X]
end TensorSum

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam

lemma terminalJacobian_first_Q {ρ : ℝ} (h0 : 0<ρ) (hT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y))
      ((r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ 0).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)))) ρ := by
  have hL : (lam:ℝ)*r≠0 := mul_ne_zero (ne_of_gt hlam) hr.ne'
  convert terminalJacobian_deriv hF x hr hlam hl hT0 hT1 h0 hT y using 1
  rw [TensorSum.terminalQ_zero_eval,ContinuousLinearMap.comp_smul,smul_smul]
  congr 1
  field_simp [ne_of_gt (show (0:ℝ)<lam from hlam),hr.ne']

lemma terminalJacobian_Q_deriv (n : ℕ) {ρ : ℝ} (h0 : 0<ρ) (hT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => (r*((lam:ℝ)*r)) •
      (terminalJacobian hF x hr hl hT0 hT1 (t,y)).comp
        ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
          (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y))))
      ((r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ (n+1)).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)))) ρ := by
  let Q := (TensorSum.terminalQ n).val
  have hD := TensorSum.HasMaterial.matrixEval_path (Q.material_spec (TensorSum.terminalQ n).property)
    hF x hr hlam hl hT0 hT1 h0 hT y
  have hB := terminalJacobian_deriv hF x hr hlam hl hT0 hT1 h0 hT y
  have hh := (hB.clm_comp hD).const_smul (r*((lam:ℝ)*r))
  convert hh using 1; try rfl
  rw [TensorSum.terminalQ_succ_eval,TensorSum.firstMatrix_eval,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_assoc,smul_smul]
  congr 2
  have hL : (lam:ℝ)*r≠0 := mul_ne_zero (ne_of_gt hlam) hr.ne'
  congr 1
  field_simp [ne_of_gt (show (0:ℝ)<lam from hlam),hr.ne']

theorem terminalJacobian_iteratedDeriv_Q (n : ℕ) {ρ : ℝ} (h0 : 0<ρ) (hT : ρ<T)
    (y : Point d) :
    iteratedDeriv (n+1) (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)) ρ =
      (r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) := by
  induction n generalizing ρ with
  | zero =>
    rw [zero_add,iteratedDeriv_one]
    exact (terminalJacobian_first_Q hF x hr hlam hl hT0 hT1 h0 hT y).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)) =ᶠ[nhds ρ]
        (fun t => (r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (t,y)).comp
          ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
            (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y)))) := by
      filter_upwards [Ioo_mem_nhds h0 hT] with t ht
      exact ih ht.1 ht.2
    rw [he.deriv_eq]
    exact (terminalJacobian_Q_deriv hF x hr hlam hl hT0 hT1 n h0 hT y).deriv

theorem terminalJacobian_iteratedDeriv_Q_closed (hTpos : 0<T) (n : ℕ)
    (ρ : Icc (0:ℝ) T) (y : Point d) :
    iteratedDeriv (n+1) (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)) ρ =
      (r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) := by
  let B := fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)
  let X := fun t => terminalBackward hF x hr.le hl hT0 hT1 (t,y)
  let H := fun t => (r*((lam:ℝ)*r)) • (B t).comp
    ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r) (t,X t))
  have hB : ContDiff ℝ (⊤:ℕ∞) B :=
    (terminalJacobian_smooth hF x hr hl hT0 hT1).comp (contDiff_id.prodMk contDiff_const)
  have hX : Continuous X :=
    (terminalBackward_smooth hF x hr.le hl hT0 hT1).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hH : ContinuousOn H (Icc 0 T) := by
    intro t ht
    have hq := TensorSum.matrixEval_smoothAt hF x hr hlam hl
      (by linarith [ht.1] : -1<t) (ht.2.trans_lt hT1) (TensorSum.terminalQ n).val (X t)
    have hs : ContinuousAt (fun _ : ℝ => r*((lam:ℝ)*r)) t := continuousAt_const
    exact (hs.smul (hB.continuous.continuousAt.clm_comp
      (hq.continuousAt.comp (x:=t) (f:=fun u : ℝ => (u,X u))
        (continuousAt_id.prodMk hX.continuousAt)))).continuousWithinAt
  have hD : Continuous (iteratedDeriv (n+1) B) :=
    hB.continuous_iteratedDeriv (n+1) (by exact_mod_cast (le_top : ((n+1):ℕ∞)≤⊤))
  have hc : IsClosed {t | t∈Icc (0:ℝ) T ∧ iteratedDeriv (n+1) B t=H t} :=
    isClosed_Icc.isClosed_eq hD.continuousOn hH
  have hs : Ioo (0:ℝ) T ⊆ {t | t∈Icc (0:ℝ) T ∧ iteratedDeriv (n+1) B t=H t} := by
    intro t ht
    exact ⟨⟨ht.1.le,ht.2.le⟩,terminalJacobian_iteratedDeriv_Q hF x hr hlam hl hT0 hT1 n ht.1 ht.2 y⟩
  have hh := closure_minimal hs hc
  rw [closure_Ioo hTpos.ne] at hh
  exact (hh ρ.2).2
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy
lemma matrixArray_mulVec {d : ℕ} (A : Point d →L[ℝ] Point d) (v : Point d) :
    (fun i => ∑j,matrixArray d A (Sum.elim (fun _ => i) (fun _ => j))*v.ofLp j) =
      (A v).ofLp := by
  funext i
  have hv : ∑j,v.ofLp j • EuclideanSpace.basisFun (Fin d) ℝ j=v := by
    simpa only [OrthonormalBasis.repr_apply_apply,EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left,map_one,one_mul] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hh := congrArg (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (A z)) hv
  simpa only [map_sum,map_smul,inner_sum,real_inner_smul_right,
    matrixArray_apply,Sum.elim_inl,Sum.elim_inr,EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left,map_one,one_mul,mul_comm,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul] using hh

lemma AllSplitBound.matrixArray_norm_le {d : ℕ} {A : Point d →L[ℝ] Point d}
    {M : ℝ} (h : AllSplitBound (matrixArray d A) M) (hM : 0≤M) : ‖A‖≤M := by
  have hb := (h Unit Unit (Equiv.sumComm Unit Unit)).reindex
    (Equiv.funUnique Unit (Fin d)).symm (Equiv.funUnique Unit (Fin d)).symm
  change Bound (fun i j => matrixArray d A (Sum.elim (fun _ => i) (fun _ => j))) (M^2) at hb
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg v))).mp
  have hv := hb v.ofLp
  have he (i : Fin d) := congrFun (matrixArray_mulVec A v) i
  dsimp only at he
  simp_rw [he] at hv
  simpa only [←EuclideanSpace.real_norm_sq_eq,mul_pow] using hv

lemma AllSplitBound.of_spatialTensor_zero {d : ℕ} {S : Type} [Fintype S]
    (f : (S → Fin d) → Point d → ℝ) (y : Point d) {M : ℝ}
    (h : AllSplitBound (spatialTensor f (List.finRange 0) y) M) :
    AllSplitBound (fun c => f c y) M := by
  let e : Fin 0 ⊕ S ≃ S :=
    ⟨Sum.elim Fin.elim0 id,Sum.inr,by rintro (a|a); exact Fin.elim0 a; rfl,by intro a; rfl⟩
  have hh := h.reindex e
  change AllSplitBound (fun c => f (fun s => c s) y) M at hh
  exact hh

end TensorEnergy
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

namespace TensorSum
lemma matrixEval_norm_le {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (y : Point d) :
    ‖A.matrixEval F x r ((lam:ℝ)*r) (ρ,y)‖≤A.spatialBound F x r ρ ((lam:ℝ)*r) 0 y := by
  have hh := (A.spatialBound_allSplit hF x hr hlam hl h0 h1 0 y).of_spatialTensor_zero
    (A.slice F x r ρ ((lam:ℝ)*r)) y
  apply TensorEnergy.AllSplitBound.matrixArray_norm_le _ (A.spatialBound_nonneg _ _ _ _ _ _ _)
  simpa only [matrixEval,TensorEnergy.matrixArray_arrayMatrix,slice] using hh
end TensorSum

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

lemma terminalBackward_measurePreserving (t : Icc (0:ℝ) T) :
    MeasurePreserving (fun y => terminalBackward hF x hr.le hl hT0.le hT1 (t,y))
      (interpolationLaw F x r T) (interpolationLaw F x r t) := by
  have he : (fun y => terminalBackward hF x hr.le hl hT0.le hT1 (t,y))=
      probabilityTransport hF x hr.le hl hT0.le hT1 ⟨T,hT0.le,le_rfl⟩ t :=
    funext (terminalBackward_eq hF x hr.le hl hT0.le hT1 t)
  rw [he]
  exact ⟨(probabilityTransport_continuous hF x hr.le hl hT0.le hT1 _ _).measurable,
    probabilityTransport_pushforward hF x hr.le hl hT0.le hT1 _ _⟩

include hlam in
lemma terminalJacobian_iteratedDeriv_norm_le (n : ℕ) (t : Icc (0:ℝ) T) (y : Point d) :
    ‖iteratedDeriv (n+1) (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t‖≤
      (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
        (TensorSum.terminalQ n).val.spatialBound F x r t ((lam:ℝ)*r) 0
          (terminalBackward hF x hr.le hl hT0.le hT1 (t,y)) := by
  rw [terminalJacobian_iteratedDeriv_Q_closed hF x hr hlam hl hT0.le hT1 hT0,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤r*((lam:ℝ)*r))]
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)).trans
  have hb := mul_le_mul (terminalJacobian_norm_le hF x hr hl hT0.le hT1 t y)
    (TensorSum.matrixEval_norm_le hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1)
      (TensorSum.terminalQ n).val (terminalBackward hF x hr.le hl hT0.le hT1 (t,y)))
    (norm_nonneg _) (Real.exp_pos _).le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
    (show 0≤r*((lam:ℝ)*r) by positivity)

include hlam in

theorem terminalJacobian_iteratedDeriv_eLpNorm (hd : 1≤d) (n : ℕ)
    (t : Icc (0:ℝ) T) {p : ℝ≥0∞} (hp : 1≤p) (hpf : p≠⊤) :
    eLpNorm (fun y => iteratedDeriv (n+1)
      (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t) p
      (interpolationLaw F x r T)≤
      ENNReal.ofReal (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
        ((TensorSum.terminalQ n).val.momentBudget d 0 p)*
        ENNReal.ofReal ((Real.sqrt (1-(t:ℝ)^2))⁻¹)^(2*n) := by
  let A := (TensorSum.terminalQ n).val
  let g := fun y => terminalBackward hF x hr.le hl hT0.le hT1 (t,y)
  let V := A.spatialBound F x r t ((lam:ℝ)*r) 0
  let c := r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4)
  have hV : AEStronglyMeasurable V (interpolationLaw F x r t) := (A.spatialBound_measurable hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) 0).aestronglyMeasurable
  have hDerivative : Continuous (fun y => iteratedDeriv (n+1)
      (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t) := by
    simp_rw [terminalJacobian_iteratedDeriv_Q_closed hF x hr hlam hl hT0.le hT1 hT0]
    have hJacobian : Continuous (fun point : Point d =>
        terminalJacobian hF x hr hl hT0.le hT1 ((t:ℝ),point)) :=
      (terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_id)
    have hBackward : Continuous g :=
      (terminalBackward_smooth hF x hr.le hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_id)
    apply continuous_iff_continuousAt.mpr
    intro point
    have hMatrix := TensorSum.matrixEval_smoothAt hF x hr hlam hl
      (by linarith [t.2.1] : -1<(t:ℝ)) (t.2.2.trans_lt hT1)
      (TensorSum.terminalQ n).val (g point)
    have hScalar : ContinuousAt (fun _ : Point d => r*((lam:ℝ)*r)) point :=
      continuousAt_const
    exact hScalar.smul (hJacobian.continuousAt.clm_comp
      (hMatrix.continuousAt.comp (x:=point) (f:=fun value : Point d => ((t:ℝ),g value))
        (continuousAt_const.prodMk hBackward.continuousAt)))
  have hb := eLpNorm_mono_real (μ:=interpolationLaw F x r T) (p:=p)
    hDerivative.aestronglyMeasurable
    (terminalJacobian_iteratedDeriv_norm_le hF x hr hlam hl hT0 hT1 n t)
  have he : (fun y => c*V (g y))=c • (V ∘ g) := rfl
  change _ ≤ eLpNorm (fun y => c*V (g y)) p _ at hb
  rw [he,eLpNorm_const_smul,
    eLpNorm_comp_measurePreserving hV (terminalBackward_measurePreserving hF x hr hl hT0 hT1 t),
    Real.enorm_eq_ofReal_abs,abs_of_nonneg (by positivity : 0≤c)] at hb
  apply hb.trans
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  simpa only [Nat.add_zero] using A.spatialBound_Lp hF x hr hlam hl t.2.1
    (t.2.2.trans_lt hT1) hd (TensorSum.terminalQ n).property 0 hp hpf
end LogConcaveSampling

end

end

end OAI
