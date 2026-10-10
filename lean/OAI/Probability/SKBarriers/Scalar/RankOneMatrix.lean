import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixSKGuerra
import OAI.Probability.SKBarriers.Scalar.VectorBlocks
import OAI.Probability.SKBarriers.SpinGlass.FinitePrefix

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def replicaSpinMap (d : ℕ) : (Fin d → ℝ) →L[ℝ] (Config d → ℝ) :=
  ContinuousLinearMap.pi (fun s => ∑ i, spin (s i) • ContinuousLinearMap.proj i)

@[simp] theorem replicaSpinMap_apply (d : ℕ) (x : Fin d → ℝ) (s : Config d) :
    replicaSpinMap d x s=∑ i, spin (s i)*x i := by
  simp [replicaSpinMap]

theorem replicaSpin_terminal (d : ℕ) :
    siteValueTerminal (fun _ : Config d => 0) ∘ replicaSpinMap d=
      fun x => ∑ i, scalarSpinTerminal (x i) := by
  funext x
  have H := congrFun (affineLogPartition_product d
    (fun (_ : Fin d) (_ : Bool) => (0:ℝ))
    (fun i b => spin b • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) x
  simp only [affineLogPartition_bool,ContinuousLinearMap.proj_apply] at H
  simpa only [Function.comp_def,siteValueTerminal,affineLogPartition,
    Finset.sum_const_zero,zero_add,replicaSpinMap_apply,sum_apply,
    smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,scalarSpinTerminal] using H

section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem vectorBlockHierarchy_one (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f : E → ℝ) :
    vectorBlockHierarchy 1 n m (fun i _ => v i) f=vectorHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change vectorBlockHierarchy 1 n _ _ (vectorStep (m (Fin.last n)) (v (Fin.last n)) f)=_
    exact ih _ _ _
end Vector

def rankOnePath {n : ℕ} (d : ℕ) (b : Fin n → Fin d → ℝ) (j : Fin n) : Fin d → Fin d → ℝ :=
  fun u v => ∑ i, if i ≤ j then b i u*b i v else 0

theorem factorPath_rankOne {k : ℕ} (d : ℕ) (b : Fin (k+1) → Fin d → ℝ) (j : Fin (k+1)) :
    factorPath d 1 k (fun i _ => b i) j=rankOnePath d b j := by
  funext u v
  simp [factorPath,factorCovariance,rankOnePath]

theorem rankOne_siteValue {k : ℕ} (d : ℕ) (β : ℝ) (m : Fin (k+1) → ℝ) (hm : m 0=0)
    (b : Fin (k+1) → Fin d → ℝ) :
    vectorHierarchy ((k+1)*1) (siteBlockMass 1 k (zeroInitialAtoms k m))
      (matrixSiteVector β (fun i _ => b i) (fun (s : Config d) u => spin (s u)))
      (siteValueTerminal (fun _ : Config d => 0)) 0=
      vectorHierarchy (k+1) m (fun i => β • b i) (fun x => ∑ u, scalarSpinTerminal (x u)) 0 := by
  rw [funext (siteBlockMass_zeroInitial m hm)]
  have hev : matrixSiteVector β (fun i (_ : Fin 1) => b i) (fun (s : Config d) u => spin (s u))=
      replicaSpinMap d ∘ (fun i => β • b (finProdFinEquiv.symm i).1) := by
    funext i s
    simp only [matrixSiteVector,Function.comp_apply,replicaSpinMap_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hev]
  have H := congrFun (vectorHierarchy_pullback (replicaSpinMap d) ((k+1)*1)
    (fun i => m (finProdFinEquiv.symm i).1)
    (fun i => β • b (finProdFinEquiv.symm i).1)
    (siteValueTerminal (fun _ : Config d => 0))) (0 : Fin d → ℝ)
  simp only [Function.comp_apply,map_zero] at H
  rw [← H,replicaSpin_terminal]
  rw [vectorHierarchy_blocks (k+1) 1 m (fun i _ => β • b i),vectorBlockHierarchy_one]

theorem matrixConstrainedPressure_rankOne {N d k : ℕ} (hN : 0<N) (β : ℝ)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (m : Fin (k+1) → ℝ) (hm0 : m 0=0) (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (b : Fin (k+1) → Fin d → ℝ) :
    matrixConstrainedPressure N d β D ≤
      vectorHierarchy (k+1) m (fun i => β • b i) (fun x => ∑ u,scalarSpinTerminal (x u)) 0+
        β^2/4*matrixSquare d (fun i j => D i j-rankOnePath d b (Fin.last k) i j)-
        β^2/4*∑ i : Fin k,m i.succ*(matrixSquare d (rankOnePath d b i.succ)-
          matrixSquare d (rankOnePath d b i.castSucc)) := by
  have H := matrixConstrainedPressure_le hN (by norm_num : 0<1) β D (fun _ _ => 0) hD
    (fun i (_ : Fin 1) => b i) (zeroInitialAtoms k m)
    (zeroInitialAtoms_nonneg m hm hmono) (zeroInitialAtoms_sum m)
  have hz : matrixSiteWeight (fun (_ _ : Fin d) => (0:ℝ)) (fun (s : Config d) u => spin (s u))=fun _ => 0 := by
    funext s; simp [matrixSiteWeight]
  rw [hz,rankOne_siteValue d β m hm0 b] at H
  simp only [matrixInner,zero_mul,Finset.sum_const_zero,sub_zero] at H
  simp_rw [factorPath_rankOne] at H
  rw [zeroInitialAtoms_sum_mul_parts] at H
  rw [matrixSquare_sub]
  unfold matrixInner
  convert H using 1
  ring

end SK.Analytic

end
end

end OAI
