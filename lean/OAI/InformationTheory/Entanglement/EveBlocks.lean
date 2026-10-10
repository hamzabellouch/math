import OAI.InformationTheory.Entanglement.Coherence
import OAI.InformationTheory.Entanglement.PowersStormer

namespace OAI

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def eveBlock (R D : Mat n) : Mat n := (CFC.sqrt R*D*CFC.sqrt R)ᵀ
lemma eveBlock_psd {R D : Mat n} (hD : D.PosSemidef) : (eveBlock R D).PosSemidef := by
  unfold eveBlock
  have h : (CFC.sqrt R*D*CFC.sqrt R).PosSemidef := by
    simpa only [sqrt_herm] using hD.mul_mul_conjTranspose_same (CFC.sqrt R)
  exact h.transpose
lemma eveBlock_trace {R D : Mat n} (hR : R.PosSemidef) :
    Matrix.trace (eveBlock R D)=Matrix.trace (D*R) := by
  unfold eveBlock
  rw [Matrix.trace_transpose,Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self R hR.nonneg,Matrix.trace_mul_comm]
lemma eveBlock_gram {R D : Mat n} (hD : D.PosSemidef) :
    CFC.sqrt R*D*CFC.sqrt R=(CFC.sqrt D*CFC.sqrt R)ᴴ*(CFC.sqrt D*CFC.sqrt R) := by
  simp only [Matrix.conjTranspose_mul,sqrt_herm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt D),CFC.sqrt_mul_sqrt_self D hD.nonneg]
lemma eveBlock_fidelity {R A B : Mat n} (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    fidelity (eveBlock R A) (eveBlock R B)=traceNorm (CFC.sqrt A*R*CFC.sqrt B) := by
  unfold eveBlock
  rw [fidelity_transpose (by simpa only [sqrt_herm] using hA.mul_mul_conjTranspose_same (CFC.sqrt R))
    (by simpa only [sqrt_herm] using hB.mul_mul_conjTranspose_same (CFC.sqrt R)),
    eveBlock_gram hA,eveBlock_gram hB,fidelity_polar]
  simp only [Matrix.conjTranspose_mul,sqrt_herm]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt R),CFC.sqrt_mul_sqrt_self R hR.nonneg]

lemma eveBlock_coherence (R : Mat (n × m)) (hR : Represented R)
    (X : Fin 2 → Mat n) (Y : Fin 2 → Mat m)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef) :
    let τ := fun i j => eveBlock R (X i ⊗ₖ Y j)
    let p := fun i j => (Matrix.trace (τ i j)).re
    fidelity (τ 0 0) (τ 1 1) ≤
      Real.sqrt (p 0 0*p 0 1)+Real.sqrt (p 1 0*p 1 1)+2*Real.sqrt (p 0 1*p 1 0) := by
  dsimp only
  rw [eveBlock_fidelity hR.1 ((hX 0).kronecker (hY 0)) ((hX 1).kronecker (hY 1))]
  simp only [eveBlock_trace hR.1]
  exact four_effect R hR X Y hX hY

open scoped Matrix.Norms.L2Operator in
lemma continuous_traceNorm : Continuous (traceNorm : Mat n → ℝ) := by
  have h : Continuous (fun A : Mat n => CFC.sqrt (Aᴴ*A)) := by
    exact CFC.continuousOn_sqrt.comp_continuous (by fun_prop)
      (fun A => (Matrix.posSemidef_conjTranspose_mul_self A).nonneg)
  change Continuous (fun A : Mat n => (Matrix.trace (CFC.sqrt (Aᴴ*A))).re)
  unfold Matrix.trace Matrix.diag
  fun_prop

end SecretKey

end

end OAI
