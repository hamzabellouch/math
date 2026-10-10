import OAI.Analysis.Mahler.LogJet
import Mathlib.Analysis.Calculus.FDeriv.Congr

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype J]

abbrev ComplexTwoJet (E J : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  (J → ℂ) × (J → E →L[ℂ] ℂ) × (J → E →L[ℂ] (E →L[ℂ] ℂ))

def sumNormSq (v : J → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

def sumNormSqD (v : J → ℂ) (A : J → E →L[ℂ] ℂ) : E →L[ℝ] ℝ :=
  ∑ j, (squareD (v j).re (projectD Complex.reCLM (A j)) +
    squareD (v j).im (projectD Complex.imCLM (A j)))

def sumNormSqD2 (v : J → ℂ) (A : J → E →L[ℂ] ℂ)
    (B : J → E →L[ℂ] (E →L[ℂ] ℂ)) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∑ j, (squareD2 (v j).re (projectD Complex.reCLM (A j)) (projectD2 Complex.reCLM (B j)) +
    squareD2 (v j).im (projectD Complex.imCLM (A j)) (projectD2 Complex.imCLM (B j)))

lemma continuous_sumNormSq : Continuous (sumNormSq : (J → ℂ) → ℝ) := by
  unfold sumNormSq
  exact continuous_finsetSum _ (fun j _ => Complex.continuous_normSq.comp (continuous_apply j))

lemma continuous_sumNormSqD :
    Continuous (fun q : ComplexTwoJet E J => sumNormSqD q.1 q.2.1) := by
  apply continuous_finsetSum
  intro j _
  have hv : Continuous (fun q : ComplexTwoJet E J => q.1 j) :=
    (continuous_apply j).comp continuous_fst
  have ha : Continuous (fun q : ComplexTwoJet E J => q.2.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  exact ((continuous_const.mul (Complex.continuous_re.comp hv)).smul
    ((projectD Complex.reCLM).continuous.comp ha)).add
    ((continuous_const.mul (Complex.continuous_im.comp hv)).smul
    ((projectD Complex.imCLM).continuous.comp ha))

lemma continuous_sumNormSqD2 :
    Continuous (fun q : ComplexTwoJet E J => sumNormSqD2 q.1 q.2.1 q.2.2) := by
  have : ContinuousAdd (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] (E →L[ℝ] ℝ))).toContinuousAdd
  unfold sumNormSqD2
  apply continuous_finsetSum
  intro j _
  have hv : Continuous (fun q : ComplexTwoJet E J => q.1 j) :=
    (continuous_apply j).comp continuous_fst
  have ha : Continuous (fun q : ComplexTwoJet E J => q.2.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun q : ComplexTwoJet E J => q.2.2 j) :=
    (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  have hp (p : ℂ →L[ℝ] ℝ) : Continuous (fun q : ComplexTwoJet E J =>
      squareD2 (p (q.1 j)) (projectD p (q.2.1 j)) (projectD2 p (q.2.2 j))) := by
    have hpa := (projectD p).continuous.comp ha
    have hpb := (compL ℝ E (E →L[ℂ] ℂ) (E →L[ℝ] ℝ) (projectD p)).continuous.comp
      ((restrictScalarsL ℂ E (E →L[ℂ] ℂ) ℝ ℝ).continuous.comp hb)
    exact ((continuous_const.mul (p.continuous.comp hv)).smul hpb).add
      (((smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        ((continuous_const (y := (2 : ℝ))).smul hpa)).clm_apply hpa)
  exact (hp Complex.reCLM).add (hp Complex.imCLM)

lemma hasFDerivAt_sumNormSq {f : J → E → ℂ} {a : J → E →L[ℂ] ℂ} {x : E}
    (hf : ∀ j, HasFDerivAt (f j) (a j) x) :
    HasFDerivAt (fun y => sumNormSq (fun j => f j y))
      (sumNormSqD (fun j => f j x) a) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasFDerivAt_square (hasFDerivAt_project (hf j) Complex.reCLM)).fun_add
      (hasFDerivAt_square (hasFDerivAt_project (hf j) Complex.imCLM)))
  simpa [sumNormSq, sumNormSqD, Complex.normSq_apply, pow_two] using h

lemma hasFDerivAt_sumNormSqD {f : J → E → ℂ} {a : J → E → (E →L[ℂ] ℂ)}
    {b : J → E →L[ℂ] (E →L[ℂ] ℂ)} {x : E}
    (hf : ∀ j, HasFDerivAt (f j) (a j x) x)
    (ha : ∀ j, HasFDerivAt (a j) (b j) x) :
    HasFDerivAt (fun y => sumNormSqD (fun j => f j y) (fun j => a j y))
      (sumNormSqD2 (fun j => f j x) (fun j => a j x) b) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasFDerivAt_squareD (hasFDerivAt_project (hf j) Complex.reCLM)
      (hasFDerivAt_projectD (ha j) Complex.reCLM)).fun_add
    (hasFDerivAt_squareD (hasFDerivAt_project (hf j) Complex.imCLM)
      (hasFDerivAt_projectD (ha j) Complex.imCLM)))
  simpa [sumNormSqD, sumNormSqD2] using h

end
end SymmetricMahler

end OAI
