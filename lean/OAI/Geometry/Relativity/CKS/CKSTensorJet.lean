import OAI.Geometry.Relativity.CKS.MixedMassCoefficient
import OAI.Geometry.Relativity.CKS.MixedSqrtJet

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev TensorInput := MassInput × ScalarJet × (A → ScalarJet)
abbrev TensorParameter := ScalarThreeJet × TensorInput
instance tensorInputNormed : NormedAddCommGroup TensorInput := by
  letI : NormedAddCommGroup (ScalarJet × (A → ScalarJet)) := inferInstance
  exact Prod.normedAddCommGroup
instance tensorInputSpace : NormedSpace ℝ TensorInput := by
  letI : NormedSpace ℝ (ScalarJet × (A → ScalarJet)) := inferInstance
  exact Prod.normedSpace
instance tensorParameterNormed : NormedAddCommGroup TensorParameter := Prod.normedAddCommGroup
instance tensorParameterSpace : NormedSpace ℝ TensorParameter := Prod.normedSpace

def tensorBase (p : TensorParameter) : MassParameter := (p.1,p.2.1)
def tensorQ (p : TensorParameter) : MatrixScalarJet := lowerMatrixJet (coefficientMetric p.1 p.2.1)
def tensorK (p : TensorParameter) : MatrixScalarJet := lowerMatrixJet (p.2.1.1 0)+
  mulMatrixJet (powJet p.1.1 3) (p.2.1.2.1 1)+mulMatrixJet (powJet p.1.1 4) (p.2.1.2.1 2)
def tensorH (p : TensorParameter) (a : A) : ScalarJet := (coefficientShift p.1 p.2.1 a).1

def tensorDen (p : TensorParameter) : ScalarJet :=
  constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2.1)
def tensorLapseSq (p : TensorParameter) : ScalarJet :=
  productJet (constantJet 1+powJet p.1.1 2) (reciprocalJet (tensorDen p))
def tensorLapse (p : TensorParameter) : ScalarJet :=
  productJet (sqrtJet (constantJet 1+powJet p.1.1 2)) (reciprocalJet (sqrtJet (tensorDen p)))

def tensorCross (p : TensorParameter) : ScalarJet := ∑ a, productJet (tensorH p a) (p.2.2.2 a)
def tensorNormalQuad (p : TensorParameter) : ScalarJet := ∑ a, ∑ b,
  productJet (tensorK p a b) (productJet (tensorH p a) (tensorH p b))

def tensorLCoeff (p : TensorParameter) : ScalarJet := productJet (tensorLapseSq p)
  (p.2.2.1-p.2.1.2.2.2 0-productJet p.1.1 (p.2.1.2.2.2 1)+productJet (powJet p.1.1 3)
    (coefficientBB p.1 p.2.1-(2:ℝ) • tensorCross p+tensorNormalQuad p))
def tensorEtaCoeff (p : TensorParameter) (a : A) : ScalarJet := productJet (tensorLapse p)
  (p.2.2.2 a-∑ b, productJet (tensorH p b) (tensorK p b a))
def tensorTauCoeff (p : TensorParameter) : MatrixScalarJet :=
  p.2.1.2.1 1-lowerMatrixJet (p.2.1.1 1)+
  mulMatrixJet p.1.1 (p.2.1.2.1 2-lowerMatrixJet (p.2.1.1 2))-
  mulMatrixJet (coefficientT p.1 p.2.1) (tensorQ p)

def tensorCoefficients (p : TensorParameter) : ScalarJet × (A → ScalarJet) × MatrixScalarJet :=
  (tensorLCoeff p,tensorEtaCoeff p,tensorTauCoeff p)

def tensorRegion : Set TensorParameter :=
  {p | determinant (fun i k => (coefficientMetric p.1 p.2.1 i k).1.1) ≠ 0 ∧ 0 < (tensorDen p).1}

lemma tensorBase_smooth : ContDiff ℝ ∞ tensorBase := by unfold tensorBase; fun_prop
lemma tensorQ_smooth : ContDiff ℝ ∞ tensorQ :=
  lowerMatrixJet_smooth.comp (coefficientMetric_smooth.comp tensorBase_smooth)
lemma tensorK_smooth : ContDiff ℝ ∞ tensorK := by unfold tensorK; fun_prop
attribute [local irreducible] tensorK tensorQ
lemma tensorH_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) (a : A) :
    ContDiffAt ℝ ∞ (fun t => tensorH t a) p := by
  have hbase : determinant (fun i k => (coefficientMetric (tensorBase p).1 (tensorBase p).2 i k).1.1) ≠ 0 := by
    simpa only [tensorBase] using hp.1
  have hh := (coefficientShift_smooth hbase).comp p tensorBase_smooth.contDiffAt
  have ha := (contDiffAt_pi.mp hh a).fst
  simpa only [Function.comp_def,tensorBase,tensorH] using ha
attribute [local irreducible] tensorH
lemma tensorDen_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorDen p := by
  have hV := (coefficientV_smooth (p := (p.1,p.2.1)) hp.1).comp p tensorBase_smooth.contDiffAt
  dsimp only [Function.comp_def,tensorBase] at hV
  unfold tensorDen
  fun_prop
attribute [local irreducible] tensorDen
lemma tensorLapseSq_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorLapseSq p := by
  unfold tensorLapseSq
  exact productJet_contDiffAt (by fun_prop)
    ((reciprocalJet_smooth hp.2.ne').comp p (tensorDen_smooth hp))
attribute [local irreducible] tensorLapseSq
lemma tensorLapse_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorLapse p := by
  have hpos : 0 < (constantJet 1+powJet p.1.1 2).1 := by
    change 0 < 1+(powJet p.1.1 2).1
    rw [powJet_fst]; positivity
  have hs := (sqrtJet_smooth hp.2).comp p (tensorDen_smooth hp)
  unfold tensorLapse
  have ha : ContDiffAt ℝ ∞ (fun t : TensorParameter => constantJet 1+powJet t.1.1 2) p := by fun_prop
  have hs0 := sqrtJet_smooth (j := constantJet 1+powJet p.1.1 2) hpos
  have hs1 := hs0.comp p ha
  have hi0 := reciprocalJet_smooth (j := sqrtJet (tensorDen p)) (Real.sqrt_pos.mpr hp.2).ne'
  have hi1 := hi0.comp p hs
  exact productJet_contDiffAt hs1 hi1
attribute [local irreducible] tensorLapse
lemma tensorCross_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorCross p := by
  unfold tensorCross
  apply ContDiffAt.sum
  intro a _
  exact productJet_contDiffAt (tensorH_smooth hp a) (by fun_prop)
attribute [local irreducible] tensorCross
lemma tensorNormalQuad_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorNormalQuad p := by
  unfold tensorNormalQuad
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact productJet_contDiffAt (contDiffAt_pi.mp (contDiffAt_pi.mp tensorK_smooth.contDiffAt a) b)
    (productJet_contDiffAt (tensorH_smooth hp a) (tensorH_smooth hp b))
attribute [local irreducible] tensorNormalQuad
lemma tensorLCoeff_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorLCoeff p := by
  have hBB := (coefficientBB_smooth (p := (p.1,p.2.1)) hp.1).comp p tensorBase_smooth.contDiffAt
  dsimp only [Function.comp_def,tensorBase] at hBB
  have hC := tensorCross_smooth hp
  have hQ := tensorNormalQuad_smooth hp
  unfold tensorLCoeff
  apply productJet_contDiffAt (tensorLapseSq_smooth hp)
  fun_prop
attribute [local irreducible] tensorLCoeff
lemma tensorEtaCoeff_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorEtaCoeff p := by
  apply contDiffAt_pi.mpr
  intro a
  unfold tensorEtaCoeff
  apply productJet_contDiffAt (tensorLapse_smooth hp)
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum
  intro b _
  exact productJet_contDiffAt (tensorH_smooth hp b)
    (contDiffAt_pi.mp (contDiffAt_pi.mp tensorK_smooth.contDiffAt b) a)
attribute [local irreducible] tensorEtaCoeff
lemma tensorTauCoeff_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorTauCoeff p := by
  have hT := (coefficientT_smooth (p := (p.1,p.2.1)) hp.1).comp p tensorBase_smooth.contDiffAt
  dsimp only [Function.comp_def,tensorBase] at hT
  have hQ := tensorQ_smooth.contDiffAt (x := p)
  unfold tensorTauCoeff
  fun_prop
attribute [local irreducible] tensorTauCoeff
lemma tensorCoefficients_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorCoefficients p :=
  (tensorLCoeff_smooth hp).prodMk ((tensorEtaCoeff_smooth hp).prodMk (tensorTauCoeff_smooth hp))

end
end CKSMixedGeometry

end

end OAI
