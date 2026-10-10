import OAI.Geometry.Relativity.CKS.FoliationCurvatureOperator
import OAI.Geometry.Relativity.CKS.MixedMatrixJets
import OAI.Geometry.Relativity.CKS.CollarLapseCoefficient

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev RawMetricData := ((Fin 3 → MatrixScalarJet) × (Fin 2 → I → MatrixScalarJet)) ×
  (CovectorJet × (I → I → ScalarJet))
abbrev RawTensorData := ((Fin 5 → ScalarJet) × CovectorJet) × (CovariantTensorJet × (I → ℝ))
instance rawMetricNormedGroup : NormedAddCommGroup RawMetricData := inferInstance
instance rawTensorNormedGroup : NormedAddCommGroup RawTensorData := inferInstance
instance rawMetricNormedSpace : NormedSpace ℝ RawMetricData := inferInstance
instance rawTensorNormedSpace : NormedSpace ℝ RawTensorData := inferInstance
abbrev RawCollarData := RawMetricData × RawTensorData
instance rawCollarNormedGroup : NormedAddCommGroup RawCollarData := inferInstance
instance rawCollarNormedSpace : NormedSpace ℝ RawCollarData := inferInstance

abbrev RawCollarInput := (Fin 5 → ℝ) × RawCollarData
abbrev rz (p : RawCollarInput) := p.1 0
abbrev re (p : RawCollarInput) := p.1 1
abbrev rθ (p : RawCollarInput) := p.1 2
abbrev rpad (p : RawCollarInput) := p.1 3
abbrev rwgt (p : RawCollarInput) := p.1 4
abbrev rmat (p : RawCollarInput) := p.2.1.1.1
abbrev rdmat (p : RawCollarInput) := p.2.1.1.2
abbrev rshift (p : RawCollarInput) := p.2.1.2.1
abbrev rdshift (p : RawCollarInput) := p.2.1.2.2
abbrev rscalar (p : RawCollarInput) := p.2.2.1.1
abbrev reta (p : RawCollarInput) := p.2.2.1.2
abbrev rtau (p : RawCollarInput) := p.2.2.2.1
abbrev retar (p : RawCollarInput) := p.2.2.2.2

def rawQ (p : RawCollarInput) : MatrixScalarJet := rmat p 0+ (rz p^3*(1-re p)) • rmat p 1
def rawDQ (p : RawCollarInput) (a : I) : MatrixScalarJet := rdmat p 0 a+(rz p^3*(1-re p)) • rdmat p 1 a
def rawS (p : RawCollarInput) : CovectorJet := (1-re p) • rshift p
def rawDS (p : RawCollarInput) : I → I → ScalarJet := (1-re p) • rdshift p
def rawQr (p : RawCollarInput) : MatrixScalarJet := (1-re p) • rmat p 2-rθ p • rmat p 1
def rawExpansionInput (p : RawCollarInput) : ExpansionInput :=
  (rawQ p,rawDQ p,rawQr p,rawS p,rawDS p)
def rawC (p : RawCollarInput) (i k : I) : ScalarJet :=
  rawQr p i k-rz p • normalizedLieJet (rawExpansionInput p) i k

def matrixTraceJet (q t : MatrixScalarJet) : ScalarJet :=
  ∑ i, ∑ k, productJet (inverseMatrixJet q i k) (t k i)
def traceFreeJet (q t : MatrixScalarJet) (i k : I) : ScalarJet :=
  t i k-(1/2:ℝ) • productJet (matrixTraceJet q t) (q i k)
def rawD (p : RawCollarInput) : ScalarJet := (1/4:ℝ) • matrixTraceJet (rawQ p) (rawC p)
def rawT (p : RawCollarInput) : ScalarJet := (1-re p) • rscalar p 0
def rawF (p : RawCollarInput) : ScalarJet :=
  (1-re p) • rscalar p 1+re p • rscalar p 4+constantJet (rpad p)
def rawL (p : RawCollarInput) : ScalarJet := (1-re p) • rscalar p 2
def rawTr (p : RawCollarInput) : ScalarJet := (1-re p) • rscalar p 3-rθ p • rscalar p 0
def rawLapseInput (p : RawCollarInput) : LapseCoefficientInput := (rz p,rawT p,rawF p,rawD p)
def rawA (p : RawCollarInput) : ScalarJet := lapseA (rawLapseInput p)
def rawLambda (p : RawCollarInput) : ℝ := Real.sqrt (1+rz p^2)*(1+rz p^3*(rawA p).1)
def rawX (p : RawCollarInput) (i k : I) : ℝ :=
  (rawLambda p/2)*(traceFreeJet (rawQ p) (rawC p) i k).1

def scalarMatrixToJet (q : MatrixScalarJet) : Jet :=
  ((fun i k => (q i k).1),(fun a i k => (q i k).2.1 a),(fun a b i k => (q i k).2.2 a b))
def rawMomentumInput (p : RawCollarInput) : MomentumInput :=
  (rz p,rwgt p,scalarMatrixToJet (rawQ p),![rawA p,rawT p,rawL p,rawTr p,rawD p],
    rawS p,(1-re p) • reta p,(1-re p) • traceFreeJet (rawQ p) (rtau p),
    rawX p,fun a => (1-re p)*retar p a-rθ p*(reta p a).1)

def rawRegular (p : RawCollarInput) : Prop := determinant (fun i k => (rawQ p i k).1) ≠ 0

lemma rawQ_smooth : ContDiff ℝ ∞ rawQ := by unfold rawQ; fun_prop
lemma rawExpansionInput_smooth : ContDiff ℝ ∞ rawExpansionInput := by
  unfold rawExpansionInput rawQ rawDQ rawQr rawS rawDS
  fun_prop
lemma rawC_smooth (i k : I) : ContDiff ℝ ∞ (fun p => rawC p i k) := by
  unfold rawC
  exact (by unfold rawQr; fun_prop : ContDiff ℝ ∞ (fun p : RawCollarInput => rawQr p i k)).sub
    ((by fun_prop : ContDiff ℝ ∞ rz).fun_smul ((normalizedLieJet_smooth i k).comp rawExpansionInput_smooth))
lemma matrixTraceJet_smooth {q t : MatrixScalarJet}
    (h : determinant (fun i k => (q i k).1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => matrixTraceJet qt.1 qt.2) (q,t) := by
  unfold matrixTraceJet
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact productJet_smooth.contDiffAt.comp (q,t)
    (((inverseMatrixJet_smooth h i k).comp (q,t) (by fun_prop :
      ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.1) (q,t))).prodMk (by fun_prop : ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.2 k i) (q,t)))
lemma traceFreeJet_smooth {q t : MatrixScalarJet}
    (h : determinant (fun i k => (q i k).1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => traceFreeJet qt.1 qt.2) (q,t) := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  unfold traceFreeJet
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.2 i k) (q,t)).sub
    ((productJet_smooth.contDiffAt.comp (q,t) ((matrixTraceJet_smooth h).prodMk (by fun_prop))).const_smul (1/2:ℝ))
lemma rawD_smooth {p : RawCollarInput} (hp : rawRegular p) : ContDiffAt ℝ ∞ rawD p := by
  have hc : ContDiff ℝ ∞ rawC := contDiff_pi.mpr fun i => contDiff_pi.mpr fun k => rawC_smooth i k
  exact ((matrixTraceJet_smooth hp).comp p (rawQ_smooth.contDiffAt.prodMk hc.contDiffAt)).const_smul (1/4:ℝ)
lemma rawT_smooth : ContDiff ℝ ∞ rawT := by unfold rawT; fun_prop
lemma rawF_smooth : ContDiff ℝ ∞ rawF := by
  unfold rawF constantJet
  fun_prop
lemma rawLapseInput_smooth {p : RawCollarInput} (hp : rawRegular p) :
    ContDiffAt ℝ ∞ rawLapseInput p :=
  (by fun_prop : ContDiffAt ℝ ∞ rz p).prodMk
    (rawT_smooth.contDiffAt.prodMk (rawF_smooth.contDiffAt.prodMk (rawD_smooth hp)))
lemma rawA_smooth {p : RawCollarInput} (hp : rawRegular p)
    (hl : rawLapseInput p ∈ lapseCoefficientRegion) : ContDiffAt ℝ ∞ rawA p :=
  (lapseA_smooth hl).comp p (rawLapseInput_smooth hp)
lemma rawMomentumInput_smooth {p : RawCollarInput} (hp : rawRegular p)
    (hl : rawLapseInput p ∈ lapseCoefficientRegion) : ContDiffAt ℝ ∞ rawMomentumInput p := by
  have hq := rawQ_smooth.contDiffAt (x:=p)
  have ha := rawA_smooth hp hl
  have hD := rawD_smooth hp
  have ht0 := traceFreeJet_smooth (q:=rawQ p) (t:=rtau p) hp
  have ht1 := ht0.comp p (hq.prodMk
      (by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => rtau p) p))
  have hτ : ContDiffAt ℝ ∞ (fun p : RawCollarInput => traceFreeJet (rawQ p) (rtau p)) p := ht1
  have hc : ContDiff ℝ ∞ rawC := contDiff_pi.mpr fun i => contDiff_pi.mpr fun k => rawC_smooth i k
  have hx0 := traceFreeJet_smooth (q:=rawQ p) (t:=rawC p) hp
  have hx1 := hx0.comp p (hq.prodMk hc.contDiffAt)
  have hχ : ContDiffAt ℝ ∞ (fun p : RawCollarInput => traceFreeJet (rawQ p) (rawC p)) p := hx1
  have hs : ContDiff ℝ ∞ (fun p : RawCollarInput => Real.sqrt (1+rz p^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : RawCollarInput => 1+rz p^2)).sqrt (by intro p; positivity)
  have hspeed : ContDiffAt ℝ ∞ rawLambda p := by
    unfold rawLambda
    exact hs.contDiffAt.mul (contDiffAt_const.add ((by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => rz p^3) p).mul (contDiffAt_fst.comp p ha)))
  have hX : ContDiffAt ℝ ∞ rawX p := by
    apply contDiffAt_pi.mpr; intro i
    apply contDiffAt_pi.mpr; intro k
    exact (hspeed.div_const 2).mul (contDiffAt_fst.comp p (contDiffAt_pi.mp (contDiffAt_pi.mp hχ i) k))
  unfold rawMomentumInput scalarMatrixToJet
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk
  · fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    fin_cases a <;> dsimp <;>
      first | exact ha | exact rawT_smooth.contDiffAt | exact hD | dsimp [rawL,rawTr]; fun_prop
  apply ContDiffAt.prodMk
  · unfold rawS; fun_prop
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => 1-re p) p).smul hτ
  exact hX.prodMk (by fun_prop)

end
end CKSAngularGeometry

end

end OAI
