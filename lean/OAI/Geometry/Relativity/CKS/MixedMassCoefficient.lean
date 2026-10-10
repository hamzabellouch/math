import OAI.Geometry.Relativity.CKS.CKSMassCoefficient
import OAI.Geometry.Relativity.CKS.MixedMatrixJets
import OAI.Geometry.Relativity.CKS.MixedJetPolynomial

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MassInput := (Fin 3 → MatrixThreeJet) × (Fin 3 → MatrixScalarJet) ×
  (A → ScalarThreeJet) × (A → ScalarJet)

instance massInputNormed : NormedAddCommGroup MassInput := by
  letI : NormedAddCommGroup (Fin 3 → MatrixThreeJet) := inferInstance
  letI : NormedAddCommGroup (Fin 3 → MatrixScalarJet) := inferInstance
  letI : NormedAddCommGroup ((A → ScalarThreeJet) × (A → ScalarJet)) := inferInstance
  exact Prod.normedAddCommGroup
instance massInputSpace : NormedSpace ℝ MassInput := by
  letI : NormedSpace ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  letI : NormedSpace ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  letI : NormedSpace ℝ ((A → ScalarThreeJet) × (A → ScalarJet)) := inferInstance
  exact Prod.normedSpace
abbrev MassParameter := ScalarThreeJet × MassInput

def lowerMatrixJet (q : MatrixThreeJet) : MatrixScalarJet := fun i k => (q i k).1
def mulMatrixJet (z : ScalarJet) (q : MatrixScalarJet) : MatrixScalarJet := fun i k => productJet z (q i k)
def mulMatrixThreeJet (z : ScalarThreeJet) (q : MatrixThreeJet) : MatrixThreeJet := fun i k => productThreeJet z (q i k)
def traceProductJet (q p : MatrixScalarJet) : ScalarJet := ∑ i, ∑ k, productJet (q i k) (p k i)

def coefficientMetric (z : ScalarThreeJet) (j : MassInput) : MatrixThreeJet :=
  j.1 0+mulMatrixThreeJet (powThreeJet z 3) (j.1 1)+mulMatrixThreeJet (powThreeJet z 4) (j.1 2)
def coefficientShift (z : ScalarThreeJet) (j : MassInput) : A → ScalarThreeJet :=
  fun a => ∑ b, productThreeJet (inverseMatrixThreeJet (coefficientMetric z j) a b) (j.2.2.1 b)
def lieJet (q : MatrixThreeJet) (h : A → ScalarThreeJet) : MatrixScalarJet := fun i k => ∑ a,
  (productJet (h a).1 ((q i k).2 a.succ)+productJet (q a k).1 ((h a).2 i.succ)+
    productJet (q i a).1 ((h a).2 k.succ))
def coefficientLie (z : ScalarThreeJet) (j : MassInput) : MatrixScalarJet :=
  lieJet (coefficientMetric z j) (coefficientShift z j)
def coefficientD (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  (1/4:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)))
    ((-3:ℝ) • lowerMatrixJet (j.1 1)+mulMatrixJet z.1 (j.2.1 0-(2:ℝ) • lowerMatrixJet (j.1 2)-coefficientLie z j))
def coefficientT (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  (1/2:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)))
    (j.2.1 1-lowerMatrixJet (j.1 1)+mulMatrixJet z.1 (j.2.1 2-lowerMatrixJet (j.1 2)))
def coefficientBB (z : ScalarThreeJet) (j : MassInput) : ScalarJet := ∑ i, ∑ k,
  productJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)) i k)
    (productJet (j.2.2.1 i).1 (j.2.2.1 k).1)
def coefficientV (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  j.2.2.2 0+productJet z.1 (j.2.2.2 1)+
    productJet (powJet z.1 2) (j.2.2.2 0)+productJet (powJet z.1 3) (j.2.2.2 1)-
    productJet (productJet (powJet z.1 3) (constantJet 1+powJet z.1 2)) (coefficientBB z j)
def cksMassJet (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  normalizedMassJet z.1 (coefficientD z j) (coefficientT z j) (coefficientV z j)
def leadingMassJet (j : MassInput) : ScalarJet :=
  (1/2:ℝ) • j.2.2.2 0+
    (1/4:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (j.1 0))) (lowerMatrixJet (j.1 1))+
    (1/2:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (j.1 0))) (j.2.1 1)

lemma traceProductJet_sub (q p s : MatrixScalarJet) :
    traceProductJet q (p-s) = traceProductJet q p-traceProductJet q s := by
  simp [traceProductJet,productJet_sub_right,Finset.sum_sub_distrib]
lemma traceProductJet_smul (c : ℝ) (q p : MatrixScalarJet) :
    traceProductJet q (c • p) = c • traceProductJet q p := by
  simp [traceProductJet,productJet_smul_right]
@[simp] lemma mulMatrixJet_zero (q : MatrixScalarJet) : mulMatrixJet 0 q = 0 := by
  funext i k; exact productJet_zero_left _
@[simp] lemma mulMatrixThreeJet_zero (q : MatrixThreeJet) : mulMatrixThreeJet 0 q = 0 := by
  funext i k; exact productThreeJet_zero_left _
@[simp] lemma coefficientMetric_zero (j : MassInput) : coefficientMetric 0 j = j.1 0 := by
  simp [coefficientMetric]

lemma cksMassJet_zero (j : MassInput) : cksMassJet 0 j = leadingMassJet j := by
  simp only [cksMassJet,normalizedMassJet_zero,coefficientD,coefficientT,coefficientV,
    coefficientMetric_zero,Prod.fst_zero,mulMatrixJet_zero,powJet_zero_succ,
    productJet_zero_left,add_zero,sub_zero,leadingMassJet]
  erw [traceProductJet_sub,traceProductJet_smul]
  module

@[fun_prop] lemma lowerMatrixJet_smooth : ContDiff ℝ ∞ lowerMatrixJet := by unfold lowerMatrixJet; fun_prop
lemma traceProductJet_smooth : ContDiff ℝ ∞
    (fun j : MatrixScalarJet × MatrixScalarJet => traceProductJet j.1 j.2) := by
  unfold traceProductJet
  fun_prop
lemma mulMatrixJet_smooth : ContDiff ℝ ∞
    (fun j : ScalarJet × MatrixScalarJet => mulMatrixJet j.1 j.2) := by
  unfold mulMatrixJet
  fun_prop
lemma mulMatrixThreeJet_smooth : ContDiff ℝ ∞
    (fun j : ScalarThreeJet × MatrixThreeJet => mulMatrixThreeJet j.1 j.2) := by
  unfold mulMatrixThreeJet
  fun_prop
section SmoothRules
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[fun_prop] lemma mulMatrixThreeJet_contDiff {f : E → ScalarThreeJet} {g : E → MatrixThreeJet}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => mulMatrixThreeJet (f x) (g x)) :=
  mulMatrixThreeJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma mulMatrixJet_contDiff {f : E → ScalarJet} {g : E → MatrixScalarJet}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => mulMatrixJet (f x) (g x)) :=
  mulMatrixJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma mulMatrixJet_contDiffAt {f : E → ScalarJet} {g : E → MatrixScalarJet} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => mulMatrixJet (f y) (g y)) x :=
  mulMatrixJet_smooth.contDiffAt.comp x (hf.prodMk hg)
end SmoothRules

lemma coefficientMetric_smooth : ContDiff ℝ ∞ (fun p : MassParameter => coefficientMetric p.1 p.2) := by
  unfold coefficientMetric
  fun_prop
attribute [local irreducible] coefficientMetric

lemma coefficientShift_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientShift t.1 t.2) p := by
  unfold coefficientShift
  apply contDiffAt_pi.mpr
  intro a
  apply ContDiffAt.sum
  intro b _
  apply productThreeJet_contDiffAt
  · exact (inverseMatrixThreeJet_smooth (q := coefficientMetric p.1 p.2) hp a b).comp p coefficientMetric_smooth.contDiffAt
  · fun_prop
attribute [local irreducible] coefficientShift

lemma lieJet_smooth : ContDiff ℝ ∞ (fun p : MatrixThreeJet × (A → ScalarThreeJet) => lieJet p.1 p.2) := by
  unfold lieJet
  fun_prop
attribute [local irreducible] lieJet
lemma coefficientLie_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientLie t.1 t.2) p := by
  unfold coefficientLie
  exact lieJet_smooth.contDiffAt.comp p
    (coefficientMetric_smooth.contDiffAt.prodMk (coefficientShift_smooth (p := p) hp))
attribute [local irreducible] coefficientLie
lemma coefficientInverse_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => inverseMatrixJet (lowerMatrixJet (coefficientMetric t.1 t.2))) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact (inverseMatrixJet_smooth (q := lowerMatrixJet (coefficientMetric p.1 p.2)) hp i k).comp p
    (lowerMatrixJet_smooth.contDiffAt.comp p coefficientMetric_smooth.contDiffAt)
lemma coefficientD_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientD t.1 t.2) p := by
  have hl := coefficientLie_smooth (p := p) hp
  have hlower (order : Fin 3) : ContDiffAt ℝ ∞
      (fun t : MassParameter => lowerMatrixJet (t.2.1 order)) p := by
    fun_prop
  have harg : ContDiffAt ℝ ∞ (fun t : MassParameter =>
      (-3:ℝ) • lowerMatrixJet (t.2.1 1)+mulMatrixJet t.1.1
        (t.2.2.1 0-(2:ℝ) • lowerMatrixJet (t.2.1 2)-coefficientLie t.1 t.2)) p := by
    apply ContDiffAt.add
    · exact (contDiffAt_const (c := (-3 : ℝ))).smul (hlower 1)
    · apply mulMatrixJet_contDiffAt
      · fun_prop
      · exact ((by fun_prop : ContDiffAt ℝ ∞ (fun t : MassParameter => t.2.2.1 0) p).sub
          ((contDiffAt_const (c := (2 : ℝ))).smul (hlower 2))).sub hl
  unfold coefficientD
  exact (traceProductJet_smooth.contDiffAt.comp p
    ((coefficientInverse_smooth (p := p) hp).prodMk harg)).const_smul _
attribute [local irreducible] coefficientD
lemma coefficientT_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientT t.1 t.2) p := by
  have harg : ContDiff ℝ ∞ (fun t : MassParameter =>
      t.2.2.1 1-lowerMatrixJet (t.2.1 1)+mulMatrixJet t.1.1
        (t.2.2.1 2-lowerMatrixJet (t.2.1 2))) := by fun_prop
  unfold coefficientT
  exact (traceProductJet_smooth.contDiffAt.comp p
    ((coefficientInverse_smooth (p := p) hp).prodMk harg.contDiffAt)).const_smul _
attribute [local irreducible] coefficientT
lemma coefficientBB_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientBB t.1 t.2) p := by
  unfold coefficientBB
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  apply productJet_contDiffAt
  · exact contDiffAt_pi.mp (contDiffAt_pi.mp (coefficientInverse_smooth (p := p) hp) i) k
  · fun_prop
attribute [local irreducible] coefficientBB
lemma coefficientV_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientV t.1 t.2) p := by
  have hbb := coefficientBB_smooth (p := p) hp
  unfold coefficientV
  fun_prop
attribute [local irreducible] coefficientV
lemma cksMassJet_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0)
    (hv : (constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2)).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => cksMassJet t.1 t.2) p := by
  have hz : ContDiffAt ℝ ∞ (fun t : MassParameter => t.1.1) p := by fun_prop
  have hinner := hz.prodMk ((coefficientD_smooth (p := p) hp).prodMk
    ((coefficientT_smooth (p := p) hp).prodMk (coefficientV_smooth (p := p) hp)))
  have hh := (normalizedMassJet_smooth
    (j := (p.1.1,coefficientD p.1 p.2,coefficientT p.1 p.2,coefficientV p.1 p.2)) hv).comp p hinner
  exact hh

end
end CKSMixedGeometry

end

end OAI
