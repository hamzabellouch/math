import OAI.Geometry.Relativity.CKS.JetPolynomial
import OAI.Geometry.Relativity.CKS.CollarExpansionInputNorm

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MassInput := (Fin 3 → MatrixThreeJet) × (Fin 3 → MatrixScalarJet) ×
  (I → ScalarThreeJet) × (I → ScalarJet)

def lowerMatrixJet (q : MatrixThreeJet) : MatrixScalarJet := fun i k => (q i k).1

def traceProductJet (q p : MatrixScalarJet) : ScalarJet :=
  ∑ i, ∑ k, productJet (q i k) (p k i)

def coefficientMetric (z : ℝ) (j : MassInput) : MatrixThreeJet :=
  j.1 0+z^3 • j.1 1+z^4 • j.1 2

def coefficientShift (z : ℝ) (j : MassInput) : I → ScalarThreeJet :=
  raisedMixedJet (coefficientMetric z j,j.2.2.1)

def coefficientLie (z : ℝ) (j : MassInput) : MatrixScalarJet :=
  normalizedLieJet (packExpansion (coefficientMetric z j) 0 (coefficientShift z j))

def coefficientD (z : ℝ) (j : MassInput) : ScalarJet :=
  (1/4:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)))
    ((-3:ℝ) • lowerMatrixJet (j.1 1)+z • (j.2.1 0-(2:ℝ) • lowerMatrixJet (j.1 2)-coefficientLie z j))

def coefficientT (z : ℝ) (j : MassInput) : ScalarJet :=
  (1/2:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)))
    (j.2.1 1-lowerMatrixJet (j.1 1)+z • (j.2.1 2-lowerMatrixJet (j.1 2)))

def coefficientBB (z : ℝ) (j : MassInput) : ScalarJet :=
  ∑ i, ∑ k, productJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)) i k)
    (productJet (j.2.2.1 i).1 (j.2.2.1 k).1)

def coefficientV (z : ℝ) (j : MassInput) : ScalarJet :=
  j.2.2.2 0+z • j.2.2.2 1+z^2 • j.2.2.2 0+z^3 • j.2.2.2 1-
    (z^3*(1+z^2)) • coefficientBB z j

def cksMassJet (z : ℝ) (j : MassInput) : ScalarJet :=
  normalizedMassJet z (coefficientD z j) (coefficientT z j) (coefficientV z j)

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

lemma coefficientMetric_zero (j : MassInput) : coefficientMetric 0 j = j.1 0 := by
  simp [coefficientMetric]

lemma cksMassJet_zero (j : MassInput) : cksMassJet 0 j = leadingMassJet j := by
  simp only [cksMassJet,normalizedMassJet_zero,coefficientD,coefficientT,coefficientV,
    coefficientMetric_zero,zero_smul,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_mul,add_zero,sub_zero,
    leadingMassJet]
  erw [traceProductJet_sub,traceProductJet_smul]
  module

lemma lowerMatrixJet_smooth : ContDiff ℝ ∞ lowerMatrixJet := by unfold lowerMatrixJet; fun_prop
lemma traceProductJet_smooth : ContDiff ℝ ∞
    (fun j : MatrixScalarJet × MatrixScalarJet => traceProductJet j.1 j.2) := by
  unfold traceProductJet
  exact ContDiff.sum fun i _ => ContDiff.sum fun k _ => productJet_smooth.comp
    (by fun_prop : ContDiff ℝ ∞ (fun j : MatrixScalarJet × MatrixScalarJet => (j.1 i k,j.2 k i)))
lemma coefficientMetric_smooth : ContDiff ℝ ∞ (fun p : ℝ × MassInput => coefficientMetric p.1 p.2) := by
  unfold coefficientMetric
  fun_prop

lemma coefficientShift_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => coefficientShift t.1 t.2) p :=
  (raisedMixedJet_smooth hp).comp p
    (coefficientMetric_smooth.contDiffAt.prodMk (by fun_prop))

lemma coefficientLie_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => coefficientLie t.1 t.2) p := by
  have hpack : ContDiffAt ℝ ∞ (fun t : ℝ × MassInput =>
      packExpansion (coefficientMetric t.1 t.2) 0 (coefficientShift t.1 t.2)) p := by
    have h : ContDiff ℝ ∞ (fun t : MatrixThreeJet × (I → ScalarThreeJet) => packExpansion t.1 0 t.2) := by
      unfold packExpansion
      fun_prop
    exact h.contDiffAt.comp p (coefficientMetric_smooth.contDiffAt.prodMk (coefficientShift_smooth hp))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact (normalizedLieJet_smooth i k).contDiffAt.comp p hpack

lemma coefficientInverse_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => inverseMatrixJet (lowerMatrixJet (coefficientMetric t.1 t.2))) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact (inverseMatrixJet_smooth hp i k).comp p
    (lowerMatrixJet_smooth.contDiffAt.comp p coefficientMetric_smooth.contDiffAt)

lemma coefficientD_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => coefficientD t.1 t.2) p := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ × MassInput => lowerMatrixJet (t.2.1 1)) :=
    lowerMatrixJet_smooth.comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ × MassInput => lowerMatrixJet (t.2.1 2)) :=
    lowerMatrixJet_smooth.comp (by fun_prop)
  have harg : ContDiffAt ℝ ∞ (fun t : ℝ × MassInput =>
      (-3:ℝ) • lowerMatrixJet (t.2.1 1)+t.1 • (t.2.2.1 0-(2:ℝ) • lowerMatrixJet (t.2.1 2)-coefficientLie t.1 t.2)) p := by
    exact ((contDiffAt_const (c := (-3:ℝ))).smul h1.contDiffAt).add
      (contDiffAt_fst.smul (((by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => t.2.2.1 0) p).sub
        ((contDiffAt_const (c := (2:ℝ))).smul h2.contDiffAt)).sub (coefficientLie_smooth hp)))
  exact (traceProductJet_smooth.contDiffAt.comp p ((coefficientInverse_smooth hp).prodMk harg)).const_smul _

lemma coefficientT_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => coefficientT t.1 t.2) p := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ × MassInput => lowerMatrixJet (t.2.1 1)) :=
    lowerMatrixJet_smooth.comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ × MassInput => lowerMatrixJet (t.2.1 2)) :=
    lowerMatrixJet_smooth.comp (by fun_prop)
  have harg : ContDiff ℝ ∞ (fun t : ℝ × MassInput =>
      t.2.2.1 1-lowerMatrixJet (t.2.1 1)+t.1 • (t.2.2.1 2-lowerMatrixJet (t.2.1 2))) := by fun_prop
  exact (traceProductJet_smooth.contDiffAt.comp p ((coefficientInverse_smooth hp).prodMk harg.contDiffAt)).const_smul _

lemma coefficientBB_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => coefficientBB t.1 t.2) p := by
  unfold coefficientBB
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro k hk
  have hbb : ContDiff ℝ ∞ (fun t : ℝ × MassInput => productJet (t.2.2.2.1 i).1 (t.2.2.2.1 k).1) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ × MassInput => ((t.2.2.2.1 i).1,(t.2.2.2.1 k).1)))
  exact productJet_smooth.contDiffAt.comp p
    ((contDiffAt_pi.mp (contDiffAt_pi.mp (coefficientInverse_smooth hp) i) k).prodMk hbb.contDiffAt)

lemma coefficientV_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => coefficientV t.1 t.2) p := by
  unfold coefficientV
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ × MassInput =>
    t.2.2.2.2 0+t.1 • t.2.2.2.2 1+t.1^2 • t.2.2.2.2 0+t.1^3 • t.2.2.2.2 1) p).sub
    ((by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => t.1^3*(1+t.1^2)) p).smul
      (coefficientBB_smooth hp))

lemma cksMassJet_smooth {p : ℝ × MassInput}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0)
    (hv : (constantJet 1+p.1^3 • coefficientV p.1 p.2).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × MassInput => cksMassJet t.1 t.2) p := by
  have hD := coefficientD_smooth hp
  have hT := coefficientT_smooth hp
  have hV := coefficientV_smooth hp
  have harg : ContDiffAt ℝ ∞ (fun t : ℝ × MassInput =>
      (t.1,coefficientD t.1 t.2,coefficientT t.1 t.2,coefficientV t.1 t.2)) p :=
    contDiffAt_fst.prodMk (hD.prodMk (hT.prodMk hV))
  have houter : ContDiffAt ℝ ∞ (fun k : ℝ × ScalarJet × ScalarJet × ScalarJet =>
      normalizedMassJet k.1 k.2.1 k.2.2.1 k.2.2.2)
      (p.1,coefficientD p.1 p.2,coefficientT p.1 p.2,coefficientV p.1 p.2) :=
    normalizedMassJet_smooth hv
  have hh := houter.comp p harg
  exact hh

end
end CKSAngularGeometry

end

end OAI
