import OAI.Geometry.Relativity.CKS.CKSMassFields
import OAI.Geometry.Relativity.CKS.MixedMassRealization
import OAI.Geometry.Relativity.CKS.MixedFieldJets

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure MassFields where
  sigma : Point → Mat
  mg : Point → Mat
  eg : Point → Mat
  er : Point → Mat
  mK : Point → Mat
  ek : Point → Mat
  b : Point → A → ℝ
  mr : Point → ℝ
  err : Point → ℝ

structure MassFields.RegularAt (f : MassFields) (x : Point) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma x
  mg : ContDiffAt ℝ 3 f.mg x
  eg : ContDiffAt ℝ 3 f.eg x
  er : ContDiffAt ℝ 2 f.er x
  mK : ContDiffAt ℝ 2 f.mK x
  ek : ContDiffAt ℝ 2 f.ek x
  b : ContDiffAt ℝ 3 f.b x
  mr : ContDiffAt ℝ 2 f.mr x
  err : ContDiffAt ℝ 2 f.err x

def massInputOf (f : MassFields) (x : Point) : MassInput :=
  (![matrixThreeJets f.sigma x,matrixThreeJets f.mg x,matrixThreeJets f.eg x],
    ![matrixScalarJets f.er x,matrixScalarJets f.mK x,matrixScalarJets f.ek x],
    (fun a => actualThreeJet (fun y => f.b y a) x),
    ![actualScalarJet f.mr x,actualScalarJet f.err x])

def cksQField (z : Point → ℝ) (f : MassFields) : Point → Mat :=
  fun y => f.sigma y+z y^3 • f.mg y+z y^4 • f.eg y

def cksHField (z : Point → ℝ) (f : MassFields) : Point → A → ℝ :=
  fun y a => ∑ b, inverse (cksQField z f y) a b*f.b y b

def cksLieField (z : Point → ℝ) (f : MassFields) : Point → Mat :=
  normalizedLie (cksQField z f) (cksHField z f)

def cksDField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => (1/4:ℝ)*traceProduct (inverse (cksQField z f y))
    ((-3:ℝ) • f.mg y+z y • (f.er y-(2:ℝ) • f.eg y-cksLieField z f y))

def cksTField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => (1/2:ℝ)*traceProduct (inverse (cksQField z f y))
    (f.mK y-f.mg y+z y • (f.ek y-f.eg y))

def cksBBField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => ∑ i, ∑ k, inverse (cksQField z f y) i k*(f.b y i*f.b y k)

def cksVField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => f.mr y+z y*f.err y+z y^2*f.mr y+z y^3*f.err y-
    (z y^3*(1+z y^2))*cksBBField z f y

def cksFField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  normalizedMassField z (cksDField z f) (cksTField z f) (cksVField z f)

def cksLeadingField (f : MassFields) : Point → ℝ :=
  fun y => (1/2:ℝ)*f.mr y+(1/4:ℝ)*traceProduct (inverse (f.sigma y)) (f.mg y)+
    (1/2:ℝ)*traceProduct (inverse (f.sigma y)) (f.mK y)

lemma cksQField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (cksQField z f) x := (hf.sigma.add ((hz.pow 3).smul hf.mg)).add ((hz.pow 4).smul hf.eg)

lemma cksHField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 3 (cksHField z f) x := by
  have hi := inverse_diff_at (cksQField_diff hz hf) h0
  apply contDiffAt_pi.mpr
  intro a
  exact ContDiffAt.sum fun b _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul
    (contDiffAt_pi.mp hf.b b)

lemma cksLieField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksLieField z f) x := by
  exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun k =>
    normalizedLie_diff (cksQField_diff hz hf) (cksHField_diff hz hf h0) i k

lemma cksDField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksDField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at ((cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hp := (hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).const_smul (-3:ℝ)
  have he := (hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).const_smul (2:ℝ)
  exact (traceProduct_diff hi (hp.add (hz2.smul ((hf.er.sub he).sub (cksLieField_diff hz hf h0))))).const_smul (1/4:ℝ)

lemma cksTField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksTField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at ((cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  exact (traceProduct_diff hi ((hf.mK.sub (hf.mg.of_le (by norm_num))).add
    (hz2.smul (hf.ek.sub (hf.eg.of_le (by norm_num)))))).const_smul (1/2:ℝ)

lemma cksBBField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksBBField z f) x := by
  have hi := inverse_diff_at ((cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hb (i : A) := (contDiffAt_pi.mp hf.b i).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hi i k).mul ((hb i).mul (hb k))

lemma cksVField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksVField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (((hf.mr.add (hz2.mul hf.err)).add ((hz2.pow 2).mul hf.mr)).add
    ((hz2.pow 3).mul hf.err)).sub (((hz2.pow 3).mul (contDiffAt_const.add (hz2.pow 2))).mul (cksBBField_diff hz hf h0))

lemma cksQField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    matrixThreeJets (cksQField z f) x = coefficientMetric (actualThreeJet z x) (massInputOf f x) := by
  unfold cksQField coefficientMetric
  erw [matrixThreeJets_add (hf.sigma.add ((hz.pow 3).smul hf.mg)) ((hz.pow 4).smul hf.eg),
    matrixThreeJets_add hf.sigma ((hz.pow 3).smul hf.mg),
    matrixThreeJets_mul (hz.pow 3) hf.mg,matrixThreeJets_mul (hz.pow 4) hf.eg,
    actualThreeJet_pow hz,actualThreeJet_pow hz]
  rfl

lemma cksHField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    (fun a => actualThreeJet (fun y => cksHField z f y a) x) =
      coefficientShift (actualThreeJet z x) (massInputOf f x) := by
  have hq := cksQField_diff hz hf
  have hi := inverse_diff_at hq h0
  funext a
  unfold cksHField coefficientShift
  rw [actualThreeJet_sum _ (fun b _ => (component_diff hi a b).mul (contDiffAt_pi.mp hf.b b))]
  apply Finset.sum_congr rfl
  intro b _
  rw [actualThreeJet_mul (component_diff hi a b) (contDiffAt_pi.mp hf.b b),
    actual_inverseMatrixThreeJet hq h0,cksQField_realized hz hf]
  rfl

lemma cksLieField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    matrixScalarJets (cksLieField z f) x =
      coefficientLie (actualThreeJet z x) (massInputOf f x) := by
  funext i k
  change actualScalarJet (fun y => normalizedLie (cksQField z f) (cksHField z f) y i k) x = _
  rw [actual_normalizedLieJet (cksQField_diff hz hf) (cksHField_diff hz hf h0),
    cksQField_realized hz hf,cksHField_realized hz hf h0]
  rfl

end
end CKSMixedGeometry

end

end OAI
