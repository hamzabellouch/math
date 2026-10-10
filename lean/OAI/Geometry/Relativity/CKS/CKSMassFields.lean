import OAI.Geometry.Relativity.CKS.CKSMetricInput
import OAI.Geometry.Relativity.CKS.MassJetRealization

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure MassFields where
  sigma : Point → Mat
  mg : Point → Mat
  eg : Point → Mat
  er : Point → Mat
  mK : Point → Mat
  ek : Point → Mat
  b : Point → Point
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

def cksQField (z : ℝ) (f : MassFields) : Point → Mat :=
  fun y => f.sigma y+z^3 • f.mg y+z^4 • f.eg y

def cksHField (z : ℝ) (f : MassFields) : Point → Point :=
  fun y a => ∑ b, inverse (cksQField z f y) a b*f.b y b

def cksLieField (z : ℝ) (f : MassFields) : Point → Mat :=
  normalizedLie (cksQField z f) (cksHField z f)

def cksDField (z : ℝ) (f : MassFields) : Point → ℝ :=
  fun y => (1/4:ℝ)*traceProduct (inverse (cksQField z f y))
    ((-3:ℝ) • f.mg y+z • (f.er y-(2:ℝ) • f.eg y-cksLieField z f y))

def cksTField (z : ℝ) (f : MassFields) : Point → ℝ :=
  fun y => (1/2:ℝ)*traceProduct (inverse (cksQField z f y))
    (f.mK y-f.mg y+z • (f.ek y-f.eg y))

def cksBBField (z : ℝ) (f : MassFields) : Point → ℝ :=
  fun y => ∑ i, ∑ k, inverse (cksQField z f y) i k*(f.b y i*f.b y k)

def cksVField (z : ℝ) (f : MassFields) : Point → ℝ :=
  fun y => f.mr y+z*f.err y+z^2*f.mr y+z^3*f.err y-
    (z^3*(1+z^2))*cksBBField z f y

def cksFField (z : ℝ) (f : MassFields) : Point → ℝ :=
  normalizedMassField z (cksDField z f) (cksTField z f) (cksVField z f)

def cksLeadingField (f : MassFields) : Point → ℝ :=
  fun y => (1/2:ℝ)*f.mr y+(1/4:ℝ)*traceProduct (inverse (f.sigma y)) (f.mg y)+
    (1/2:ℝ)*traceProduct (inverse (f.sigma y)) (f.mK y)

lemma cksQField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (cksQField z f) x := (hf.sigma.add (hf.mg.const_smul _)).add (hf.eg.const_smul _)

lemma cksHField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 3 (cksHField z f) x := by
  have hi := inverse_diff_at (cksQField_diff z hf) h0
  apply contDiffAt_pi.mpr
  intro a
  exact ContDiffAt.sum fun b _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul
    (contDiffAt_pi.mp hf.b b)

lemma cksLieField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksLieField z f) x := by
  exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun k =>
    normalizedLie_diff (cksQField_diff z hf) (cksHField_diff z hf h0) i k

lemma cksDField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksDField z f) x := by
  have hi := inverse_diff_at ((cksQField_diff z hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hp := (hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).const_smul (-3:ℝ)
  have he := (hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).const_smul (2:ℝ)
  exact (traceProduct_diff hi (hp.add (((hf.er.sub he).sub (cksLieField_diff z hf h0)).const_smul z))).const_smul (1/4:ℝ)

lemma cksTField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksTField z f) x := by
  have hi := inverse_diff_at ((cksQField_diff z hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  exact (traceProduct_diff hi ((hf.mK.sub (hf.mg.of_le (by norm_num))).add
    ((hf.ek.sub (hf.eg.of_le (by norm_num))).const_smul z))).const_smul (1/2:ℝ)

lemma cksBBField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksBBField z f) x := by
  have hi := inverse_diff_at ((cksQField_diff z hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hb (i : I) := (contDiffAt_pi.mp hf.b i).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hi i k).mul ((hb i).mul (hb k))

lemma cksVField_diff (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksVField z f) x := by
  exact (((hf.mr.add (hf.err.const_smul z)).add (hf.mr.const_smul (z^2))).add
    (hf.err.const_smul (z^3))).sub ((cksBBField_diff z hf h0).const_smul (z^3*(1+z^2)))

lemma cksQField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    matrixThreeJets (cksQField z f) x = coefficientMetric z (massInputOf f x) := by
  change matrixThreeJets (fun y => f.sigma y+z^3 • f.mg y+z^4 • f.eg y) x =
    matrixThreeJets f.sigma x+z^3 • matrixThreeJets f.mg x+z^4 • matrixThreeJets f.eg x
  rw [matrixThreeJets_add (hf.sigma.add (hf.mg.const_smul _)) (hf.eg.const_smul _),
    matrixThreeJets_add hf.sigma (hf.mg.const_smul _),matrixThreeJets_smul _ hf.mg,matrixThreeJets_smul _ hf.eg]

lemma cksHField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    (fun a => actualThreeJet (fun y => cksHField z f y a) x) = coefficientShift z (massInputOf f x) := by
  rw [show cksHField z f = (fun y a => ∑ b, inverse (cksQField z f y) a b*f.b y b) from rfl,
    actual_raisedMixedJet (cksQField_diff z hf) hf.b h0,cksQField_realized z hf]
  rfl

lemma cksLieField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    matrixScalarJets (cksLieField z f) x =
      coefficientLie z (massInputOf f x) := by
  funext i k
  change actualScalarJet (fun y => normalizedLie (cksQField z f) (cksHField z f) y i k) x = _
  rw [actual_normalizedLieJet (Q := fun _ => 0) (cksQField_diff z hf) (cksHField_diff z hf h0),
    actualExpansionInput_pack,cksQField_realized z hf,cksHField_realized z hf h0]
  rfl

end
end CKSAngularGeometry

end

end OAI
