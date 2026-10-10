import OAI.Geometry.Relativity.CKS.CKSCoefficientRealization
import OAI.Geometry.Relativity.CKS.CollarRawNull
import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure CollarCoefficientFields where
  metric : Fin 3 → Point → Mat
  shift : Point → Point
  scalar : Fin 5 → Point → ℝ
  eta : Point → Point
  tau : Point → Mat
  etar : Point → Point
  massRadial : Point → ℝ
  massGap : Point → ℝ

def CollarCoefficientFields.RegularAt (f : CollarCoefficientFields) (x : Point) : Prop :=
  (ContDiffAt ℝ 3 (f.metric 0) x ∧ ContDiffAt ℝ 3 (f.metric 1) x ∧
    ContDiffAt ℝ 2 (f.metric 2) x) ∧ ContDiffAt ℝ 3 f.shift x ∧
  (∀ i, ContDiffAt ℝ 2 (f.scalar i) x) ∧ ContDiffAt ℝ 2 f.eta x ∧
    ContDiffAt ℝ 2 f.tau x

def fieldRaw (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : RawNullInput :=
  let m : RawMetricData :=
    (((fun i => matrixScalarJets (f.metric i) x),
      fun i a => matrixScalarJets (fun y j k => D (basis a) (fun z => f.metric i.castSucc z j k) y) x),
      ((fun a => actualScalarJet (fun y => f.shift y a) x),
      fun a k => actualScalarJet (D (basis a) (fun y => f.shift y k)) x))
  let t : RawTensorData :=
    (((fun i => actualScalarJet (f.scalar i) x),
      (fun a => actualScalarJet (fun y => f.eta y a) x)),
      (matrixScalarJets f.tau x,f.etar x))
  ((b,(m,t)),(f.massRadial x,f.massGap x))

def fieldQ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  f.metric 0 y+(b 0^3*(1-b 1)) • f.metric 1 y

def fieldQr (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  (1-b 1) • f.metric 2 y-b 2 • f.metric 1 y

def fieldS (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Point :=
  (1-b 1) • f.shift y

def fieldC (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  fun i k => fieldQr b f y i k-b 0*normalizedLie (fieldQ b f) (fieldS b f) y i k

def fieldD (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ :=
  (1/4:ℝ)*∑ i, ∑ k, inverse (fieldQ b f y) i k*fieldC b f y k i

def fieldT (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ := (1-b 1)*f.scalar 0 y

def fieldF (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ :=
  (1-b 1)*f.scalar 1 y+b 1*f.scalar 4 y+b 3

def fieldL (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ := (1-b 1)*f.scalar 2 y

def fieldTr (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ :=
  (1-b 1)*f.scalar 3 y-b 2*f.scalar 0 y

lemma fieldQ_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (fieldQ b f) x := (hf.1.1).add ((hf.1.2.1).const_smul _)
lemma fieldQr_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldQr b f) x := (hf.1.2.2.const_smul _).sub ((hf.1.2.1.of_le (by norm_num)).const_smul _)
lemma fieldS_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (fieldS b f) x := hf.2.1.const_smul _

lemma field_rawQ (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (fieldQ b f) x=rawQ (fieldRaw b f x).1 := by
  unfold fieldQ
  rw [matrixScalarJets_add ((hf.1.1).of_le (by norm_num)) (((hf.1.2.1).of_le (by norm_num)).const_smul _),
    matrixScalarJets_smul _ ((hf.1.2.1).of_le (by norm_num))]
  rfl
lemma field_rawQr (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (fieldQr b f) x=rawQr (fieldRaw b f x).1 := by
  unfold fieldQr
  rw [matrixScalarJets_sub (((hf.1.2.2).of_le (by norm_num)).const_smul _) (((hf.1.2.1).of_le (by norm_num)).const_smul _),
    matrixScalarJets_smul _ ((hf.1.2.2).of_le (by norm_num)),matrixScalarJets_smul _ ((hf.1.2.1).of_le (by norm_num))]
  rfl
lemma field_rawS (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) (a : I) :
    actualScalarJet (fun y => fieldS b f y a) x=rawS (fieldRaw b f x).1 a := by
  exact actualScalarJet_smul (1-b 1) ((contDiffAt_pi.mp hf.2.1 a).of_le (by norm_num))

end
end CKSAngularGeometry

end

end OAI
