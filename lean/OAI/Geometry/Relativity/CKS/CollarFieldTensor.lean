import OAI.Geometry.Relativity.CKS.CollarFieldLapse

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceFreeField (q t : Point → Mat) (y : Point) : Mat := fun i k =>
  t y i k-(1/2:ℝ)*(∑ a, ∑ b, inverse (q y) a b*t y b a)*q y i k

lemma traceFreeField_diff {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 2 (traceFreeField q t) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  exact (component_diff ht i k).sub
    ((contDiffAt_const.mul (matrixTraceField_diff hq ht h0)).mul (component_diff hq i k))

lemma actual_traceFreeJet {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    matrixScalarJets (traceFreeField q t) x=traceFreeJet (matrixScalarJets q x) (matrixScalarJets t x) := by
  funext i k
  change actualScalarJet (fun y => t y i k-(1/2:ℝ)*(∑ a, ∑ b, inverse (q y) a b*t y b a)*q y i k) x=_
  have htrace := matrixTraceField_diff hq ht h0
  erw [actualScalarJet_sub (component_diff ht i k) ((contDiffAt_const.mul htrace).mul (component_diff hq i k)),
    actualScalarJet_mul (contDiffAt_const.mul htrace) (component_diff hq i k),
    actualScalarJet_smul (1/2:ℝ) htrace,actual_matrixTraceJet hq ht h0]
  unfold traceFreeJet
  rw [productJet_smul_left]
  rfl

def fieldEta (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Point := (1-b 1) • f.eta y

def fieldTau (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  (1-b 1) • traceFreeField (fieldQ b f) f.tau y

def fieldEr (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Point :=
  fun a => (1-b 1)*f.etar y a-b 2*f.eta y a

def fieldX (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  (Real.sqrt (1+b 0^2)*fieldNormalizedLapse b f y/2) • traceFreeField (fieldQ b f) (fieldC b f) y

lemma field_rawEta (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    (fun a => actualScalarJet (fun y => fieldEta b f y a) x)=
      (1-re (fieldRaw b f x).1) • reta (fieldRaw b f x).1 := by
  funext a
  exact actualScalarJet_smul (1-b 1) (contDiffAt_pi.mp hf.2.2.2.1 a)

lemma field_rawTau (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) :
    matrixScalarJets (fieldTau b f) x=
      (1-re (fieldRaw b f x).1) • traceFreeJet (rawQ (fieldRaw b f x).1) (rtau (fieldRaw b f x).1) := by
  unfold fieldTau
  rw [matrixScalarJets_smul _ (traceFreeField_diff ((fieldQ_diff b hf).of_le (by norm_num)) hf.2.2.2.2 h0),
    actual_traceFreeJet ((fieldQ_diff b hf).of_le (by norm_num)) hf.2.2.2.2 h0,field_rawQ b hf]
  rfl

lemma field_rawX (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    fieldX b f x=rawX (fieldRaw b f x).1 := by
  have hl := congrArg Prod.fst (field_normalizedLapse_jet b hf h0 hr hd)
  change fieldNormalizedLapse b f x=1+b 0^3*(rawA (fieldRaw b f x).1).1 at hl
  have ht := actual_traceFreeJet ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0
  rw [field_rawQ b hf,field_rawC b hf] at ht
  funext i k
  have hv := congrArg (fun t : MatrixScalarJet => (t i k).1) ht
  change traceFreeField (fieldQ b f) (fieldC b f) x i k=(traceFreeJet _ _ i k).1 at hv
  change (Real.sqrt (1+b 0^2)*fieldNormalizedLapse b f x/2)*traceFreeField (fieldQ b f) (fieldC b f) x i k=_
  rw [hl,hv]
  rfl

end
end CKSAngularGeometry

end

end OAI
