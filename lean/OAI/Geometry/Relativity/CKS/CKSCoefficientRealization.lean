import OAI.Geometry.Relativity.CKS.CKSTensorFields

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixScalarJets_sub {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y-p y) x = matrixScalarJets q x-matrixScalarJets p x := by
  funext i k
  exact actualScalarJet_sub (component_diff hq i k) (component_diff hp i k)

lemma cksQField_two_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (cksQField z f) x = lowerMatrixJet (coefficientMetric z (massInputOf f x)) :=
  congrArg lowerMatrixJet (cksQField_realized z hf)

lemma cksDField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksDField z f) x = coefficientD z (massInputOf f x) := by
  have hq := (cksQField_diff z hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hlie := cksLieField_diff z hf h0
  have hp := (hmg.const_smul (-3:ℝ)).add (((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie).const_smul z)
  unfold cksDField coefficientD
  rw [actualScalarJet_smul (1/4:ℝ) (traceProduct_diff hi hp),actual_traceProductJet hi hp,
    actual_inverseJets hq h0,cksQField_two_realized z hf,
    matrixScalarJets_add (hmg.const_smul (-3:ℝ)) (((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie).const_smul z),
    matrixScalarJets_smul (-3) hmg,matrixScalarJets_smul z ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie),
    matrixScalarJets_sub (hf.er.sub (heg.const_smul (2:ℝ))) hlie,
    matrixScalarJets_sub hf.er (heg.const_smul (2:ℝ)),matrixScalarJets_smul (2:ℝ) heg,
    cksLieField_realized z hf h0]
  rfl

lemma cksTField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksTField z f) x = coefficientT z (massInputOf f x) := by
  have hq := (cksQField_diff z hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hp := (hf.mK.sub hmg).add ((hf.ek.sub heg).const_smul z)
  unfold cksTField coefficientT
  rw [actualScalarJet_smul (1/2:ℝ) (traceProduct_diff hi hp),actual_traceProductJet hi hp,
    actual_inverseJets hq h0,cksQField_two_realized z hf,
    matrixScalarJets_add (hf.mK.sub hmg) ((hf.ek.sub heg).const_smul z),
    matrixScalarJets_sub hf.mK hmg,matrixScalarJets_smul z (hf.ek.sub heg),
    matrixScalarJets_sub hf.ek heg]
  rfl

lemma cksBBField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksBBField z f) x = coefficientBB z (massInputOf f x) := by
  have hq := (cksQField_diff z hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hb (i : I) := (contDiffAt_pi.mp hf.b i).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold cksBBField coefficientBB
  rw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ => (component_diff hi i k).mul ((hb i).mul (hb k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [actualScalarJet_sum _ (fun k _ => (component_diff hi i k).mul ((hb i).mul (hb k)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [actualScalarJet_mul (component_diff hi i k) ((hb i).mul (hb k)),
    actualScalarJet_mul (hb i) (hb k),actual_inverseMatrixJet hq h0]
  have heq := cksQField_two_realized z hf
  change productJet (inverseMatrixJet (matrixScalarJets (cksQField z f) x) i k)
      (productJet (actualScalarJet (fun y => f.b y i) x) (actualScalarJet (fun y => f.b y k) x)) = _
  rw [heq]
  rfl

lemma cksVField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksVField z f) x = coefficientV z (massInputOf f x) := by
  have hmr := hf.mr
  have herr := hf.err
  have hbb := cksBBField_diff z hf h0
  unfold cksVField coefficientV
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_sub,actualScalarJet_smul]
  rw [cksBBField_realized z hf h0]
  rfl

lemma cksFField_realized (z : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hV : 1+z^3*cksVField z f x ≠ 0) :
    actualScalarJet (cksFField z f) x = cksMassJet z (massInputOf f x) := by
  unfold cksFField cksMassJet
  rw [actual_normalizedMassJet z (cksDField_diff z hf h0) (cksTField_diff z hf h0) (cksVField_diff z hf h0) hV,
    cksDField_realized z hf h0,cksTField_realized z hf h0,cksVField_realized z hf h0]

lemma cksLeadingField_realized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) :
    actualScalarJet (cksLeadingField f) x = leadingMassJet (massInputOf f x) := by
  have hs := hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hs h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have htg := traceProduct_diff hi hmg
  have htk := traceProduct_diff hi hf.mK
  have hmr := hf.mr
  unfold cksLeadingField leadingMassJet
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_smul]
  rw [actual_traceProductJet hi hmg,actual_traceProductJet hi hf.mK,actual_inverseJets hs h0]
  rfl

end
end CKSAngularGeometry

end

end OAI
