import OAI.Geometry.Relativity.CKS.MixedMassFields

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma cksQField_two_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    matrixScalarJets (cksQField z f) x = lowerMatrixJet (coefficientMetric (actualThreeJet z x) (massInputOf f x)) :=
  congrArg lowerMatrixJet (cksQField_realized hz hf)

lemma cksDField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksDField z f) x = coefficientD (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hlie := cksLieField_diff hz hf h0
  have hp := (hmg.const_smul (-3:ℝ)).add (hz2.smul ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie))
  unfold cksDField coefficientD
  erw [actualScalarJet_smul (1/4:ℝ) (traceProduct_diff hi hp),actual_traceProductJet hi hp,
    actual_inverseJets hq h0,cksQField_two_realized hz hf,
    matrixScalarJets_add (hmg.const_smul (-3:ℝ)) (hz2.smul ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie)),
    matrixScalarJets_smul (-3) hmg,matrixScalarJets_mul hz2 ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie),
    matrixScalarJets_sub (hf.er.sub (heg.const_smul (2:ℝ))) hlie,
    matrixScalarJets_sub hf.er (heg.const_smul (2:ℝ)),matrixScalarJets_smul (2:ℝ) heg,
    cksLieField_realized hz hf h0]
  rfl

lemma cksTField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksTField z f) x = coefficientT (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hp := (hf.mK.sub hmg).add (hz2.smul (hf.ek.sub heg))
  unfold cksTField coefficientT
  erw [actualScalarJet_smul (1/2:ℝ) (traceProduct_diff hi hp),actual_traceProductJet hi hp,
    actual_inverseJets hq h0,cksQField_two_realized hz hf,
    matrixScalarJets_add (hf.mK.sub hmg) (hz2.smul (hf.ek.sub heg)),
    matrixScalarJets_sub hf.mK hmg,matrixScalarJets_mul hz2 (hf.ek.sub heg),
    matrixScalarJets_sub hf.ek heg]
  rfl

lemma cksBBField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksBBField z f) x = coefficientBB (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hb (i : A) := (contDiffAt_pi.mp hf.b i).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold cksBBField coefficientBB
  rw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ => (component_diff hi i k).mul ((hb i).mul (hb k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [actualScalarJet_sum _ (fun k _ => (component_diff hi i k).mul ((hb i).mul (hb k)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [actualScalarJet_mul (component_diff hi i k) ((hb i).mul (hb k)),
    actualScalarJet_mul (hb i) (hb k),actual_inverseMatrixJet hq h0]
  have heq := cksQField_two_realized hz hf
  change productJet (inverseMatrixJet (matrixScalarJets (cksQField z f) x) i k)
      (productJet (actualScalarJet (fun y => f.b y i) x) (actualScalarJet (fun y => f.b y k) x)) = _
  rw [heq]
  rfl

lemma cksVField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksVField z f) x = coefficientV (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hmr := hf.mr
  have herr := hf.err
  have hbb := cksBBField_diff hz hf h0
  unfold cksVField coefficientV
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_sub,actualScalarJet_mul,actualScalarJet_pow,actualScalarJet_const]
  rw [cksBBField_realized hz hf h0]
  rfl

lemma cksFField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hV : 1+z x^3*cksVField z f x ≠ 0) :
    actualScalarJet (cksFField z f) x = cksMassJet (actualThreeJet z x) (massInputOf f x) := by
  unfold cksFField cksMassJet
  rw [actual_normalizedMassJet (hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) (cksDField_diff hz hf h0) (cksTField_diff hz hf h0) (cksVField_diff hz hf h0) hV,
    cksDField_realized hz hf h0,cksTField_realized hz hf h0,cksVField_realized hz hf h0]
  rfl

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
end CKSMixedGeometry

end

end OAI
