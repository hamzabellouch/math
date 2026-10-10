import OAI.Geometry.Relativity.CKS.CKSCoefficientRealization

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actual_tensorH {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (a : A) :
    actualScalarJet (fun y => cksHField z f.base y a) x =
      tensorH (actualThreeJet z x,tensorInputOf f x) a := by
  have h := congrFun (cksHField_realized hz hf.base h0) a
  exact congrArg Prod.fst h

lemma tensorCrossField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorCrossField z f) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ContDiffAt.sum fun a _ => (contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hf.kb a)

lemma tensorQuadField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorQuadField z f) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hK := tensorKField_diff hz hf
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    (component_diff hK a b).mul ((contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hH b))

lemma actual_tensorCross {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    actualScalarJet (tensorCrossField z f) x = tensorCross (actualThreeJet z x,tensorInputOf f x) := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold tensorCrossField tensorCross
  rw [actualScalarJet_sum _ (fun a _ => (contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hf.kb a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [actualScalarJet_mul (contDiffAt_pi.mp hH a) (contDiffAt_pi.mp hf.kb a),actual_tensorH hz hf h0]
  rfl

lemma actual_tensorQuad {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    actualScalarJet (tensorQuadField z f) x = tensorNormalQuad (actualThreeJet z x,tensorInputOf f x) := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hK := tensorKField_diff hz hf
  have hprod (a b : A) := (component_diff hK a b).mul
    ((contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hH b))
  unfold tensorQuadField tensorNormalQuad
  rw [actualScalarJet_sum _ (fun a _ => ContDiffAt.sum fun b _ => hprod a b)]
  apply Finset.sum_congr rfl
  intro a _
  rw [actualScalarJet_sum _ (fun b _ => hprod a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [actualScalarJet_mul (component_diff hK a b) ((contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hH b)),
    actualScalarJet_mul (contDiffAt_pi.mp hH a) (contDiffAt_pi.mp hH b),
    actual_tensorH hz hf h0,actual_tensorH hz hf h0]
  have hk := congrFun (congrFun (actual_tensorK hz hf) a) b
  exact congrArg (fun j => productJet j
    (productJet (tensorH (actualThreeJet z x,tensorInputOf f x) a)
      (tensorH (actualThreeJet z x,tensorInputOf f x) b))) hk

lemma tensorLapseSqField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    ContDiffAt ℝ 2 (tensorLapseSqField z f) x := by
  exact (contDiffAt_const.add ((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 2)).mul
    ((tensorDenField_diff hz hf h0).inv hd.ne')

lemma tensorLapseField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    ContDiffAt ℝ 2 (tensorLapseField z f) x := by
  have ht : ContDiffAt ℝ 2 (fun y => 1+z y^2) x :=
    contDiffAt_const.add ((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 2)
  exact (ht.sqrt (ne_of_gt (by positivity))).mul
    (((tensorDenField_diff hz hf h0).sqrt hd.ne').inv (Real.sqrt_pos.mpr hd).ne')

lemma actual_tensorL {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    actualScalarJet (tensorLField z f) x = tensorLCoeff (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hkr := hf.kr
  have hmr := hf.base.mr
  have herr := hf.base.err
  have hl := tensorLapseSqField_diff hz hf h0 hd
  have hbb := cksBBField_diff hz hf.base h0
  have hcross := tensorCrossField_diff hz hf h0
  have hquad := tensorQuadField_diff hz hf h0
  unfold tensorLField tensorLCoeff
  simp (disch := fun_prop) only [actualScalarJet_mul,actualScalarJet_add,actualScalarJet_sub,
    actualScalarJet_pow,actualScalarJet_const,productJet_constant_left]
  rw [actual_tensorLapseSq hz hf h0 hd,cksBBField_realized hz hf.base h0,
    actual_tensorCross hz hf h0,actual_tensorQuad hz hf h0]
  rfl

lemma actual_tensorEta {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) (a : A) :
    actualScalarJet (fun y => tensorEtaField z f y a) x =
      tensorEtaCoeff (actualThreeJet z x,tensorInputOf f x) a := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hK := tensorKField_diff hz hf
  have hm (b : A) := (contDiffAt_pi.mp hH b).mul (component_diff hK b a)
  unfold tensorEtaField tensorEtaCoeff
  rw [actualScalarJet_mul (tensorLapseField_diff hz hf h0 hd)
    ((contDiffAt_pi.mp hf.kb a).sub (ContDiffAt.sum fun b _ => hm b)),
    actual_tensorLapse hz hf h0 hd,
    actualScalarJet_sub (contDiffAt_pi.mp hf.kb a) (ContDiffAt.sum fun b _ => hm b),
    actualScalarJet_sum _ (fun b _ => hm b)]
  congr 2
  apply Finset.sum_congr rfl
  intro b _
  rw [actualScalarJet_mul (contDiffAt_pi.mp hH b) (component_diff hK b a),actual_tensorH hz hf h0]
  exact congrArg (productJet (tensorH (actualThreeJet z x,tensorInputOf f x) b))
    (congrFun (congrFun (actual_tensorK hz hf) b) a)

lemma actual_tensorTau {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    matrixScalarJets (tensorTauField z f) x = tensorTauCoeff (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hmg := hf.base.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.base.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf.base).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have ht := cksTField_diff hz hf.base h0
  unfold tensorTauField tensorTauCoeff
  erw [matrixScalarJets_sub ((hf.base.mK.sub hmg).add (hz2.smul (hf.base.ek.sub heg))) (ht.smul hq),
    matrixScalarJets_add (hf.base.mK.sub hmg) (hz2.smul (hf.base.ek.sub heg)),
    matrixScalarJets_sub hf.base.mK hmg,matrixScalarJets_mul hz2 (hf.base.ek.sub heg),
    matrixScalarJets_sub hf.base.ek heg,matrixScalarJets_mul ht hq,
    cksTField_realized hz hf.base h0,cksQField_two_realized hz hf.base]
  rfl

lemma tensorLField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    ContDiffAt ℝ 2 (tensorLField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (tensorLapseSqField_diff hz hf h0 hd).mul
    (((hf.kr.sub hf.base.mr).sub (hz2.mul hf.base.err)).add
      ((hz2.pow 3).mul (((cksBBField_diff hz hf.base h0).sub
        (contDiffAt_const.mul (tensorCrossField_diff hz hf h0))).add (tensorQuadField_diff hz hf h0))))

lemma tensorEtaField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) (a : A) :
    ContDiffAt ℝ 2 (fun y => tensorEtaField z f y a) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (tensorLapseField_diff hz hf h0 hd).mul ((contDiffAt_pi.mp hf.kb a).sub
    (ContDiffAt.sum fun b _ => (contDiffAt_pi.mp hH b).mul (component_diff (tensorKField_diff hz hf) b a)))

lemma tensorTauField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorTauField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hmg := hf.base.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.base.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf.base).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (((hf.base.mK.sub hmg).add (hz2.smul (hf.base.ek.sub heg))).sub
    ((cksTField_diff hz hf.base h0).smul hq))

end
end CKSMixedGeometry

end

end OAI
