import OAI.Geometry.Relativity.CKS.MixedCoefficientRealization
import OAI.Geometry.Relativity.CKS.CKSTensorJet

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure TensorFields where
  base : MassFields
  kr : Point → ℝ
  kb : Point → A → ℝ

structure TensorFields.RegularAt (f : TensorFields) (x : Point) : Prop where
  base : f.base.RegularAt x
  kr : ContDiffAt ℝ 2 f.kr x
  kb : ContDiffAt ℝ 2 f.kb x

def tensorInputOf (f : TensorFields) (x : Point) : TensorInput :=
  (massInputOf f.base x,actualScalarJet f.kr x,fun a => actualScalarJet (fun y => f.kb y a) x)

def tensorKField (z : Point → ℝ) (f : TensorFields) : Point → Mat := fun y =>
  f.base.sigma y+z y^3 • f.base.mK y+z y^4 • f.base.ek y

def tensorDenField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  1+z y^3*cksVField z f.base y

def tensorLapseSqField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  (1+z y^2)*(tensorDenField z f y)⁻¹

def tensorLapseField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  Real.sqrt (1+z y^2)*(Real.sqrt (tensorDenField z f y))⁻¹

def tensorCrossField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  ∑ a, cksHField z f.base y a*f.kb y a

def tensorQuadField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  ∑ a, ∑ b, tensorKField z f y a b*(cksHField z f.base y a*cksHField z f.base y b)

def tensorLField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  tensorLapseSqField z f y*(f.kr y-f.base.mr y-z y*f.base.err y+
    z y^3*(cksBBField z f.base y-2*tensorCrossField z f y+tensorQuadField z f y))

def tensorEtaField (z : Point → ℝ) (f : TensorFields) : Point → A → ℝ := fun y a =>
  tensorLapseField z f y*(f.kb y a-∑ b, cksHField z f.base y b*tensorKField z f y b a)

def tensorTauField (z : Point → ℝ) (f : TensorFields) : Point → Mat := fun y =>
  f.base.mK y-f.base.mg y+z y • (f.base.ek y-f.base.eg y)-
    cksTField z f.base y • cksQField z f.base y

lemma tensorKField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (tensorKField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ((hf.base.sigma.of_le (by norm_num)).add ((hz2.pow 3).smul hf.base.mK)).add
    ((hz2.pow 4).smul hf.base.ek)

lemma tensorDenField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorDenField z f) x :=
  contDiffAt_const.add (((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 3).mul
    (cksVField_diff hz hf.base h0))

lemma actual_tensorK {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    matrixScalarJets (tensorKField z f) x = tensorK (actualThreeJet z x,tensorInputOf f x) := by
  have hs := hf.base.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold tensorKField tensorK tensorInputOf massInputOf
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  erw [matrixScalarJets_add (hs.add ((hz2.pow 3).smul hf.base.mK)) ((hz2.pow 4).smul hf.base.ek),
    matrixScalarJets_add hs ((hz2.pow 3).smul hf.base.mK),
    matrixScalarJets_mul (hz2.pow 3) hf.base.mK,matrixScalarJets_mul (hz2.pow 4) hf.base.ek,
    actualScalarJet_pow hz2,actualScalarJet_pow hz2]
  rfl

lemma actual_tensorDen {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    actualScalarJet (tensorDenField z f) x = tensorDen (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hv := cksVField_diff hz hf.base h0
  unfold tensorDenField tensorDen tensorInputOf
  simp only [actualScalarJet_add contDiffAt_const ((hz2.pow 3).mul hv),actualScalarJet_const,
    actualScalarJet_mul (hz2.pow 3) hv,actualScalarJet_pow hz2,cksVField_realized hz hf.base h0]
  rfl

lemma actual_tensorLapseSq {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    actualScalarJet (tensorLapseSqField z f) x = tensorLapseSq (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have ht : ContDiffAt ℝ 2 (fun y => 1+z y^2) x := contDiffAt_const.add (hz2.pow 2)
  have hden := tensorDenField_diff hz hf h0
  unfold tensorLapseSqField tensorLapseSq
  erw [actualScalarJet_mul ht (hden.inv hd.ne')]
  have hi := actual_reciprocal hden hd.ne'
  simp only [one_div] at hi
  erw [hi,actual_tensorDen hz hf h0,actualScalarJet_add contDiffAt_const (hz2.pow 2),
    actualScalarJet_const,actualScalarJet_pow hz2]
  rfl

lemma actual_tensorLapse {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    actualScalarJet (tensorLapseField z f) x = tensorLapse (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have ht : ContDiffAt ℝ 2 (fun y => 1+z y^2) x := contDiffAt_const.add (hz2.pow 2)
  have hpos : 0 < 1+z x^2 := by positivity
  have hden := tensorDenField_diff hz hf h0
  have hsd := hden.sqrt hd.ne'
  unfold tensorLapseField tensorLapse
  erw [actualScalarJet_mul (ht.sqrt hpos.ne') (hsd.inv (Real.sqrt_pos.mpr hd).ne')]
  have hi := actual_reciprocal hsd (Real.sqrt_pos.mpr hd).ne'
  simp only [one_div] at hi
  erw [hi,actualScalarJet_sqrt ht hpos,actualScalarJet_sqrt hden hd,actual_tensorDen hz hf h0,
    actualScalarJet_add contDiffAt_const (hz2.pow 2),actualScalarJet_const,actualScalarJet_pow hz2]
  rfl

end
end CKSMixedGeometry

end

end OAI
