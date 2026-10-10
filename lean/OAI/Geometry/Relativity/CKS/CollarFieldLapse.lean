import OAI.Geometry.Relativity.CKS.CollarLapseRealization
import OAI.Geometry.Relativity.CKS.CollarFieldExpansion

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma fieldT_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldT b f) x := by
  unfold fieldT; exact contDiffAt_const.mul (hf.2.2.1 0)
lemma fieldF_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldF b f) x :=
by
  unfold fieldF
  exact ((contDiffAt_const.mul (hf.2.2.1 1)).add (contDiffAt_const.mul (hf.2.2.1 4))).add contDiffAt_const
lemma fieldL_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldL b f) x := by
  unfold fieldL; exact contDiffAt_const.mul (hf.2.2.1 2)
lemma fieldTr_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldTr b f) x := by
  unfold fieldTr; exact (contDiffAt_const.mul (hf.2.2.1 3)).sub (contDiffAt_const.mul (hf.2.2.1 0))

lemma field_rawT (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldT b f) x=rawT (fieldRaw b f x).1 :=
  actualScalarJet_smul _ (hf.2.2.1 0)
lemma field_rawF (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldF b f) x=rawF (fieldRaw b f x).1 := by
  unfold fieldF
  erw [actualScalarJet_add ((contDiffAt_const.mul (hf.2.2.1 1)).add (contDiffAt_const.mul (hf.2.2.1 4))) contDiffAt_const,
    actualScalarJet_add (contDiffAt_const.mul (hf.2.2.1 1)) (contDiffAt_const.mul (hf.2.2.1 4)),
    actualScalarJet_smul _ (hf.2.2.1 1),actualScalarJet_smul _ (hf.2.2.1 4),actualScalarJet_const]
  rfl
lemma field_rawL (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldL b f) x=rawL (fieldRaw b f x).1 :=
  actualScalarJet_smul _ (hf.2.2.1 2)
lemma field_rawTr (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldTr b f) x=rawTr (fieldRaw b f x).1 := by
  unfold fieldTr
  erw [actualScalarJet_sub (contDiffAt_const.mul (hf.2.2.1 3)) (contDiffAt_const.mul (hf.2.2.1 0)),
    actualScalarJet_smul _ (hf.2.2.1 3),actualScalarJet_smul _ (hf.2.2.1 0)]
  rfl

def fieldA (b : Fin 5 → ℝ) (f : CollarCoefficientFields) : Point → ℝ :=
  lapseAField (b 0) (fieldT b f) (fieldF b f) (fieldD b f)

def fieldNormalizedLapse (b : Fin 5 → ℝ) (f : CollarCoefficientFields) : Point → ℝ :=
  lapseNormalizedField (b 0) (fieldT b f) (fieldF b f) (fieldD b f)

lemma field_rawA (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    actualScalarJet (fieldA b f) x=rawA (fieldRaw b f x).1 := by
  unfold fieldA
  rw [actual_lapseAField _ (fieldT_diff b hf) (fieldF_diff b hf) (fieldD_diff b hf h0) hr hd,
    field_rawT b hf,field_rawF b hf,field_rawD b hf h0]
  rfl

lemma field_normalizedLapse_jet (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    actualScalarJet (fieldNormalizedLapse b f) x=constantJet 1+b 0^3 • rawA (fieldRaw b f x).1 := by
  unfold fieldNormalizedLapse
  rw [actual_normalized_lapse_coefficient _ (fieldT_diff b hf) (fieldF_diff b hf) (fieldD_diff b hf h0) hr hd,
    field_rawT b hf,field_rawF b hf,field_rawD b hf h0]
  rfl

lemma lapse_radical_reconstruction {r T F : ℝ} (hr : 0 < r) :
    1+(r*(1+(1/r)^3*T))^2-2*F/r =
      (1+r^2)*(1+(1/r)^3*((2*T+(1/r)^3*T^2-2*F)/(1+(1/r)^2))) := by
  have hz : 1+(1/r)^2 ≠ 0 := by positivity
  field_simp
  ring

lemma lapse_sqrt_reconstruction {r T F D : ℝ} (hr : 0 < r) :
    Real.sqrt (1+(r*(1+(1/r)^3*T))^2-2*F/r)/(1+(1/r)^3*D) =
      Real.sqrt (1+r^2)*(Real.sqrt (1+(1/r)^3*((2*T+(1/r)^3*T^2-2*F)/(1+(1/r)^2)))/(1+(1/r)^3*D)) := by
  rw [lapse_radical_reconstruction hr,Real.sqrt_mul (by positivity : 0 ≤ 1+r^2)]
  ring

end
end CKSAngularGeometry

end

end OAI
