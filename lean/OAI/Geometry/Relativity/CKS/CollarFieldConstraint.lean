import OAI.Geometry.Relativity.CKS.CollarFieldTensor
import OAI.Geometry.Relativity.CKS.CollarFieldBounded

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def fieldMomentumInput (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : MomentumInput :=
  (b 0,b 4,actualJet (fieldQ b f) x,
    ![actualScalarJet (fieldA b f) x,actualScalarJet (fieldT b f) x,
      actualScalarJet (fieldL b f) x,actualScalarJet (fieldTr b f) x,
      actualScalarJet (fieldD b f) x],
    (fun a => actualScalarJet (fun y => fieldS b f y a) x),
    (fun a => actualScalarJet (fun y => fieldEta b f y a) x),
    matrixScalarJets (fieldTau b f) x,fieldX b f x,fieldEr b f x)

def fieldNullInput (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : NullInput :=
  (fieldMomentumInput b f x,actualScalarJet (fieldF b f) x,
    (1-b 1)*f.massRadial x-b 2*f.massGap x)

def oldParams (b : Fin 5 → ℝ) : Fin 5 → ℝ := fun i => if i=0 then b 0 else 0

lemma scalarMatrixToJet_actual (q : Point → Mat) (x : Point) :
    scalarMatrixToJet (matrixScalarJets q x)=actualJet q x := rfl

lemma field_momentum_realization (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    fieldMomentumInput b f x=rawMomentumInput (fieldRaw b f x).1 := by
  have hq : actualJet (fieldQ b f) x=scalarMatrixToJet (rawQ (fieldRaw b f x).1) := by
    rw [← field_rawQ b hf]; rfl
  have hs : (fun a => actualScalarJet (fun y => fieldS b f y a) x)=rawS (fieldRaw b f x).1 :=
    funext (field_rawS b hf)
  have he : fieldEr b f x=(fun a => (1-re (fieldRaw b f x).1)*retar (fieldRaw b f x).1 a-
      rθ (fieldRaw b f x).1*(reta (fieldRaw b f x).1 a).1) := rfl
  unfold fieldMomentumInput rawMomentumInput
  rw [hq,hs,he,field_rawA b hf h0 hr hd,field_rawT b hf,field_rawL b hf,
    field_rawTr b hf,field_rawD b hf h0,field_rawEta b hf,field_rawTau b hf h0,
    field_rawX b hf h0 hr hd]
  rfl

lemma field_null_realization (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    fieldNullInput b f x=rawNullMap (fieldRaw b f x) := by
  unfold fieldNullInput rawNullMap
  rw [field_momentum_realization b hf h0 hr hd,field_rawF b hf]
  rfl

lemma fieldRaw_old (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) :
    fieldRaw (oldParams b) f x=rawNullOriginal (fieldRaw b f x) := rfl

lemma field_angular_matrix (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) : fieldQ b f x=rawAngularMatrix (fieldRaw b f x) := by
  have hh := field_rawQ b hf
  exact congrArg (fun q : MatrixScalarJet => fun i k => (q i k).1) hh

theorem bounded_field_coordinate_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.BoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (fieldQ b f x) 1 0=(fieldQ b f x) 0 1 →
      (fieldQ (oldParams b) f x) 1 0=(fieldQ (oldParams b) f x) 0 1 →
      determinant (fieldQ b f x) ≠ 0 → determinant (fieldQ (oldParams b) f x) ≠ 0 →
      0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x →
      0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) f) (fieldF (oldParams b) f) x →
      lapseDField (b 0) (fieldD b f) x ≠ 0 →
      lapseDField ((oldParams b) 0) (fieldD (oldParams b) f) x ≠ 0 →
      coordinateDEC (fieldNullInput (oldParams b) f x) r → coordinateDEC (fieldNullInput b f x) r := by
  obtain ⟨R,hR,hh⟩ := bounded_field_map_DEC hK hreg hB hA
  refine ⟨R,hR,?_⟩
  intro b f x hf hq hb hbound r hr hz hw hparams hs hs₀ hdet hdet₀ hrad hrad₀ hd hd₀ hDEC
  rw [field_null_realization b hf hdet hrad hd]
  rw [field_null_realization (oldParams b) hf hdet₀ hrad₀ hd₀,fieldRaw_old] at hDEC
  rw [field_angular_matrix b hf] at hs
  rw [field_angular_matrix (oldParams b) hf,fieldRaw_old] at hs₀
  exact hh b f x hq hb hbound r hr hz hw hparams hs hs₀ hDEC

end
end CKSAngularGeometry

end

end OAI
