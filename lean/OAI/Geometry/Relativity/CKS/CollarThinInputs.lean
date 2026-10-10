import OAI.Geometry.Relativity.CKS.CollarFieldBounded
import OAI.Geometry.Relativity.CKS.CollarThinInvariance

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def CollarCoefficientFields.freezeRadial (f : CollarCoefficientFields) (x : Point) : CollarCoefficientFields :=
  { f with scalar := fun i y => if i=3 then f.scalar 3 x else f.scalar i y }

lemma fieldRaw_freeze (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) :
    fieldRaw b (f.freezeRadial x) x=thinRaw (fieldRaw b f x) := by
  have he : (fun i => actualScalarJet ((f.freezeRadial x).scalar i) x)=
      (fun i => if i=3 then constantJet (actualScalarJet (f.scalar i) x).1 else actualScalarJet (f.scalar i) x) := by
    funext i
    by_cases hi : i=3
    · subst i; simp only [CollarCoefficientFields.freezeRadial,ite_true]
      exact actualScalarJet_const _ _
    · simp only [CollarCoefficientFields.freezeRadial,hi,ite_false]
  unfold fieldRaw
  rw [he]
  rfl

lemma freezeRadial_regular {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    (f.freezeRadial x).RegularAt x := by
  refine ⟨hf.1,hf.2.1,?_,hf.2.2.2⟩
  intro i
  by_cases hi : i=3
  · simpa only [CollarCoefficientFields.freezeRadial,hi,ite_true] using
      (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : Point => f.scalar 3 x) x)
  · simpa only [CollarCoefficientFields.freezeRadial,hi,ite_false] using hf.2.2.1 i

def CollarCoefficientFields.ThinBoundedAt (f : CollarCoefficientFields) (B : ℝ) (x : Point) : Prop :=
  (∀ i : Fin 2, ‖matrixThreeJets (f.metric i.castSucc) x‖ ≤ B) ∧
  ‖matrixScalarJets (f.metric 2) x‖ ≤ B ∧
  ‖fun a => actualThreeJet (fun y => f.shift y a) x‖ ≤ B ∧
  (∀ i, i ≠ 3 → ‖actualScalarJet (f.scalar i) x‖ ≤ B) ∧ |f.scalar 3 x| ≤ B ∧
  ‖fun a => actualScalarJet (fun y => f.eta y a) x‖ ≤ B ∧
  ‖matrixScalarJets f.tau x‖ ≤ B ∧ ‖f.etar x‖ ≤ B ∧
  |f.massRadial x| ≤ B ∧ |f.massGap x| ≤ B

lemma freezeRadial_bounded {f : CollarCoefficientFields} {B : ℝ} {x : Point}
    (hB : 0 ≤ B) (hf : f.ThinBoundedAt B x) : (f.freezeRadial x).BoundedAt B x := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2.2.2⟩
  intro i
  by_cases hi : i=3
  · subst i
    change ‖actualScalarJet (fun _ : Point => f.scalar 3 x) x‖ ≤ B
    rw [actualScalarJet_const]
    exact norm_prod_le_iff.mpr ⟨by simpa only [constantJet,Real.norm_eq_abs] using hf.2.2.2.2.1,
      norm_prod_le_iff.mpr ⟨by simpa [constantJet] using hB,by simpa [constantJet] using hB⟩⟩
  · simpa only [CollarCoefficientFields.freezeRadial,hi,ite_false] using hf.2.2.2.1 i hi

lemma fieldRaw_thin_norm {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {B : ℝ} {x : Point}
    (hB : 0 ≤ B) (hb : ‖b‖ ≤ B) (hf : f.ThinBoundedAt B x) :
    ‖thinRaw (fieldRaw b f x)‖ ≤ B := by
  rw [← fieldRaw_freeze]
  exact fieldRaw_norm hB hb (freezeRadial_bounded hB hf)

theorem bounded_thin_field_map_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (rawAngularMatrix (fieldRaw b f x)) 1 0=(rawAngularMatrix (fieldRaw b f x)) 0 1 →
      (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 1 0=
        (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 0 1 →
      coordinateDEC (rawNullMap (rawNullOriginal (fieldRaw b f x))) r →
      coordinateDEC (rawNullMap (fieldRaw b f x)) r := by
  obtain ⟨R,hR,hh⟩ := bounded_raw_DEC hK hreg B A hA
  refine ⟨R,hR,?_⟩
  intro b f x hq hb hf r hr hz hw hparams hs hs₀ hDEC
  apply (thinRaw_DEC (fieldRaw b f x) r).mp
  apply hh (thinRaw (fieldRaw b f x)) hq (fieldRaw_thin_norm hB hb hf) r hr hz hw hparams hs
  · simpa only [← thinRaw_old,thinRaw_angular] using hs₀
  · rw [← thinRaw_old]
    exact (thinRaw_DEC _ r).mpr hDEC

end
end CKSAngularGeometry

end

end OAI
