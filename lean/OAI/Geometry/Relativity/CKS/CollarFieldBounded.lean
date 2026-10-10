import OAI.Geometry.Relativity.CKS.CollarRawDEC
import OAI.Geometry.Relativity.CKS.CollarFieldJets
import OAI.Geometry.Relativity.CKS.CKSCollarExpansion

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixDerivedJets_norm_le_three (q : Point → Mat) (x : Point) (a : I) :
    ‖matrixScalarJets (fun y i k => D (basis a) (fun z => q z i k) y) x‖ ≤ ‖matrixThreeJets q x‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i k
  exact ((norm_le_pi_norm (matrixThreeJets q x i k).2 a).trans
    (norm_snd_le (matrixThreeJets q x i k))).trans
    (Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x))

def CollarCoefficientFields.BoundedAt (f : CollarCoefficientFields) (B : ℝ) (x : Point) : Prop :=
  (∀ i : Fin 2, ‖matrixThreeJets (f.metric i.castSucc) x‖ ≤ B) ∧
  ‖matrixScalarJets (f.metric 2) x‖ ≤ B ∧
  ‖fun a => actualThreeJet (fun y => f.shift y a) x‖ ≤ B ∧
  (∀ i, ‖actualScalarJet (f.scalar i) x‖ ≤ B) ∧
  ‖fun a => actualScalarJet (fun y => f.eta y a) x‖ ≤ B ∧
  ‖matrixScalarJets f.tau x‖ ≤ B ∧ ‖f.etar x‖ ≤ B ∧
  |f.massRadial x| ≤ B ∧ |f.massGap x| ≤ B

lemma fieldRaw_norm {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {x : Point}
    {B : ℝ} (hB : 0 ≤ B) (hb : ‖b‖ ≤ B) (hf : f.BoundedAt B x) :
    ‖fieldRaw b f x‖ ≤ B := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply norm_prod_le_iff.mpr
    refine ⟨hb,?_⟩
    apply norm_prod_le_iff.mpr
    constructor
    · apply norm_prod_le_iff.mpr
      constructor
      · apply norm_prod_le_iff.mpr
        constructor
        · apply (pi_norm_le_iff_of_nonneg hB).mpr
          intro i
          fin_cases i
          · exact (matrixScalarJets_norm_le_three _ _).trans (hf.1 0)
          · exact (matrixScalarJets_norm_le_three _ _).trans (hf.1 1)
          · exact hf.2.1
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro i
          apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          exact (matrixDerivedJets_norm_le_three _ _ _).trans (hf.1 i)
      · apply norm_prod_le_iff.mpr
        constructor
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          exact (norm_fst_le (actualThreeJet (fun y => f.shift y a) x)).trans
            ((norm_le_pi_norm (fun a => actualThreeJet (fun y => f.shift y a) x) a).trans hf.2.2.1)
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          apply (pi_norm_le_iff_of_nonneg hB).mpr; intro k
          exact ((norm_le_pi_norm (actualThreeJet (fun y => f.shift y k) x).2 a).trans
            (norm_snd_le (actualThreeJet (fun y => f.shift y k) x))).trans
            ((norm_le_pi_norm (fun k => actualThreeJet (fun y => f.shift y k) x) k).trans hf.2.2.1)
    · apply norm_prod_le_iff.mpr
      constructor
      · exact norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg hB).mpr hf.2.2.2.1,hf.2.2.2.2.1⟩
      · exact norm_prod_le_iff.mpr ⟨hf.2.2.2.2.2.1,hf.2.2.2.2.2.2.1⟩
  · apply norm_prod_le_iff.mpr
    simpa only [fieldRaw, Real.norm_eq_abs] using (show ‖f.massRadial x‖ ≤ B ∧ ‖f.massGap x‖ ≤ B from
      And.intro (by simpa only [Real.norm_eq_abs] using hf.2.2.2.2.2.2.2.1)
        (by simpa only [Real.norm_eq_abs] using hf.2.2.2.2.2.2.2.2))

theorem bounded_field_map_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.BoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (rawAngularMatrix (fieldRaw b f x)) 1 0=(rawAngularMatrix (fieldRaw b f x)) 0 1 →
      (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 1 0=
        (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 0 1 →
      coordinateDEC (rawNullMap (rawNullOriginal (fieldRaw b f x))) r →
      coordinateDEC (rawNullMap (fieldRaw b f x)) r := by
  obtain ⟨R,hR,hh⟩ := bounded_raw_DEC hK hreg B A hA
  refine ⟨R,hR,?_⟩
  intro b f x hq hb hf
  exact hh (fieldRaw b f x) hq (fieldRaw_norm hB hb hf)

end
end CKSAngularGeometry

end

end OAI
