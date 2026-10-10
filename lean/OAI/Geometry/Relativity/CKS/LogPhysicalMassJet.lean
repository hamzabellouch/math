import OAI.Geometry.Relativity.CKS.CKSMetricPositivity
import OAI.Geometry.Relativity.CKS.CKSMassMixed
import OAI.Geometry.Relativity.CKS.LogPhysicalMass

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logMetric (f : MassFields) (x : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  CKSAngularGeometry.metricBlock (logRadialMetric f x) (f.b x) (logGamma f x)

lemma logMetric_normalized_positive {f : MassFields} {x : Point}
    (h : (logMetric f x).PosDef) :
    (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x).PosDef ∧ 0 < logSchur f x := by
  constructor
  · have hγ : (logGamma f x).PosDef := CKSAngularGeometry.metricBlock_leaf_posDef h
    have he : cksQField (radiusPower (-1)) (normalizeMassLogFields f) x =
        (1/Real.exp (x 0)^2) • logGamma f x := by
      rw [logGamma_normalized]
      simp only [radiusPower_two]
      rw [smul_smul]
      have hc : (1/Real.exp (x 0)^2)*Real.exp (x 0)^2=1 := by
        have hr := Real.exp_ne_zero (x 0)
        field_simp
      rw [hc,one_smul]
    rw [he]
    exact hγ.smul (one_div_pos.mpr (by positivity))
  · exact CKSAngularGeometry.metricBlock_schur_positive h

lemma MassFields.RegularAt.eventually {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  filter_upwards [hf.sigma.eventually (by norm_num),hf.mg.eventually (by norm_num),
    hf.eg.eventually (by norm_num),hf.er.eventually (by norm_num),
    hf.mK.eventually (by norm_num),hf.ek.eventually (by norm_num),
    hf.b.eventually (by norm_num),hf.mr.eventually (by norm_num),hf.err.eventually (by norm_num)]
    with y hs hm he her hk hek hb hr herr
  exact ⟨hs,hm,he,her,hk,hek,hb,hr,herr⟩

lemma log_physical_mass_jet_eq {f : MassFields} {x : Point}
    (hf : f.RegularAt x) (hp : ∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) :
    actualScalarJet (logPhysicalMass f) x =
      actualScalarJet (cksFField (radiusPower (-1)) (normalizeMassLogFields f)) x := by
  apply actualScalarJet_congr
  filter_upwards [hf.eventually,hp] with y hy hpy
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hpy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  exact log_physical_mass_eq hy hd hs

theorem cks_physical_mass_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet (logPhysicalMass f) x-actualScalarJet (cksLeadingField f) x‖ ≤
        C/Real.exp (x 0) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_normalized_mass_mixed hK hreg hB
  refine ⟨R,hR,C,hC,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive
    (Filter.Eventually.self_of_nhds (x := x) (p := fun y : Point => (logMetric f y).PosDef) hp)
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hV : 1+(radiusPower (-1) x)^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x ≠ 0 := by
    rw [radiusPower_inverse,← log_schur_coefficient]
    exact ne_of_gt (mul_pos (by positivity) hS)
  rw [log_physical_mass_jet_eq hf hp]
  exact hh f x hr hf hσ hs hmg heg hmk hek hb hmr herr hd hV

end
end CKSMixedGeometry

end

end OAI
