import OAI.Analysis.AllenCahn.DefectDrift
import OAI.Analysis.AllenCahn.NormalMass
import OAI.Analysis.AllenCahn.EllipticRegularity
import OAI.Analysis.AllenCahn.DriftPropagation
import OAI.Analysis.AllenCahn.Eikonal
import OAI.Analysis.AllenCahn.EndpointSeparation

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

lemma diffuseDefect_eq_zero_of_eq_zero {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) {z : Space n} (hz : diffuseDefect v z = 0) :
    ∀ x, diffuseDefect v x = 0 := by
  have hb (x : Space n) : v x ∈ Set.Icc (-1 : ℝ) 1 := ⟨(hi x).1.le, (hi x).2.le⟩
  have hs : ContDiff ℝ ∞ v := RegularitySupport.DeGiorgi.allenCahn_smooth hv hb hAC
  exact DriftSupport.DeGiorgi.nonnegative_supersolution_eq_zero_drift
    (fun x => (2 * Real.sqrt 2 * v x) • gradient (inverseProfile v) x)
    (B := 2 * Real.sqrt 2) (by positivity) (diffuseDrift_bound hv hi hAC)
    (smooth_C2 (diffuseDefect_smooth hs hi)) (diffuseDefect_nonneg hv hi hAC)
    (diffuseDefect_drift_inequality hs hi hAC) hz

lemma classified_of_defect_zero_at {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) {z : Space n} (hz : diffuseDefect v z = 0) : Classified v :=
  EikonalSupport.DeGiorgi.classified_of_zero_defect hv hi
    (diffuseDefect_eq_zero_of_eq_zero hv hi hAC hz)

theorem classified_or_positive_defect {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn v) :
    Classified v ∨ ((∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) ∧ ∀ x, 0 < diffuseDefect v x) := by
  rcases EndpointSupport.DeGiorgi.endpoint_separation hv hb hAC with h1 | hn | hi
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl hn))
  by_cases hzero : ∃ z, diffuseDefect v z = 0
  · obtain ⟨z, hz⟩ := hzero
    exact Or.inl (classified_of_defect_zero_at hv hi hAC hz)
  · exact Or.inr ⟨hi, fun x => lt_of_le_of_ne (diffuseDefect_nonneg hv hi hAC x)
      (fun h => hzero ⟨x, h.symm⟩)⟩

lemma positiveDefectClass_of_zero_positive {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hb : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) (hAC : AllenCahn v)
    {z : Space n} (h0 : v z=0) (hD : 0<diffuseDefect v z) : v ∈ positiveDefectClass n := by
  have hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rcases EndpointSupport.DeGiorgi.endpoint_separation hv hb hAC with h | h | h
    · have H := h z; linarith
    · have H := h z; linarith
    · exact h
  refine ⟨RegularitySupport.DeGiorgi.allenCahn_smooth hv hb hAC,hi,hAC,?_⟩
  intro x
  have hx := diffuseDefect_nonneg hv hi hAC x
  by_contra hnot
  have hz : diffuseDefect v x=0 := le_antisymm (le_of_not_gt hnot) hx
  have H := diffuseDefect_eq_zero_of_eq_zero hv hi hAC hz z
  linarith

theorem diffuse_mean_window {n : ℕ} (hn : 2≤n) {c : ℝ}
    (hc : 1/(2*Real.sqrt 2)<c) :
    ∃ P > (0 : ℝ), ∃ δ ∈ Set.Ioc (0 : ℝ) (1/2),
      ∀ v : Space n → ℝ, ContDiff ℝ 2 v → (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) →
      AllenCahn v → ∀ z : Space n, v z=0 → 0<diffuseDefect v z → diffuseDefect v z<δ →
      gradient (inverseProfile v) z≠0 ∧
      ∀ P'≥P, |diffuseMeanCurvature v z| ≤
        (c/(4*Real.sqrt 2/3))*(∫ s in -P'..P', defectWeight v (z+s • diffuseNormal v z)^3 *
          diffuseDefect v (z+s • diffuseNormal v z)) := by
  obtain ⟨P,hP,δ,hδ,H⟩ := diffuse_mean_window_positive (by omega : 0<n) hc
  refine ⟨P,hP,δ,hδ,?_⟩
  intro v hv hb hAC z h0 hD hδz
  have hv' := positiveDefectClass_of_zero_positive hv hb hAC h0 hD
  constructor
  · intro hp
    have hDz : diffuseDefect v z=1 := by simp [diffuseDefect,hp]
    rw [hDz] at hδz
    linarith [hδ.2]
  · intro P' hPP'
    exact (H v hv' z h0 hδz).trans
      (mul_le_mul_of_nonneg_left (normalDefectMass_mono hv' z hP.le hPP')
        (div_nonneg (le_of_lt ((by positivity : 0<1/(2*Real.sqrt 2)).trans hc)) (by positivity)))

theorem diffuse_strict_mean {n : ℕ} (hn : 2≤n) :
    1/(2*Real.sqrt 2)<(3/8 : ℝ) ∧ (3/8 : ℝ)<Real.sqrt 2/3 ∧
    ∃ P > (0 : ℝ), ∃ δ ∈ Set.Ioc (0 : ℝ) (1/2),
      ∀ v : Space n → ℝ, ContDiff ℝ 2 v → (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) →
      AllenCahn v → ∀ z : Space n, v z=0 → 0<diffuseDefect v z → diffuseDefect v z<δ →
      gradient (inverseProfile v) z≠0 ∧
      ∀ P'≥P, |diffuseMeanCurvature v z| ≤
        ((3/8 : ℝ)/(4*Real.sqrt 2/3))*(∫ s in -P'..P', defectWeight v (z+s • diffuseNormal v z)^3 *
          diffuseDefect v (z+s • diffuseNormal v z)) := by
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hc : 1/(2*Real.sqrt 2)<(3/8 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0<2*Real.sqrt 2)).mpr
    nlinarith
  refine ⟨hc,?_,diffuse_mean_window hn hc⟩
  nlinarith

end DeGiorgi
end

end OAI
