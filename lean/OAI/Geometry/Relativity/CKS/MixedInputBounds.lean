import OAI.Geometry.Relativity.CKS.CKSMassInputBounds
import OAI.Geometry.Relativity.CKS.LogRadiusJets
import OAI.Geometry.Relativity.CKS.JetBounds
import OAI.Geometry.Relativity.CKS.CKSTensorFields

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_nat (n : ℕ) (x : Point) : radiusPower n x = Real.exp (x 0)^n := by
  exact Real.exp_nat_mul (x 0) n

lemma normalize_two_bound {n : ℕ} {f : Point → ℝ} {x : Point} {B : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hb : ‖actualScalarJet f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖actualScalarJet (fun y => radiusPower n y*f y) x‖ ≤ 4*(max 1 |(n:ℝ)|)^2*B := by
  rw [actualScalarJet_mul (radiusPower_diff n 2 x) hf]
  have h := productJet_norm (radiusPower_two_norm n x) hb
  have hr : Real.exp (x 0)^n ≠ 0 := ne_of_gt (pow_pos (Real.exp_pos _) _)
  calc
    _ ≤ 4*((max 1 |(n:ℝ)|)^2*radiusPower n x)*(B/Real.exp (x 0)^n) := h
    _ = 4*(max 1 |(n:ℝ)|)^2*B := by rw [radiusPower_nat]; field_simp

lemma normalize_three_bound {n : ℕ} {f : Point → ℝ} {x : Point} {B : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hb : ‖actualThreeJet f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖actualThreeJet (fun y => radiusPower n y*f y) x‖ ≤ 8*(max 1 |(n:ℝ)|)^3*B := by
  rw [actualThreeJet_mul (radiusPower_diff n 3 x) hf]
  have h := productThreeJet_norm (radiusPower_three_norm n x) hb
  have hr : Real.exp (x 0)^n ≠ 0 := ne_of_gt (pow_pos (Real.exp_pos _) _)
  calc
    _ ≤ 8*((max 1 |(n:ℝ)|)^3*radiusPower n x)*(B/Real.exp (x 0)^n) := h
    _ = 8*(max 1 |(n:ℝ)|)^3*B := by rw [radiusPower_nat]; field_simp

lemma normalize_matrix_three {n : ℕ} {f : Point → Mat} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 3 f x) (hb : ‖matrixThreeJets f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖matrixThreeJets (fun y => radiusPower n y • f y) x‖ ≤ 8*(max 1 |(n:ℝ)|)^3*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact normalize_three_bound (component_diff hf i k)
    ((norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ i).trans hb))

lemma normalize_matrix_two {n : ℕ} {f : Point → Mat} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f x) (hb : ‖matrixScalarJets f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖matrixScalarJets (fun y => radiusPower n y • f y) x‖ ≤ 4*(max 1 |(n:ℝ)|)^2*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact normalize_two_bound (component_diff hf i k)
    ((norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ i).trans hb))

def radialMatrixD (f : Point → Mat) : Point → Mat := fun y i k => D (basis 0) (fun z => f z i k) y

lemma radialMatrixD_regular {f : Point → Mat} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    ContDiffAt ℝ 2 (radialMatrixD f) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact contDiffAt_D (component_diff hf i k) (by norm_num) (basis 0)

lemma radialMatrixD_bound {f : Point → Mat} {x : Point} {B : ℝ}
    (hb : ‖matrixThreeJets f x‖ ≤ B) : ‖matrixScalarJets (radialMatrixD f) x‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro k
  have hh : ‖actualThreeJet (fun y => f y i k) x‖ ≤ B :=
    (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ i).trans hb)
  exact (norm_le_pi_norm _ 0).trans (norm_prod_le_iff.mp hh).2

def normalizeMassLogFields (f : MassFields) : MassFields where
  sigma := f.sigma
  mg := f.mg
  eg := fun y => radiusPower 2 y • f.eg y
  er := fun y => radiusPower 2 y • radialMatrixD f.eg y
  mK := f.mK
  ek := fun y => radiusPower 2 y • f.ek y
  b := fun y => radiusPower 3 y • f.b y
  mr := f.mr
  err := fun y => radiusPower 6 y*f.err y

lemma normalizeMassLogFields_regular {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    (normalizeMassLogFields f).RegularAt x := by
  exact ⟨hf.sigma,hf.mg,(radiusPower_diff 2 3 x).smul hf.eg,
    (radiusPower_diff 2 2 x).smul (radialMatrixD_regular hf.eg),hf.mK,
    (radiusPower_diff 2 2 x).smul hf.ek,(radiusPower_diff 3 3 x).smul hf.b,
    hf.mr,(radiusPower_diff 6 2 x).mul hf.err⟩

lemma massInputOf_norm {f : MassFields} {x : Point} {B : ℝ} (hB : 0 ≤ B)
    (hs : ‖matrixThreeJets f.sigma x‖ ≤ B) (hmg : ‖matrixThreeJets f.mg x‖ ≤ B)
    (heg : ‖matrixThreeJets f.eg x‖ ≤ B) (her : ‖matrixScalarJets f.er x‖ ≤ B)
    (hmk : ‖matrixScalarJets f.mK x‖ ≤ B) (hek : ‖matrixScalarJets f.ek x‖ ≤ B)
    (hb : ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B)
    (hmr : ‖actualScalarJet f.mr x‖ ≤ B) (herr : ‖actualScalarJet f.err x‖ ≤ B) :
    ‖massInputOf f x‖ ≤ B := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    fin_cases i <;> first | exact hs | exact hmg | exact heg
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    fin_cases i <;> first | exact her | exact hmk | exact hek
  apply norm_prod_le_iff.mpr
  refine ⟨hb,?_⟩
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  fin_cases i <;> first | exact hmr | exact herr

theorem normalized_log_mass_input_bound {B : ℝ} (hB : 0 ≤ B)
    {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hs : ‖matrixThreeJets f.sigma x‖ ≤ B) (hmg : ‖matrixThreeJets f.mg x‖ ≤ B)
    (heg : ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2)
    (hmk : ‖matrixScalarJets f.mK x‖ ≤ B) (hek : ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2)
    (hb : ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3)
    (hmr : ‖actualScalarJet f.mr x‖ ≤ B) (herr : ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6) :
    ‖massInputOf (normalizeMassLogFields f) x‖ ≤ 216*B := by
  have hB216 : B ≤ 216*B := by linarith
  refine massInputOf_norm (f := normalizeMassLogFields f) (x := x) (by positivity)
    (hs.trans hB216) (hmg.trans hB216) ?_ ?_ (hmk.trans hB216) ?_ ?_ (hmr.trans hB216) ?_
  · exact (normalize_matrix_three hB hf.eg heg).trans (by norm_num; linarith)
  · exact (normalize_matrix_two hB (radialMatrixD_regular hf.eg) (radialMatrixD_bound heg)).trans (by norm_num; linarith)
  · exact (normalize_matrix_two hB hf.ek hek).trans (by norm_num; linarith)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have h := normalize_three_bound (contDiffAt_pi.mp hf.b a) ((norm_le_pi_norm _ a).trans hb)
    norm_num at h
    exact h
  · exact (normalize_two_bound hf.err herr).trans (by norm_num; linarith)

end
end CKSMixedGeometry

end

end OAI
