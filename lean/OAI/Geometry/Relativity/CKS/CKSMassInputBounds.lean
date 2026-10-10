import OAI.Geometry.Relativity.CKS.CKSMassFields

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def normalizeMassFields (r : ℝ) (f : MassFields) : MassFields where
  sigma := f.sigma
  mg := f.mg
  eg := fun y => r^2 • f.eg y
  er := fun y => r^3 • f.er y
  mK := f.mK
  ek := fun y => r^2 • f.ek y
  b := fun y => r^3 • f.b y
  mr := f.mr
  err := fun y => r^6*f.err y

lemma normalizeMassFields_regular (r : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    (normalizeMassFields r f).RegularAt x :=
  ⟨hf.sigma,hf.mg,hf.eg.const_smul (r^2),hf.er.const_smul (r^3),hf.mK,
    hf.ek.const_smul (r^2),hf.b.const_smul (r^3),hf.mr,hf.err.const_smul (r^6)⟩

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

lemma normalized_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} {r B : ℝ} (hr : 0 < r) (n : ℕ) (hv : ‖v‖ ≤ B/r^n) :
    ‖r^n • v‖ ≤ B := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hr n)]
  calc
    r^n*‖v‖ ≤ r^n*(B/r^n) := mul_le_mul_of_nonneg_left hv (pow_nonneg hr.le n)
    _ = B := by field_simp

lemma normalized_b_jet (r : ℝ) {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    (fun a => actualThreeJet (fun y => (normalizeMassFields r f).b y a) x) =
      r^3 • (fun a => actualThreeJet (fun y => f.b y a) x) := by
  funext a
  exact actualThreeJet_smul (r^3) (contDiffAt_pi.mp hf.b a)

theorem normalized_mass_input_bound {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hs : ‖matrixThreeJets f.sigma x‖ ≤ B) (hmg : ‖matrixThreeJets f.mg x‖ ≤ B)
    (heg : ‖matrixThreeJets f.eg x‖ ≤ B/r^2) (her : ‖matrixScalarJets f.er x‖ ≤ B/r^3)
    (hmk : ‖matrixScalarJets f.mK x‖ ≤ B) (hek : ‖matrixScalarJets f.ek x‖ ≤ B/r^2)
    (hb : ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/r^3)
    (hmr : ‖actualScalarJet f.mr x‖ ≤ B) (herr : ‖actualScalarJet f.err x‖ ≤ B/r^6) :
    ‖massInputOf (normalizeMassFields r f) x‖ ≤ B := by
  refine massInputOf_norm (f := normalizeMassFields r f) (x := x) hB hs hmg ?_ ?_ hmk ?_ ?_ hmr ?_
  · change ‖matrixThreeJets (fun y => r^2 • f.eg y) x‖ ≤ B
    rw [matrixThreeJets_smul (r^2) hf.eg]
    exact normalized_norm_le hr 2 heg
  · change ‖matrixScalarJets (fun y => r^3 • f.er y) x‖ ≤ B
    rw [matrixScalarJets_smul (r^3) hf.er]
    exact normalized_norm_le hr 3 her
  · change ‖matrixScalarJets (fun y => r^2 • f.ek y) x‖ ≤ B
    rw [matrixScalarJets_smul (r^2) hf.ek]
    exact normalized_norm_le hr 2 hek
  · rw [normalized_b_jet r hf]
    exact normalized_norm_le hr 3 hb
  · change ‖actualScalarJet (fun y => r^6*f.err y) x‖ ≤ B
    rw [actualScalarJet_smul (r^6) hf.err]
    exact normalized_norm_le hr 6 herr

end
end CKSAngularGeometry

end

end OAI
