import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.ScaledPullback

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma source_two_jet_bound {f : Point → ℝ} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f (logRadiusChart x))
    (hb : ScaledComponentBound f 2 q B (logRadiusChart x)) :
    ‖actualScalarJet (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  have he (l : List I) (hl : l.length ≤ 2) :
      |coordinateIter l (fun y => f (logRadiusChart y)) x| ≤ B/Real.exp (x 0)^q := by
    rw [coordinateIter_pullback l (hf.of_le (by exact_mod_cast hl))]
    simpa only [logRadiusChart,ite_true] using hb l hl
  apply scalarJet_norm_of_components (by positivity)
  · exact he [] (by simp)
  · intro a; exact he [a] (by simp)
  · intro a b; exact he [a,b] (by simp)

lemma source_three_jet_bound {f : Point → ℝ} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 3 f (logRadiusChart x))
    (hb : ScaledComponentBound f 3 q B (logRadiusChart x)) :
    ‖actualThreeJet (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  have he (l : List I) (hl : l.length ≤ 3) :
      |coordinateIter l (fun y => f (logRadiusChart y)) x| ≤ B/Real.exp (x 0)^q := by
    rw [coordinateIter_pullback l (hf.of_le (by exact_mod_cast hl))]
    simpa only [logRadiusChart,ite_true] using hb l hl
  apply norm_prod_le_iff.mpr
  constructor
  · apply scalarJet_norm_of_components (by positivity)
    · exact he [] (by simp)
    · intro a; exact he [a] (by simp)
    · intro a b; exact he [a,b] (by simp)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    apply scalarJet_norm_of_components (by positivity)
    · exact he [a] (by simp)
    · intro b; exact he [b,a] (by simp)
    · intro b c; exact he [b,c,a] (by simp)

lemma source_matrix_three_bound {f : Point → Mat} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 3 f (logRadiusChart x))
    (hb : ∀ i k, ScaledComponentBound (fun y => f y i k) 3 q B (logRadiusChart x)) :
    ‖matrixThreeJets (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact source_three_jet_bound hB (component_diff hf i k) (hb i k)

lemma source_matrix_two_bound {f : Point → Mat} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f (logRadiusChart x))
    (hb : ∀ i k, ScaledComponentBound (fun y => f y i k) 2 q B (logRadiusChart x)) :
    ‖matrixScalarJets (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact source_two_jet_bound hB (component_diff hf i k) (hb i k)

end
end CKSMixedGeometry

end

end OAI
