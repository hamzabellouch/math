import OAI.Geometry.Relativity.CKS.ScaledJetOutput

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

lemma coordinateIter_le_threeJet (l : List I) {f : Point → ℝ} {x : Point}
    (hl : l.length ≤ 3) : |coordinateIter l f x| ≤ ‖actualThreeJet f x‖ := by
  by_cases h2 : l.length ≤ 2
  · exact (coordinateIter_le_scalarJet l h2).trans (norm_fst_le (actualThreeJet f x))
  rcases l with _ | ⟨a,l⟩
  · simp at h2
  rcases l with _ | ⟨b,l⟩
  · simp at h2
  rcases l with _ | ⟨c,l⟩
  · simp at h2
  rcases l with _ | ⟨d,l⟩
  · have he := coordinateIter_le_scalarJet (f := D (basis c) f) (x := x) [a,b] (by simp)
    exact he.trans ((norm_le_pi_norm (actualThreeJet f x).2 c).trans (norm_snd_le (actualThreeJet f x)))
  · simp only [List.length_cons] at hl
    omega

lemma source_scaled_bound_of_threeJet {f : Point → ℝ} {x : Point} {q : ℕ} {B : ℝ}
    (hf : ContDiffAt ℝ 3 f (logRadiusChart x))
    (hb : ‖actualThreeJet (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q) :
    ScaledComponentBound f 3 q B (logRadiusChart x) := by
  intro l hl
  have he := (coordinateIter_le_threeJet l hl).trans hb
  rw [coordinateIter_pullback l (hf.of_le (by exact_mod_cast hl))] at he
  simpa only [logRadiusChart,ite_true] using he

end
end CKSMixedGeometry

end

end OAI
