import OAI.Geometry.Relativity.CKS.CKSScaledBounds

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

lemma coordinateIter_le_scalarJet (l : List I) {f : Point → ℝ} {x : Point}
    (hl : l.length ≤ 2) : |coordinateIter l f x| ≤ ‖actualScalarJet f x‖ := by
  rcases l with _ | ⟨a,l⟩
  · exact norm_fst_le (actualScalarJet f x)
  rcases l with _ | ⟨b,l⟩
  · exact (norm_le_pi_norm (actualScalarJet f x).2.1 a).trans
      ((norm_fst_le (actualScalarJet f x).2).trans (norm_snd_le (actualScalarJet f x)))
  rcases l with _ | ⟨c,l⟩
  · exact (norm_le_pi_norm ((actualScalarJet f x).2.2 a) b).trans
      ((norm_le_pi_norm (actualScalarJet f x).2.2 a).trans
        ((norm_snd_le (actualScalarJet f x).2).trans (norm_snd_le (actualScalarJet f x))))
  · simp only [List.length_cons] at hl
    omega

lemma source_scaled_bound_of_jet {f : Point → ℝ} {x : Point} {q : ℕ} {B : ℝ}
    (hf : ContDiffAt ℝ 2 f (logRadiusChart x))
    (hb : ‖actualScalarJet (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q) :
    ScaledComponentBound f 2 q B (logRadiusChart x) := by
  intro l hl
  have he := (coordinateIter_le_scalarJet l hl).trans hb
  rw [coordinateIter_pullback l (hf.of_le (by exact_mod_cast hl))] at he
  simpa only [logRadiusChart,ite_true] using he

end
end CKSMixedGeometry

end

end OAI
