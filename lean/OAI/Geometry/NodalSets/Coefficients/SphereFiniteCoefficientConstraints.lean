import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientAtlasInclusionLemmas

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_coefficient_constraints {ι : Type*}
    (s : Finset ι) (P : ι → Finset Base) (J : ι → ℕ) (eps : ι → ℝ)
    (heps : ∀ i ∈ s, 0 < eps i) :
    ∃ (Q : Finset Base) (m : ℕ) (eta : ℝ), 0 < eta ∧
      ∀ (d b : SphereEnergyData),
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
        sphereCoefficientDistance Q m d.tensor d.density b.tensor b.density < eta →
        ∀ i ∈ s, sphereCoefficientDistance (P i) (J i) d.tensor d.density b.tensor b.density < eps i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,0,1,by norm_num,by simp⟩
  | @insert i s his ih =>
    obtain ⟨Q,m,eta,heta,H⟩ := ih (fun j hj ↦ heps j (Finset.mem_insert_of_mem hj))
    refine ⟨P i ∪ Q,max (J i) m,min (eps i) eta,
      lt_min (heps i (Finset.mem_insert_self _ _)) heta,?_⟩
    intro d b hd hb hdist j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (sphereCoefficientDistance_mono_order (P j) d b hd hb (J j) (max (J j) m) (le_max_left _ _)).trans_lt
        ((sphereCoefficientDistance_mono_atlas (P j) (P j ∪ Q) Finset.subset_union_left d b hd hb _).trans_lt
          (hdist.trans_le (min_le_left _ _)))
    · apply H d b hd hb ?_ j hj
      exact (sphereCoefficientDistance_mono_order Q d b hd hb m (max (J i) m) (le_max_right _ _)).trans_lt
        ((sphereCoefficientDistance_mono_atlas Q (P i ∪ Q) Finset.subset_union_right d b hd hb _).trans_lt
          (hdist.trans_le (min_le_right _ _)))

end
end Yau.Target

end OAI
