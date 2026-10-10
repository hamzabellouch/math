import OAI.Analysis.CircleDomains.Topology.CompactLevelTangent
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

namespace OAI

/-! Global integral curves of compactly supported smooth planar vector
fields, from a uniform Picard interval and the existing continuation theorem. -/
open Set Function Filter Metric
open scoped Topology ContDiff Manifold NNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_vector_field_global_curve {V : ℂ → ℂ}
    (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V) (x : ℂ) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hV (by simp)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hV.continuous
  let M : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hM (z : ℂ) : ‖V z‖ ≤ M := (hC z).trans (le_max_left _ _)
  have hlocal (z : ℂ) : ∃ γ : ℝ → ℂ, γ 0 = z ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt γ (V (γ t)) t := by
    let t₀ : Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    have hp : IsPicardLindelof (fun _ : ℝ => V) t₀ z (M+1) 0 M L := by
      refine ⟨fun _ _ => hL.lipschitzOnWith,fun _ _ => continuousOn_const,
        fun _ _ w _ => hM w,?_⟩
      simp only [t₀,NNReal.coe_add,NNReal.coe_one,NNReal.coe_zero,sub_zero,zero_sub,
        neg_neg,max_self]
      simp
    obtain ⟨γ,hγ0,hγ⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (mem_closedBall_self (show (0 : ℝ) ≤ (0 : ℝ≥0) from le_rfl))
    refine ⟨γ,hγ0,?_⟩
    intro t ht
    exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hv : ContMDiff (𝓘(ℝ,ℂ)) (𝓘(ℝ,ℂ)).tangent 1
      (fun z : ℂ => (⟨z,V z⟩ : TangentBundle (𝓘(ℝ,ℂ)) ℂ)) := by
    intro z
    apply (Bundle.contMDiffAt_section (IB := 𝓘(ℝ,ℂ))
      (E := TangentSpace (𝓘(ℝ,ℂ))) (s := fun z : ℂ => V z) z).mpr
    convert ((hV.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contMDiff).contMDiffAt using 1
    simp [mfld_simps]

  obtain ⟨γ,hγ0,hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hv
    (show (0 : ℝ) < 1 by norm_num) (fun z => by
      obtain ⟨γ,hγ0,hγ⟩ := hlocal z
      refine ⟨γ,hγ0,?_⟩
      intro t ht
      exact (hasMFDerivAt_iff_hasFDerivAt.mpr (hγ t ht).hasFDerivAt).hasMFDerivWithinAt) x
  refine ⟨γ,hγ0,?_⟩
  intro t
  exact hasDerivAt_iff_hasFDerivAt.mpr (hasMFDerivAt_iff_hasFDerivAt.mp (hγ t))

end CircleDomainRigidity

end

end OAI
