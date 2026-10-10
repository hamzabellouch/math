import OAI.Probability.SLE.Loewner.InitialInverseLimitAt

namespace OAI

/-! The complementary hydrodynamic mass, measured from the common final
domain to each initial domain. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma initialForward_comparison_to_final (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (Q : SimpleSlitChart p) (t : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane) :
    ‖initialForwardChart p hi h0 hH t (Q.inverse z)-z‖≤
      (Q.capacity-initialCapacity p hi h0 hH t)/z.im := by
  by_cases ht : t=0
  · simpa only [ht,initialForwardChart_zero,initialCapacity_zero,id_eq,sub_zero] using
      Q.inverse_displacement hz
  · rw [initialForwardChart,dite_eq_right ht,initialCapacity,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).inverse_comparison Q
      (initialSubarc_range_subset p t) hz

lemma initialInverse_limit_forward_on_final (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (hs : s≠0) (ht : Tendsto t atTop (𝓝 s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ z∈upperHalfPlane \ range p,
      Tendsto (fun n => initialForwardChart p hi h0 hH (t (φ n)) z)
        atTop (𝓝 ((initialSlitChart p hi h0 hH s hs).forward z)) := by
  let P := initialSlitChart p hi h0 hH s hs
  have heF := initialInverse_limit_eq_at p hi h0 hH hF hlim hs ht
  have hPinv : EqOn F P.inverse upperHalfPlane := by
    simpa only [initialInverseChart,dite_eq_right hs] using heF
  obtain ⟨φ,hφ,hforward⟩ := initialInverse_limit_forward_subsequence p hi h0 hH hF hlim
  refine ⟨φ,hφ,fun z hz => ?_⟩
  have hzP : z∈upperHalfPlane \ range (initialSubarc p s) :=
    ⟨hz.1,fun hh => hz.2 (initialSubarc_range_subset p s hh)⟩
  have hcov : SurjOn F upperHalfPlane (upperHalfPlane \ range p) :=
    initialInverse_limit_covers_final_domain p hi h0 hH hF hlim
  have he : invFunOn F upperHalfPlane z=P.forward z := by
    apply initialInverse_limit_injOn p hi h0 hH hlim
      (hcov.mapsTo_invFunOn hz) (P.bijOn.mapsTo hzP)
    rw [hcov.rightInvOn_invFunOn hz,hPinv (P.bijOn.mapsTo hzP),P.left_inverse z hzP]
  rw [← he]
  exact hforward z hz

end SLEExactGauge

end

end OAI
