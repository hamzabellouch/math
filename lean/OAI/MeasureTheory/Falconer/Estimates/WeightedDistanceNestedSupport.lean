import OAI.MeasureTheory.Falconer.Estimates.WeightedDistancePushforward
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceJetSupport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_weighted_distance_nested_support {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ], N₀ ≤ d.N → d.sig = sig → d.J = J →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, ∀ᵐ z ∂d.cellPair, d.spatialWeight z ≠ 0 →
        z ∈ ({d with t := v, i := d.i+1} : PositiveDistanceData).good := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorAngleMask_support hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hN hsig' hJ' hQ hcarry hq ht v hv
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have ha : ∀ᵐ z ∂d.cellPair, ∀ n : ℕ,
      (∃ P ∈ occupiedAnchorPaths d.Q d.ρ n, z.1 ∈ (d.Q.descendant P).carrier) ∧
      (∃ P ∈ occupiedAnchorPaths d.Q d.ρ n, z.2 ∈ (d.Q.descendant P).carrier) :=
    (ae_mono (Measure.prod_mono (μ' := d.ρ) (ν' := d.ρ)
      Measure.restrict_le_self Measure.restrict_le_self)) (ae_all_occupied_pair d.Q d.ρ hcarry)
  filter_upwards [ha] with z hz hn
  have hm : d.minimalMask z ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have hm₁ := (mul_ne_zero_iff.mp hm).1
  have hm₂ := (mul_ne_zero_iff.mp hm).2
  intro b hb
  have hb' := policyDescriptorList_mono (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) (le_refl d.a) hv hb
  have hvalid := policyDescriptor_valid _ hq ht hb'
  have hmask (x : Plane)
      (hx : ∃ P ∈ occupiedAnchorPaths d.Q d.ρ (descriptorAnchor b), x ∈ (d.Q.descendant P).carrier)
      (hmx : descriptorSpatialMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b x
        (sourceRadialUnit z.2 z.1) ≠ 0) :
      (x,sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood
        d.Q d.ρ d.mass d.N d.lam d.sig d.J (d.i+1) b := by
    obtain ⟨P,hP,hx⟩ := hx
    apply endpointDescriptorGood_of_occupied d.Q hQpos d.ρ d.mass d.N d.lam d.sig d.J
      (d.i+1) b x _ P hP hx
    have hh := h₀ d.N hN d.Q hQ d.ρ d.mass d.lam d.i b hvalid P hP x hx
    rw [← hsig',← hJ'] at hh
    have hmem : sourceAngle (sourceRadialUnit z.2 z.1) ∈
        tsupport (descriptorAngleMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b x) := by
      apply subset_tsupport
      simpa only [Function.mem_support,descriptorAngleMask,sourceUnitDirection_sourceAngle] using hmx
    simpa only [mem_preimage,sourceUnitDirection_sourceAngle] using hh hmem
  exact ⟨hmask z.1 (hz _).1 (Finset.prod_ne_zero_iff.mp hm₁ b hb'),
    hmask z.2 (hz _).2 (Finset.prod_ne_zero_iff.mp hm₂ b hb')⟩

end PlanarFalconer

end OAI
