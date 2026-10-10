import OAI.Probability.SLE.Loewner.InitialInverseChart
import OAI.Probability.SLE.Geometry.HalfPlaneCayleyInverse

namespace OAI

/-! Forward maps for initial slits, all defined analytically on the final slit complement. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

noncomputable def initialForwardChart (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) : ℂ → ℂ :=
  if ht : t=0 then id else (initialSlitChart p hi h0 hH t ht).forward

@[simp] lemma initialForwardChart_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    initialForwardChart p hi h0 hH 0=id := by simp [initialForwardChart]

lemma initialSubarc_range_subset (p : C(unitInterval,ℂ)) (t : unitInterval) :
    range (initialSubarc p t) ⊆ range p := by
  rintro _ ⟨u,rfl⟩
  exact mem_range_self (t*u)

lemma initialForwardChart_mapsTo (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) :
    MapsTo (initialForwardChart p hi h0 hH t) (upperHalfPlane \ range p) upperHalfPlane := by
  intro z hz
  by_cases ht : t=0
  · simpa only [ht,initialForwardChart_zero,id_eq] using hz.1
  · rw [initialForwardChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).bijOn.mapsTo
      ⟨hz.1,fun h => hz.2 (initialSubarc_range_subset p t h)⟩

lemma initialForwardChart_differentiableOn (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) :
    DifferentiableOn ℂ (initialForwardChart p hi h0 hH t) (upperHalfPlane \ range p) := by
  by_cases ht : t=0
  · simp only [ht,initialForwardChart_zero]
    exact differentiableOn_id
  · rw [initialForwardChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).forward_differentiable.mono
      (fun _ hz => ⟨hz.1,fun h => hz.2 (initialSubarc_range_subset p t h)⟩)

lemma initialInverse_forward_on_final (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range p) :
    initialInverseChart p hi h0 hH t (initialForwardChart p hi h0 hH t z)=z := by
  by_cases ht : t=0
  · simp [ht]
  · rw [initialInverseChart,dite_eq_right ht,initialForwardChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).left_inverse _
      ⟨hz.1,fun h => hz.2 (initialSubarc_range_subset p t h)⟩

lemma initialForward_inverse (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane) :
    initialForwardChart p hi h0 hH t (initialInverseChart p hi h0 hH t z)=z := by
  by_cases ht : t=0
  · simp [ht]
  · rw [initialForwardChart,dite_eq_right ht,initialInverseChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).right_inverse _ hz

lemma halfPlaneCayley_differentiableOn : DifferentiableOn ℂ halfPlaneCayley upperHalfPlane := by
  apply (differentiableOn_id.sub_const I).div (differentiableOn_id.add_const I)
  exact fun z hz => halfPlaneCayley_den_ne (show 0<z.im from hz).le

end SLEExactGauge

end

end OAI
