import OAI.MeasureTheory.Falconer.Estimates.PositiveDistancePushforward

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem descriptorSpatialMask_eq_one_of_good (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) {x : Plane} {dir : UnitCircle}
    (hx : ∃ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b), x ∈ (Q.descendant P).carrier)
    (hg : (x,dir) ∈ endpointDescriptorGood Q ρ m N lam sig J i b) :
    descriptorSpatialMask Q ρ m N lam sig J i b x dir = 1 := by
  obtain ⟨P,hP,hx⟩ := hx
  unfold descriptorSpatialMask
  rw [spatialAnchorMask_eq Q hQ ρ _ _ _ _ hP hx]
  exact circleTestMask_eq_one _ _ _ (hg P (Finset.mem_filter.mp hP).1 hx)

namespace PositiveDistanceData

noncomputable def minimalMask (d : PositiveDistanceData) (z : Plane × Plane) : ℝ :=
  descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.1 (sourceRadialUnit z.2 z.1) *
  descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.2 (sourceRadialUnit z.2 z.1)

theorem measurable_minimalMask (d : PositiveDistanceData) :
    Measurable d.minimalMask := by
  let descriptors := policyDescriptorList
    (fun level => d.mass level-(level:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  let mask : Plane × UnitCircle → ℝ := fun point =>
    descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i descriptors
      point.1 point.2
  have hmask : Measurable mask :=
    measurable_descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i descriptors
  change Measurable (fun point : Plane × Plane =>
    mask (point.1, sourceRadialUnit point.2 point.1) *
      mask (point.2, sourceRadialUnit point.2 point.1))
  exact (hmask.comp (measurable_fst.prodMk measurable_pairRadialUnit)).mul
    (hmask.comp (measurable_snd.prodMk measurable_pairRadialUnit))

theorem minimalMask_bounds (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) : 0 ≤ d.minimalMask z ∧ d.minimalMask z ≤ 1 := by
  have h₁ := descriptorListMask_bounds d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := descriptorListMask_bounds d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,
    (mul_le_mul_of_nonneg_right h₁.2 h₂.1).trans (by simpa only [one_mul] using h₂.2)⟩

theorem ae_minimalMask_eq_one_on_good (d : PositiveDistanceData) [SFinite d.ρ]
    (hQ : 0 < d.Q.side) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ∀ᵐ z ∂d.cellPair, z ∈ d.good → d.minimalMask z = 1 := by
  have ha : ∀ᵐ x ∂d.ρ, ∀ n : ℕ, ∃ P ∈ occupiedAnchorPaths d.Q d.ρ n,
      x ∈ (d.Q.descendant P).carrier :=
    ae_all_iff.mpr (fun n => ae_occupied_anchor d.Q d.ρ hcarry n)
  change ∀ᵐ z ∂(d.ρ.restrict (d.Q.descendant d.X).carrier).prod
    (d.ρ.restrict (d.Q.descendant d.Y).carrier), _
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae ha),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae ha)] with z hz₁ hz₂ hg
  have hprod : ∀ x : Plane,
      (∀ n : ℕ, ∃ P ∈ occupiedAnchorPaths d.Q d.ρ n, x ∈ (d.Q.descendant P).carrier) →
      (∀ b ∈ policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t,
        (x,sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b) →
      descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
        (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
        x (sourceRadialUnit z.2 z.1) = 1 := by
    intro x hx hgood
    exact Finset.prod_eq_one (fun b hb => descriptorSpatialMask_eq_one_of_good
      d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i b (hx _) (hgood b hb))
  rw [minimalMask,hprod z.1 hz₁ (fun b hb => (hg b hb).1),
    hprod z.2 hz₂ (fun b hb => (hg b hb).2),one_mul]

end PositiveDistanceData

end PlanarFalconer

end OAI
