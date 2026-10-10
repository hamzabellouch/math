import OAI.MathematicalPhysics.Boltzmann.Collision.AxialSecondMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh

namespace OAI

section

/-! # Finite exceptional axial intervals for the two-gain argument -/

noncomputable section

open Set MeasureTheory

namespace BoltzmannNonuniqueness.AxialFlow

def collapsedCenters (α t z : ℝ) : Finset ℝ :=
  {z/t,1-α,1+α,-1-α,-1+α}

def profileCenters (α γ t z : ℝ) (S : Finset ℝ) : Finset ℝ :=
  S.biUnion fun s => {velocity 1 α γ s t z,velocity (-1) α γ s t z}

def bands (S : Finset ℝ) (b : ℝ) : Set ℝ :=
  ⋃ c ∈ S, {w | |w-c| < b}

theorem outside_bands {S : Finset ℝ} {b w : ℝ} (hw : w ∉ bands S b)
    {c : ℝ} (hc : c ∈ S) : b ≤ |w-c| := by
  by_contra h
  exact hw (mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,lt_of_not_ge h⟩⟩)

theorem collapsedCenters_card_le (α t z : ℝ) : (collapsedCenters α t z).card ≤ 5 := by
  classical
  simp only [collapsedCenters]
  grind [Finset.card_insert_le,Finset.card_singleton]

theorem profileCenters_card_le (α γ t z : ℝ) (S : Finset ℝ) :
    (profileCenters α γ t z S).card ≤ 2*S.card := by
  classical
  unfold profileCenters
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _s ∈ S, (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = _ := by simp [mul_comm]

/-- A single finite list excludes every large retained scale at the second time. -/
theorem outside_profileBands_second_gap {α γ b t₁ t₂ z w s d ω : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht₂ : 0 ≤ t₂) (htt : t₂ ≤ t₁)
    (S : Finset ℝ) (hsS : s ∈ S) (hw : w ∉ bands (profileCenters α γ t₁ z S) b)
    (herr : |d*ω| ≤ b/2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    b/2 ≤ |w-JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω| := by
  have hc : velocity σ α γ s t₁ z ∈ profileCenters α γ t₁ z S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨s,hsS,?_⟩
    rcases hσ with rfl | rfl <;> simp
  exact thermal_second_gap hα hγ hs ht₂ htt (outside_bands hw hc) herr

/-- Five collapsed speeds exclude every sufficiently small positive scale. -/
theorem outside_collapsedBands_second_gap {α γ a δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ (σ s d t₁ t₂ z w ω : ℝ),
      (σ = 1 ∨ σ = -1) → 0 < s → s < μ₀ → a ≤ t₂ → t₂ ≤ t₁ → |d*ω| < δ/4 →
      w ∉ bands (collapsedCenters α t₁ z) δ →
      δ/2 ≤ |w-JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω| := by
  classical
  obtain ⟨μ₀,hμ₀,hμ⟩ := small_scale_second_gap hα hγ ha hδ
  refine ⟨μ₀,hμ₀,?_⟩
  intro σ s d t₁ t₂ z w ω hσ hs hs₀ ht₂ htt herr hw
  apply hμ σ s d t₁ t₂ z w ω hs hs₀ ht₂ htt herr
  · apply outside_bands hw
    rcases hσ with rfl | rfl <;> simp [collapsedCenters]
  · apply outside_bands hw
    rcases hσ with rfl | rfl <;> simp [collapsedCenters]
  · exact outside_bands hw (by simp [collapsedCenters])

end BoltzmannNonuniqueness.AxialFlow

end

end

section

/-! # A finite family of axial intervals has uniformly small kernel mass -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.AxialFlow

theorem bands_measurableSet (S : Finset ℝ) (b : ℝ) : MeasurableSet (bands S b) := by
  unfold bands
  exact Finset.measurableSet_biUnion S (fun c _ => measurableSet_lt (by fun_prop) measurable_const)

theorem bands_measure_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : X → ℝ) (S : Finset ℝ) (ε : ℝ≥0∞) (r : ℝ)
    (hband : ∀ c ∈ S, μ {x | |a x-c| < r} ≤ ε) :
    μ (a ⁻¹' bands S r) ≤ S.card*ε := by
  have he : a ⁻¹' bands S r = ⋃ c ∈ S, {x | |a x-c| < r} := by
    ext x
    simp [bands]
  rw [he]
  apply (measure_biUnion_finset_le S _).trans
  exact (Finset.sum_le_sum (fun c hc => hband c hc)).trans_eq (by simp)

end BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

/-- The first gain charges a finite exceptional-speed list by its cardinality
 times one uniform small-interval bound. The centers may depend on the endpoint. -/
theorem core_axial_bands {α q ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α → 0 < γ →
      0 < s → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (a : Bool)
      (x : JetPrototype.Space) (v : Velocity), transverse v ≠ 0 → ∀ S : Finset ℝ,
      normalizedCoreKernel η K α γ s d q a ((t,x),v) (axial ⁻¹' bands S δ) ≤
        S.card*(ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε) := by
  obtain ⟨δ,hδ,hint⟩ := core_axial_interval (α := α) hq₁ hq₂ hε
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro K γ s d t hK hα hγ hs hd hdmax ht η a x v hv S
  apply bands_measure_le
  intro c hc
  rw [inputKernel_region a (t,x) v (show MeasurableSet {ξ : Velocity | |axial ξ-c| < δ/2} by
    exact measurableSet_lt (by fun_prop) measurable_const)]
  apply (measure_mono (show
    (fun y => PlaneChart.chart v y.1 y.2.1 y.2.2) ⁻¹' {ξ : Velocity | |axial ξ-c| < δ/2} ⊆
      AxialModulus.axialRegion v (c-δ/2) (c+δ/2) from ?_)).trans
    (hint (c-δ/2) (c+δ/2) (by linarith) (by linarith)
      hK hα hγ hs hd hdmax ht η a x v hv)
  intro y hy
  change |axial (PlaneChart.chart v y.1 y.2.1 y.2.2)-c| < δ/2 at hy
  have hy' := abs_lt.mp hy
  exact ⟨by linarith,by linarith⟩

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
