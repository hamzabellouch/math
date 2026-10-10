import OAI.MeasureTheory.Falconer.Angular.CapDensityCharge
import OAI.MeasureTheory.Falconer.Measures.FiniteMassMultiplication

namespace OAI

/-! # Multiplying actual physical-tube charges for one retained radial cap -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

noncomputable def retainedRadialCap (μ : Measure (Space d)) (G : Set (Space d × Space d))
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (x u : Space d) (r : ℝ) : Set (Space d) :=
  {z | (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧ ‖normalize (z-x)-u‖ ≤ r}

noncomputable def radialCapHitCells (μ : Measure (Space d)) (G : Set (Space d × Space d))
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (x u : Space d) (r : ℝ) (j : ℕ) : Finset ι := by
  classical
  exact (I j).filter (fun i => ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r)

theorem multiscale_physical_cap_mass (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (x u : Space d) (r B : ℝ) (D : ℕ → ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hbound : ∀ z, (x,z) ∈ G → ‖z-x‖ ≤ B)
    (hne : ∀ z, (x,z) ∈ G → z ≠ x)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G → q ≠ x →
      μ (Q j p ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D j+2*B*r}) ≤ F j*μ (Q j p))
    (hcover : ∀ z ∈ retainedRadialCap μ G Q I θ J x u r, ∃ i ∈ I J, z ∈ Q J i) :
    μ (retainedRadialCap μ G Q I θ J x u r) ≤
      (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  classical
  let H := radialCapHitCells μ G Q I θ J x u r
  have hHI (j : ℕ) : H j ⊆ I j := Finset.filter_subset _ _
  have hmem {j : ℕ} {i : ι} (hi : i ∈ H j) :
      ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r := (Finset.mem_filter.mp hi).2
  have hparents : ∀ j < J, ∀ i ∈ H (j+1), parent j i ∈ H j := by
    intro j hj i hi
    obtain ⟨z,hz,hcap⟩ := hmem hi
    obtain ⟨hp,hsub⟩ := hparent j hj i (hHI _ hi)
    exact Finset.mem_filter.mpr ⟨hp,z,hsub hz,hcap⟩
  have hcharge : ∀ j < J, ∀ p ∈ H j,
      (∑ i ∈ H (j+1) with parent j i = p, μ (Q (j+1) i)) ≤
        (θ⁻¹*F j)*μ (Q j p) := by
    intro j hj p hp
    let C := (H (j+1)).filter (fun i => parent j i = p)
    have hCI : C ⊆ I (j+1) := fun i hi => hHI _ (Finset.mem_filter.mp hi).1
    have hCQ : ∀ i ∈ C, Q (j+1) i ⊆ Q j p := by
      intro i hi
      have hs := (hparent j hj i (hCI hi)).2
      rwa [(Finset.mem_filter.mp hi).2] at hs
    have hCdisj : (C : Set ι).PairwiseDisjoint (Q (j+1)) := by
      intro i hi k hk hne
      exact hdisj (j+1) (by omega) (hCI hi) (hCI hk) hne
    have hh := cap_density_children_charge μ G hG Q I J (j+1) (by omega)
      C hCI (Q j p) x u hθ hθtop
      (fun i hi => hQ (j+1) (by omega) i (hCI hi)) hCdisj hCQ
      (fun i hi => hdiam j hj i (hCI hi))
      (fun i hi => by
        obtain ⟨z,hz,hcap⟩ := hmem (Finset.mem_filter.mp hi).1
        exact ⟨z,hz,hcap.1,hne z hcap.1.1,hbound z hcap.1.1,hcap.2⟩)
      (fun q hqp hq hqn _ => hlocal j hj p (hHI _ hp) q hqp hq.1 hqn)
    exact hh
  have hmul := finite_mass_multiplication H parent (fun j i => μ (Q j i))
    (fun j => θ⁻¹*F j) J hparents hcharge
  have hsub : retainedRadialCap μ G Q I θ J x u r ⊆ ⋃ i ∈ H J, Q J i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hi,z,hzi,hz⟩,hzi⟩⟩
  have hzero : (∑ i ∈ H 0, μ (Q 0 i)) ≤ μ univ := by
    rw [← measure_biUnion_finset (fun i hi k hk hik =>
      hdisj 0 (Nat.zero_le _) (hHI _ hi) (hHI _ hk) hik)
      (fun i hi => hQ 0 (Nat.zero_le _) i (hHI _ hi))]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ μ (⋃ i ∈ H J, Q J i) := measure_mono hsub
    _ ≤ ∑ i ∈ H J, μ (Q J i) := measure_biUnion_finset_le _ _
    _ ≤ (∏ j ∈ Finset.range J, θ⁻¹*F j)*(∑ i ∈ H 0, μ (Q 0 i)) := hmul
    _ ≤ _ := mul_le_mul' le_rfl hzero

end Falconer

end OAI
