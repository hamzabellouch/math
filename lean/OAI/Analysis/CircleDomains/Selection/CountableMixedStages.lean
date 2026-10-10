import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.MixedCoordinateModel
import OAI.Analysis.CircleDomains.Topology.OrderedCoordinateExhaustion

namespace OAI

/-! Actual mixed transfers of a countable ordered coordinate family.
The finite lists inherit the original order, and every prescribed mark
and every coordinate is eventually included. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_countable_mixed_stages
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    {G U : Set Sphere} (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) (hUB : U ⊆ (π '' Gᶜ)ᶜ)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {S : Type*} [Countable S] (σ : S → Sphere) (hσ : Injective σ)
    (hσB : ∀ s, σ s ∈ π '' Gᶜ) (hσU : ∀ s, σ s ∉ U)
    {C : Type*} [LinearOrder C] [Countable C]
    (data : C → MaskedCoordinateData G U π σ)
    (retained : ℕ → C) (hinj : Injective retained)
    (R : RealCoordinateSubfamily data retained)
    (hcompat : ∀ (c : C) (d : ℕ) (labels : Fin d → C), (∀ i, labels i < c) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (data c).graph
          (fun c => (data c).graph) labels) = 0)
    (K₀ : ℕ → Set (ℝ × ℝ)) (hK₀ : ∀ n, IsClosed (K₀ n))
    (hK₀G : ∀ n, K₀ n ⊆ realChartDomain G)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε ρ : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hρ : ∀ n, 0 < ρ n) :
    ∃ (size : ℕ → ℕ) (label : ∀ n, Fin (size n) ↪o C)
      (slot : ∀ n, Fin (n + 1) → Fin (size n)) (Flag : ℕ → Set S),
      (∀ n, Injective (slot n)) ∧
      (∀ n j, label n (slot n j) = retained j) ∧
      (∀ c, ∀ᶠ n in atTop, c ∈ range (label n)) ∧
      (∀ n, (Flag n).Finite) ∧ Monotone Flag ∧ (∀ n, (Flag n).Nonempty) ∧
      ∃ Q : ∀ n, MixedCoordinateStage (fun j => data (label n j)) (slot n)
        (fun j => R.physical j)
        (Flag n) (O n) (K₀ n) (ε n) (ρ n) n,
        ∀ s, ∀ᶠ n in atTop, s ∈ (Q n).indices := by
  classical
  obtain ⟨size, label, slot, hsize, hslot, hretained, hmono, hcover⟩ :=
    exists_ordered_coordinate_exhaustion retained hinj
  obtain ⟨F, hF, hFm, hFc⟩ := exists_increasing_finite_marks S
  let Flag (n : ℕ) : Set S := F n ∪ (fun c => (data c).singular) '' range (label n)
  have hFlag (n : ℕ) : (Flag n).Finite :=
    (hF n).union ((Set.finite_range (label n)).image (fun c => (data c).singular))
  have hflag (n : ℕ) (j : Fin (size n)) : (data (label n j)).singular ∈ Flag n :=
    Or.inr ⟨label n j, mem_range_self j, rfl⟩
  have hFlagm : Monotone Flag := fun n m hnm =>
    union_subset_union (hFm hnm) (image_mono (hmono hnm))
  have hnonempty (n : ℕ) : Nonempty (MixedCoordinateStage (fun j => data (label n j)) (slot n)
      (fun j => R.physical j)
      (Flag n) (O n) (K₀ n) (ε n) (ρ n) n) := by
    apply nonempty_mixed_coordinate_stage hsard hsch hcompact hfinite hG hinfty
      π hπ hclosed hsurj hr hTD hUB hPU (hK₀ n) (hK₀G n) (hsize n)
      σ hσ hσB hσU (fun j => data (label n j)) (slot n) (hslot n)
      (R.reindex (label n) (fun j : Fin (n + 1) => (j : ℕ)) (slot n) (hretained n))
      (Flag n) (hFlag n) (hflag n)
      ?_ (O n) (hO n) (hε n) (hρ n) n
    intro j d labels hlabels
    exact hcompat (label n j) d (fun i => label n (labels i))
      (fun i => (label n).strictMono (hlabels i))
  let Q (n : ℕ) := Classical.choice (hnonempty n)
  refine ⟨size, label, slot, Flag, hslot, hretained, hcover, hFlag, hFlagm,
    (fun n => ⟨(data (label n ⟨0, hsize n⟩)).singular, hflag n _⟩), Q, ?_⟩
  intro s
  exact (hFc s).mono (fun n hn => (Q n).flags (Or.inl hn))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
