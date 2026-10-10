import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Selection.CountableMixedStages
import OAI.Analysis.CircleDomains.Selection.RealCoordinateData
import OAI.Analysis.CircleDomains.Selection.RealStageBands
import OAI.Analysis.CircleDomains.Transfer.EnlargedRealModels

namespace OAI

/-! Normal-family exhaustions whose finite models simultaneously retain
all the ordered period tests and the original real barrier family. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}

structure MixedModelExhaustion
    (d : CountableRealCoordinates G π σ) {C : Type*} [LinearOrder C]
    (data : C → MaskedCoordinateData G d.source π σ) (retained : ℕ → C)
    (O : ℕ → S → Set Sphere) (ε ρ : ℕ → ℝ) where
  real : RealModelExhaustion d O ε
  size : ℕ → ℕ
  label : ∀ n, Fin (size n) ↪o C
  slot : ∀ n, Fin (n + 1) → Fin (size n)
  slot_injective : ∀ n, Injective (slot n)
  label_real : ∀ n j, label n (slot n j) = retained j
  coordinate_eventually : ∀ c, ∀ᶠ n in atTop, c ∈ range (label n)
  stages : ∀ n, MixedCoordinateStage (fun j => data (label n j)) (slot n)
    (fun j => d.physical j) (real.flags n) (O n) (realChartDomain (real.cores n)) (ε n) (ρ n) n
  same_indices : ∀ n, (stages n).indices = (real.stages n).indices
  same_terminals : ∀ n, HEq (stages n).terminals (real.stages n).terminals
  same_forward : ∀ n, (stages n).model.forward = (real.stages n).forward
  same_inverse : ∀ n, (stages n).model.inverse = (real.stages n).inverse
  same_domain : ∀ n, (stages n).model.domain = (real.stages n).domain

 theorem exists_mixed_model_exhaustion
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (hG : IsOpen G) (hconn : IsConnected G) (hinfty : OnePoint.infty ∈ G)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) [Countable S]
    (d : CountableRealCoordinates G π σ) (hUB : d.source ⊆ (π '' Gᶜ)ᶜ)
    (s₀ : S) {C : Type*} [LinearOrder C] [Countable C]
    (data : C → MaskedCoordinateData G d.source π σ)
    (retained : ℕ → C) (hinj : Injective retained)
    (hdata : ∀ j, data (retained j) = d.maskedCoordinate hG s₀ j)
    (hcompat : ∀ (c : C) (k : ℕ) (labels : Fin k → C), (∀ i, labels i < c) →
      (volume.prod (Measure.pi (fun _ : Fin k => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (data c).graph
          (fun c => (data c).graph) labels) = 0)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε ρ : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hρ : ∀ n, 0 < ρ n) :
    Nonempty (MixedModelExhaustion d data retained O ε ρ) := by
  classical
  let R : RealCoordinateSubfamily data retained := {
    physical := d.physical
    quotient := d.coordinate
    bound := d.bound
    bounded := d.coordinate_bounded
    full_mask := fun j => by rw [hdata j]; rfl
    smooth := d.physical_smooth
    energy := d.physical_energy
    pullback := (d.realSubfamily hG s₀).pullback
    projection := fun j x => by rw [hdata j]; rfl
    width := fun j s => by
      rw [hdata j]
      exact (d.realSubfamily hG s₀).width j s }
  obtain ⟨r, D, K, hrpos, hDo, hDc, hDm, _, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinfty
  obtain ⟨size, label, slot, Flag, hslot, hretained, hcoords, hFlag, hFlagm, hFlagne, Q, hmarks⟩ :=
    exists_countable_mixed_stages hsard hsch hcompact hfinite hG hinfty
      π hπ hclosed hsurj hr hTD hUB d.source_map σ d.labels_injective d.labels_dust
      (fun s hs => hUB hs (d.labels_dust s)) data retained hinj R hcompat
      (fun n => realChartDomain (K n)) (fun n => isClosed_realChartDomain (hK n).1.isClosed)
      (fun n => preimage_mono (hK n).2) O hO ε ρ hε hρ
  let T (n : ℕ) := (Q n).realStage hG
    (fun j => by simpa only [hretained] using R.full_mask j)
    (fun j => d.physical_smooth j) (fun j => d.physical_energy j)
    (fun j x => by simpa only [hretained] using R.projection j x)
  have hwidth (n : ℕ) (j : Fin (n + 1)) (s : S) :
      (data (label n (slot n j))).upper s - (data (label n (slot n j))).lower s =
        d.upper j s - d.lower j s := by
    rw [hretained, hdata]
    rfl
  let T' (n : ℕ) : d.Stage n (Flag n) (O n) (realChartDomain (K n)) (ε n) :=
    (T n).withBands (fun j => d.lower j) (fun j => d.upper j) (hwidth n)
  have hplane (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ K n :=
    (hDK n).trans interior_subset
  let M : RealModelExhaustion d O ε := {
    radius := 2 * r
    radius_pos := mul_pos (by norm_num) hrpos
    plane := D
    plane_open := hDo
    plane_connected := hDc
    plane_monotone := hDm
    cores := K
    core_compact := fun n => (hK n).1
    core_source := fun n => (hK n).2
    plane_core := hplane
    exhausts := by simpa only [image_iUnion, iUnion_union, iUnion_const] using hcover
    exterior_core := by
      intro n p hp
      apply hplane n
      cases p using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe z =>
        refine Or.inl ⟨z, hDm (Nat.zero_le n) (hext ?_), rfl⟩
        change 2 * r ≤ ‖z‖
        simpa only [mem_compl_iff, OnePoint.coe_injective.mem_set_image,
          mem_ball, dist_zero_right, not_lt] using hp
    exterior_plane := by
      intro z hz
      apply hext
      change 2 * r ≤ ‖z‖
      change 2 * (2 * r) ≤ ‖z‖ at hz
      linarith
    flags := Flag
    flags_finite := hFlag
    flags_monotone := hFlagm
    stages := T'
    indices_nonempty := fun n _ => (hFlagne n).mono (Q n).flags
    marks := hmarks }
  exact ⟨{
    real := M
    size := size
    label := label
    slot := slot
    slot_injective := hslot
    label_real := hretained
    coordinate_eventually := hcoords
    stages := Q
    same_indices := fun _ => rfl
    same_terminals := fun _ => HEq.rfl
    same_forward := fun _ => rfl
    same_inverse := fun _ => rfl
    same_domain := fun _ => rfl }⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
