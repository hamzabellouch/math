import OAI.Geometry.IsometricImmersion.Coordinates.ExteriorCenterNets
import OAI.Geometry.IsometricImmersion.Coordinates.OrientationNet
import Mathlib.Data.Nat.Pairing

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

abbrev OrientationLabel := {R : Matrix (Fin 2) (Fin 2) ℝ // R ∈ orientationRotations}

def orientationLabelCode (R : OrientationLabel) : ℕ :=
  (Fintype.equivFin OrientationLabel R).val

theorem orientationLabelCode_injective : Function.Injective orientationLabelCode := by
  intro R S h
  apply (Fintype.equivFin OrientationLabel).injective
  exact Fin.ext h

def orientedLayerIndex (k : ℕ) (R : OrientationLabel) : ℕ :=
  Nat.pair k (orientationLabelCode R)

theorem orientedLayerIndex_injective :
    Function.Injective (fun a : ℕ × OrientationLabel => orientedLayerIndex a.1 a.2) := by
  intro a b h
  have hab := Nat.pair_eq_pair.mp h
  exact Prod.ext hab.1 (orientationLabelCode_injective hab.2)

theorem orientedLayerIndex_ge_stage (k : ℕ) (R : OrientationLabel) : k ≤ orientedLayerIndex k R :=
  Nat.left_le_pair k (orientationLabelCode R)

theorem orientedLayerIndex_tendsto (R : OrientationLabel) :
    Tendsto (fun k => orientedLayerIndex k R) atTop atTop :=
  tendsto_atTop_mono (fun k => orientedLayerIndex_ge_stage k R) tendsto_id

def orientedExteriorCenters (n k : ℕ) (R : OrientationLabel) : Finset Coord :=
  exteriorCenterNet n (orientedLayerIndex k R)

theorem orientedExteriorCenters_mem_layer (n k : ℕ) (R : OrientationLabel)
    {p : Coord} (hp : p ∈ orientedExteriorCenters n k R) :
    p ∈ exteriorOpenLayer n (orientedLayerIndex k R) :=
  exteriorCenterNet_mem_layer n (orientedLayerIndex k R) hp

theorem orientedExteriorCenters_avoid_disks (n k : ℕ) (R : OrientationLabel)
    {p : Coord} (hp : p ∈ orientedExteriorCenters n k R) (m : ℕ) :
    p ∉ accumulatingDisk m := exteriorCenterNet_avoids_every_disk n (orientedLayerIndex k R) hp m

theorem orientedExteriorLayers_disjoint (n : ℕ) {a b : ℕ × OrientationLabel} (hab : a ≠ b) :
    Disjoint (exteriorClosedLayer n (orientedLayerIndex a.1 a.2))
      (exteriorClosedLayer n (orientedLayerIndex b.1 b.2)) :=
  exteriorClosedLayers_pairwise_disjoint n (fun h => hab (orientedLayerIndex_injective h))

theorem every_boundary_point_every_orientation_centers (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) (R : OrientationLabel) :
    ∃ centers : ℕ → Coord, (∀ k, centers k ∈ orientedExteriorCenters n k R) ∧
      Tendsto centers atTop (𝓝 p) := by
  obtain ⟨centers, hcenters, ht⟩ := every_boundary_point_has_finite_net_sequence n p hp
  exact ⟨fun k => centers (orientedLayerIndex k R),
    fun k => hcenters (orientedLayerIndex k R), ht.comp (orientedLayerIndex_tendsto R)⟩

theorem every_boundary_point_every_rotation_centers (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n))
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R ∈ orientationRotations) :
    ∃ centers : ℕ → Coord,
      (∀ k, centers k ∈ orientedExteriorCenters n k ⟨R, hR⟩) ∧
      (∀ k, centers k ∈ exteriorOpenLayer n (orientedLayerIndex k ⟨R, hR⟩)) ∧
      Tendsto centers atTop (𝓝 p) := by
  obtain ⟨centers, hcenters, ht⟩ := every_boundary_point_every_orientation_centers n p hp ⟨R, hR⟩
  exact ⟨centers, hcenters, fun k => orientedExteriorCenters_mem_layer n k ⟨R, hR⟩ (hcenters k), ht⟩

end SmoothLocal.Geometry

end

end OAI
