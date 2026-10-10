import OAI.Geometry.RCD.Coordinates.PositiveForms

namespace OAI

/-!
# Fixed centers for directional patch energies

This is the selection in equation `re:fixed-center`: a positive lower
energy floor permits one fixed point in each patch with energy at most
twice every active point's energy. No continuity or measurability of the
energy function is used. Directional pair bounds then give the actual
fixed-center bound used to construct the correction fields.
-/

open Set
open scoped InnerProductSpace

namespace RegularPointCoordinates

theorem exists_energy_center {X : Type*} {s : Set X} (hs : s.Nonempty)
    {energy : X → ℝ} {floor : ℝ} (hfloor : 0 < floor)
    (hlower : ∀ x ∈ s, floor ≤ energy x) :
    ∃ z ∈ s, ∀ x ∈ s, energy z ≤ 2 * energy x := by
  have hne : (energy '' s).Nonempty := hs.image energy
  have hbdd : BddBelow (energy '' s) := by
    refine ⟨floor, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hlower x hx
  have hinf : floor ≤ sInf (energy '' s) := by
    apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    exact hlower x hx
  obtain ⟨_, ⟨z, hz, rfl⟩, hnear⟩ := exists_lt_of_csInf_lt hne
    (by linarith : sInf (energy '' s) < 2 * sInf (energy '' s))
  refine ⟨z, hz, ?_⟩
  intro x hx
  have hxinf := csInf_le hbdd (mem_image_of_mem energy hx)
  linarith

theorem exists_patch_energy_centers {X ι : Type*} (patch : ι → Set X)
    (energy : X → ℝ) (hne : ∀ j, (patch j).Nonempty)
    (hfloor : ∀ j, ∃ floor : ℝ, 0 < floor ∧ ∀ x ∈ patch j, floor ≤ energy x) :
    ∃ center : ι → X, ∀ j, center j ∈ patch j ∧
      ∀ x ∈ patch j, energy (center j) ≤ 2 * energy x := by
  classical
  have hc (j : ι) : ∃ z ∈ patch j, ∀ x ∈ patch j, energy z ≤ 2 * energy x := by
    obtain ⟨floor, hf, hl⟩ := hfloor j
    exact exists_energy_center (hne j) hf hl
  choose center hmem henergy using hc
  exact ⟨center, fun j => ⟨hmem j, henergy j⟩⟩

variable {X E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pairwise directional estimate becomes a bound against the
energy at the testing point alone after the fixed-center selection. -/
theorem centered_patch_energy_le (u : X → E) (D : E →L[ℝ] E)
    {energy : X → ℝ} {C r : ℝ} {x z : X} (hC : 0 ≤ C)
    (hz : energy z ≤ 2 * energy x)
    (hpair : ⟪u x - u z, D (u x - u z)⟫_ℝ ≤
      C * r ^ 2 * (energy x + energy z)) :
    ⟪u x - u z, D (u x - u z)⟫_ℝ ≤ (3 * C) * r ^ 2 * energy x := by
  calc
    _ ≤ C * r ^ 2 * (energy x + energy z) := hpair
    _ ≤ C * r ^ 2 * (energy x + 2 * energy x) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (sq_nonneg r))
    _ = _ := by ring

/-- Simultaneous construction of the fixed affine centers for a family
of patches. The conclusion is the displacement-energy hypothesis used
by `PatchIterationGeometry`, without adding regularity to the energies. -/
theorem exists_patch_centers_with_energy_bound
    (patch : ι → Set X) (energy : X → ℝ) (u : X → E)
    (D : ι → E →L[ℝ] E) {C r : ℝ} (hC : 0 ≤ C)
    (hne : ∀ j, (patch j).Nonempty)
    (hfloor : ∀ j, ∃ floor : ℝ, 0 < floor ∧ ∀ x ∈ patch j, floor ≤ energy x)
    (hpair : ∀ j, ∀ x ∈ patch j, ∀ z ∈ patch j,
      ⟪u x - u z, D j (u x - u z)⟫_ℝ ≤ C * r ^ 2 * (energy x + energy z)) :
    ∃ center : ι → X, ∀ j, center j ∈ patch j ∧ ∀ x ∈ patch j,
      ⟪u x - u (center j), D j (u x - u (center j))⟫_ℝ ≤
        (3 * C) * r ^ 2 * energy x := by
  obtain ⟨center, hc⟩ := exists_patch_energy_centers patch energy hne hfloor
  refine ⟨center, fun j => ⟨(hc j).1, ?_⟩⟩
  intro x hx
  exact centered_patch_energy_le u (D j) hC ((hc j).2 x hx)
    (hpair j x hx (center j) (hc j).1)

end RegularPointCoordinates

end OAI
