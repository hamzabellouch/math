import Mathlib.AlgebraicGeometry.Morphisms.Affine

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme}

theorem isUnit_of_basicOpen_eq_top (r : Γ(X,⊤)) (hr : X.basicOpen r = ⊤) :
    IsUnit r := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ r
  intro x hx
  exact (X.mem_basicOpen_top r x).mp (by rw [hr]; trivial)

theorem appTop_reflects_isUnit (f : Y ⟶ X) (hf : Function.Surjective f)
    (r : Γ(X,⊤)) (hr : IsUnit (f.appTop r)) : IsUnit r := by
  apply isUnit_of_basicOpen_eq_top r
  apply top_unique
  intro x hx
  obtain ⟨y, rfl⟩ := hf x
  have hy : y ∈ f ⁻¹ᵁ X.basicOpen r := by
    rw [Scheme.preimage_basicOpen_top, Y.basicOpen_of_isUnit hr]
    trivial
  exact hy

theorem isAffineOpen_basicOpen_of_le (r : Γ(X,⊤)) (U : X.Opens)
    (hU : IsAffineOpen U) (hr : X.basicOpen r ≤ U) :
    IsAffineOpen (X.basicOpen r) := by
  have h := hU.basicOpen (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r)
  rwa [Scheme.basicOpen_res, inf_eq_right.mpr hr] at h

theorem isAffine_of_surjective_appTop (f : Y ⟶ X) [IsAffine Y]
    (hf : Function.Surjective f) (hΓ : Function.Surjective f.appTop) : IsAffine X := by
  let S : Set Γ(X,⊤) := {r | IsAffineOpen (X.basicOpen r)}
  have hcover : (⊤ : Y.Opens) ≤ ⨆ a : (f.appTop '' S), Y.basicOpen a.1 := by
    intro y hy
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨a, haU, hya⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (⟨y, hyU⟩ : f ⁻¹ᵁ U) (by trivial)
    obtain ⟨r, hr⟩ := hΓ a
    have hrU : X.basicOpen r ≤ U := by
      intro x hx
      obtain ⟨z, rfl⟩ := hf x
      apply haU
      have hz : z ∈ f ⁻¹ᵁ X.basicOpen r := hx
      rwa [Scheme.preimage_basicOpen_top, hr] at hz
    have hrS : r ∈ S := isAffineOpen_basicOpen_of_le r U hU hrU
    exact Opens.mem_iSup.mpr ⟨⟨a, r, hrS, hr⟩, hya⟩
  have hmap : Ideal.map f.appTop.hom (Ideal.span S) = ⊤ := by
    rw [Ideal.map_span]
    exact (isAffineOpen_top Y).self_le_iSup_basicOpen_iff.mp hcover
  obtain ⟨r, hrS, hr⟩ := (Ideal.mem_map_iff_of_surjective f.appTop.hom hΓ).mp
    (show (1 : Γ(Y,⊤)) ∈ Ideal.map f.appTop.hom (Ideal.span S) by rw [hmap]; trivial)
  have hunit : IsUnit r := appTop_reflects_isUnit f hf r (hr ▸ isUnit_one)
  exact isAffine_of_isAffineOpen_basicOpen S
    ((Ideal.span S).eq_top_of_isUnit_mem hrS hunit) (fun r hr => hr)

end
end PiExponentSeshadri.Geometry

end OAI
