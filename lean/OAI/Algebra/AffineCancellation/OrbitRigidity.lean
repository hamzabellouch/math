import OAI.Algebra.AffineCancellation.Rigidity
import OAI.Algebra.AffineCancellation.Orbit

namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]
  [Field K] [CharZero K] [Algebra k K]

/-- Orbit rigidity for a locally nilpotent derivation, with the nonsquare condition
in the original coefficient field. -/
theorem fixed_of_square_cube (D : Derivation k R R) (hD : LocallyNilpotent D)
    (f : R →ₐ[k] K) (hf : Function.Injective f) {a d u : R}
    (ha : a ≠ 0) (hd : d ≠ 0) (hu : u ≠ 0) (hn : d ^ 2 + a ^ 2 * u ^ 3 ≠ 0)
    (hlin : D (D (d ^ 2 + a ^ 2 * u ^ 3)) = 0)
    (hns : ∀ z : K, z ^ 2 ≠ -(f u) ^ 3) : D a = 0 ∧ D d = 0 ∧ D u = 0 := by
  let φ : R →ₐ[k] K[X] :=
    (Polynomial.mapAlgHom f).comp (orbitHom D hD)
  have hφ (r : R) : φ r = (orbit D hD r).map f.toRingHom := rfl
  have hφinj : Function.Injective φ :=
    (Polynomial.map_injective f.toRingHom hf).comp (orbit_injective D hD)
  have hφ0 (r : R) : (φ r).coeff 0 = f r := by simp [hφ]
  have hφ1 (r : R) : (φ r).coeff 1 = f (D r) := by simp [hφ]
  have hdeg : (φ (d ^ 2 + a ^ 2 * u ^ 3)).natDegree ≤ 1 :=
    (Polynomial.natDegree_map_le).trans (orbit_degree_le_one D hD hlin)
  have h := Rigidity.orbit_constant
    (a := φ a) (d := φ d) (u := φ u) (n := φ (d ^ 2 + a ^ 2 * u ^ 3))
    (by intro he; apply ha; apply hφinj; simpa only [map_zero] using he)
    (by intro he; apply hd; apply hφinj; simpa only [map_zero] using he)
    (by intro he; apply hu; apply hφinj; simpa only [map_zero] using he)
    (by intro he; apply hn; apply hφinj; simpa only [map_zero] using he)
    hdeg (by simp) (by simpa only [hφ0] using hns)
  have hc (r : R) (hr : φ r = C ((φ r).coeff 0)) : D r = 0 := by
    apply hf
    have hh := congrArg (fun p : K[X] => p.coeff 1) hr
    simpa [hφ1] using hh
  exact ⟨hc a h.1, hc d h.2.1, hc u h.2.2⟩

end ComplexCancellation.LND

end

end OAI
