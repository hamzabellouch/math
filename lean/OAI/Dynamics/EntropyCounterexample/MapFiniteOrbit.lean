import OAI.Dynamics.EntropyCounterexample.Map

namespace OAI

noncomputable section
open scoped OnePoint
namespace Problem340.Construction

theorem rawMap_main_ne_infty_iff (D : SphereData) (x : RawManifold) :
    (rawMap D x).2.1 ≠ ∞ ↔ x.2.1 ≠ ∞ := by
  rcases x with ⟨t, z, v⟩
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp [rawMap]

theorem raw_iterate_main_ne_infty_iff (D : SphereData) (x : RawManifold) (n : ℕ) :
    ((rawMap D)^[n] x).2.1 ≠ ∞ ↔ x.2.1 ≠ ∞ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', rawMap_main_ne_infty_iff, ih]

theorem exists_finiteMainOrbit (D : SphereData) (x : RawManifold) (hx : x.2.1 ≠ ∞) :
    ∃ z : ℕ → ℂ,
      (∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1) ∧
      ∀ n, z (n + 1) = z n ^ 2 +
        readout D ((rawMap D)^[n] x).1 ((rawMap D)^[n] x).2.2 := by
  classical
  have hex : ∀ n, ∃ z : ℂ, (z : Sphere) = ((rawMap D)^[n] x).2.1 := by
    intro n
    exact OnePoint.ne_infty_iff_exists.mp ((raw_iterate_main_ne_infty_iff D x n).mpr hx)
  choose z hz using hex
  refine ⟨z, hz, ?_⟩
  intro n
  apply OnePoint.coe_injective
  rw [hz (n + 1), Function.iterate_succ_apply']
  change perturbedSquare (readout D ((rawMap D)^[n] x).1
    ((rawMap D)^[n] x).2.2) (((rawMap D)^[n] x).2.1) = _
  rw [← hz n]
  rfl

theorem raw_iterate_register_ne_infty (D : SphereData) (x : RawManifold)
    (n : ℕ) (i : Fin 3) : ((rawMap D)^[n + 1] x).2.2 i ≠ ∞ := by
  rw [Function.iterate_succ_apply']
  exact rawMap_register_ne_infty D _ i

theorem finiteMainOrbit_recurrence (D : SphereData) (x : RawManifold) (z : ℕ → ℂ)
    (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1) (n : ℕ) :
    z (n + 1) = z n ^ 2 +
      readout D ((rawMap D)^[n] x).1 ((rawMap D)^[n] x).2.2 := by
  apply OnePoint.coe_injective
  rw [hz (n + 1), Function.iterate_succ_apply']
  change perturbedSquare (readout D ((rawMap D)^[n] x).1
    ((rawMap D)^[n] x).2.2) (((rawMap D)^[n] x).2.1) = _
  rw [← hz n]
  rfl

theorem exists_finiteRegisterOrbit (D : SphereData) (x : RawManifold) :
    ∃ v : ℕ → Fin 3 → ℂ,
      (∀ n i, (v n i : Sphere) = ((rawMap D)^[n + 1] x).2.2 i) ∧
      ∀ n i, v (n + 1) i =
        (periodicGain D ((rawMap D)^[n + 1] x).1 : ℂ) * D.saturation (v n i : Sphere) +
          input D i ((rawMap D)^[n + 1] x).1 ((rawMap D)^[n + 1] x).2.1 := by
  classical
  have hex : ∀ n i, ∃ v : ℂ, (v : Sphere) = ((rawMap D)^[n + 1] x).2.2 i := by
    intro n i
    exact OnePoint.ne_infty_iff_exists.mp (raw_iterate_register_ne_infty D x n i)
  choose v hv using hex
  refine ⟨v, hv, ?_⟩
  intro n i
  apply OnePoint.coe_injective
  rw [hv (n + 1) i, Function.iterate_succ_apply']
  change (((periodicGain D ((rawMap D)^[n + 1] x).1 : ℂ) *
      D.saturation (((rawMap D)^[n + 1] x).2.2 i) +
      input D i ((rawMap D)^[n + 1] x).1 ((rawMap D)^[n + 1] x).2.1 : ℂ) : Sphere) = _
  rw [← hv n i]

end Problem340.Construction

end

end OAI
