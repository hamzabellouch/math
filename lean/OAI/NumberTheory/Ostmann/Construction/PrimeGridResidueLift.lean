import OAI.NumberTheory.Ostmann.Construction.PrimeGridSupport
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCRT

namespace OAI

/-! # The original grid labels give the actual CRT unit lifts -/

namespace Ostmann
open scoped Classical BigOperators

theorem primeGridLabel_lift {N q : ℕ} [NeZero q] (s h : ℝ)
    (c₀ : Fin N × (ZMod q)ˣ) (p : ℕ)
    (hp : p ∈ primeCellSupport q (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h)) :
    (p : ZMod q) =
      ((primeCellLabel q gridResidue (gridLower s h) (gridUpper s h) c₀ p).2 : ZMod q) := by
  have hc := primeCellLabel_mem q gridResidue (gridLower s h) (gridUpper s h) c₀ p hp
  have hr := (mem_primeLogCellSet_iff.mp hc).2.1
  have he := (ZMod.natCast_eq_natCast_iff _ _ q).mpr hr
  simpa only [gridResidue, ZMod.natCast_zmod_val] using he

theorem bulkResidueEquiv_spectator_lift {I J : Type*} [Fintype I]
    (r : ℕ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (value : J → ℕ) (z : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value j : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (i : I) (j : J) :
    (value j : ZMod (p i)) = ((bulkResidueEquiv r p hc z).2 i j : ZMod (p i)) := by
  have he := congrArg (ZMod.castHom
    (Finset.dvd_prod_of_mem (bulkResidueModuli r p) (Finset.mem_univ (Sum.inr i : Unit ⊕ I)))
    (ZMod (p i))) (hz j)
  rw [map_natCast] at he
  change (value j : ZMod (p i)) =
    ((show (ZMod (p i))ˣ from crtUnitEquiv (bulkResidueModuli r p) hc (z j) (.inr i)) : ZMod (p i))
  rw [crtUnitEquiv_apply]
  exact he

theorem bulkResidueEquiv_frequency_lift {I J : Type*} [Fintype I]
    (r : ℕ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (value : J → ℕ) (z : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value j : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (j : J) :
    (value j : ZMod r) = ((bulkResidueEquiv r p hc z).1 j : ZMod r) := by
  have he := congrArg (ZMod.castHom
    (Finset.dvd_prod_of_mem (bulkResidueModuli r p) (Finset.mem_univ (Sum.inl () : Unit ⊕ I)))
    (ZMod r)) (hz j)
  rw [map_natCast] at he
  change (value j : ZMod r) =
    ((show (ZMod r)ˣ from crtUnitEquiv (bulkResidueModuli r p) hc (z j) (.inl ())) : ZMod r)
  rw [crtUnitEquiv_apply]
  exact he

end Ostmann

end OAI
