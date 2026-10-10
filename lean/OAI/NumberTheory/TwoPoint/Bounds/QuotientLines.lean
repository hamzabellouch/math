import OAI.NumberTheory.TwoPoint.Bounds.LinearPivots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing

namespace OAI

/-!
# Quotient coordinates in the forest code

The quotient keeps a basis chosen from the original coordinate directions.
Failure to extend an independent family by a direction and a departure
difference forces that difference onto the corresponding quotient line.
-/

namespace TwoPointCorrelations

open Finset Submodule

variable {K ι κ V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The exact maximality consequence used for a regular label. -/
theorem quotient_line_of_nonextendable_pair (v : κ → V) (hv : LinearIndependent K v)
    (x y : V) (hx : (span K (Set.range v)).mkQ x ≠ 0)
    (hmax : ¬LinearIndependent K (Sum.elim v ![y, x])) :
    ∃ c : K, (span K (Set.range v)).mkQ y = c • (span K (Set.range v)).mkQ x := by
  classical
  let D := span K (Set.range v)
  let vlift : κ → D := fun i => ⟨v i, subset_span ⟨i, rfl⟩⟩
  have hvlift : LinearIndependent K vlift := by
    apply LinearIndependent.of_comp D.subtype
    exact hv
  have hq : ¬LinearIndependent K (D.mkQ ∘ ![y, x]) := by
    intro h
    apply hmax
    exact hvlift.sumElim_of_quotient ![y, x] h
  have heq : ∃ c : K, c • D.mkQ x = D.mkQ y := by
    by_contra! hc
    apply hq
    apply linearIndependent_fin2.mpr
    exact ⟨hx, hc⟩
  obtain ⟨c, hc⟩ := heq
  exact ⟨c, hc.symm⟩

/-- All designated departures for a regular label lie on one quotient line. -/
theorem quotient_departures_on_line (v : κ → V) (hv : LinearIndependent K v)
    (direction : V) (departure : ι → V) (base : ι)
    (hx : (span K (Set.range v)).mkQ direction ≠ 0)
    (hmax : ∀ i, ¬LinearIndependent K
      (Sum.elim v ![departure i - departure base, direction])) :
    ∀ i, ∃ c : K, (span K (Set.range v)).mkQ (departure i) =
      (span K (Set.range v)).mkQ (departure base) +
        c • (span K (Set.range v)).mkQ direction := by
  intro i
  obtain ⟨c, hc⟩ := quotient_line_of_nonextendable_pair v hv direction
    (departure i - departure base) hx (hmax i)
  refine ⟨c, ?_⟩
  rw [map_sub] at hc
  exact sub_eq_iff_eq_add'.mp hc

/-- A coordinate basis survives the quotient after exactly `dim D` labels
are omitted. This fixes the count, even when the subspace is not spanned by
coordinate vectors. -/
theorem exists_coordinate_quotient_basis [Fintype ι] [DecidableEq ι]
    (D : Submodule K (ι → K)) :
    ∃ S : Finset ι, Sᶜ.card = Module.finrank K D ∧
      LinearIndependent K (fun i : S => D.mkQ (Pi.basisFun K ι i)) ∧
      span K (Set.range (fun i : S => D.mkQ (Pi.basisFun K ι i))) = ⊤ := by
  classical
  let v : ι → ((ι → K) ⧸ D) := fun i => D.mkQ (Pi.basisFun K ι i)
  have hv : span K (Set.range v) = ⊤ := by
    change span K (Set.range (D.mkQ ∘ Pi.basisFun K ι)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun K ι).span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr D.mkQ_surjective]
  obtain ⟨η, a, ha, hspan, hind⟩ := exists_linearIndependent' K v
  let : Finite η := Finite.of_injective a ha
  let : Fintype η := Fintype.ofFinite η
  let b : Module.Basis η K ((ι → K) ⧸ D) := Module.Basis.mk hind (by rw [hspan, hv])
  let S : Finset ι := univ.image a
  let e : η ≃ S := Equiv.ofBijective (fun j => ⟨a j, mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩)
    ⟨fun j k h => ha (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩
  let bs := b.reindex e
  have hbs (i : S) : bs i = v i := by
    rw [show bs = b.reindex e from rfl, Module.Basis.reindex_apply]
    simp only [b, Module.Basis.mk_apply, Function.comp_apply]
    have hi : a (e.symm i) = i := congrArg Subtype.val (e.apply_symm_apply i)
    rw [hi]
  have heq : (bs : S → ((ι → K) ⧸ D)) = (fun i : S => D.mkQ (Pi.basisFun K ι i)) :=
    funext hbs
  have hcard : S.card = Module.finrank K ((ι → K) ⧸ D) := by
    simpa only [Fintype.card_coe] using (Module.finrank_eq_card_basis bs).symm
  have hdim := D.finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hdim
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [card_compl, hcard]
    omega
  · rw [← heq]
    exact bs.linearIndependent
  · rw [← heq]
    exact bs.span_eq

end TwoPointCorrelations

end OAI
