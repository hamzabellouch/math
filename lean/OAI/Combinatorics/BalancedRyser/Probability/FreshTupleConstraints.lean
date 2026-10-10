import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability
import OAI.Combinatorics.BalancedRyser.Probability.GlobalTupleLaw

namespace OAI

namespace Balanced.FreshTupleConstraints

open TupleAlignment FreshWitnessProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposed_tuplePoint_uniform
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D) :
    (exposedLaw D a).map (fun M => tuplePoint M T) =
      PMF.uniformOfFintype (Fin 4 → Point F) := by
  let hd := adjacent_ne_of_injective T hT
  let r : MergedPairs F → Fin 4 → Bool → F := fun M i => M (T.generator i)
  have hr := exposedLaw_map_fresh D a ⟨T.generator, hT⟩ hfresh
  simp only [Function.Embedding.coeFn_mk] at hr
  have hf : (fun M => tuplePoint M T) =
      tuplePositionEquiv T.generator hd T.side ∘ r := by
    funext M i
    rfl
  rw [hf, ← PMF.map_comp]
  change ((exposedLaw D a).map (fun M i => M (T.generator i))).map _ = _
  rw [hr]
  exact tuplePosition_uniform T.generator hd T.side

theorem tuple_box_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (B : Fin 4 → Finset (Point F)) :
    ((exposedLaw D a).toOuterMeasure
      {M | ∀ i, tuplePoint M T i ∈ B i}).toReal =
      (∏ i, ((B i).card : ℝ)) / (Fintype.card F : ℝ)^8 := by
  let E : Set (Fin 4 → Point F) := {p | ∀ i, p i ∈ B i}
  have h := congrArg (fun p => (p.toOuterMeasure E).toReal)
    (exposed_tuplePoint_uniform D a T hT hfresh)
  rw [PMF.toOuterMeasure_map_apply] at h
  have hcard : Fintype.card E = ∏ i, (B i).card := by
    change Fintype.card {p : Fin 4 → Point F // ∀ i, p i ∈ B i} = _
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun i p => p ∈ B i)), Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i hi
    exact Fintype.card_coe (B i)
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, hcard] at h
  simpa only [E, Set.preimage_ofPred_eq, Fintype.card_fun, Point,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_prod, Nat.cast_pow,
    Nat.cast_mul, ← pow_two, ← pow_mul] using h

theorem pinned_positions_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (J : Finset (Fin 4)) (x : Fin 4 → Point F)
    (hx : ∀ i ∈ J, OnLine (x i) S) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ i, OnLine (tuplePoint M T i) S) ∧
      ∀ i ∈ J, tuplePoint M T i = x i}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (4 + J.card) := by
  let B : Fin 4 → Finset (Point F) := fun i =>
    if i ∈ J then {x i} else linePoints S
  have hevent : {M : MergedPairs F |
      (∀ i, OnLine (tuplePoint M T i) S) ∧
      ∀ i ∈ J, tuplePoint M T i = x i} =
      {M | ∀ i, tuplePoint M T i ∈ B i} := by
    ext M
    constructor
    · rintro ⟨hon, hpin⟩ i
      by_cases hi : i ∈ J
      · simp [B, hi, hpin i hi]
      · simpa [B, hi, linePoints] using hon i
    · intro h
      constructor
      · intro i
        by_cases hi : i ∈ J
        · have hp : tuplePoint M T i = x i := by simpa [B, hi] using h i
          simpa [hp] using hx i hi
        · simpa [B, hi, linePoints] using h i
      · intro i hi
        simpa [B, hi] using h i
  rw [hevent, tuple_box_probability D a T hT hfresh B]
  have hprod : (∏ i, ((B i).card : ℝ)) =
      (Fintype.card F : ℝ)^(4 - J.card) := by
    simp only [B, apply_ite Finset.card, Finset.card_singleton,
      linePoints_card, Nat.cast_ite, Nat.cast_one]
    rw [Finset.prod_ite]
    have hc : (Finset.univ.filter (fun i : Fin 4 => i ∉ J)) = Jᶜ := by
      ext i
      simp
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const, hc,
      Finset.card_compl, Fintype.card_fin]
  rw [hprod]
  have hj : J.card ≤ 4 := by simpa using J.card_le_univ
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexp : (4 - J.card) + (4 + J.card) = 8 := by omega
  calc
    _ = (Fintype.card F : ℝ)^(4 - J.card) /
        ((Fintype.card F : ℝ)^(4 - J.card) *
          (Fintype.card F : ℝ)^(4 + J.card)) := by rw [← pow_add, hexp]
    _ = ((Fintype.card F : ℝ)^(4 + J.card))⁻¹ := by
      field_simp
    _ = _ := (inv_pow _ _).symm

theorem one_pinned_position_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (i : Fin 4) (x : Point F) (hx : OnLine x S) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ j, OnLine (tuplePoint M T j) S) ∧ tuplePoint M T i = x}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  have h := pinned_positions_probability D a T hT hfresh S {i} (fun _ => x)
    (fun _ _ => hx)
  simpa using h

theorem two_pinned_positions_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (i j : Fin 4) (hij : i ≠ j)
    (x y : Point F) (hx : OnLine x S) (hy : OnLine y S) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ k, OnLine (tuplePoint M T k) S) ∧
      tuplePoint M T i = x ∧ tuplePoint M T j = y}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 6 := by
  let p : Fin 4 → Point F := fun k => if k = i then x else y
  have hp : ∀ k ∈ ({i, j} : Finset (Fin 4)), OnLine (p k) S := by
    intro k hk
    by_cases hki : k = i
    · simpa [p, hki] using hx
    · simpa [p, hki] using hy
  have h := pinned_positions_probability D a T hT hfresh S {i, j} p hp
  simpa [p, hij, hij.symm] using h

end
end Balanced.FreshTupleConstraints

end OAI
