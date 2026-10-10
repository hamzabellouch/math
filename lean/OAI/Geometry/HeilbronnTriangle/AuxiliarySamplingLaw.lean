import OAI.Geometry.HeilbronnTriangle.AuxiliaryAffineWeights
import OAI.Geometry.HeilbronnTriangle.AuxiliarySet
import OAI.Geometry.HeilbronnTriangle.LiftingProbability

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling

open scoped BigOperators

structure Law (q H : ℕ) [Fact q.Prime] where
  Outcome : Type
  outcomeFintype : Fintype Outcome
  weight : Outcome → ℝ
  sets : Outcome → Finset (Fin 3 → ZMod q)
  size : ℕ
  size_pos : 0 < size
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : @Finset.sum Outcome ℝ _ (@Finset.univ Outcome outcomeFintype) weight = 1
  sets_card : ∀ ω, (sets ω).card = size
  size_lower : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * size
  zero_not_mem : ∀ ω, (0 : Fin 3 → ZMod q) ∉ sets ω
  isCap : ∀ ω, AuxiliaryCap.IsCap (sets ω : Set (Fin 3 → ZMod q))
  short_relation : ∀ ω (p : Fin 3 → (Fin 3 → ZMod q)),
    (∀ i, p i ∈ sets ω) → Function.Injective p →
    ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
      (∑ i, (x i : ZMod q) • p i) ≠ 0
  weight_le_eight : ∀ p : Fin 3 → (Fin 3 → ZMod q),
    AffineIndependent (ZMod q) p →
    @LiftingProbability.auxiliaryWeight Outcome (Fin 3 → ZMod q) outcomeFintype
      q size weight sets p ≤ 8
  weight_le_four : ∀ (p : Fin 3 → (Fin 3 → ZMod q)) (i j : Fin 3), p i ≠ p j →
    @LiftingProbability.auxiliaryWeight Outcome (Fin 3 → ZMod q) outcomeFintype
      q size weight sets p ≤ 4 * ((q : ℝ) ^ 3 / size)
  weight_le_two : ∀ p : Fin 3 → (Fin 3 → ZMod q),
    @LiftingProbability.auxiliaryWeight Outcome (Fin 3 → ZMod q) outcomeFintype
      q size weight sets p ≤ 2 * ((q : ℝ) ^ 3 / size) ^ 2

attribute [instance] Law.outcomeFintype

private theorem affine_apply_inputShift {q : ℕ} [Fact q.Prime]
    (e : (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))
    (x : Fin 3 → ZMod q) :
    e x = (AffineTripleOrbit.inputShiftEquiv e).1
      ((AffineTripleOrbit.inputShiftEquiv e).2 + x) := by
  have h := congrArg
    (fun f : (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q) => f x)
    (AffineTripleOrbit.inputShiftEquiv.symm_apply_apply e)
  exact h.symm.trans (AffineTripleOrbit.inputShiftEquiv_symm_apply
    (AffineTripleOrbit.inputShiftEquiv e).1 (AffineTripleOrbit.inputShiftEquiv e).2 x)

theorem nonempty_law_of_cap {q H w : ℕ} [Fact q.Prime]
    (hH : 1 ≤ H) (hHq : H < q)
    (S : Finset (Fin 3 → ZMod q)) (hS : S.Nonempty)
    (hcap : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (hsize : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * S.card)
    (A : Finset (Fin 3 → ZMod q)) (hA : q ^ 3 ≤ 2 * A.card)
    (hallowed : ∀ a ∈ A, ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w)) :
    Nonempty (Law q H) := by
  classical
  let Aff := (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)
  let : Finite Aff := Finite.of_injective
    (fun e : Aff => (e : (Fin 3 → ZMod q) → (Fin 3 → ZMod q)))
    DFunLike.coe_injective
  let : Fintype Aff := Fintype.ofFinite Aff
  let T : Finset Aff := AuxiliaryWeights.affineMapsWithInputShift A
  have hA' : Fintype.card (Fin 3 → ZMod q) ≤ 2 * A.card := by
    simpa using hA
  have hT : T.Nonempty := AuxiliaryWeights.affineMapsWithInputShift_nonempty A hA'
  have hTsize : Fintype.card Aff ≤ 2 * T.card :=
    AuxiliaryWeights.affineMapsWithInputShift_halfDensity A hA'
  let μ : T → ℝ := fun _ => (T.card : ℝ)⁻¹
  let V : T → Finset (Fin 3 → ZMod q) := fun e => S.image e.1
  have hV (e : T) : V e = AuxiliarySet.transformed S
      (AffineTripleOrbit.inputShiftEquiv e.1).2
      (AffineTripleOrbit.inputShiftEquiv e.1).1 := by
    ext y
    simp only [V, Finset.mem_image, AuxiliarySet.mem_transformed]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (affine_apply_inputShift e.1 x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, affine_apply_inputShift e.1 x⟩
  have hall (e : T) : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * (AffineTripleOrbit.inputShiftEquiv e.1).2 0 ∉
        Auxiliary.integerWindow q (3 * H * w) := by
    apply hallowed
    exact (Finset.mem_filter.mp e.2).2
  have hprops (e : T) := AuxiliarySet.transformed_properties hH hHq hcap hbox
    (AffineTripleOrbit.inputShiftEquiv e.1).2 (hall e)
    (AffineTripleOrbit.inputShiftEquiv e.1).1
  have hW (p : Fin 3 → (Fin 3 → ZMod q)) :
      LiftingProbability.auxiliaryWeight q S.card μ V p =
        AuxiliaryWeights.affineInclusionWeight S T p := by
    rw [AuxiliaryWeights.affineInclusionWeight_eq_uniform_sum]
    simp only [LiftingProbability.auxiliaryWeight, LiftingProbability.inclusionMass,
      ZMod.card]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    simp only [LiftingProbability.TripleIn, μ, V, Finset.mem_image]
    split_ifs <;> simp_all
  refine ⟨{
    Outcome := T
    outcomeFintype := inferInstance
    weight := μ
    sets := V
    size := S.card
    size_pos := hS.card_pos
    weight_nonneg := ?_
    weight_sum := ?_
    sets_card := ?_
    size_lower := hsize
    zero_not_mem := ?_
    isCap := ?_
    short_relation := ?_
    weight_le_eight := ?_
    weight_le_four := ?_
    weight_le_two := ?_ }⟩
  · intro e
    dsimp [μ]
    positivity
  · simp only [μ, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hT.card_pos.ne')
  · intro e
    rw [hV]
    exact (hprops e).1
  · intro e
    rw [hV]
    exact (hprops e).2.1
  · intro e
    rw [hV]
    exact (hprops e).2.2.1
  · intro e p hp hinj x hx hne
    exact (hprops e).2.2.2 p (fun i => hV e ▸ hp i) hinj x hx hne
  · intro p hp
    rw [hW]
    exact AuxiliaryWeights.affineInclusionWeight_le_eight S hS T hT hTsize p hp
  · intro p i j hp
    rw [hW]
    simpa only [ZMod.card] using
      AuxiliaryWeights.affineInclusionWeight_le_four_of_ne S hS T hT hTsize p i j hp
  · intro p
    rw [hW]
    simpa only [ZMod.card] using
      AuxiliaryWeights.affineInclusionWeight_le_two S hS T hT hTsize p

theorem nonempty_law {q H : ℕ} [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q) : Nonempty (Law q H) := by
  classical
  let w := q / (1000 * H ^ 2)
  have hd : 0 < 1000 * H ^ 2 := by positivity
  have hdq : 1000 * H ^ 2 ≤ q := by omega
  have hwq : w ≤ q := Nat.div_le_self _ _
  have hq2 : q ≠ 2 := by
    have hHsq : 1 ≤ H ^ 2 := by nlinarith
    omega
  obtain ⟨S, hbox, hsize, hcap⟩ := AuxiliaryCap.exists_cap_in_residueBox hq2 hwq
  have hfloor : q ≤ 2000 * H ^ 2 * w := by
    calc
      q ≤ 2 * (1000 * H ^ 2) * w := AuxiliarySet.le_twice_mul_div hd hdq
      _ = 2000 * H ^ 2 * w := by ring
  have hc : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * S.card := by
    have hcube : q ^ 3 ≤ (2000 * H ^ 2 * w) ^ 3 := by gcongr
    have hm : q * q ^ 2 ≤ q * (2000 ^ 3 * H ^ 6 * S.card) := by
      calc
        q * q ^ 2 = q ^ 3 := by ring
        _ ≤ (2000 * H ^ 2 * w) ^ 3 := hcube
        _ = (2000 ^ 3 * H ^ 6) * w ^ 3 := by ring
        _ ≤ (2000 ^ 3 * H ^ 6) * (q * S.card) := Nat.mul_le_mul_left _ hsize
        _ = q * (2000 ^ 3 * H ^ 6 * S.card) := by ring
    exact Nat.le_of_mul_le_mul_left hm (Fact.out : q.Prime).pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : S.card = 0 := by omega
    have hp : 0 < q ^ 2 := pow_pos (Fact.out : q.Prime).pos 2
    simp only [hz, mul_zero] at hc
    omega
  let A := Auxiliary.vectorShifts (Auxiliary.allowedShifts
    (Auxiliary.positiveMultipliers q H) (Auxiliary.integerWindow q (3 * H * w)))
  have hw : 1000 * H ^ 2 * w ≤ q := Nat.mul_div_le _ _
  have hA : q ^ 3 ≤ 2 * A.card :=
    (Auxiliary.auxiliary_allowed_vector_card_gt_half q H w hH hq hw).le
  have hmult : 3 * H < q := Auxiliary.auxiliary_multiplier_range q H hH hq
  apply nonempty_law_of_cap hH (by omega) S hS hcap (fun v hv => hbox v hv 0) hc A hA
  intro a ha n hn hnH
  have ha' := (Auxiliary.mem_vectorShifts_iff _ a).mp ha
  have ha'' := (Auxiliary.mem_allowedShifts_iff _ _
    (Auxiliary.positiveMultipliers_ne_zero q H hmult) (a 0)).mp ha'
  apply ha''
  exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn, hnH⟩, rfl⟩

end Problem355.AuxiliarySampling

end

end OAI
