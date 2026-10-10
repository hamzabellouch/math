import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorDiagram
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenMovingSamples
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFieldUnitAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkPageBound

namespace OAI

/-! # The actual spectator Haar factor as a fixed function of the bulk residues -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {σ : Type*} {q : ℕ} [Fact q.Prime]
  (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
  (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))

noncomputable def frozenBulkSpectatorPair (g : ZMod q → ℂ)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℂ :=
  movingFieldGiantAmplitude g (D false)
    (buildMovingGiantTree n (t false) (movingSlotValues base n (small false))
      ((samples false).values base)) a.1 a.2
    ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)) *
  conj (movingFieldGiantAmplitude g (D true)
    (buildMovingGiantTree n (t true) (movingSlotValues base n (small true))
      ((samples true).values base)) a.1 a.2
    ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct (z ∘ e.symm))))

noncomputable def frozenBulkSpectatorHaar (g : ZMod q → ℂ)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℂ :=
  ((Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)) *
    ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ a, frozenBulkSpectatorPair base n m t small samples D e g a z)

theorem frozenBulkSpectatorPair_actual (value : σ → ℕ)
    (hv : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hs : ∀ b, (samples b).values value = (samples b).values base)
    (slot : TreeLeafIndex n × Fin m → σ) (g : ZMod q → ℂ)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    movingSpectatorPairFactor value q g D
      (fun b => buildMovingSlotData n (t b) (small b)
        (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot)
        (samples b)) a.1 a.2 =
      frozenBulkSpectatorPair base n m t small samples D e g a z := by
  unfold movingSpectatorPairFactor
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [buildMovingSlotData_modular_spectator value g (D false) n (t false)
      (small false) _ (samples false) a.1 a.2 _
      (bulkSlotLeaves_naturalLift value n m slot z hz),
    buildMovingSlotData_modular_spectator value g (D true) n (t true)
      (small true) _ (samples true) a.1 a.2 _
      (bulkSlotLeaves_naturalLift value n m (slot ∘ e.symm) (z ∘ e.symm)
        (fun j => hz (e.symm j))), hv, hv, hs, hs]
  rfl

theorem frozenBulkSpectatorHaar_actual (value : σ → ℕ)
    (hv : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hs : ∀ b, (samples b).values value = (samples b).values base)
    (slot : TreeLeafIndex n × Fin m → σ) (g : ZMod q → ℂ) (hg : g 0 = 0)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    movingSpectatorHaarAverage value q g D
      (fun b => buildMovingSlotData n (t b) (small b)
        (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot)
        (samples b)) = frozenBulkSpectatorHaar base n m t small samples D e g z := by
  rw [movingSpectatorHaarAverage_eq_units value g hg]
  simp_rw [frozenBulkSpectatorPair_actual base n m t small samples D e value hv hs slot g _ z hz]
  rfl

end

private theorem norm_finite_average_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (δ : ℝ) (hf : ∀ a, ‖f a‖ ≤ δ) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ δ := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, δ :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = δ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem frozenBulkSpectatorPair_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ (n + 2))
    (small : Bool → TreeLeafTuple (List σ) (n + 2))
    (samples : Bool → MovingSampleSlots σ (n + 2))
    (hfreq : ∀ b, movingGiantFrequencyUnits q (n + 2) (t b))
    (hsmall : ∀ b, ((treeLeafProduct (n + 2) (movingSlotValues base (n + 2) (small b)) : ℕ) :
      ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) ≤ δ ^ 2)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ z, frozenBulkSpectatorPair base (n + 2) m t small samples D e
        (normalizedResidueTransform S) a z‖ ≤ δ := by
  have hex (b : Bool) := (buildMovingGiantTree (n + 2) (t b)
    (movingSlotValues base (n + 2) (small b)) ((samples b).values base)).exists_field_diagram
      (buildMovingGiantTree_units (t b) _ _ (hfreq b) (hsmall b) (hsamples b))
  choose U R _ _ hR using hex
  let d (b : Bool) : SpectatorDiagram q (n + 2) :=
    ⟨D b, U b, R b, a.1, a.2, transferConjugations (n + 2) false⟩
  have he (z : TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) :
      frozenBulkSpectatorPair base (n + 2) m t small samples D e
        (normalizedResidueTransform S) a z =
      (d false).bulkValue (normalizedResidueTransform S) z *
        conj ((d true).bulkValue (normalizedResidueTransform S) (z ∘ e.symm)) := by
    unfold frozenBulkSpectatorPair
    rw [show movingFieldGiantAmplitude (normalizedResidueTransform S) (D false)
        (buildMovingGiantTree (n + 2) (t false) (movingSlotValues base (n + 2) (small false))
          ((samples false).values base)) a.1 a.2 _ = _ from
        hR false (normalizedResidueTransform S) (D false) a.1 a.2 _ false,
      show movingFieldGiantAmplitude (normalizedResidueTransform S) (D true)
        (buildMovingGiantTree (n + 2) (t true) (movingSlotValues base (n + 2) (small true))
          ((samples true).values base)) a.1 a.2 _ = _ from
        hR true (normalizedResidueTransform S) (D true) a.1 a.2 _ false]
    rfl
  simp_rw [he]
  exact normalized_transfer_bulk_mean hq n m hm e hgood S hlo hhi hS hSq
    β ε hε hε1 hprincipal hβ hbias (d false) (d true) rfl δ hδ hnum

theorem frozenBulkSpectatorHaar_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ (n + 2))
    (small : Bool → TreeLeafTuple (List σ) (n + 2))
    (samples : Bool → MovingSampleSlots σ (n + 2))
    (hfreq : ∀ b, movingGiantFrequencyUnits q (n + 2) (t b))
    (hsmall : ∀ b, ((treeLeafProduct (n + 2) (movingSlotValues base (n + 2) (small b)) : ℕ) :
      ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) ≤ δ ^ 2)
    : ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ z, frozenBulkSpectatorHaar base (n + 2) m t small samples D e
        (normalizedResidueTransform S) z‖ ≤ δ := by
  let F := frozenBulkSpectatorPair base (n + 2) m t small samples D e
    (normalizedResidueTransform S)
  have hpair (a : (ZMod q)ˣ × (ZMod q)ˣ) :
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        ∑ z, F a z‖ ≤ δ :=
    frozenBulkSpectatorPair_mean_le hq base n m hm t small samples hfreq hsmall
      hsamples D e hgood S hlo hhi hS hSq β ε hε hε1 hprincipal hβ hbias δ hδ hnum a
  have hmean := norm_finite_average_le _ δ hpair
  have hswap :
      (Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        ∑ z, frozenBulkSpectatorHaar base (n + 2) m t small samples D e
          (normalizedResidueTransform S) z =
      ((Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)) *
        ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
          ∑ a, (Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
            ∑ z, F a z) := by
    simp only [frozenBulkSpectatorHaar, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [F]
    ring
  have hratio : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by positivity : (0 : ℝ) < q)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  rw [hswap, norm_mul]
  exact (mul_le_mul_of_nonneg_left hmean (norm_nonneg _)).trans
    (by simpa using mul_le_mul_of_nonneg_right hratio hδ)

end Ostmann

end OAI
