import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Canonical ordered comparison lists obtained from actual colliding witnesses. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def collisionSurvivors {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) : Finset ℕ :=
  (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j)

def survivingIndex {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) :
    Fin (collisionSurvivors p q η ξ i k).card ↪o ℕ :=
  (collisionSurvivors p q η ξ i k).orderEmbOfFin rfl

lemma survivingIndex_mem {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ)
    (j : Fin (collisionSurvivors p q η ξ i k).card) :
    survivingIndex p q η ξ i k j ∈ collisionSurvivors p q η ξ i k :=
  (collisionSurvivors p q η ξ i k).orderEmbOfFin_mem rfl j

lemma prod_survivingIndex {M : Type*} [CommMonoid M] {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) (f : ℕ → M) :
    (∏ j : Fin (collisionSurvivors p q η ξ i k).card, f (survivingIndex p q η ξ i k j)) =
      ∏ r ∈ collisionSurvivors p q η ξ i k, f r := by
  calc
    _ = ∏ r ∈ Finset.univ.image (survivingIndex p q η ξ i k), f r := by
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact (survivingIndex p q η ξ i k).injective hab
    _ = _ := by rw [show Finset.univ.image (survivingIndex p q η ξ i k) =
        collisionSurvivors p q η ξ i k from
          (collisionSurvivors p q η ξ i k).image_orderEmbOfFin_univ rfl]

lemma survivingIndex_first {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hik : i ≤ k)
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i) :
    ∃ hb : 0 < (collisionSurvivors p q η ξ i k).card,
      survivingIndex p q η ξ i k ⟨0,hb⟩=i := by
  have hi : i ∈ collisionSurvivors p q η ξ i k :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hik⟩,hfirst⟩
  have hb := Finset.card_pos.mpr ⟨i,hi⟩
  refine ⟨hb,?_⟩
  rw [survivingIndex,Finset.orderEmbOfFin_zero rfl hb]
  apply le_antisymm
  · exact Finset.min'_le _ _ hi
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp
      (Finset.min'_mem _ ⟨i,hi⟩)).1).1

def survivingPair {x : ℝ} {H : ℕ} (p q : ℕ) (η ξ : RemainderDatum (L x H)) (i k : ℕ) :
    ShiftedPair (collisionSurvivors p q η ξ i k).card where
  left := fun j => wholeWitnessPrime p η (survivingIndex p q η ξ i k j)
  right := fun j => wholeWitnessPrime q ξ (survivingIndex p q η ξ i k j)
  remainder := (suffixPreimage ξ k).totient

theorem surviving_collision_identity {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ)
    (hp : p.Prime) (hL : L x H < m x) (hR : R x H < L x H)
    (hk : k < L x H) (hik : i ≤ k)
    (hv : tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ))
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hcommon : ∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) :
    (suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left =
      (survivingPair p q η ξ i k).remainder*shiftedProduct (survivingPair p q η ξ i k).right := by
  have hc := (witness_collision_cancel hη hξ hp hL hR hk hik hv hfirst hcommon).1
  have he : (Finset.Icc 0 k).filter
      (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j) =
      collisionSurvivors p q η ξ i k := by
    ext j
    simp only [collisionSurvivors,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hj,hne⟩
      refine ⟨⟨?_,hj.2⟩,hne⟩
      by_contra! hij
      exact hne (hcommon j hij)
    · rintro ⟨hj,hne⟩
      exact ⟨⟨Nat.zero_le _,hj.2⟩,hne⟩
  rw [he] at hc
  simp only [survivingPair,shiftedProduct]
  rw [prod_survivingIndex p q η ξ i k (fun r => wholeWitnessPrime p η r-1),
    prod_survivingIndex p q η ξ i k (fun r => wholeWitnessPrime q ξ r-1)]
  exact hc

theorem surviving_good_conditions {x : ℝ} {H i p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hi : i ≤ R x H)
    (hgη : GoodWitnessConditions p η) (hgξ : GoodWitnessConditions q ξ) :
    ∀ j : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      IsNormalPrime (normalityScale x i) ((survivingPair p q η ξ i (collisionLastIndex x i)).left j) ∧
      IsNormalPrime (normalityScale x i) ((survivingPair p q η ξ i (collisionLastIndex x i)).right j) ∧
      (survivingPair p q η ξ i (collisionLastIndex x i)).left j ≠
        (survivingPair p q η ξ i (collisionLastIndex x i)).right j ∧
      SquarefreeAbove ((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1)
        (collisionSmoothCutoff x i) ∧
      SquarefreeAbove ((survivingPair p q η ξ i (collisionLastIndex x i)).right j-1)
        (collisionSmoothCutoff x i) := by
  intro j
  obtain ⟨hj,hne⟩ := Finset.mem_filter.mp (survivingIndex_mem p q η ξ i (collisionLastIndex x i) j)
  have hηi := hgη i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)
  have hξi := hgξ i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)
  exact ⟨hηi.2.1 _ hj,hξi.2.1 _ hj,hne,
    squarefreeAbove_of_dvd (Finset.dvd_prod_of_mem (fun r => wholeWitnessPrime p η r-1) hj) hηi.2.2.1,
    squarefreeAbove_of_dvd (Finset.dvd_prod_of_mem (fun r => wholeWitnessPrime q ξ r-1) hj) hξi.2.2.1⟩

end TotientAsymptotic

end

end OAI
