import OAI.NumberTheory.TotientAsymptotic.PPTComparisonBridge
import Mathlib.Data.Finset.Sort

namespace OAI

/-!
Cancel matching coordinates after the high-prime lists have been aligned.
The first mismatch is retained, so the large-head condition is preserved.
The canceled integer prime product is retained for the later reciprocal
totient summation.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def pptUnequalCoordinates {k : ℕ} (p q : Fin k → ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => p i ≠ q i)

def pptEqualCoordinates {k : ℕ} (p q : Fin k → ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => p i = q i)

def pptCoordinateEmbedding {k : ℕ} (p q : Fin k → ℕ) :
    Fin (pptUnequalCoordinates p q).card ↪o Fin k :=
  (pptUnequalCoordinates p q).orderEmbOfFin rfl

def pptCanceledPrimeProduct {k : ℕ} (p q : Fin k → ℕ) : ℕ :=
  ∏ i ∈ pptEqualCoordinates p q, p i

lemma ppt_coordinate_embedding_mem {k : ℕ} (p q : Fin k → ℕ)
    (i : Fin (pptUnequalCoordinates p q).card) :
    pptCoordinateEmbedding p q i ∈ pptUnequalCoordinates p q :=
  (pptUnequalCoordinates p q).orderEmbOfFin_mem rfl i

lemma ppt_product_coordinate_embedding {k : ℕ} (p q : Fin k → ℕ)
    (f : Fin k → ℕ) :
    (∏ i : Fin (pptUnequalCoordinates p q).card,
      f (pptCoordinateEmbedding p q i)) =
      ∏ i ∈ pptUnequalCoordinates p q, f i := by
  calc
    _ = ∏ j ∈ Finset.univ.image (pptCoordinateEmbedding p q), f j := by
      rw [Finset.prod_image]
      intro i _ j _ he
      exact (pptCoordinateEmbedding p q).injective he
    _ = _ := by
      rw [show Finset.univ.image (pptCoordinateEmbedding p q) =
          pptUnequalCoordinates p q from
        (pptUnequalCoordinates p q).image_orderEmbOfFin_univ rfl]

lemma ppt_shifted_product_coordinate_embedding {k : ℕ} (p q f : Fin k → ℕ) :
    shiftedProduct (f ∘ pptCoordinateEmbedding p q) =
      ∏ i ∈ pptUnequalCoordinates p q, (f i-1) := by
  exact ppt_product_coordinate_embedding p q (fun i => f i-1)

lemma ppt_canceled_prime_product_totient {k : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (pptCanceledPrimeProduct p q).totient =
      ∏ i ∈ pptEqualCoordinates p q, (p i-1) := by
  have hprime : ∀ r ∈ (pptEqualCoordinates p q).image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hh := TotientFibers.totient_prime_prod hprime
  rw [Finset.prod_image (fun i _ j _ he => hinj he),
    Finset.prod_image (fun i _ j _ he => hinj he)] at hh
  exact hh

lemma ppt_canceled_prime_product_split {k : ℕ} (p q : Fin k → ℕ) :
    pptCanceledPrimeProduct p q *
      (∏ i, p (pptCoordinateEmbedding p q i)) = ∏ i, p i := by
  rw [ppt_product_coordinate_embedding]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => p i = q i) p

lemma ppt_canceled_prime_product_pos {k : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) : 0 < pptCanceledPrimeProduct p q :=
  Finset.prod_pos (fun i _ => (hp i).pos)

lemma ppt_canceled_totient_split {k : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (pptCanceledPrimeProduct p q).totient *
      shiftedProduct (p ∘ pptCoordinateEmbedding p q) = shiftedProduct p := by
  rw [ppt_canceled_prime_product_totient p q hp hinj]
  rw [ppt_shifted_product_coordinate_embedding]
  unfold shiftedProduct
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => p i = q i) (fun i => p i-1)

/-- The same canceled factor which enters the reciprocal mass also
supplies the divisor in the published comparison size bound. -/
lemma ppt_canceled_comparison_size {k D : ℕ} (p q : Fin k → ℕ) {z : ℝ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hsize : ((D*shiftedProduct p : ℕ) : ℝ) ≤ z) :
    ((D*shiftedProduct (p ∘ pptCoordinateEmbedding p q) : ℕ) : ℝ) ≤
      z/(pptCanceledPrimeProduct p q).totient := by
  have hc := Nat.totient_pos.mpr (ppt_canceled_prime_product_pos p q hp)
  apply (le_div_iff₀ (by exact_mod_cast hc)).mpr
  have he : (D*shiftedProduct (p ∘ pptCoordinateEmbedding p q))*
      (pptCanceledPrimeProduct p q).totient = D*shiftedProduct p := by
    calc
      _ = D*((pptCanceledPrimeProduct p q).totient *
        shiftedProduct (p ∘ pptCoordinateEmbedding p q)) := by ring
      _ = _ := by rw [ppt_canceled_totient_split p q hp hinj]
  exact (by exact_mod_cast he :
    ((D*shiftedProduct (p ∘ pptCoordinateEmbedding p q) : ℕ) : ℝ)*
      (pptCanceledPrimeProduct p q).totient = (D*shiftedProduct p : ℕ)).le.trans hsize

lemma ppt_canceled_squarefreeAbove {k : ℕ} (p q : Fin k → ℕ) {Z : ℝ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hsq : SquarefreeAbove (shiftedProduct p) Z) :
    SquarefreeAbove (shiftedProduct (p ∘ pptCoordinateEmbedding p q)) Z := by
  apply squarefreeAbove_of_dvd _ hsq
  rw [← ppt_canceled_totient_split p q hp hinj]
  exact dvd_mul_left _ _

lemma ppt_cancel_matching_coordinates {k D E : ℕ} (p q : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime)
    (heq : D*shiftedProduct p = E*shiftedProduct q) :
    D*shiftedProduct (p ∘ pptCoordinateEmbedding p q) =
      E*shiftedProduct (q ∘ pptCoordinateEmbedding p q) := by
  let c := ∏ i ∈ pptEqualCoordinates p q, (p i-1)
  have hc : 0 < c := Finset.prod_pos
    (fun i _ => Nat.sub_pos_of_lt (hp i).one_lt)
  have hcommon : (∏ i ∈ pptEqualCoordinates p q, (q i-1)) = c := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hleft : c*shiftedProduct (p ∘ pptCoordinateEmbedding p q) = shiftedProduct p := by
    rw [ppt_shifted_product_coordinate_embedding]
    unfold shiftedProduct
    exact Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => p i = q i) (fun i => p i-1)
  have hright : c*shiftedProduct (q ∘ pptCoordinateEmbedding p q) = shiftedProduct q := by
    rw [← hcommon]
    rw [ppt_shifted_product_coordinate_embedding]
    unfold shiftedProduct
    exact Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => p i = q i) (fun i => q i-1)
  apply Nat.eq_of_mul_eq_mul_left hc
  calc
    _ = D*(c*shiftedProduct (p ∘ pptCoordinateEmbedding p q)) := by ring
    _ = D*shiftedProduct p := by rw [hleft]
    _ = E*shiftedProduct q := heq
    _ = E*(c*shiftedProduct (q ∘ pptCoordinateEmbedding p q)) := by rw [hright]
    _ = _ := by ring

lemma ppt_coordinate_first_survives {k : ℕ} (hk : 0 < k) (p q : Fin k → ℕ)
    (hfirst : p ⟨0, hk⟩ ≠ q ⟨0, hk⟩) :
    ∃ hb : 0 < (pptUnequalCoordinates p q).card,
      pptCoordinateEmbedding p q ⟨0, hb⟩ = ⟨0, hk⟩ := by
  have hzero : (⟨0, hk⟩ : Fin k) ∈ pptUnequalCoordinates p q :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩
  have hb := Finset.card_pos.mpr ⟨_, hzero⟩
  refine ⟨hb, ?_⟩
  rw [pptCoordinateEmbedding, Finset.orderEmbOfFin_zero rfl hb]
  apply le_antisymm
  · exact Finset.min'_le _ _ hzero
  · exact Nat.zero_le _

lemma ppt_surviving_coordinates_unequal {k : ℕ} (p q : Fin k → ℕ)
    (i : Fin (pptUnequalCoordinates p q).card) :
    p (pptCoordinateEmbedding p q i) ≠ q (pptCoordinateEmbedding p q i) :=
  (Finset.mem_filter.mp (ppt_coordinate_embedding_mem p q i)).2

lemma ppt_surviving_coordinates_strictAnti {k : ℕ} (p q : Fin k → ℕ)
    (hp : StrictAnti p) (hq : StrictAnti q) :
    StrictAnti (p ∘ pptCoordinateEmbedding p q) ∧
      StrictAnti (q ∘ pptCoordinateEmbedding p q) := by
  exact ⟨hp.comp_strictMono (pptCoordinateEmbedding p q).strictMono,
    hq.comp_strictMono (pptCoordinateEmbedding p q).strictMono⟩

end TotientAsymptotic

end

end OAI
