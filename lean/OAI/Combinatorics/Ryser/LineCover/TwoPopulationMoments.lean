import OAI.Combinatorics.Ryser.LineCover.TwoPopulationSampling

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

theorem prob_product_average_right
    {A B : Type*} [Fintype A] [Fintype B]
    (mu : FiniteLaw A) (nu : FiniteLaw B) (P : A × B → Prop) :
    (mu.prod nu).prob P = nu.expectation (fun b => mu.prob (fun a => P (a, b))) := by
  rw [FiniteLaw.prob_prod_average]
  unfold FiniteLaw.expectation FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P (a, b) <;> simp [hp, mul_comm]

theorem prob_coordinate_product
    {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty (I ↪ A)] [Nonempty (J ↪ B)]
    (i : I) (j : J) (P : A × B → Prop) :
    ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (J ↪ B))).prob
        (fun z => P (z.1 i, z.2 j)) =
      ((FiniteLaw.uniform A).prod (FiniteLaw.uniform B)).prob P := by
  rw [FiniteLaw.prob_prod_average, FiniteLaw.prob_prod_average]
  calc
    _ = (FiniteLaw.uniform (I ↪ A)).expectation
        (fun a => (FiniteLaw.uniform B).prob (fun b => P (a i, b))) := by
      congr 1
      funext a
      exact prob_coordinate j (fun b => P (a i, b))
    _ = _ := expectation_coordinate i
      (fun a => (FiniteLaw.uniform B).prob (fun b => P (a, b)))

theorem prob_coordinate_pair_mem
    {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty (I ↪ A)] [Nonempty (J ↪ B)]
    (S : Finset (A × B)) (i : I) (j : J) :
    ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (J ↪ B))).prob
        (fun z => (z.1 i, z.2 j) ∈ S) =
      (S.card : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) := by
  rw [prob_coordinate_product, ← FiniteLaw.uniform_prod, FiniteLaw.uniform_prob]
  have hfilter : @Finset.filter _ (fun z => z ∈ S)
      (fun z => Classical.propDecidable (z ∈ S)) Finset.univ = S := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, Fintype.card_prod, Nat.cast_mul]

def relationCount {A B : Type*} [Fintype A] [Fintype B] {t : ℕ}
    (S : Finset (A × B)) (z : (Fin t ↪ A) × (Fin t ↪ B)) : ℕ :=
  (Finset.univ.filter fun ij : Fin t × Fin t => (z.1 ij.1, z.2 ij.2) ∈ S).card

theorem expectation_relationCount
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    {t : ℕ} [Nonempty (Fin t ↪ A)] [Nonempty (Fin t ↪ B)]
    (S : Finset (A × B)) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).expectation
        (fun z => (relationCount S z : ℝ)) =
      (t : ℝ) ^ 2 * S.card / ((Fintype.card A : ℝ) * Fintype.card B) := by
  let mu := (FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))
  have hcount (z : (Fin t ↪ A) × (Fin t ↪ B)) :
      (relationCount S z : ℝ) =
        ∑ ij : Fin t × Fin t, if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0 :=
    Finset.natCast_card_filter _ _
  calc
    _ = mu.expectation (fun z =>
        ∑ ij : Fin t × Fin t, if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0) := by
      congr 1
      funext z
      exact hcount z
    _ = ∑ ij : Fin t × Fin t,
        mu.expectation (fun z => if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0) :=
      mu.expectation_sum _
    _ = ∑ ij : Fin t × Fin t,
        mu.prob (fun z => (z.1 ij.1, z.2 ij.2) ∈ S) := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [FiniteLaw.prob_eq_expectation]
      congr 1
      funext z
      by_cases hz : (z.1 ij.1, z.2 ij.2) ∈ S <;> simp [hz]
    _ = ∑ _ij : Fin t × Fin t,
        (S.card : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact prob_coordinate_pair_mem S ij.1 ij.2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

theorem prob_hits_finset_le
    {A : Type*} [Fintype A] [Nonempty A] {t : ℕ} [Nonempty (Fin t ↪ A)]
    (S : Finset A) :
    (FiniteLaw.uniform (Fin t ↪ A)).prob (fun z => ∃ i, z i ∈ S) ≤
      (t : ℝ) * S.card / Fintype.card A := by
  have hfilter : @Finset.filter _ (fun a => a ∈ S)
      (fun a => Classical.propDecidable (a ∈ S)) Finset.univ = S := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    _ ≤ ∑ i : Fin t, (FiniteLaw.uniform (Fin t ↪ A)).prob (fun z => z i ∈ S) :=
      (FiniteLaw.uniform (Fin t ↪ A)).prob_exists_le _
    _ = ∑ _i : Fin t, (S.card : ℝ) / Fintype.card A := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prob_coordinate i, FiniteLaw.uniform_prob, hfilter]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
