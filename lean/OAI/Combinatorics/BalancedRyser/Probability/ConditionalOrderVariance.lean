import OAI.Combinatorics.BalancedRyser.Probability.PermutationSubsetLaw
import OAI.Combinatorics.BalancedRyser.Probability.UncoveredSubsetVariance

namespace OAI

open scoped BigOperators

namespace Balanced.ConditionalOrderVariance

open WithoutReplacement PermutationSubsetLaw UncoveredSampling

theorem variance_two_images_conditioned_target
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (I : Finset α) (J : Finset β) (i x : α) (hi : i ∉ I)
    (g : Finset α → Finset β → ℝ) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm β)))
      (fun p => g (I.map p.1.toEmbedding) (J.map p.2.toEmbedding)) =
    finiteVariance ((Finset.univ.erase x).powersetCard I.card ×ˢ
      (Finset.univ : Finset β).powersetCard J.card) (fun p => g p.1 p.2) := by
  unfold finiteVariance
  simp_rw [Finset.expect_product]
  rw [expect_two_images_conditioned_target I J i x hi g]
  exact expect_two_images_conditioned_target I J i x hi
    (fun S T => (g S T - (𝔼 A ∈ (Finset.univ.erase x).powersetCard I.card,
      𝔼 B ∈ (Finset.univ : Finset β).powersetCard J.card, g A B))^2)

theorem conditioned_order_variance_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (I : Finset α) (J : Finset β) (i x : α) (hi : i ∉ I)
    (g : Finset α → Finset β → ℝ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfirst : ∀ S : Finset α, S ⊆ Finset.univ.erase x → S.card = I.card →
      ∀ T : Finset β, T ⊆ Finset.univ → T.card = J.card →
      ∀ a ∈ S, ∀ b ∈ Finset.univ.erase x, b ∉ S →
        |g S T - g (insert b (S.erase a)) T| ≤ c)
    (hsecond : ∀ S : Finset α, S ⊆ Finset.univ.erase x → S.card = I.card →
      ∀ T : Finset β, T ⊆ Finset.univ → T.card = J.card →
      ∀ a ∈ T, ∀ b ∈ Finset.univ, b ∉ T →
        |g S T - g S (insert b (T.erase a))| ≤ d) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm β)))
      (fun p => g (I.map p.1.toEmbedding) (J.map p.2.toEmbedding)) ≤
        (I.card : ℝ) * c^2 + (J.card : ℝ) * d^2 := by
  rw [variance_two_images_conditioned_target I J i x hi]
  have hI : I ⊆ Finset.univ.erase i := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ _⟩
  have hm : I.card ≤ (Finset.univ.erase x).card := by
    simpa using Finset.card_le_card hI
  exact finiteVariance_powersetCard_product_le _ _ _ _ g hc hd hm
    (Finset.card_le_card (Finset.subset_univ J)) hfirst hsecond

section Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def populationLines (U : Finset (Line F)) (S : Finset U) : Finset (Line F) :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

omit [Field F] [Fintype F] in
@[simp] theorem populationLines_insert (U : Finset (Line F)) (S : Finset U) (a : U) :
    populationLines U (insert a S) = insert a.val (populationLines U S) := by
  simp [populationLines]

omit [Field F] [Fintype F] in
@[simp] theorem populationLines_erase (U : Finset (Line F)) (S : Finset U) (a : U) :
    populationLines U (S.erase a) = (populationLines U S).erase a.val := by
  simp [populationLines, Finset.map_erase]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem mem_populationLines (U : Finset (Line F)) (S : Finset U) {a : U}
    (ha : a ∈ S) : a.val ∈ populationLines U S :=
  Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem plane_conditioned_order_variance_le
    (U V : Finset (Line F)) (I : Finset U) (J : Finset V)
    (i x : U) (hi : i ∉ I) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm V)))
      (fun p => planeFraction
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding))) ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  have hc : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have h := conditioned_order_variance_le I J i x hi
    (fun S T => planeFraction (populationLines U S) (populationLines V T)) hc hc
    (by
      intro S _ _ T _ _ a ha b _ _
      simpa using planeFraction_exchange_left (populationLines U S)
        (populationLines V T) (mem_populationLines U S ha) b.val)
    (by
      intro S _ _ T _ _ a ha b _ _
      simpa using planeFraction_exchange_right (populationLines U S)
        (populationLines V T) (mem_populationLines V T ha) b.val)
  exact h.trans_eq (by ring)

theorem target_conditioned_order_variance_le
    (U V : Finset (Line F)) (hUV : Disjoint U V)
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    finiteVariance
      ((Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm V)))
      (fun p => targetFraction x.val
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding))) ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  have hc : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have hxV (a : V) : x.val ≠ a.val := by
    intro h
    exact Finset.disjoint_left.mp hUV x.property (h ▸ a.property)
  have h := conditioned_order_variance_le I J i x hi
    (fun S T => targetFraction x.val (populationLines U S) (populationLines V T)) hc hc
    (by
      intro S hS _ T _ _ a ha b hb _
      have hxa : x.val ≠ a.val := by
        intro h
        exact (Finset.mem_erase.mp (hS ha)).1 (Subtype.ext h.symm)
      have hxb : x.val ≠ b.val := by
        intro h
        exact (Finset.mem_erase.mp hb).1 (Subtype.ext h.symm)
      simpa using targetFraction_exchange_left x.val (populationLines U S)
        (populationLines V T) (mem_populationLines U S ha) b.val hxa hxb)
    (by
      intro S _ _ T _ _ a ha b _ _
      simpa using targetFraction_exchange_right x.val (populationLines U S)
        (populationLines V T) (mem_populationLines V T ha) b.val (hxV a) (hxV b))
  exact h.trans_eq (by ring)

abbrev OrderPair (U V : Finset (Line F)) := Equiv.Perm U × Equiv.Perm V

noncomputable def conditionedOrderLaw (U V : Finset (Line F)) (i x : U) :
    PMF (OrderPair U V) :=
  PMF.uniformOfFinset
    ((Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
      (Finset.univ : Finset (Equiv.Perm V)))
    ⟨(Equiv.swap i x, Equiv.refl V), by simp⟩

theorem plane_conditioned_order_measure_variance_le
    (U V : Finset (Line F))
    [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    ProbabilityTheory.variance
      (fun p : OrderPair U V => planeFraction
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding)))
      (conditionedOrderLaw U V i x).toMeasure ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  erw [conditionedOrderLaw, variance_uniformOfFinset]
  exact plane_conditioned_order_variance_le U V I J i x hi

theorem target_conditioned_order_measure_variance_le
    (U V : Finset (Line F))
    [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
    (hUV : Disjoint U V) (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    ProbabilityTheory.variance
      (fun p : OrderPair U V => targetFraction x.val
        (populationLines U (I.map p.1.toEmbedding))
        (populationLines V (J.map p.2.toEmbedding)))
      (conditionedOrderLaw U V i x).toMeasure ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 := by
  erw [conditionedOrderLaw, variance_uniformOfFinset]
  exact target_conditioned_order_variance_le U V hUV I J i x hi

end Affine

end Balanced.ConditionalOrderVariance

end OAI
