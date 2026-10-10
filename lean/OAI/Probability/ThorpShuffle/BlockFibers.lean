import OAI.Probability.ThorpShuffle.BlockEmbedding

namespace OAI

universe uI uβ uα uK

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα} [Fintype I] [Fintype β] [Fintype α] [DecidableEq α] [DecidableEq β]

def fiberEquiv (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) :
    Equiv.Perm β ≃ {k : Equiv.Perm α // restriction e i k = restriction e i g} :=
  Equiv.ofBijective (fun h => ⟨g * embedding e (Pi.mulSingle i h), restriction_right e i g h⟩)
    ⟨fun h k hh => single_embedding_injective e i (mul_left_cancel (congrArg Subtype.val hh)),
      fun ⟨k,hk⟩ => by
        obtain ⟨h, hh⟩ := restriction_fiber e i g k hk
        exact ⟨h, Subtype.ext hh⟩⟩

lemma push_restriction (e : α ≃ I × β) (i : I) (μ : Equiv.Perm α → ℝ) (g : Equiv.Perm α) :
    Trim.push μ (restriction e i) (restriction e i g) = Trim.cosetMass (embedding e) μ i g := by
  calc
    _ = ∑ k : {k : Equiv.Perm α // restriction e i k = restriction e i g}, μ k.val := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun k : Equiv.Perm α => restriction e i k = restriction e i g)) (by simp),
        Finset.sum_filter]
      unfold Trim.push
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> rfl
    _ = _ := (Equiv.sum_comp (fiberEquiv e i g) (fun k => μ k.val)).symm

lemma push_uniform_restriction (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) :
    Trim.push (fun _ : Equiv.Perm α => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹)
      (restriction e i) (restriction e i g) =
      (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α) := by
  rw [push_restriction]
  simp only [Trim.cosetMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

variable {K : Type uK} [Fintype K]

def orderedRestriction (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i) (g : Equiv.Perm α) : K → α :=
  restriction e i g ∘ o

omit [Fintype I] [Fintype β] [Fintype α] [DecidableEq α] [DecidableEq β] [Fintype K] in
lemma orderedRestriction_eq_iff (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i)
    (g k : Equiv.Perm α) : orderedRestriction e i o g = orderedRestriction e i o k ↔
      restriction e i g = restriction e i k := by
  constructor
  · intro h
    funext x
    obtain ⟨k,rfl⟩ := o.surjective x
    exact congrFun h k
  · intro h
    unfold orderedRestriction
    rw [h]

omit [Fintype K] in
lemma push_orderedRestriction (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i)
    (μ : Equiv.Perm α → ℝ) (g : Equiv.Perm α) :
    Trim.push μ (orderedRestriction e i o) (orderedRestriction e i o g) =
      Trim.cosetMass (embedding e) μ i g := by
  rw [← push_restriction e i μ g]
  unfold Trim.push
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : restriction e i k = restriction e i g
  · have ho := (orderedRestriction_eq_iff e i o k g).mpr hk
    simp only [ite_eq_left hk, ite_eq_left ho]
  · have ho := mt (orderedRestriction_eq_iff e i o k g).mp hk
    simp only [ite_eq_right hk, ite_eq_right ho]

omit [Fintype K] in
lemma uniform_orderedRestriction (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i)
    (g : Equiv.Perm α) :
    Trim.push (fun _ : Equiv.Perm α => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹)
      (orderedRestriction e i o) (orderedRestriction e i o g) =
      (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α) := by
  rw [push_orderedRestriction]
  simp only [Trim.cosetMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

lemma discarded_ordered_bound [DecidableEq K] (e : α ≃ I × β) (o : ∀ i, K ≃ complement (β:=β) i)
    (μ : Equiv.Perm α → ℝ) (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1) :
    Trim.discarded (embedding e) μ ≤
      2 * ∑ i, tv (Trim.push μ (orderedRestriction e i (o i)))
        (Trim.push (fun _ : Equiv.Perm α => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) (orderedRestriction e i (o i))) := by
  exact Trim.discarded_bound (embedding e) μ hμ h1 (fun _ : I => K → α)
    (fun i => orderedRestriction e i (o i))
    (fun i g => push_orderedRestriction e i (o i) μ g)
    (fun i g => uniform_orderedRestriction e i (o i) g)

end Block

lemma law_nonneg (d t : ℕ) (g : State d) : 0 ≤ law d t g := fairMass_nonneg (run d t) g

lemma law_sum (d t : ℕ) : ∑ g, law d t g = 1 := fairMass_sum (run d t)

namespace Block
open scoped Classical

def eightEquiv (d : ℕ) : Position (d+1+2) ≃ Fin 8 × Position d :=
  Fintype.equivOfCardEq (by simp only [card_position, Fintype.card_prod, Fintype.card_fin, pow_add]; norm_num; omega)

lemma complement_card (d : ℕ) (i : Fin 8) :
    Fintype.card (complement (β:=Position d) i) = 7 * 2^d := by
  rw [card_complement, Fintype.card_fin, card_position]

def ordering (d : ℕ) (i : Fin 8) : Fin (7 * 2^d) ≃ complement (β:=Position d) i :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, complement_card])

def domain (d : ℕ) (i : Fin 8) : Fin (7*2^d) → Position (d+1+2) :=
  complementIn (eightEquiv d) i ∘ ordering d i

lemma domain_injective (d : ℕ) (i : Fin 8) : Function.Injective (domain d i) :=
  (complementIn_injective _ _).comp (ordering d i).injective

lemma push_law_ordered (d : ℕ) (i : Fin 8) :
    Trim.push (law (d+1+2) (200*(d+1+2))) (orderedRestriction (eightEquiv d) i (ordering d i)) =
      fairMass (fun ω : History (d+1+2) (200*(d+1+2)) => run (d+1+2) (200*(d+1+2)) ω ∘ domain d i) := by
  simpa only [law, Function.comp_def, orderedRestriction, restriction, domain] using
    Trim.push_fairMass (run (d+1+2) (200*(d+1+2))) (orderedRestriction (eightEquiv d) i (ordering d i))

lemma push_uniform_ordered (d : ℕ) (i : Fin 8) :
    Trim.push (fun _ : State (d+1+2) => (Fintype.card (State (d+1+2)) : ℝ)⁻¹)
      (orderedRestriction (eightEquiv d) i (ordering d i)) =
      fairMass (fun g : State (d+1+2) => g ∘ domain d i) := by
  rw [Trim.uniform_eq_fairMass_id]
  simpa only [Function.comp_def, orderedRestriction, restriction, domain, id_eq] using
    Trim.push_fairMass (id : State (d+1+2) → State (d+1+2)) (orderedRestriction (eightEquiv d) i (ordering d i))

def discarded (d : ℕ) : ℝ :=
  Trim.discarded (embedding (eightEquiv d)) (law (d+1+2) (200*(d+1+2)))

lemma discarded_nonneg (d : ℕ) : 0 ≤ discarded d :=
  Trim.discarded_nonneg _ _ (law_nonneg _ _)

lemma discarded_le (d : ℕ) : discarded d ≤ 16 * Conditional.marginalRate d := by
  have h := discarded_ordered_bound (eightEquiv d) (ordering d) (law (d+1+2) (200*(d+1+2)))
    (law_nonneg (d+1+2) (200*(d+1+2))) (law_sum (d+1+2) (200*(d+1+2)))
  simp only [push_law_ordered, push_uniform_ordered] at h
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => Conditional.marginal_tv_rate d (domain d i) (domain_injective d i))
  have hc : (∑ _ : Fin 8, Conditional.marginalRate d) = 8 * Conditional.marginalRate d := by simp
  rw [hc] at hb
  exact h.trans (by linarith)

lemma discarded_tendsto : Tendsto discarded atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using Conditional.marginalRate_tendsto.const_mul 16)
    discarded_nonneg discarded_le

end Block

end Thorp

end

end OAI
