import OAI.Dynamics.ConditionalShuffle.SweepPoint

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional
variable {α ι : Type*} [Fintype α] [Fintype ι] [decidableEq_α : DecidableEq α]

lemma mean_perm_embedding (e : ι ↪ α) (F : (ι ↪ α) → ℝ) :
    mean (fun g : Equiv.Perm α => F (e.trans g.toEmbedding)) = mean F := by
  let : Nonempty (ι ↪ α) := ⟨e⟩
  have he (z : ι ↪ α) : mean (fun g : Equiv.Perm α => F (z.trans g.toEmbedding)) =
      mean (fun g : Equiv.Perm α => F (e.trans g.toEmbedding)) := by
    obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e z e.injective z.injective
    have hh := mean_equiv (Equiv.mulRight σ) (fun g : Equiv.Perm α => F (e.trans g.toEmbedding))
    convert hh using 1
    apply mean_congr; intro g
    congr 1
    ext i
    exact congrArg g (hσ i).symm
  calc
    _ = mean (fun z : ι ↪ α => mean (fun g : Equiv.Perm α => F (z.trans g.toEmbedding))) := by
      simp only [he, mean_const]
    _ = mean (fun g : Equiv.Perm α => mean (fun z : ι ↪ α => F (z.trans g.toEmbedding))) := mean_comm _
    _ = mean (fun _ : Equiv.Perm α => mean F) := by
      apply mean_congr; intro g
      exact mean_equiv (Equiv.embeddingCongr (Equiv.refl ι) g) F
    _ = _ := mean_const _

lemma sum_embedding_prod_le (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ e : ι ↪ α, ∏ i, f (e i)) ≤ (∑ a, f a) ^ Fintype.card ι := by
  have hh : (∑ e : ι ↪ α, ∏ i, f (e i)) ≤ ∑ e : ι → α, ∏ i, f (e i) := by
    let S : Finset (ι → α) := (Finset.univ : Finset (ι ↪ α)).image (fun e : ι ↪ α => (e : ι → α))
    have hs : (∑ e : ι ↪ α, ∏ i, f (e i)) = ∑ e ∈ S, ∏ i, f (e i) := by
      dsimp only [S]
      rw [Finset.sum_image]
      intro e _ z _ h; exact DFunLike.coe_injective h
    rw [hs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => Finset.prod_nonneg (fun i _ => hf (e i)))
  simpa only [← Fintype.prod_sum, Finset.prod_const, Finset.card_univ] using hh

lemma mean_perm_prod_le (e : ι ↪ α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    mean (fun g : Equiv.Perm α => ∏ i, f (g (e i))) ≤
      (∑ a, f a) ^ Fintype.card ι / (Fintype.card α).descFactorial (Fintype.card ι) := by
  have hh := mean_perm_embedding e (fun z => ∏ i, f (z i))
  change mean (fun g : Equiv.Perm α => ∏ i, f (g (e i))) = _ at hh
  rw [hh, mean, Fintype.card_embedding_eq]
  exact div_le_div_of_nonneg_right (sum_embedding_prod_le f hf) (Nat.cast_nonneg _)

lemma sum_half_free (B : α → Bool) :
    (∑ x, if B x then (1/2 : ℝ) else 1) = Fintype.card α - (freeCount B : ℝ)/2 := by
  let retained_decidableEq_α := decidableEq_α
  have hh : (∑ x, if B x then (1/2 : ℝ) else 1) +
      (∑ x, if B x then (1 : ℝ) else 0)/2 = Fintype.card α := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    have hp (x : α) : (if B x then (1/2 : ℝ) else 1) +
        (if B x then (1 : ℝ) else 0)/2 = 1 := by cases B x <;> norm_num
    simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [sum_free_indicator] at hh
  linarith

lemma mean_perm_half_le {t : ℕ} (e : Fin t ↪ α) (B : α → Bool)
    (hm : Fintype.card α + 1 ≤ 64 * (freeCount B + 1))
    (ht : 256 * (t+1) ≤ Fintype.card α + 1) :
    mean (fun g : Equiv.Perm α => ∏ i, (if B (g (e i)) then (1/2 : ℝ) else 1)) ≤
      (255/256 : ℝ)^t := by
  let N := Fintype.card α
  let A : ℝ := ∑ x, if B x then (1/2 : ℝ) else 1
  have hA : 0 ≤ A := Finset.sum_nonneg (fun x _ => by split <;> norm_num)
  have hD : 0 < N+1-t := by dsimp [N]; omega
  have hD' : (0 : ℝ) < (N+1-t : ℕ) := by exact_mod_cast hD
  have hp : ((N+1-t : ℕ) : ℝ)^t ≤ (N.descFactorial t : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N t
  have hh := mean_perm_prod_le e (fun x => if B x then (1/2 : ℝ) else 1)
    (fun x => by split <;> norm_num)
  simp only [Fintype.card_fin] at hh
  have hratio : A / ((N+1-t : ℕ) : ℝ) ≤ 255/256 := by
    apply (div_le_iff₀ hD').mpr
    dsimp only [A]
    rw [sum_half_free, Nat.cast_sub (by dsimp [N]; omega : t ≤ N+1), Nat.cast_add, Nat.cast_one]
    have hm' : (N : ℝ)+1 ≤ 64*((freeCount B : ℝ)+1) := by exact_mod_cast hm
    have ht' : 256*((t : ℝ)+1) ≤ (N : ℝ)+1 := by exact_mod_cast ht
    change (N : ℝ) - ↑(freeCount B)/2 ≤ _
    linarith
  calc
    _ ≤ A^t / (N.descFactorial t : ℝ) := hh
    _ ≤ A^t / (((N+1-t : ℕ) : ℝ)^t) :=
      div_le_div_of_nonneg_left (pow_nonneg hA _) (pow_pos hD' _) hp
    _ = (A / ((N+1-t : ℕ) : ℝ))^t := (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (div_nonneg hA hD'.le) hratio t

end Thorp.Conditional

end

end OAI
