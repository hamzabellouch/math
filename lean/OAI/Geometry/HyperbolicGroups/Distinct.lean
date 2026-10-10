import Mathlib
import OAI.Geometry.HyperbolicGroups.FiberLaw

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
lemma map_uniform_equiv [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (uniform : FiniteLaw α).map e = (uniform : FiniteLaw β) := by
  classical
  apply ext
  funext b
  unfold map uniform
  dsimp only
  rw [Finset.sum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a _ ha
    simp [show e a ≠ b by intro h; exact ha (e.injective (h.trans (e.apply_symm_apply b).symm))]
  · simp

def embeddingSubtypeEquiv : (α ↪ β) ≃ {f : α → β // Function.Injective f} where
  toFun f := ⟨f,f.injective⟩
  invFun f := ⟨f.val,f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma distinct_tv [Nonempty β] [Nonempty (α ↪ β)] :
    ((uniform : FiniteLaw (α ↪ β)).map (fun f : α ↪ β => (f : α → β))).totalVariation
      (uniform : FiniteLaw (α → β)) =
      1 - ((Fintype.card β).descFactorial (Fintype.card α) : ℝ) /
        (Fintype.card β : ℝ) ^ Fintype.card α := by
  classical
  let e : (α ↪ β) ≃ {f : α → β // Function.Injective f} := embeddingSubtypeEquiv
  let : Nonempty {f : α → β // Function.Injective f} :=
    ⟨e (Classical.choice inferInstance)⟩
  have hh : (uniform : FiniteLaw (α ↪ β)).map (fun f : α ↪ β => (f : α → β)) =
      (uniform : FiniteLaw {f : α → β // Function.Injective f}).map Subtype.val := by
    rw [← map_uniform_equiv e,map_map]
    rfl
  rw [hh,uniform_subtype_tv]
  have hc : Fintype.card {f : α → β // Function.Injective f} =
      (Fintype.card β).descFactorial (Fintype.card α) :=
    (Fintype.card_congr e).symm.trans Fintype.card_embedding_eq
  simp only [hc,Fintype.card_fun,Nat.cast_pow]

/-- Distinct sampling and iid sampling have vanishing TV distance at each fixed
number of leaves. This uses the exact falling-factorial ratio. -/
theorem distinct_error_tendsto (t : ℕ) :
    Tendsto (fun N : ℕ => 1 - ((N.descFactorial t : ℕ) : ℝ) / (N : ℝ) ^ t) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hi (i : ℕ) : Tendsto (fun N : ℕ => 1 - (i : ℝ) / N) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hinv.const_mul (i : ℝ))
    simpa [div_eq_mul_inv] using h
  have hp : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range t, (1 - (i : ℝ) / N)) atTop (𝓝 1) := by
    simpa using tendsto_finsetProd (Finset.range t) (fun i _ => hi i)
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
  apply (show Tendsto (fun N : ℕ => 1 - ∏ i ∈ Finset.range t, (1 - (i : ℝ) / N)) atTop (𝓝 0) by simpa using hh).congr'
  filter_upwards [eventually_ge_atTop (max t 1)] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  congr 1
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  symm
  have he (i : ℕ) (hi : i ∈ Finset.range t) : ((N - i : ℕ) : ℝ) / N = 1 - (i : ℝ) / N := by
    have hni : i ≤ N := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hni,sub_div,div_self (ne_of_gt hn)]
  calc
    _ = ∏ i ∈ Finset.range t, ((N - i : ℕ) : ℝ) / N := by
      rw [Finset.prod_div_distrib]
      simp
    _ = _ := Finset.prod_congr rfl he

end FiniteLaw
end HyperbolicObstruction
end
end

section

end
end

end OAI
