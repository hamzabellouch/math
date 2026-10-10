import OAI.Combinatorics.BalancedRyser.Incidence.UnusedOffsetIncidence
import OAI.Combinatorics.BalancedRyser.Local.LocalConditionFibers

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical BigOperators
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {b κ n : ℕ}

def GoodSpecification (u : Position b → α) (I : Finset (Position b))
    (σ : Fin n → Position b × Code b κ) : Prop :=
  Function.Injective (fun k => u (σ k).1) ∧
    (∀ k, (σ k).1 ∈ I) ∧
    ∃ rank : α → ℕ, ∀ i j,
      u (σ j).1 ∈ (anchors (σ i).2).image u →
        rank (u (σ i).1) < rank (u (σ j).1)

theorem specification_product_bound (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (v₀ : Position b) (σ : Fin n → Position b × Code b κ)
    (hσ : GoodSpecification u I σ) :
    UnusedOffsetIncidence.probability (fun x : α → F => ∀ k,
      PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) ≤
        (2 * (B : ℝ) / Fintype.card F) ^ n := by
  obtain ⟨hτ, hI, rank, hrank⟩ := hσ
  let τ : Fin n → α := fun k => u (σ k).1
  let s : Finset α := Finset.univ.image τ
  let test : α → Position b := Function.extend τ (fun k => (σ k).1) (fun _ => v₀)
  let code : α → Code b κ := Function.extend τ (fun k => (σ k).2) (fun _ => Sum.inl ())
  have htest : ∀ k, test (τ k) = (σ k).1 := fun k => hτ.extend_apply _ _ k
  have hcode : ∀ k, code (τ k) = (σ k).2 := fun k => hτ.extend_apply _ _ k
  have hs : ∀ i ∈ s, ∃ k, τ k = i := by
    intro i hi
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    exact ⟨k, hk⟩
  have hp := pointHolds_product_bound a p M B hB hmult u point s test code rank
    (fun i hi => by obtain ⟨k, rfl⟩ := hs i hi; rw [htest])
    (fun i hi w hw hwi => by
      obtain ⟨k, rfl⟩ := hs i hi
      rw [hcode] at hw
      exact (lt_irrefl _) (hrank k k (Finset.mem_image.mpr ⟨w, hw, hwi⟩)))
    (fun i hi => by obtain ⟨k, rfl⟩ := hs i hi; rw [htest]; exact hinj _ (hI k))
    (fun i hi => by obtain ⟨k, rfl⟩ := hs i hi; rw [htest]; exact hline _ (hI k))
    (fun i hi j hj hdep => by
      obtain ⟨k, rfl⟩ := hs i hi
      obtain ⟨l, rfl⟩ := hs j hj
      rw [hcode] at hdep
      exact hrank k l hdep)
  have hcard : s.card = n := by
    rw [Finset.card_image_of_injective _ hτ]
    simp
  rw [hcard] at hp
  have hevent : (fun x : α → F => ∀ i ∈ s,
      PointHolds a p M (fun w => point w (x (u w))) (test i) (code i)) =
      (fun x : α → F => ∀ k,
        PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) := by
    funext x
    apply propext
    constructor
    · intro h k
      simpa only [htest, hcode] using h (τ k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    · intro h i hi
      obtain ⟨k, rfl⟩ := hs i hi
      simpa only [htest, hcode] using h k
  unfold UnusedOffsetIncidence.probability
  convert hp using 1
  congr 3
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Eq.to_iff (congrFun hevent x).symm

theorem specifications_probability_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (hb : 1 ≤ b) :
    UnusedOffsetIncidence.probability (fun x : α → F =>
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification u I σ ∧ ∀ k,
          PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (B : ℝ) / Fintype.card F) ^ (3 - κ) := by
  let E := fun (σ : Fin (3 - κ) → Position b × Code b κ) (x : α → F) =>
    GoodSpecification u I σ ∧ ∀ k,
      PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2
  have hE : ∀ σ, UnusedOffsetIncidence.probability (E σ) ≤
      (2 * (B : ℝ) / Fintype.card F) ^ (3 - κ) := by
    intro σ
    by_cases hσ : GoodSpecification u I σ
    · apply (UnusedOffsetIncidence.probability_mono (fun x h => h.2)).trans
      exact specification_product_bound a p M B hB hmult u point I hinj hline
        (⟨0, by omega⟩, 0) σ hσ
    · simp only [E, hσ, false_and, UnusedOffsetIncidence.probability,
        Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  have hsum := (UnusedOffsetIncidence.probability_exists_fintype_le E).trans
    (Finset.sum_le_sum (fun σ _ => hE σ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hc := card_specifications_le b κ hb
  have hcr : (Fintype.card (Fin (3 - κ) → Position b × Code b κ) : ℝ) ≤
      (148 * (b : ℝ) ^ 3) ^ 3 := by exact_mod_cast hc
  calc
    _ ≤ (148 * (b : ℝ) ^ 3) ^ 3 := hcr
    _ = (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 := by ring

end
end Balanced.Local.ConditionSpec

end OAI
