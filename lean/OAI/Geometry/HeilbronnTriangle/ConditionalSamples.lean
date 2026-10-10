import Mathlib

namespace OAI


namespace Problem355.ConditionalSamples

noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

def productWeight (μ : α → ℝ) (x : ι → α) : ℝ := ∏ i, μ (x i)

lemma sum_productWeight (μ : α → ℝ) (hμ : ∑ a, μ a = 1) :
    ∑ x : ι → α, productWeight μ x = 1 := by
  classical
  have h := (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α))
    (fun _ a => μ a)).symm
  simpa [productWeight, hμ] using h

omit [Fintype α] [DecidableEq ι] in
lemma productWeight_nonneg (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (x : ι → α) :
    0 ≤ productWeight μ x :=
  Finset.prod_nonneg fun i _ => hμ (x i)

omit [Fintype α] [DecidableEq ι] in
lemma productWeight_split (μ : α → ℝ) (p : ι → Prop) [DecidablePred p]
    (x : ι → α) : productWeight μ x =
      productWeight μ (fun i : {i // p i} => x i) *
        productWeight μ (fun i : {i // ¬p i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => μ (x i))).symm

lemma sum_productWeight_restrict (μ : α → ℝ) (hμ : ∑ a, μ a = 1)
    (p : ι → Prop) [DecidablePred p] (F : ({i // p i} → α) → ℝ) :
    (∑ x : ι → α, productWeight μ x * F (fun i => x i)) =
      ∑ y : {i // p i} → α, productWeight μ y * F y := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => α)
  calc
    (∑ x : ι → α, productWeight μ x * F (fun i => x i)) =
        ∑ yz : ({i // p i} → α) × ({i // ¬p i} → α),
          (productWeight μ yz.1 * productWeight μ yz.2) * F yz.1 := by
      apply Fintype.sum_equiv e
      intro x
      rw [productWeight_split μ p x]
      rfl
    _ = ∑ y : {i // p i} → α, productWeight μ y * F y := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ z : {i // ¬p i} → α,
            (productWeight μ y * productWeight μ z) * F y) =
            ∑ z : {i // ¬p i} → α,
              (productWeight μ y * F y) * productWeight μ z := by
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = productWeight μ y * F y := by
          rw [← Finset.mul_sum, sum_productWeight μ hμ, mul_one]

lemma sum_productWeight_comp {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : α → ℝ) (hμ : ∑ a, μ a = 1) (e : κ → ι)
    (he : Function.Injective e) (F : (κ → α) → ℝ) :
    (∑ x : ι → α, productWeight μ x * F (x ∘ e)) =
      ∑ y : κ → α, productWeight μ y * F y := by
  classical
  let : Fintype (Set.range e) := Subtype.fintype _
  let er : κ ≃ Set.range e := Equiv.ofInjective e he
  let ar := Equiv.piCongrLeft (fun _ : Set.range e => α) er
  have hrestrict := sum_productWeight_restrict μ hμ
    (fun i => i ∈ Set.range e) (fun y => F (fun j => y (er j)))
  change (∑ x : ι → α, productWeight μ x * F (x ∘ e)) = _ at hrestrict
  rw [hrestrict]
  apply Fintype.sum_equiv ar.symm
  intro y
  have hprod : productWeight μ y = productWeight μ (ar.symm y) := by
    exact (er.prod_comp (fun i => μ (y i))).symm
  rw [hprod]
  rfl

variable {Θ : Type*}

def sharedWeight (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (z : Θ × (ι → α)) : ℝ :=
  ρ z.1 * productWeight (μ z.1) z.2

omit [Fintype α] [DecidableEq ι] in
lemma sharedWeight_nonneg (ρ : Θ → ℝ) (μ : Θ → α → ℝ)
    (hρ : ∀ θ, 0 ≤ ρ θ) (hμ : ∀ θ a, 0 ≤ μ θ a) (z : Θ × (ι → α)) :
    0 ≤ sharedWeight ρ μ z :=
  mul_nonneg (hρ z.1) (productWeight_nonneg (μ z.1) (hμ z.1) z.2)

lemma sum_sharedWeight [Fintype Θ] (ρ : Θ → ℝ) (μ : Θ → α → ℝ)
    (hρ : ∑ θ, ρ θ = 1) (hμ : ∀ θ, ∑ a, μ θ a = 1) :
    ∑ z : Θ × (ι → α), sharedWeight ρ μ z = 1 := by
  classical
  simp only [sharedWeight, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_productWeight _ (hμ _), mul_one]
  exact hρ

lemma shared_marginal [Fintype Θ] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
    (e : κ → ι) (he : Function.Injective e) (F : Θ → (κ → α) → ℝ) :
    (∑ z : Θ × (ι → α), sharedWeight ρ μ z * F z.1 (z.2 ∘ e)) =
      ∑ z : Θ × (κ → α), sharedWeight ρ μ z * F z.1 z.2 := by
  classical
  simp only [sharedWeight, Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  rw [sum_productWeight_comp (μ θ) (hμ θ) e he (F θ)]

lemma shared_pair_marginal [Fintype Θ]
    (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
    {i j : ι} (hij : i ≠ j) (F : Θ → α → α → ℝ) :
    (∑ z : Θ × (ι → α), sharedWeight ρ μ z * F z.1 (z.2 i) (z.2 j)) =
      ∑ z : Θ × (Fin 2 → α), sharedWeight ρ μ z * F z.1 (z.2 0) (z.2 1) := by
  have he : Function.Injective (![i, j] : Fin 2 → ι) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  simpa using shared_marginal ρ μ hμ (![i, j] : Fin 2 → ι) he
    (fun θ x => F θ (x 0) (x 1))

lemma shared_triple_marginal [Fintype Θ]
    (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (F : Θ → α → α → α → ℝ) :
    (∑ z : Θ × (ι → α), sharedWeight ρ μ z * F z.1 (z.2 i) (z.2 j) (z.2 k)) =
      ∑ z : Θ × (Fin 3 → α),
        sharedWeight ρ μ z * F z.1 (z.2 0) (z.2 1) (z.2 2) := by
  have he : Function.Injective (![i, j, k] : Fin 3 → ι) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  simpa using shared_marginal ρ μ hμ (![i, j, k] : Fin 3 → ι) he
    (fun θ x => F θ (x 0) (x 1) (x 2))

end
end Problem355.ConditionalSamples

end OAI
