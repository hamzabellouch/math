import OAI.Combinatorics.ContingencyTables.Transport.ProductIntegerSignature

namespace OAI

/-!
# The first paper's actual line and small-slot subgroup product

Each small-slot subgroup is contained in a disjoint line group. The literal
product after two removals is factored into the two-level kernel. Zero
integer counts are masked and invalid repeated removals subtract a
nonnegative diagonal.
-/

namespace ContingencyTables.NestedProductSignature

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures ProductIntegerSignature

variable {I G : Type*} [Fintype I] [Fintype G]

def unitExtension (c : G → ℝ) : Option G → ℝ := fun o => o.elim 1 c

def subgroup (line : I → G) (inner : I → Bool) (i : I) : Option G :=
  if inner i then some (line i) else none

noncomputable def nestedRemoval (line : I → G) (inner : I → Bool)
    (a₀ a₁ a₂ c₀ c₁ c₂ : G → ℝ) : Matrix I I ℝ := fun i j =>
  productTwoUpdates a₀ a₁ a₂ (line i) (line j) *
    productTwoUpdates (unitExtension c₀) (unitExtension c₁) (unitExtension c₂)
      (subgroup line inner i) (subgroup line inner j)

omit [Fintype I] in
lemma nestedRemoval_factor (line : I → G) (inner : I → Bool)
    (a₀ a₁ a₂ c₀ c₁ c₂ : G → ℝ)
    (ha₀ : ∀ g, a₀ g ≠ 0) (ha₁ : ∀ g, a₁ g ≠ 0)
    (hc₀ : ∀ g, c₀ g ≠ 0) (hc₁ : ∀ g, c₁ g ≠ 0) (i j : I) :
    nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂ i j =
      ((∏ g, a₀ g) * ∏ g, c₀ g) *
        ((a₁ (line i)/a₀ (line i)) * (if inner i then c₁ (line i)/c₀ (line i) else 1)) *
        ((a₁ (line j)/a₀ (line j)) * (if inner j then c₁ (line j)/c₀ (line j) else 1)) *
        twoLevelKernel line inner
          (fun g => a₀ g*a₂ g/(a₁ g)^2) (fun g => c₀ g*c₂ g/(c₁ g)^2) i j := by
  have hce₀ : ∀ g, unitExtension c₀ g ≠ 0 := by intro g; cases g <;> simp [unitExtension,hc₀]
  have hce₁ : ∀ g, unitExtension c₁ g ≠ 0 := by intro g; cases g <;> simp [unitExtension,hc₁]
  unfold nestedRemoval
  rw [productTwoUpdates_factor _ _ _ ha₀ ha₁,productTwoUpdates_factor _ _ _ hce₀ hce₁]
  simp only [Fintype.prod_option,unitExtension,Option.elim_none,Option.elim_some,one_mul]
  cases hi : inner i <;> cases hj : inner j <;> by_cases hline : line i=line j <;>
    simp [subgroup,hi,hj,hline,twoLevelKernel] <;> ring

/-- Signature of the literal nested product update matrix. -/
theorem nestedRemoval_onePositive (line : I → G) (inner : I → Bool)
    (a₀ a₁ a₂ c₀ c₁ c₂ : G → ℝ)
    (ha₀ : ∀ g, 0 < a₀ g) (ha₁ : ∀ g, 0 < a₁ g) (ha₂ : ∀ g, 0 ≤ a₂ g)
    (hc₀ : ∀ g, 0 < c₀ g) (hc₁ : ∀ g, 0 < c₁ g)
    (halc : ∀ g, a₀ g*a₂ g ≤ (a₁ g)^2)
    (hclc : ∀ g, c₀ g*c₂ g ≤ (c₁ g)^2) :
    OnePositiveDirection (nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂).toBilin' := by
  let W := (∏ g, a₀ g) * ∏ g, c₀ g
  let α : I → ℝ := fun i => (a₁ (line i)/a₀ (line i)) *
    (if inner i then c₁ (line i)/c₀ (line i) else 1)
  let γ : G → ℝ := fun g => a₀ g*a₂ g/(a₁ g)^2
  let δ : G → ℝ := fun g => c₀ g*c₂ g/(c₁ g)^2
  have he : nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂ =
      weightedCorrection (twoLevelKernel line inner γ δ) W α (fun _ => 0) := by
    ext i j
    rw [nestedRemoval_factor line inner a₀ a₁ a₂ c₀ c₁ c₂
      (fun g => ne_of_gt (ha₀ g)) (fun g => ne_of_gt (ha₁ g))
      (fun g => ne_of_gt (hc₀ g)) (fun g => ne_of_gt (hc₁ g))]
    simp only [weightedCorrection,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      scaledMatrix,Matrix.diagonal_apply,ite_self,sub_zero]
    ring
  rw [he]
  exact correctedTwoLevel_onePositive line inner γ δ W α (fun _ => 0)
    (fun g => div_nonneg (mul_nonneg (ha₀ g).le (ha₂ g)) (sq_nonneg _))
    (fun g => (div_le_one (sq_pos_of_pos (ha₁ g))).mpr (halc g))
    (fun g => (div_le_one (sq_pos_of_pos (hc₁ g))).mpr (hclc g))
    (mul_nonneg (Finset.prod_nonneg fun g _ => (ha₀ g).le)
      (Finset.prod_nonneg fun g _ => (hc₀ g).le)) (fun _ => le_rfl)

noncomputable def smallTotal (line : I → G) (inner : I → Bool) (z : I → ℕ) (g : G) : ℕ :=
  lineTotal (fun i => (line i,inner i)) z (g,true)

noncomputable def nestedWeight (line : I → G) (inner : I → Bool)
    (a c : G → ℕ → ℝ) (z : I → ℕ) : ℝ :=
  (∏ g, a g (lineTotal line z g)) * ∏ g, c g (smallTotal line inner z g)

omit [Fintype G] in
lemma smallTotal_removeTwo (line : I → G) (inner : I → Bool) (z : I → ℕ)
    (i j : I) (hv : ValidPair z i j) (g : G) :
    smallTotal line inner (removeTwo z i j) g +
      (if subgroup line inner i=some g then 1 else 0) +
      (if subgroup line inner j=some g then 1 else 0) = smallTotal line inner z g := by
  have h := lineTotal_removeTwo (fun k => (line k,inner k)) z i j hv (g,true)
  cases hi : inner i <;> cases hj : inner j <;>
    simpa [smallTotal,subgroup,hi,hj,Prod.mk.injEq] using h

/-- Exact literal nested product at every valid integer two-removal entry. -/
theorem nestedWeight_removeTwo (line : I → G) (inner : I → Bool) (a c : G → ℕ → ℝ)
    (z : I → ℕ) (i j : I) (hv : ValidPair z i j) :
    nestedWeight line inner a c (removeTwo z i j) =
      nestedRemoval line inner
        (fun g => a g (lineTotal line z g)) (fun g => a g (lineTotal line z g-1))
        (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
        (fun g => c g (smallTotal line inner z g)) (fun g => c g (smallTotal line inner z g-1))
        (fun g => if 2 ≤ smallTotal line inner z g then c g (smallTotal line inner z g-2) else 0) i j := by
  unfold nestedWeight nestedRemoval productTwoUpdates
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    have ht := lineTotal_removeTwo line z i j hv g
    by_cases hi : g=line i
    · by_cases hj : g=line j
      · have hn : 2 ≤ lineTotal line z g := by simp only [hi.symm,hj.symm,ite_true] at ht; omega
        have he : lineTotal line (removeTwo z i j) g=lineTotal line z g-2 := by
          simp only [hi.symm,hj.symm,ite_true] at ht; omega
        simp only [ite_eq_left hi,ite_eq_left hj,ite_eq_left hn,he]
      · have he : lineTotal line (removeTwo z i j) g=lineTotal line z g-1 := by
          simp only [hi.symm,ite_true,Ne.symm hj,ite_false] at ht; omega
        simp only [ite_eq_left hi,ite_eq_right hj,he]
    · by_cases hj : g=line j
      · have he : lineTotal line (removeTwo z i j) g=lineTotal line z g-1 := by
          simp only [Ne.symm hi,ite_false,hj.symm,ite_true] at ht; omega
        simp only [ite_eq_right hi,ite_eq_left hj,he]
      · have he : lineTotal line (removeTwo z i j) g=lineTotal line z g := by
          simp only [Ne.symm hi,Ne.symm hj,ite_false,add_zero] at ht; exact ht
        simp only [ite_eq_right hi,ite_eq_right hj,he]
  · rw [Fintype.prod_option]
    simp only [unitExtension,Option.elim_none,ite_self,one_mul]
    apply Finset.prod_congr rfl
    intro g _
    have ht := smallTotal_removeTwo line inner z i j hv g
    by_cases hi : some g=subgroup line inner i
    · by_cases hj : some g=subgroup line inner j
      · have hn : 2 ≤ smallTotal line inner z g := by simp only [hi.symm,hj.symm,ite_true] at ht; omega
        have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g-2 := by
          simp only [hi.symm,hj.symm,ite_true] at ht; omega
        simp only [ite_eq_left hi,ite_eq_left hj,Option.elim_some,ite_eq_left hn,he]
      · have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g-1 := by
          simp only [hi.symm,ite_true,Ne.symm hj,ite_false] at ht; omega
        simp only [ite_eq_left hi,ite_eq_right hj,Option.elim_some,he]
    · by_cases hj : some g=subgroup line inner j
      · have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g-1 := by
          simp only [Ne.symm hi,ite_false,hj.symm,ite_true] at ht; omega
        simp only [ite_eq_right hi,ite_eq_left hj,Option.elim_some,he]
      · have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g := by
          simp only [Ne.symm hi,Ne.symm hj,ite_false,add_zero] at ht; exact ht
        simp only [ite_eq_right hi,ite_eq_right hj,Option.elim_some,he]

omit [Fintype I] in
private lemma masked_correction (h : (I → ℕ) → ℝ) (z : I → ℕ) (H : Matrix I I ℝ)
    (hentry : ∀ i j, ValidPair z i j → h (removeTwo z i j)=H i j) :
    integerRemovalMatrix h z = scaledMatrix H (activeMask z) -
      Matrix.diagonal (fun i => if z i=1 then H i i else 0) := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.diagonal_apply,integerRemovalMatrix,scaledMatrix,activeMask]
  by_cases hv : ValidPair z i j
  · have hi : 0 < z i := hv.1
    have hj : 0 < z j := by have := hv.2; omega
    rw [ite_eq_left hv,hentry i j hv]
    simp only [hi,hj,ite_true,one_mul,mul_one]
    by_cases hij : i=j
    · subst j
      have hn : z i ≠ 1 := by have := hv.2; simp at this; omega
      simp [hn]
    · simp [hij]
  · rw [ite_eq_right hv]
    by_cases hi : 0 < z i
    · by_cases hj : 0 < z j
      · have hij : i=j := by by_contra h; exact hv ⟨hi,by simpa [Ne.symm h] using hj⟩
        subst j
        have hn : z i=1 := by simp [ValidPair] at hv; omega
        simp [hn]
      · by_cases hij : i=j
        · subst j
          have hn : z i=0 := by omega
          simp [hn]
        · simp [hj,hij]
    · by_cases hij : i=j
      · subst j
        have hn : z i=0 := by omega
        simp [hn]
      · simp [hi,hij]

private lemma updates_nonnegative {A : Type*} [Fintype A] [DecidableEq A]
    (a₀ a₁ a₂ : A → ℝ) (ha₀ : ∀ k, 0 ≤ a₀ k) (ha₁ : ∀ k, 0 ≤ a₁ k) (ha₂ : ∀ k, 0 ≤ a₂ k)
    (i j : A) : 0 ≤ productTwoUpdates a₀ a₁ a₂ i j := by
  apply Finset.prod_nonneg
  intro k _
  split_ifs <;> first | exact ha₀ k | exact ha₁ k | exact ha₂ k

/-- The exact integer two-removal signature for the first paper's full
line penalties and nested small-slot subset penalties. -/
theorem nested_product_removal_onePositive (line : I → G) (inner : I → Bool)
    (a c : G → ℕ → ℝ) (z : I → ℕ)
    (ha : ∀ g n, n ≤ lineTotal line z g → 0 < a g n)
    (hc : ∀ g n, n ≤ smallTotal line inner z g → 0 < c g n)
    (halc : ∀ g, 2 ≤ lineTotal line z g →
      a g (lineTotal line z g)*a g (lineTotal line z g-2) ≤ a g (lineTotal line z g-1)^2)
    (hclc : ∀ g, 2 ≤ smallTotal line inner z g →
      c g (smallTotal line inner z g)*c g (smallTotal line inner z g-2) ≤
        c g (smallTotal line inner z g-1)^2) :
    OnePositiveDirection (integerRemovalMatrix (nestedWeight line inner a c) z).toBilin' := by
  let a₀ := fun g => a g (lineTotal line z g)
  let a₁ := fun g => a g (lineTotal line z g-1)
  let a₂ := fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0
  let c₀ := fun g => c g (smallTotal line inner z g)
  let c₁ := fun g => c g (smallTotal line inner z g-1)
  let c₂ := fun g => if 2 ≤ smallTotal line inner z g then c g (smallTotal line inner z g-2) else 0
  let H := nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂
  have ha₀ : ∀ g, 0 < a₀ g := fun g => ha g _ le_rfl
  have ha₁ : ∀ g, 0 < a₁ g := fun g => ha g _ (Nat.sub_le _ _)
  have ha₂ : ∀ g, 0 ≤ a₂ g := by intro g; dsimp [a₂]; split_ifs; exact (ha g _ (Nat.sub_le _ _)).le; exact le_rfl
  have hc₀ : ∀ g, 0 < c₀ g := fun g => hc g _ le_rfl
  have hc₁ : ∀ g, 0 < c₁ g := fun g => hc g _ (Nat.sub_le _ _)
  have hc₂ : ∀ g, 0 ≤ c₂ g := by intro g; dsimp [c₂]; split_ifs; exact (hc g _ (Nat.sub_le _ _)).le; exact le_rfl
  have hH : OnePositiveDirection H.toBilin' := nestedRemoval_onePositive line inner a₀ a₁ a₂ c₀ c₁ c₂
    ha₀ ha₁ ha₂ hc₀ hc₁
    (fun g => by dsimp [a₀,a₁,a₂]; split_ifs with h; exact halc g h; simp [sq_nonneg])
    (fun g => by dsimp [c₀,c₁,c₂]; split_ifs with h; exact hclc g h; simp [sq_nonneg])
  have hHdiag (i : I) : 0 ≤ H i i := by
    apply mul_nonneg
    · exact updates_nonnegative a₀ a₁ a₂ (fun g => (ha₀ g).le) (fun g => (ha₁ g).le) ha₂ _ _
    · apply updates_nonnegative
      · intro g; cases g <;> simp [unitExtension,(hc₀ _).le]
      · intro g; cases g <;> simp [unitExtension,(hc₁ _).le]
      · intro g; cases g <;> simp [unitExtension,hc₂]
  have hsig : OnePositiveDirection (scaledMatrix H (activeMask z)).toBilin' := by
    intro x hx y hxy
    rw [scaledMatrix_form] at hx hxy ⊢
    exact hH _ hx _ hxy
  apply onePositive_of_dominated_compression (scaledMatrix H (activeMask z)).toBilin'
    (integerRemovalMatrix (nestedWeight line inner a c) z).toBilin' LinearMap.id
  · exact fun x y => (matrix_bilin_symm _ (fun i j => by
      simp only [integerRemovalMatrix,validPair_symm z i j,removeTwo_comm z i j])).eq x y
  · exact hsig
  · intro v
    rw [masked_correction _ z H (nestedWeight_removeTwo line inner a c z)]
    simp only [map_sub,LinearMap.sub_apply,diagonalMatrix_form,LinearMap.id_apply]
    apply sub_le_self
    apply Finset.sum_nonneg
    intro i _
    have hκ : 0 ≤ if z i=1 then H i i else 0 := by split_ifs; exact hHdiag i; exact le_rfl
    nlinarith [mul_nonneg hκ (sq_nonneg (v i))]

end ContingencyTables.NestedProductSignature

end OAI
