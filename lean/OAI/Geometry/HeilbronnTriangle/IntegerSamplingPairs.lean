import OAI.Geometry.HeilbronnTriangle.LiftCollisions
import OAI.Geometry.HeilbronnTriangle.LiftingProbability
import OAI.Geometry.HeilbronnTriangle.IntegerSampling

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.IntegerSamplingPairs

open LiftCollisions

def collisionMass {X : Type*} [Fintype X] (col : X → Column)
    (p q : X → ℝ) : ℝ := by
  classical
  exact ∑ x, ∑ y, if project (col x) = project (col y) then p x * q y else 0

theorem collisionMass_le {X : Type*} [Fintype X]
    (col : X → Column) (hcol : Function.Injective col)
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (hbox : ∀ x, InBox N (col x)) (p q : X → ℝ)
    (hq0 : ∀ x, 0 ≤ q x)
    (hp : ∀ x, p x ≤ 1 / (L : ℝ) ^ 3)
    (hq : ∀ x, q x ≤ 1 / (L : ℝ) ^ 3) :
    collisionMass col p q ≤ 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  classical
  let U := Finset.univ.image col
  let S : Finset (X × X) := Finset.univ.filter
    (fun z => project (col z.1) = project (col z.2))
  let T := (U ×ˢ U).filter (fun z => project z.1 = project z.2)
  let f : X × X → Column × Column := fun z => (col z.1, col z.2)
  have hf : Set.MapsTo f ↑S ↑T := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨z.1, Finset.mem_univ _, rfl⟩,
       Finset.mem_image.mpr ⟨z.2, Finset.mem_univ _, rfl⟩⟩,
      (Finset.mem_filter.mp hz).2⟩
  have hi : Set.InjOn f ↑S := by
    intro a ha b hb hab
    exact Prod.ext (hcol (congrArg Prod.fst hab)) (hcol (congrArg Prod.snd hab))
  have hU : ∀ u ∈ U, InBox N u := by
    intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    exact hbox x
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcount : (S.card : ℝ) ≤ 8 * (N : ℝ) ^ 3 := by
    exact_mod_cast (Finset.card_le_card_of_injOn f hf hi).trans
      (card_equal_projection_pairs_le N hNpos U U hU hU)
  have hsum : collisionMass col p q = ∑ z ∈ S, p z.1 * q z.2 := by
    simp only [collisionMass, S, Finset.sum_filter, Fintype.sum_prod_type]
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [hsum]
  calc
    (∑ z ∈ S, p z.1 * q z.2) ≤
        ∑ _z ∈ S, (1 / (L : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (hp z.1) (hq z.2) (hq0 z.2) (by positivity)
    _ = (S.card : ℝ) * ((1 / (L : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3)) := by simp
    _ ≤ (8 * (N : ℝ) ^ 3) * ((1 / (L : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
      rw [hN]
      push_cast
      field_simp

theorem conditionalColumnMass_le {X A B : Type*}
    (f : X → A) (g : X → B) (a : A) (V : Finset B)
    (s L : ℕ) (hs : 0 < s) (x : X) :
    LiftingProbability.conditionalColumnMass f g a V s L x ≤ 1 / (L : ℝ) ^ 3 := by
  classical
  unfold LiftingProbability.conditionalColumnMass
  split_ifs
  · have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    by_cases hL : L = 0
    · simp [hL]
    · apply one_div_le_one_div_of_le (by positivity)
      nlinarith [pow_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) 3]
  · positivity

theorem mixture_mass_le {I X : Type*} [Fintype I]
    (w : I → ℝ) (p : I → X → ℝ) (C : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hp : ∀ i x, p i x ≤ C) (x : X) :
    (∑ i, w i * p i x) ≤ C := by
  calc
    (∑ i, w i * p i x) ≤ ∑ i, w i * C :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i x) (hw0 i))
    _ = C := by rw [← Finset.sum_mul, hw, one_mul]

theorem conditional_collisionMass_le {X A B : Type*} [Fintype X]
    (col : X → Column) (hcol : Function.Injective col)
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (hbox : ∀ x, InBox N (col x)) (f : X → A) (g : X → B)
    (a₁ a₂ : A) (V₁ V₂ : Finset B) (s₁ s₂ : ℕ)
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    collisionMass col
      (LiftingProbability.conditionalColumnMass f g a₁ V₁ s₁ L)
      (LiftingProbability.conditionalColumnMass f g a₂ V₂ s₂ L) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  apply collisionMass_le col hcol N Q L hQ hL hN hbox
  · exact LiftingProbability.conditionalColumnMass_nonneg f g a₂ V₂ s₂ L
  · exact conditionalColumnMass_le f g a₁ V₁ s₁ L hs₁
  · exact conditionalColumnMass_le f g a₂ V₂ s₂ L hs₂

theorem mixture_collisionMass_le {X I J : Type*}
    [Fintype X] [Fintype I] [Fintype J]
    (col : X → Column) (hcol : Function.Injective col)
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (hbox : ∀ x, InBox N (col x))
    (w : I → ℝ) (v : J → ℝ) (p : I → X → ℝ) (q : J → X → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hv0 : ∀ j, 0 ≤ v j)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hq0 : ∀ j x, 0 ≤ q j x)
    (hp : ∀ i x, p i x ≤ 1 / (L : ℝ) ^ 3)
    (hq : ∀ j x, q j x ≤ 1 / (L : ℝ) ^ 3) :
    collisionMass col (fun x => ∑ i, w i * p i x)
      (fun x => ∑ j, v j * q j x) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  apply collisionMass_le col hcol N Q L hQ hL hN hbox
  · intro x
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hv0 j) (hq0 j x))
  · exact mixture_mass_le w p _ hw0 hw hp
  · exact mixture_mass_le v q _ hv0 hv hq

theorem collisionMass_eq_finTwo {X : Type*} [Fintype X]
    (col : X → Column) (p : X → ℝ) :
    collisionMass col p p =
      ∑ x : Fin 2 → X, (∏ i, p (x i)) *
        (if project (col (x 0)) = project (col (x 1)) then 1 else 0) := by
  classical
  symm
  calc
    _ = ∑ z : X × X,
        if project (col z.1) = project (col z.2) then p z.1 * p z.2 else 0 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv X)
      intro x
      simp only [Fin.prod_univ_two]
      change (p (x 0) * p (x 1)) * (if _ then 1 else 0) = _
      split_ifs <;> simp_all
    _ = collisionMass col p p := by
      simp only [collisionMass, Fintype.sum_prod_type]

def boxColumn {N : ℕ} (x : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)) :
    Column := fun i => (x i).val

theorem boxColumn_injective (N : ℕ) :
    Function.Injective (@boxColumn N) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem boxColumn_inBox {N : ℕ}
    (x : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)) :
    InBox N (boxColumn x) := by
  have hx := (x 0).property
  have hy := (x 1).property
  have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := (x 2).property
  simp [IntegerSampling.samplingShift] at hx hy
  change 0 ≤ (x 0).val ∧ (x 0).val < N ∧ 0 ≤ (x 1).val ∧ (x 1).val < N ∧
    (N : ℤ) ≤ (x 2).val ∧ (x 2).val < 2 * N
  omega

@[simp] theorem project_boxColumn {N : ℕ}
    (x : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)) :
    project (boxColumn x) = IntegerSampling.project x := rfl

theorem columnLaw_collision_le (h q L s₁ s₂ : ℕ)
    (hh : 0 < h) (hq : 0 < q) (hL : 0 < L) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (a₁ a₂ : Fin 3 → ZMod h) (V₁ V₂ : Finset (Fin 3 → ZMod q)) :
    (∑ x : IntegerSampling.Box (L * (h * q)) 3
        (IntegerSampling.samplingShift (L * (h * q))), ∑ y,
      if IntegerSampling.project x = IntegerSampling.project y then
        IntegerSampling.columnLaw h q L _ a₁ V₁ s₁ x *
          IntegerSampling.columnLaw h q L _ a₂ V₂ s₂ y else 0) ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  have H := conditional_collisionMass_le boxColumn (boxColumn_injective _)
    (L * (h * q)) (h * q) L (Nat.mul_pos hh hq) hL (Nat.mul_comm _ _)
    boxColumn_inBox (IntegerSampling.residue h) (IntegerSampling.residue q)
    a₁ a₂ V₁ V₂ s₁ s₂ hs₁ hs₂
  simp only [collisionMass, project_boxColumn, IntegerSampling.columnLaw] at H ⊢
  convert H using 1
  congr 1

theorem box_finTwo_collision_le (N Q L : ℕ)
    (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (p : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N) → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∀ x, p x ≤ 1 / (L : ℝ) ^ 3) :
    (∑ x : Fin 2 → IntegerSampling.Box N 3 (IntegerSampling.samplingShift N),
      (∏ i, p (x i)) *
        (if IntegerSampling.project (x 0) = IntegerSampling.project (x 1) then 1 else 0)) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  have H := collisionMass_le boxColumn (boxColumn_injective N)
    N Q L hQ hL hN boxColumn_inBox p p hp0 hp hp
  rw [collisionMass_eq_finTwo] at H
  simp only [project_boxColumn] at H
  convert H using 1
  congr 1

theorem mixture_columnLaw_finTwo_collision_le {I : Type*} [Fintype I]
    (h q L : ℕ) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (w : I → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (a : I → Fin 3 → ZMod h) (V : I → Finset (Fin 3 → ZMod q))
    (s : I → ℕ) (hs : ∀ i, 0 < s i) :
    (∑ x : Fin 2 → IntegerSampling.Box (L * (h * q)) 3
        (IntegerSampling.samplingShift (L * (h * q))),
      (∏ j, ∑ i, w i * IntegerSampling.columnLaw h q L _ (a i) (V i) (s i) (x j)) *
        (if IntegerSampling.project (x 0) = IntegerSampling.project (x 1) then 1 else 0)) ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  let p := fun x : IntegerSampling.Box (L * (h * q)) 3
      (IntegerSampling.samplingShift (L * (h * q))) =>
    ∑ i, w i * IntegerSampling.columnLaw h q L _ (a i) (V i) (s i) x
  have hp0 : ∀ x, 0 ≤ p x := by
    intro x
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i)
      (IntegerSampling.columnLaw_nonneg h q L _ (a i) (V i) (s i) x))
  have hp : ∀ x, p x ≤ 1 / (L : ℝ) ^ 3 := by
    apply mixture_mass_le w _ _ hw0 hw
    intro i x
    exact conditionalColumnMass_le _ _ (a i) (V i) (s i) L (hs i) x
  have H := box_finTwo_collision_le _ (h * q) L (Nat.mul_pos hh hq) hL
    (Nat.mul_comm _ _) p hp0 hp
  convert H using 1

end Problem355.IntegerSamplingPairs

end

end OAI
