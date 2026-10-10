import OAI.Probability.SwitchChain.PairFibers

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.IndependentCell

variable {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]

def jointCount (X : Ω → α) (Y : Ω → β) (x : α) (y : β) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ω => X ω = x ∧ Y ω = y)).card

theorem sum_coordinate_product (X : Ω → α) (Y : Ω → β)
    (f : α → ℝ) (g : β → ℝ) :
    (∑ ω, f (X ω) * g (Y ω)) =
      ∑ x, ∑ y, (jointCount X Y x y : ℝ) * f x * g y := by
  classical
  have h := Finset.sum_fiberwise (Finset.univ : Finset Ω)
    (fun ω => (X ω, Y ω)) (fun ω => f (X ω) * g (Y ω))
  rw [Fintype.sum_prod_type] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hf : (Finset.univ.filter (fun ω => (X ω, Y ω) = (x,y))) =
      Finset.univ.filter (fun ω => X ω = x ∧ Y ω = y) := by
    ext ω
    simp
  rw [hf]
  calc
    _ = ∑ _ω ∈ Finset.univ.filter (fun ω => X ω = x ∧ Y ω = y), f x * g y := by
      apply Finset.sum_congr rfl
      intro ω hω
      obtain ⟨hx,hy⟩ := (Finset.mem_filter.mp hω).2
      rw [hx,hy]
    _ = _ := by simp [jointCount, mul_assoc]

theorem sum_product_of_jointCount (X : Ω → α) (Y : Ω → β)
    (a : α → ℝ) (b : β → ℝ)
    (hcount : ∀ x y, (jointCount X Y x y : ℝ) = a x * b y)
    (f : α → ℝ) (g : β → ℝ) :
    (∑ ω, f (X ω) * g (Y ω)) =
      (∑ x, a x * f x) * (∑ y, b y * g y) := by
  rw [sum_coordinate_product]
  simp_rw [hcount]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem independent_of_jointCount (X : Ω → α) (Y : Ω → β)
    (a : α → ℝ) (b : β → ℝ)
    (hcount : ∀ x y, (jointCount X Y x y : ℝ) = a x * b y)
    (f : α → ℝ) (g : β → ℝ) :
    (∑ ω, f (X ω) * g (Y ω)) =
      (∑ ω, f (X ω)) * (∑ ω, g (Y ω)) / (Fintype.card Ω : ℝ) := by
  classical
  by_cases hΩ : Fintype.card Ω = 0
  · have : IsEmpty Ω := Fintype.card_eq_zero_iff.mp hΩ
    simp
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hΩ
  have hNprod := sum_product_of_jointCount X Y a b hcount (fun _ => 1) (fun _ => 1)
  have hf := sum_product_of_jointCount X Y a b hcount f (fun _ => 1)
  have hg := sum_product_of_jointCount X Y a b hcount (fun _ => 1) g
  simp only [mul_one, one_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hNprod hf hg
  rw [sum_product_of_jointCount X Y a b hcount, hf, hg]
  apply (eq_div_iff hN).mpr
  rw [hNprod]
  ring

theorem inner_eq_sum (f g : EuclideanSpace ℝ Ω) :
    ⟪f,g⟫ = ∑ ω, f ω * g ω := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem sum_expectation (R : Setoid Ω) (f : EuclideanSpace ℝ Ω) :
    (∑ ω, PairFibers.expectation R f ω) = ∑ ω, f ω := by
  let one : EuclideanSpace ℝ Ω := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hone : one ∈ PairFibers.constantSubspace R := by
    intro x y hxy
    rfl
  have h := Submodule.starProjection_inner_eq_zero f one hone
  change ⟪f - PairFibers.expectation R f, one⟫ = 0 at h
  rw [inner_sub_left, inner_eq_sum, inner_eq_sum] at h
  simp only [one, mul_one] at h
  linarith

theorem projection_covariance_of_jointCount (X : Ω → α) (Y : Ω → β)
    (a : α → ℝ) (b : β → ℝ)
    (hcount : ∀ x y, (jointCount X Y x y : ℝ) = a x * b y)
    (f g : EuclideanSpace ℝ Ω) :
    ⟪PairFibers.expectation (Setoid.ker X) f,
      PairFibers.expectation (Setoid.ker Y) g⟫ =
      (∑ ω, f ω) * (∑ ω, g ω) / (Fintype.card Ω : ℝ) := by
  let p := PairFibers.expectation (Setoid.ker X) f
  let q := PairFibers.expectation (Setoid.ker Y) g
  have hp : Function.FactorsThrough (fun ω => p ω) X := by
    intro ω ν h
    exact PairFibers.expectation_constant (Setoid.ker X) f h
  have hq : Function.FactorsThrough (fun ω => q ω) Y := by
    intro ω ν h
    exact PairFibers.expectation_constant (Setoid.ker Y) g h
  obtain ⟨u,hu⟩ := (Function.factorsThrough_iff (fun ω => p ω)).mp hp
  obtain ⟨v,hv⟩ := (Function.factorsThrough_iff (fun ω => q ω)).mp hq
  have h := independent_of_jointCount X Y a b hcount u v
  have hup (ω : Ω) : u (X ω) = p ω := congrFun hu ω |>.symm
  have hvq (ω : Ω) : v (Y ω) = q ω := congrFun hv ω |>.symm
  simp_rw [hup,hvq] at h
  rw [inner_eq_sum]
  change (∑ ω, p ω * q ω) = _
  rw [h]
  change (∑ ω, PairFibers.expectation (Setoid.ker X) f ω) *
    (∑ ω, PairFibers.expectation (Setoid.ker Y) g ω) / _ = _
  rw [sum_expectation, sum_expectation]

end Problem315.IndependentCell

end

end OAI
