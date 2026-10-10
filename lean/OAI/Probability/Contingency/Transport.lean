import Mathlib
import OAI.Probability.Contingency.Signature

namespace OAI

/-! Transport. -/

noncomputable section

open scoped BigOperators
open QuadraticMap
open scoped BigOperators
open QuadraticMap

namespace Contingency

 

section FutureSquare
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

 

omit [FiniteDimensional ℝ V] in
theorem pair_mixed_telescope (D : ℕ) (S : ℕ → V →ₗ[ℝ] ℝ) (sD : S D = 0)
    (h : V) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (D+1), pairPrevious S j h * g j) =
      ∑ j ∈ Finset.range (D+1), S j h * g (j+1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp [pairPrevious, sD]

 

omit [FiniteDimensional ℝ V] in
theorem future_square_sequence (D : ℕ) (u : ℕ → ℝ)
    (S : ℕ → V →ₗ[ℝ] ℝ) (Q : ℕ → QuadraticForm ℝ V)
    (u0 : u 0 = 0) (uD : u D = 0) (uNext : u (D+1) = 0) (sD : S D = 0)
    (h : V) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (D+1),
      pairForm (Q j) (pairPrevious S j) (S j)
        (u (j-1)) (u j) (u (j+1)) (h,g j,-g (j+1))) -
      (∑ j ∈ Finset.range (D+1), Q j h) =
    ∑ j ∈ Finset.range (D+1), u j * (g (j+1) - g j)^2 := by
  have hm := pair_mixed_telescope D S sD h g
  have hp : (∑ j ∈ Finset.range (D+1), u (j-1) * g j ^ 2) =
      ∑ j ∈ Finset.range (D+1), u j * g (j+1)^2 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp [u0,uD]
  have hn : (∑ j ∈ Finset.range (D+1), u (j+1) * g (j+1)^2) =
      ∑ j ∈ Finset.range (D+1), u j * g j^2 := by
    have hw := Finset.sum_range_succ' (fun j => u j * g j^2) (D+1)
    rw [Finset.sum_range_succ, uNext, u0] at hw
    simpa using hw.symm
  simp only [pairForm_apply]
  have he (j : ℕ) :
      Q j h + 2 * (pairPrevious S j) h * g j + 2 * S j h * -g (j+1) +
        u (j-1) * g j^2 + 2 * u j * g j * -g (j+1) + u (j+1) * (-g (j+1))^2 =
      Q j h + 2 * ((pairPrevious S j) h * g j) - 2 * (S j h * g (j+1)) +
        u (j-1) * g j^2 - 2 * (u j * g j * g (j+1)) + u (j+1) * g (j+1)^2 := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm, hp, hn]
  symm
  calc
    _ = ∑ j ∈ Finset.range (D+1),
        (u j * g (j+1)^2 - 2 * (u j * g j * g (j+1)) + u j * g j^2) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]; ring

omit [FiniteDimensional ℝ V] in
theorem future_square_nonneg (D : ℕ) (u : ℕ → ℝ)
    (S : ℕ → V →ₗ[ℝ] ℝ) (Q : ℕ → QuadraticForm ℝ V)
    (hu : ∀ j, 0 ≤ u j) (u0 : u 0 = 0) (uD : u D = 0)
    (uNext : u (D+1) = 0) (sD : S D = 0) (h : V) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (D+1), Q j h) ≤
      ∑ j ∈ Finset.range (D+1), pairForm (Q j) (pairPrevious S j) (S j)
        (u (j-1)) (u j) (u (j+1)) (h,g j,-g (j+1)) := by
  have he := future_square_sequence D u S Q u0 uD uNext sD h g
  have hn : 0 ≤ ∑ j ∈ Finset.range (D+1), u j * (g (j+1)-g j)^2 := by
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hu j) (sq_nonneg _))
  linarith

end FutureSquare

section ActualFuture
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem PositiveSlice.nonneg {f : (ι → ℤ) → ℝ} {B : ι → ℤ} {T : ℤ}
    (hf : PositiveSlice f B T) (p : ι → ℤ) : 0 ≤ f p := by
  by_cases h : InBox B p ∧ (∑ i, p i) = T
  · exact (hf.1 p h.1 h.2).le
  · rw [hf.2 p h]

 

theorem actual_future_square (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C T : ℤ)
    (hf : PositiveSlice f (pairAssembly B C C) T) (p : ι → ℤ) (D : ℕ)
    (h : ι → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (D+1),
      matrixForm (twoRemoval f (pairAssembly p (j:ℤ) ((D:ℤ)-j)))
        (pairAssembly h (g j) (-g (j+1)))) -
      matrixForm (twoRemoval (balancedMarginal f D) p) h =
    ∑ j ∈ Finset.range (D+1), pairU f p D j * (g (j+1)-g j)^2 := by
  have hb (j : ℕ) := congrArg (fun Q : QuadraticForm ℝ ((ι → ℝ) × ℝ × ℝ) =>
      Q (h,g j,-g (j+1))) (pair_block_identity f B C T hf p D j)
  have hp : matrixForm (twoRemoval (balancedMarginal f D) p) =
      ∑ j ∈ Finset.range (D+1), pairQ f p D j :=
    matrixForm_sum (Finset.range (D+1))
      (fun j i k => f (pairAssembly (removePair p i k) (j:ℤ) ((D:ℤ)-j)))
  simp only [QuadraticMap.comp_apply, pairAssemblyLinear, LinearMap.coe_mk,
    AddHom.coe_mk] at hb
  simp only [hb, hp, sum_apply]
  exact future_square_sequence D (pairU f p D) (pairS f p D) (pairQ f p D)
    (pairU_zero f B C T hf p D 0 (Or.inl rfl))
    (pairU_zero f B C T hf p D D (Or.inr le_rfl))
    (pairU_zero f B C T hf p D (D+1) (Or.inr (by omega)))
    (pairS_top f B C T hf p D) h g

theorem actual_future_monotone (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C T : ℤ)
    (hf : PositiveSlice f (pairAssembly B C C) T) (p : ι → ℤ) (D : ℕ)
    (h : ι → ℝ) (g : ℕ → ℝ) :
    matrixForm (twoRemoval (balancedMarginal f D) p) h ≤
      ∑ j ∈ Finset.range (D+1),
        matrixForm (twoRemoval f (pairAssembly p (j:ℤ) ((D:ℤ)-j)))
          (pairAssembly h (g j) (-g (j+1))) := by
  have he := actual_future_square f B C T hf p D h g
  have hn : 0 ≤ ∑ j ∈ Finset.range (D+1), pairU f p D j * (g (j+1)-g j)^2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hf.nonneg _) (sq_nonneg _)
  linarith

 

noncomputable def raisedMarginal (f : (ι ⊕ Bool → ℤ) → ℝ) (C : ℕ) (p : ι → ℤ) : ℝ :=
  ∑ j : Fin C, ((j.val+1:ℕ):ℝ) * ((C-j.val:ℕ):ℝ) *
    f (pairAssembly p ((j.val+1:ℕ):ℤ) ((C-j.val:ℕ):ℤ))

omit [DecidableEq ι] in
theorem raisedMarginal_positive (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (hC : 0 < C) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T) :
    PositiveSlice (raisedMarginal f C) B (T-(C+1:ℕ)) := by
  constructor
  · intro p hp ht
    apply Finset.sum_pos
    · intro j _
      have hj : j.val < C := j.isLt
      apply mul_pos
      · apply mul_pos <;> exact_mod_cast (by omega : 0 < _) 
      · apply hf.1
        · rw [pairAssembly_inBox]
          exact ⟨hp, by omega, by omega⟩
        · rw [pairAssembly_sum]
          omega
    · exact ⟨⟨0,hC⟩, Finset.mem_univ _⟩
  · intro p hp
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val < C := j.isLt
    have hz : f (pairAssembly p ((j.val+1:ℕ):ℤ) ((C-j.val:ℕ):ℤ)) = 0 := by
      apply hf.2
      rintro ⟨hb, ht⟩
      rw [pairAssembly_inBox] at hb
      rw [pairAssembly_sum] at ht
      exact hp ⟨hb.1, by omega⟩
    simp only [hz, mul_zero]

end ActualFuture

section BalancedStep
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def holeFunctional (f : (ι → ℤ) → ℝ) (p : ι → ℤ) (h : ι → ℝ) : ℝ :=
  ∑ i, f (removeOne p i) * h i

noncomputable def holePotential (f : (ι → ℤ) → ℝ) (p : ι → ℤ) (h : ι → ℝ) : ℝ :=
  ∑ i, f (removeOne p i) * h i ^ 2

omit [Fintype ι] in
theorem removeOne_pair_old (p : ι → ℤ) (a b : ℤ) (i : ι) :
    removeOne (pairAssembly p a b) (Sum.inl i) = pairAssembly (removeOne p i) a b := by
  funext j
  rcases j with j | b'
  · simp [removeOne, pairAssembly]
  · cases b' <;> simp [removeOne, pairAssembly]

omit [Fintype ι] in
theorem removeOne_pair_first (p : ι → ℤ) (a b : ℤ) :
    removeOne (pairAssembly p a b) (Sum.inr true) = pairAssembly p (a-1) b := by
  funext j
  rcases j with j | b'
  · simp [removeOne, pairAssembly]
  · cases b' <;> simp [removeOne, pairAssembly]

omit [Fintype ι] in
theorem removeOne_pair_second (p : ι → ℤ) (a b : ℤ) :
    removeOne (pairAssembly p a b) (Sum.inr false) = pairAssembly p a (b-1) := by
  funext j
  rcases j with j | b'
  · simp [removeOne, pairAssembly]
  · cases b' <;> simp [removeOne, pairAssembly]

theorem holeFunctional_pair (f : (ι ⊕ Bool → ℤ) → ℝ)
    (p : ι → ℤ) (a b : ℤ) (h : ι → ℝ) (x y : ℝ) :
    holeFunctional f (pairAssembly p a b) (pairAssembly h x y) =
      (∑ i, f (pairAssembly (removeOne p i) a b) * h i) +
      f (pairAssembly p (a-1) b) * x + f (pairAssembly p a (b-1)) * y := by
  simp [holeFunctional, Fintype.sum_sum_type,
    removeOne_pair_old, removeOne_pair_first, removeOne_pair_second]
  ring

theorem holePotential_pair (f : (ι ⊕ Bool → ℤ) → ℝ)
    (p : ι → ℤ) (a b : ℤ) (h : ι → ℝ) (x y : ℝ) :
    holePotential f (pairAssembly p a b) (pairAssembly h x y) =
      (∑ i, f (pairAssembly (removeOne p i) a b) * h i^2) +
      f (pairAssembly p (a-1) b) * x^2 + f (pairAssembly p a (b-1)) * y^2 := by
  simp [holePotential, Fintype.sum_sum_type,
    removeOne_pair_old, removeOne_pair_first, removeOne_pair_second]
  ring

 

theorem holeFunctional_branch (f : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (C j : ℕ)
    (h : ι → ℝ) (g : ℕ → ℝ) :
    holeFunctional f (pairAssembly p (j:ℤ) ((C:ℤ)-j))
      (pairAssembly h (g j) (-g (j+1))) =
      pairS f p (C+1) j h + pairU f p (C+1) j * g j -
        pairU f p (C+1) (j+1) * g (j+1) := by
  rw [holeFunctional_pair]
  simp only [pairS, columnLinear_apply, pairU, Nat.cast_add, Nat.cast_one]
  have he1 : (C:ℤ)+1-1-j = C-j := by ring
  have he2 : (C:ℤ)+1-1-(j+1) = C-j-1 := by ring
  have he3 : (j:ℤ)+1-1 = j := by ring
  simp only [he1,he2,he3]
  ring

theorem parent_balance_sum (f : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (C : ℕ)
    (h : ι → ℝ) :
    holeFunctional (balancedMarginal f C) p h =
      ∑ j ∈ Finset.range (C+1), pairS f p (C+1) j h := by
  simp only [holeFunctional, balancedMarginal, pairS, columnLinear_apply,
    Nat.cast_add, Nat.cast_one, Finset.sum_mul]
  simp only [add_sub_cancel_right]
  exact Finset.sum_comm

theorem balanced_child (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (_hC : 2 ≤ C) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (p : ι → ℤ) (hp : InBox B p) (ht : (∑ i, p i) + (C+1:ℕ) = T+2)
    (h : ι → ℝ) (hbal : holeFunctional (balancedMarginal f C) p h = 0)
    (j : ℕ) (hj : j ≤ C) :
    let g := pairCumulative (C+1) (pairU f p (C+1)) (pairS f p (C+1)) h
    holeFunctional f (pairAssembly p (j:ℤ) ((C:ℤ)-j))
       (pairAssembly h (g j) (-g (j+1))) = 0 := by
  dsimp only
  rw [holeFunctional_branch]
  have hb : ∑ j ∈ Finset.range (C+1), pairS f p (C+1) j h = 0 := by
    rwa [parent_balance_sum] at hbal
  have hd := pairCumulative_difference (C+1) (pairU f p (C+1)) (pairS f p (C+1))
    (pairU_positive f B C T hf p hp (C+1) (by omega) ht) h hb j (by omega)
  linarith

theorem holePotential_branch (f : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (C j : ℕ)
    (h : ι → ℝ) (g : ℕ → ℝ) :
    holePotential f (pairAssembly p (j:ℤ) ((C:ℤ)-j))
      (pairAssembly h (g j) (-g (j+1))) =
      (∑ i, f (pairAssembly (removeOne p i) (j:ℤ) ((C:ℤ)-j)) * h i^2) +
      pairU f p (C+1) j * g j^2 + pairU f p (C+1) (j+1) * g (j+1)^2 := by
  rw [holePotential_pair]
  simp only [pairU, Nat.cast_add, Nat.cast_one, neg_sq]
  congr 2 <;> congr 2 <;> ring_nf

 
theorem child_potential_increment (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C : ℕ) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (p : ι → ℤ) (h : ι → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (C+1), holePotential f (pairAssembly p (j:ℤ) ((C:ℤ)-j))
       (pairAssembly h (g j) (-g (j+1)))) - holePotential (balancedMarginal f C) p h =
      2 * ∑ j ∈ Finset.range (C+2), pairU f p (C+1) j * g j^2 := by
  have h0 := pairU_zero f B (C:ℤ) T hf p (C+1) 0 (Or.inl rfl)
  have htop := pairU_zero f B (C:ℤ) T hf p (C+1) (C+1) (Or.inr le_rfl)
  have hmain : (∑ j ∈ Finset.range (C+1),
      ∑ i, f (pairAssembly (removeOne p i) (j:ℤ) ((C:ℤ)-j)) * h i^2) =
      holePotential (balancedMarginal f C) p h := by
    simp only [holePotential, balancedMarginal, Finset.sum_mul]
    exact Finset.sum_comm
  have hn : (∑ j ∈ Finset.range (C+1), pairU f p (C+1) (j+1) * g (j+1)^2) =
      ∑ j ∈ Finset.range (C+2), pairU f p (C+1) j * g j^2 := by
    have hw := Finset.sum_range_succ' (fun j => pairU f p (C+1) j * g j^2) (C+1)
    simpa only [h0, zero_mul, add_zero] using hw.symm
  have hp' : (∑ j ∈ Finset.range (C+1), pairU f p (C+1) j * g j^2) =
      ∑ j ∈ Finset.range (C+2), pairU f p (C+1) j * g j^2 := by
    have hw := Finset.sum_range_succ (fun j => pairU f p (C+1) j * g j^2) (C+1)
    simpa only [htop, zero_mul, add_zero] using hw.symm
  simp only [holePotential_branch, Finset.sum_add_distrib, hmain, hn, hp']
  ring

 
theorem balanced_potential_bound (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (hC : 2 ≤ C) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (hs : HasSignature f (pairAssembly B (C:ℤ) C) T)
    (p : ι → ℤ) (hp : InBox B p) (ht : (∑ i, p i) + (C+1:ℕ) = T+2)
    (h : ι → ℝ) (hbal : holeFunctional (balancedMarginal f C) p h = 0) :
    let g := pairCumulative (C+1) (pairU f p (C+1)) (pairS f p (C+1)) h
    (∑ j ∈ Finset.range (C+1), holePotential f (pairAssembly p (j:ℤ) ((C:ℤ)-j))
       (pairAssembly h (g j) (-g (j+1)))) ≤
      holePotential (balancedMarginal f C) p h -
      (∑ j ∈ Finset.range (C+2), ((j:ℝ) * (C+1-j)) • pairQ f p (C+1) j) h := by
  have hb : ∑ j ∈ Finset.range (C+1), pairS f p (C+1) j h = 0 := by
    rwa [parent_balance_sum] at hbal
  have hi := actual_pair_weighted f B C hC T hf hs p hp ht h hb
  have he := child_potential_increment f B C T hf p h
    (pairCumulative (C+1) (pairU f p (C+1)) (pairS f p (C+1)) h)
  dsimp
  linarith

 

theorem branch_demand_conservation_endpoints (F : (ι ⊕ Bool → ℤ) → ℝ)
    (C : ℕ) (p : ι → ℤ) (h : ι → ℝ) (g : ℕ → ℝ)
    (h0 : pairU F p (C+1) 0 = 0) (hC : pairU F p (C+1) (C+1) = 0) :
    (∑ j ∈ Finset.range (C+1),
      holeFunctional F (pairAssembly p (j:ℤ) ((C:ℤ)-j))
        (pairAssembly h (g j) (-g (j+1)))) =
      holeFunctional (balancedMarginal F C) p h := by
  have ht : (∑ j ∈ Finset.range (C+1), pairU F p (C+1) j * g j) =
      ∑ j ∈ Finset.range (C+1), pairU F p (C+1) (j+1) * g (j+1) := by
    have hleft := Finset.sum_range_succ (fun j => pairU F p (C+1) j * g j) (C+1)
    have hright := Finset.sum_range_succ' (fun j => pairU F p (C+1) j * g j) (C+1)
    rw [hC, zero_mul, add_zero] at hleft
    rw [h0, zero_mul, add_zero] at hright
    exact hleft.symm.trans hright
  simp only [holeFunctional_branch, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ht, add_sub_cancel_right, parent_balance_sum]

 

theorem branch_demand_conservation (f : (ι ⊕ Bool → ℤ) → ℝ)
    (B : ι → ℤ) (C : ℕ) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (H : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (h : ι → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (C+1),
      holeFunctional (fun x => f x * H x) (pairAssembly p (j:ℤ) ((C:ℤ)-j))
        (pairAssembly h (g j) (-g (j+1)))) =
      holeFunctional (balancedMarginal (fun x => f x * H x) C) p h := by
  let F := fun x => f x * H x
  have hz (j : ℕ) (hj : j = 0 ∨ C+1 ≤ j) : pairU F p (C+1) j = 0 := by
    change f _ * H _ = 0
    change pairU f p (C+1) j * H _ = 0
    rw [pairU_zero f B (C:ℤ) T hf p (C+1) j hj, zero_mul]
  have ht : (∑ j ∈ Finset.range (C+1), pairU F p (C+1) j * g j) =
      ∑ j ∈ Finset.range (C+1), pairU F p (C+1) (j+1) * g (j+1) := by
    have hleft := Finset.sum_range_succ (fun j => pairU F p (C+1) j * g j) (C+1)
    have hright := Finset.sum_range_succ' (fun j => pairU F p (C+1) j * g j) (C+1)
    rw [hz (C+1) (Or.inr le_rfl), zero_mul, add_zero] at hleft
    rw [hz 0 (Or.inl rfl), zero_mul, add_zero] at hright
    exact hleft.symm.trans hright
  change (∑ j ∈ Finset.range (C+1),
    holeFunctional F (pairAssembly p (j:ℤ) ((C:ℤ)-j))
      (pairAssembly h (g j) (-g (j+1)))) = holeFunctional (balancedMarginal F C) p h
  simp only [holeFunctional_branch, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ht, add_sub_cancel_right, parent_balance_sum]

end BalancedStep

section Star
variable {ι : Type*} [Fintype ι]

 

theorem weighted_star_bound (s h H : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hbal : ∑ i, s i * h i = 0) (a : ℝ) :
    (∑ i, s i * h i * H i)^2 ≤
      (∑ i, s i * h i^2) * (∑ i, s i * (H i-a)^2) := by
  have he : (∑ i, s i * h i * (H i-a)) = ∑ i, s i * h i * H i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hbal, zero_mul,
      sub_zero]
  rw [← he]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (hs i) (sq_nonneg _)
  · intro i _
    exact mul_nonneg (hs i) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

end Star

section WeightedKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def raisedFull (f : (ι ⊕ Bool → ℤ) → ℝ) (C : ℕ) (p : ι → ℤ) : ℝ :=
  ∑ j ∈ Finset.range (C+2), (j:ℝ) * ((C:ℝ)+1-j) *
    f (pairAssembly p (j:ℤ) ((C:ℤ)+1-j))

omit [Fintype ι] [DecidableEq ι] in
theorem raisedFull_eq (f : (ι ⊕ Bool → ℤ) → ℝ) (C : ℕ) :
    raisedFull f C = raisedMarginal f C := by
  funext p
  rw [raisedFull, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, sub_self, mul_zero,
    zero_mul, Nat.cast_zero, sub_zero, add_zero]
  rw [raisedMarginal, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val ≤ C := Nat.le_of_lt j.isLt
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hj]
  congr 2 <;> ring_nf

omit [DecidableEq ι] in
theorem raisedFull_positive (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (hC : 0 < C) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T) :
    PositiveSlice (raisedFull f C) B (T-(C+1:ℕ)) := by
  rw [raisedFull_eq]
  exact raisedMarginal_positive f B C hC T hf

theorem matrixForm_raisedFull (f : (ι ⊕ Bool → ℤ) → ℝ) (C : ℕ) (p : ι → ℤ) :
    matrixForm (twoRemoval (raisedFull f C) p) =
      ∑ j ∈ Finset.range (C+2), ((j:ℝ) * (C+1-j)) • pairQ f p (C+1) j := by
  change matrixForm (fun i k => ∑ j ∈ Finset.range (C+2),
    (j:ℝ) * ((C:ℝ)+1-j) * f (pairAssembly (removePair p i k) (j:ℤ) ((C:ℤ)+1-j))) = _
  rw [matrixForm_sum]
  apply Finset.sum_congr rfl
  intro j _
  ext h
  simp only [matrixForm_apply, pairQ, twoRemoval, smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrixForm_twoRemoval_add (f g : (ι → ℤ) → ℝ) (p : ι → ℤ) (h : ι → ℝ) :
    matrixForm (twoRemoval (fun x => f x + g x) p) h =
      matrixForm (twoRemoval f p) h + matrixForm (twoRemoval g p) h := by
  simp only [matrixForm_apply, twoRemoval, add_mul, Finset.sum_add_distrib]

theorem matrixForm_zero (p : ι → ℤ) (h : ι → ℝ) :
    matrixForm (twoRemoval (fun _ => 0) p) h = 0 := by
  simp [matrixForm_apply, twoRemoval]

omit [DecidableEq ι] in
theorem PositiveSlice.add {f g : (ι → ℤ) → ℝ} {B : ι → ℤ} {T : ℤ}
    (hf : PositiveSlice f B T) (hg : PositiveSlice g B T) :
    PositiveSlice (fun x => f x + g x) B T := by
  constructor
  · intro p hp ht
    exact add_pos (hf.1 p hp ht) (hg.1 p hp ht)
  · intro p hp
    simp only [hf.2 p hp, hg.2 p hp, add_zero]

end WeightedKernel

end Contingency

end

end OAI
