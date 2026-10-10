import OAI.Probability.RadialTransition.RadialKernel

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem symmetric_row_quadratic {I : Type uI} [Fintype I] (J : I → I → ℝ) (n : I → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsymm : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, (n i) ^ 2 := by
  have ht (i j : I) : 2 * (J i j * n i * n j) ≤
      J i j * (n i ^ 2 + n j ^ 2) := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hl := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => ht i j
  have hs : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsymm]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hl
  rw [hs] at hl
  have hb : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem core_ordered_lower_small_diameter {V : Type uV} [Fintype V] [DecidableEq V] {t : ℝ} (ht : 0 ≤ t)
    (x : V → Position) (hx : ∀ i j, dist (x i) (x j) ≤ 1) :
    t ^ 2 / 4 * (Fintype.card V : ℝ) ^ 2 - t ^ 2 * Fintype.card V ≤
      ∑ i, ∑ j, if i ≠ j then coreReal t (dist (x i) (x j)) else 0 := by
  classical
  let G := shellGraph x (microLength t)
  have hG : G.CliqueFree 5 := shellGraph_cliqueFree x (microLength_pos t)
  have hbound : (8 : ℝ) * G.edgeFinset.card ≤ 3 * (Fintype.card V : ℝ) ^ 2 := by
    have hh : 8 * G.edgeFinset.card ≤ 3 * Fintype.card V ^ 2 := by
      simpa using shell_edge_bound G hG
    exact_mod_cast hh
  have hterm (i j : V) :
      t ^ 2 * ((if i ≠ j then (1 : ℝ) else 0) - (if G.Adj i j then 1 else 0)) ≤
      (if i ≠ j then coreReal t (dist (x i) (x j)) else 0) := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_left hij]
      by_cases hA : G.Adj i j
      · simp only [hA, ite_true, sub_self, mul_zero]
        exact coreReal_nonneg _ _
      · simp only [hA, ite_false, sub_zero, mul_one]
        rw [coreReal_full_of_not_shell ht (hx i j)]
        intro h
        exact hA ⟨hij, h⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm i j
  have hcount : (∑ i : V, ∑ j : V, if i ≠ j then (1 : ℝ) else 0) =
      (Fintype.card V : ℝ) ^ 2 - Fintype.card V := by
    have hite (i j : V) : (if i ≠ j then (1 : ℝ) else 0) =
        1 - (if i = j then 1 else 0) := by by_cases h : i = j <;> simp [h]
    simp_rw [hite]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hcount, sum_adj_indicator G] at hsum
  have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg t)
  nlinarith [hsum, hb]

def occupation {V : Type uV} {I : Type uI} [Fintype V] (q : V → I) (i : I) : ℝ := by
  classical
  exact (Fintype.card {a : V // q a = i} : ℝ)

theorem sum_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I] (q : V → I) :
    ∑ i, occupation q i = Fintype.card V := by
  classical
  simpa [occupation] using Fintype.sum_fiberwise q (fun _ => (1 : ℝ))

theorem sum_subtype_le_of_nonneg {V : Type uV} [Fintype V] (p : V → Prop)
    (f : V → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (by classical exact ∑ a : {a // p a}, f a) ≤ ∑ a, f a := by
  classical
  have hh := Fintype.sum_subtype_add_sum_subtype p f
  have hz : 0 ≤ ∑ a : {a // ¬p a}, f a := Finset.sum_nonneg (fun a _ => hf a)
  linarith

theorem core_ordered_cells {V : Type uV} {I : Type uI} [Fintype V] [Fintype I] [DecidableEq V]
    {t : ℝ} (ht : 0 ≤ t) (q : V → I) (x : V → Position)
    (c : V → V → ℝ) (hc : ∀ a b, 0 ≤ c a b)
    (hsame : ∀ a b, q a = q b → c a b = 1)
    (hdiam : ∀ a b, q a = q b → dist (x a) (x b) ≤ 1) :
    t ^ 2 / 4 * (∑ i, occupation q i ^ 2) - t ^ 2 * Fintype.card V ≤
      ∑ a, ∑ b, if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0 := by
  classical
  let F (a b : V) := if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0
  have hF (a b : V) : 0 ≤ F a b := by
    exact ite_nonneg (mul_nonneg (hc a b) (coreReal_nonneg _ _)) le_rfl
  have hlocal (i : I) : t ^ 2 / 4 * occupation q i ^ 2 - t ^ 2 * occupation q i ≤
      ∑ a : {a // q a = i}, ∑ b, F a b := by
    have hl := core_ordered_lower_small_diameter ht (fun a : {a // q a = i} => x a)
      (fun a b => hdiam a b (a.property.trans b.property.symm))
    change t ^ 2 / 4 * occupation q i ^ 2 - t ^ 2 * occupation q i ≤ _ at hl
    apply hl.trans
    apply Finset.sum_le_sum
    intro a _
    have heq : (∑ b : {b // q b = i},
        if a ≠ b then coreReal t (dist (x a) (x b)) else 0) =
        ∑ b : {b // q b = i}, F a b := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · subst b; simp [F]
      · have hab' : (a : V) ≠ (b : V) := fun hh => hab (Subtype.ext hh)
        simp [F, hab, hab', hsame a b (a.property.trans b.property.symm)]
    rw [heq]
    exact sum_subtype_le_of_nonneg (fun b => q b = i) (F a) (hF a)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  rw [Fintype.sum_fiberwise q (fun a => ∑ b, F a b)] at hs
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_occupation] using hs

theorem sum_by_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) (f : I → ℝ) :
    (∑ a, f (q a)) = ∑ i, occupation q i * f i := by
  classical
  rw [← Fintype.sum_fiberwise q (fun a => f (q a))]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun a : {a // q a = i} => f (q a)) = (fun _ => f i) := by
    funext a
    rw [a.property]
  rw [heq]
  simp [occupation]

theorem lifted_row_quadratic {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) (J : I → I → ℝ) {M : ℝ}
    (hJ : ∀ i j, 0 ≤ J i j) (hJsy : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    (∑ a, ∑ b, J (q a) (q b)) ≤ M * ∑ i, occupation q i ^ 2 := by
  classical
  have heq : (∑ a, ∑ b, J (q a) (q b)) =
      ∑ i, ∑ j, J i j * occupation q i * occupation q j := by
    calc
      _ = ∑ a, ∑ j, occupation q j * J (q a) j := by
        apply Finset.sum_congr rfl
        intro a _
        exact sum_by_occupation q (J (q a))
      _ = ∑ i, occupation q i * ∑ j, occupation q j * J i j :=
        sum_by_occupation q (fun i => ∑ j, occupation q j * J i j)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [heq]
  exact symmetric_row_quadratic J (occupation q) M hJ hJsy hrow

theorem modified_energy_cell_bound {N : ℕ} {I : Type uI} [Fintype I]
    {t M : ℝ} (ht : 0 ≤ t) (q : Fin N → I) (x : Fin N → Position)
    (c K : Fin N → Fin N → ℝ) (J : I → I → ℝ)
    (hc : ∀ a b, 0 ≤ c a b) (hcsy : ∀ a b, c a b = c b a)
    (hsame : ∀ a b, q a = q b → c a b = 1)
    (hdiam : ∀ a b, q a = q b → dist (x a) (x b) ≤ 1)
    (hK : ∀ a b, 0 ≤ K a b) (hKsy : ∀ a b, K a b = K b a)
    (hKJ : ∀ a b, K a b ≤ J (q a) (q b))
    (hJ : ∀ i j, 0 ≤ J i j) (hJsy : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    (t ^ 2 / 8 - M / 2) * (∑ i, occupation q i ^ 2) - t ^ 2 / 2 * N ≤
      ∑ a, ∑ b with a < b, (c a b * coreReal t (dist (x a) (x b)) - K a b) := by
  classical
  have hcore := core_ordered_cells ht q x c hc hsame hdiam
  have hrow' := lifted_row_quadratic q J hJ hJsy hrow
  have hatt : (∑ a, ∑ b, if a ≠ b then K a b else 0) ≤
      M * ∑ i, occupation q i ^ 2 := by
    apply le_trans ?_ hrow'
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    apply le_trans ?_ (hKJ a b)
    split_ifs
    · exact le_rfl
    · exact hK a b
  have hpair := twice_pair_sum
    (fun a b => c a b * coreReal t (dist (x a) (x b)) - K a b)
    (fun a b => by rw [hcsy a b, dist_comm (x a), hKsy a b])
  have heq : (∑ a, ∑ b, if a ≠ b then
      c a b * coreReal t (dist (x a) (x b)) - K a b else 0) =
      (∑ a, ∑ b, if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0) -
      (∑ a, ∑ b, if a ≠ b then K a b else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [hab]
  rw [heq] at hpair
  simp only [Fintype.card_fin] at hcore
  nlinarith

end RadialTransition

end

end OAI
