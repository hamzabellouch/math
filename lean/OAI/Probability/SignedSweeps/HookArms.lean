import OAI.Probability.SignedSweeps.BetaNumbers

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def IsSignedHook (q : ℕ) (lam : YoungDiagram) : Prop := lam.rowLen q ≤ q

lemma signedHook_no_southeast {q : ℕ} {lam : YoungDiagram}
    (h : IsSignedHook q lam) {i j : ℕ} (hm : (i,j) ∈ lam) : i < q ∨ j < q := by
  have hj := YoungDiagram.mem_iff_lt_rowLen.mp hm
  by_cases hi : i < q
  · exact Or.inl hi
  · have hh := lam.rowLen_anti q i (Nat.le_of_not_gt hi)
    unfold IsSignedHook at h
    right
    omega

lemma IsSignedHook.transpose {q : ℕ} {lam : YoungDiagram}
    (h : IsSignedHook q lam) : IsSignedHook q lam.transpose := by
  rw [IsSignedHook, YoungDiagram.rowLen_transpose]
  by_contra hh
  have hm : (q,q) ∈ lam := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hh)
  rcases signedHook_no_southeast h hm with hi | hj <;> omega

lemma signedHook_colLen_le {q j : ℕ} {lam : YoungDiagram}
    (h : IsSignedHook q lam) (hj : q ≤ j) : lam.colLen j ≤ q := by
  by_contra hh
  have hm := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hh)
  rcases signedHook_no_southeast h hm with hi | hk <;> omega

lemma rowLen_le_card (lam : YoungDiagram) (i : ℕ) : lam.rowLen i ≤ lam.card := by
  rw [YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma colLen_le_card (lam : YoungDiagram) (j : ℕ) : lam.colLen j ≤ lam.card := by
  rw [← YoungDiagram.rowLen_transpose]
  simpa [YoungDiagram.card, YoungDiagram.transpose] using rowLen_le_card lam.transpose j

lemma boxHook_le_twice_card (lam : YoungDiagram) (i j : ℕ) :
    boxHook lam i j ≤ 2 * lam.card := by
  have hr := rowLen_le_card lam i
  have hc := colLen_le_card lam j
  unfold boxHook
  omega

def rightHookProduct (q : ℕ) (lam : YoungDiagram) : ℕ :=
  ∏ c ∈ lam.cells.filter (fun c => q ≤ c.2), boxHook lam c.1 c.2

lemma prod_right_cells {M : Type*} [CommMonoid M] {q : ℕ} (lam : YoungDiagram)
    (h : IsSignedHook q lam) (f : ℕ → ℕ → M) :
    (∏ c ∈ lam.cells.filter (fun c => q ≤ c.2), f c.1 c.2) =
      ∏ i : Fin q, ∏ j : Fin (lam.rowLen i - q), f i (q + j) := by
  rw [← Fintype.prod_sigma (fun z : Σ i : Fin q, Fin (lam.rowLen i - q) => f z.1 (q + z.2))]
  apply Finset.prod_bij (fun c hc =>
    (⟨⟨c.1, by
      have hm := (Finset.mem_filter.mp hc).1
      have hj := (Finset.mem_filter.mp hc).2
      exact (signedHook_no_southeast h hm).resolve_right (Nat.not_lt.mpr hj)⟩,
      ⟨c.2 - q, by
        have hm := YoungDiagram.mem_iff_lt_rowLen.mp (Finset.mem_filter.mp hc).1
        have hj := (Finset.mem_filter.mp hc).2
        change c.2 - q < lam.rowLen c.1 - q
        omega⟩⟩ : Σ i : Fin q, Fin (lam.rowLen i - q)))
  · intro c hc; exact Finset.mem_univ _
  · intro a ha b hb he
    have hr := congrArg (fun z : Σ i : Fin q, Fin (lam.rowLen i - q) => z.1.val) he
    have hc := congrArg (fun z : Σ i : Fin q, Fin (lam.rowLen i - q) => z.2.val) he
    have haq := (Finset.mem_filter.mp ha).2
    have hbq := (Finset.mem_filter.mp hb).2
    exact Prod.ext hr (by dsimp at hc; omega)
  · intro b hb
    refine ⟨(b.1.val, q + b.2.val), Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
    · apply YoungDiagram.mem_iff_lt_rowLen.mpr
      have ht := b.2.isLt
      omega
    · apply Sigma.ext
      · rfl
      · apply (Fin.heq_ext_iff (by rfl)).mpr
        exact Nat.add_sub_cancel_left q b.2.val
  · intro a ha
    have hq := (Finset.mem_filter.mp ha).2
    dsimp
    rw [Nat.add_sub_of_le hq]

lemma right_hook_le {q : ℕ} (lam : YoungDiagram) (h : IsSignedHook q lam)
    (i : Fin q) (j : Fin (lam.rowLen i - q)) :
    boxHook lam i (q + j) ≤ (lam.rowLen i - q) - j + q := by
  have hc := signedHook_colLen_le h (Nat.le_add_right q j.val)
  unfold boxHook
  omega

lemma arm_factorial_bound (r q B : ℕ) (hB : r + q ≤ B) :
    (∏ j : Fin r, (r - j.val + q)) ≤ r.factorial * B ^ q := by
  have hmul : (∏ j : Fin r, (r - j.val + q)) * q.factorial = (r + q).factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j => r - j + q) r]
    have he : ∀ j ∈ Finset.range r, r - j + q = r + q - j := by
      intro j hj
      have := Finset.mem_range.mp hj
      omega
    rw [Finset.prod_congr rfl he, ← Nat.descFactorial_eq_prod_range]
    have hh := Nat.factorial_mul_descFactorial (Nat.le_add_right r q)
    simpa only [Nat.add_sub_cancel_left, mul_comm] using hh
  have hle : (∏ j : Fin r, (r - j.val + q)) ≤ (r + q).factorial := by
    calc
      _ = (∏ j : Fin r, (r - j.val + q)) * 1 := (mul_one _).symm
      _ ≤ (∏ j : Fin r, (r - j.val + q)) * q.factorial :=
        Nat.mul_le_mul_left _ (Nat.factorial_pos q)
      _ = _ := hmul
  have he : (r + q).factorial = r.factorial * (r + q).descFactorial q := by
    have hh := Nat.factorial_mul_descFactorial (Nat.le_add_left q r)
    simpa only [Nat.add_sub_cancel_right, mul_comm] using hh.symm
  rw [he] at hle
  apply hle.trans
  apply Nat.mul_le_mul_left
  rw [Nat.descFactorial_eq_prod_range]
  calc
    _ ≤ ∏ _j ∈ Finset.range q, B := Finset.prod_le_prod (fun j hj => (Nat.sub_le _ _).trans hB)
    _ = B ^ q := by simp

theorem rightHookProduct_le {q : ℕ} (lam : YoungDiagram) (h : IsSignedHook q lam)
    (a : Fin q → ℕ) (ha : ∀ i : Fin q, lam.rowLen i - q ≤ a i)
    (B : ℕ) (hB : lam.card + q ≤ B) :
    rightHookProduct q lam ≤ (∏ i, (a i).factorial) * B ^ (q * q) := by
  rw [rightHookProduct, prod_right_cells lam h]
  have hrow (i : Fin q) : (∏ j : Fin (lam.rowLen i - q), boxHook lam i (q+j)) ≤
      (a i).factorial * B ^ q := by
    calc
      _ ≤ ∏ j : Fin (lam.rowLen i - q), ((lam.rowLen i - q) - j.val + q) :=
        Finset.prod_le_prod (fun j _ => right_hook_le lam h i j)
      _ ≤ (lam.rowLen i - q).factorial * B ^ q := arm_factorial_bound _ _ _ (by
        have hr := rowLen_le_card lam i
        omega)
      _ ≤ (a i).factorial * B ^ q := Nat.mul_le_mul_right _ (Nat.factorial_le (ha i))
  calc
    _ ≤ ∏ i : Fin q, ((a i).factorial * B ^ q) := Finset.prod_le_prod (fun i _ => hrow i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [← pow_mul]

end SignedSweeps
end

end OAI
