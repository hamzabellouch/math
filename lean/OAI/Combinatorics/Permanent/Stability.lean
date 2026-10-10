import OAI.Combinatorics.Permanent.Model

namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Quantitative exponent-two stability estimates. -/
def rowSq (a : Site → ℝ) : ℝ := ∑ j, a j ^ 2

def rowDist (a : Site → ℝ) : ℝ := ∑ j, (a j - 1) ^ 2

def rowDot (a b : Site → ℝ) : ℝ := ∑ j, a j * b j

def pairEntries (a b : Site → ℝ) : Fin 6 → ℝ :=
  ![a 0 * b 1 + a 1 * b 0,
    a 0 * b 2 + a 2 * b 0,
    a 0 * b 3 + a 3 * b 0,
    a 1 * b 2 + a 2 * b 1,
    a 1 * b 3 + a 3 * b 1,
    a 2 * b 3 + a 3 * b 2]

def pairSq (a b : Site → ℝ) : ℝ := ∑ j, pairEntries a b j ^ 2

theorem rowSq_nonneg (a : Site → ℝ) : 0 ≤ rowSq a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rowDist_nonneg (a : Site → ℝ) : 0 ≤ rowDist a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pairSq_nonneg (a b : Site → ℝ) : 0 ≤ pairSq a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pairSq_identity (a b : Site → ℝ) :
    pairSq a b = rowSq a * rowSq b + rowDot a b ^ 2 -
      2 * ∑ j, (a j * b j) ^ 2 := by
  simp only [pairSq, pairEntries, rowSq, rowDot, Fin.sum_univ_six,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem pairSq_comm (a b : Site → ℝ) : pairSq a b = pairSq b a := by
  simp only [pairSq_identity, rowDot, mul_comm]

theorem rowDot_sq_le (a b : Site → ℝ) :
    rowDot a b ^ 2 ≤ rowSq a * rowSq b :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

theorem rowDot_sq_le_four (a b : Site → ℝ) :
    rowDot a b ^ 2 ≤ 4 * ∑ j, (a j * b j) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Site => (1 : ℝ)) (fun j => a j * b j)
  simpa [rowDot] using h

theorem pair_stability_one (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) :
    rowDist a ≤ 9 * (24 - pairSq a b) := by
  let t := rowDot a b
  let s := ∑ j, (a j * b j) ^ 2
  let d := ∑ j, (a j - b j) ^ 2
  let e := ∑ j, (a j * b j - 1) ^ 2
  let D := 24 - pairSq a b
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (hb j)
  have ht2 : t ^ 2 ≤ 16 := by
    have h := rowDot_sq_le a b
    rw [haq, hbq] at h
    norm_num at h
    exact h
  have ht4 : t ≤ 4 := by nlinarith
  have htprod : 0 ≤ t * (4 - t) := mul_nonneg ht0 (by linarith)
  have hts : t ^ 2 ≤ 4 * s := rowDot_sq_le_four a b
  have hD : D = 8 - t ^ 2 + 2 * s := by
    dsimp [D, t, s]
    rw [pairSq_identity, haq, hbq]
    ring
  have hd : d = 8 - 2 * t := by
    have h : d = rowSq a + rowSq b - 2 * t := by
      dsimp [d, rowSq, t, rowDot]
      simp only [Fin.sum_univ_four]
      ring
    rw [h, haq, hbq]
    ring
  have he : e = s - 2 * t + 4 := by
    dsimp [e, s, t, rowDot]
    simp only [Fin.sum_univ_four]
    ring
  have hdD : d ≤ D := by nlinarith
  have heD : 2 * e ≤ D := by nlinarith
  have hpoint (j : Site) : (a j - 1) ^ 2 ≤
      8 * (a j - b j) ^ 2 + 2 * (a j * b j - 1) ^ 2 := by
    have haj : a j ^ 2 ≤ 4 := by
      calc
        a j ^ 2 ≤ rowSq a :=
          Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
        _ = 4 := haq
    have h1 : (a j - 1) ^ 2 ≤ (a j ^ 2 - 1) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg (ha j) (show 0 ≤ a j + 2 by linarith [ha j]))
        (sq_nonneg (a j - 1))]
    have h2 : (a j ^ 2 - a j * b j) ^ 2 ≤ 4 * (a j - b j) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 4 - a j ^ 2 by linarith)
        (sq_nonneg (a j - b j))]
    nlinarith [sq_nonneg (a j ^ 2 - 2 * a j * b j + 1)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Site)) => hpoint j)
  have hbound : rowDist a ≤ 8 * d + 2 * e := by
    simpa only [rowDist, Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  linarith

theorem pair_stability (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) :
    rowDist a + rowDist b ≤ 18 * (24 - pairSq a b) := by
  have h1 := pair_stability_one a b ha hb haq hbq
  have h2 := pair_stability_one b a hb ha hbq haq
  rw [pairSq_comm b a] at h2
  linarith


theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℝ) :
    ∑ σ, f σ = ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm f]
  exact Fintype.sum_prod_type _

theorem decompose4_two (i : Fin 4) (e : Equiv.Perm (Fin 3)) :
    Equiv.Perm.decomposeFin.symm (i, e) 2 = Equiv.swap 0 i (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 1

theorem decompose4_three (i : Fin 4) (e : Equiv.Perm (Fin 3)) :
    Equiv.Perm.decomposeFin.symm (i, e) 3 = Equiv.swap 0 i (e 2).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 2

theorem decompose3_two (i : Fin 3) (e : Equiv.Perm (Fin 2)) :
    Equiv.Perm.decomposeFin.symm (i, e) 2 = Equiv.swap 0 i (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 1

theorem permanent_pair_identity (f : Functions) :
    (∑ π : Perm, ∏ i, f i (π i)) =
      ∑ j : Fin 6, pairEntries (f 0) (f 1) j *
        pairEntries (f 2) (f 3) (Fin.rev j) := by
  change (∑ π : Equiv.Perm (Fin 4), ∏ i : Fin 4, f i (π i)) = _
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    Fin.prod_univ_four, pairEntries]
  simp [decompose4_two, decompose4_three, decompose3_two,
    Equiv.swap_apply_def, Fin.rev]
  ring


def uniformLaw : Law := fun _ => 1 / 24

def totalDist (f : Functions) : ℝ := ∑ i, rowDist (f i)

theorem totalDist_nonneg (f : Functions) : 0 ≤ totalDist f :=
  Finset.sum_nonneg fun i _ => rowDist_nonneg (f i)

theorem pairSq_le (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) : pairSq a b ≤ 24 := by
  have h := pair_stability_one a b ha hb haq hbq
  have h0 := rowDist_nonneg a
  linarith

theorem uniform_expectation_eq (f : Functions) :
    permanentExpectation uniformLaw f = (∑ π : Perm, ∏ i, f i (π i)) / 24 := by
  simp only [permanentExpectation, uniformLaw, ← Finset.mul_sum]
  ring

theorem normalized_uniform_stability (f : Functions)
    (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation uniformLaw f ≤ 1 - totalDist f / 1728 := by
  let P := permanentExpectation uniformLaw f
  let U := pairSq (f 0) (f 1)
  let V := pairSq (f 2) (f 3)
  have hU0 : 0 ≤ U := pairSq_nonneg _ _
  have hV0 : 0 ≤ V := pairSq_nonneg _ _
  have hU : U ≤ 24 := pairSq_le _ _ (hf 0) (hf 1) (hn 0) (hn 1)
  have hV : V ≤ 24 := pairSq_le _ _ (hf 2) (hf 3) (hn 2) (hn 3)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (pairEntries (f 0) (f 1)) (fun j => pairEntries (f 2) (f 3) (Fin.rev j))
  have hrev : (∑ j : Fin 6, pairEntries (f 2) (f 3) (Fin.rev j) ^ 2) = V :=
    Equiv.sum_comp Fin.revPerm (fun j => pairEntries (f 2) (f 3) j ^ 2)
  rw [← permanent_pair_identity, hrev] at hcs
  change (∑ π : Perm, ∏ i, f i (π i)) ^ 2 ≤ U * V at hcs
  have hP2 : 576 * P ^ 2 ≤ U * V := by
    dsimp [P]
    rw [uniform_expectation_eq]
    nlinarith [hcs]
  have hUV : U * V ≤ 12 * (U + V) := by
    nlinarith [mul_nonneg hU0 (show 0 ≤ 24 - V by linarith),
      mul_nonneg hV0 (show 0 ≤ 24 - U by linarith)]
  have hd : totalDist f ≤ 18 * (48 - U - V) := by
    have h1 := pair_stability _ _ (hf 0) (hf 1) (hn 0) (hn 1)
    have h2 := pair_stability _ _ (hf 2) (hf 3) (hn 2) (hn 3)
    simp only [totalDist, Fin.sum_univ_four]
    dsimp [U, V]
    linarith
  change P ≤ _
  nlinarith [sq_nonneg (P - 1)]

end FourRow
end

end OAI
