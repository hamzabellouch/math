import OAI.Analysis.OInfinity.ConnectedProperComparison

namespace OAI

/-! # The actual common-range binary row

Three orthogonal buffer isometries construct the full binary row in the
range of both forward shrinks. Its commutation with the prescribed rows
follows from the explicit zero-corner completion polynomial. This
discharges the common-range row premise of the preceding comparison.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- A proper three-row supplies the full binary row needed in the shrink
range, including commutation with any prescribed finite family. -/
lemma exists_buffer_shrink_range_pair [Nontrivial E]
    (R : Fin 3 → E)
    (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0) :
    let p := 1 - R 0 * star (R 0)
    p ≠ 0 ∧ ∃ d : Fin 2 → E,
      (∀ i j, star (d i) * d j = if i = j then p else 0) ∧
      (∑ i, d i * star (d i)) = p ∧
      ∀ x : E, (∀ j, Commute x (R j) ∧ Commute x (star (R j))) →
        ∀ i, Commute x (d i) ∧ Commute x (star (d i)) := by
  intro p
  have hdiag (j : Fin 3) : star (R j) * R j = 1 := by
    simpa only [ite_true] using hR j j
  have h01 : star (R 0) * R 1 = 0 := by simpa using hR 0 1
  have h02 : star (R 0) * R 2 = 0 := by simpa using hR 0 2
  have h12 : star (R 1) * R 2 = 0 := by simpa using hR 1 2
  have hp : star p = p := by simp only [p, star_sub, star_one, star_mul, star_star]
  have hpR : p * R 1 = R 1 := by
    change (1 - R 0 * star (R 0)) * R 1 = R 1
    rw [sub_mul, one_mul, mul_assoc, h01, mul_zero, sub_zero]
  have hp0 : p ≠ 0 := by
    intro he
    rw [he, zero_mul] at hpR
    have hh := hdiag 1
    rw [← hpR, star_zero, mul_zero] at hh
    exact zero_ne_one hh
  obtain ⟨d₀, d₁, U, _, hd₀, hd₁, hU, hg₀, hg₁, hg01, hsum⟩ :=
    exists_zero_corner_cuntz_pair (R 0) (R 1) (R 2)
      (hdiag 0) (hdiag 1) (hdiag 2) h01 h02 h12
  let d : Fin 2 → E := ![d₀, d₁]
  have hg10 : star d₁ * d₀ = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hg01
  refine ⟨hp0, d, ?_, ?_, fun x hx i => ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [d, hg₀, hg₁, hg01, hg10, p]
  · simpa only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hsum
  · have hxp : Commute x p :=
      (Commute.one_right x).sub_right ((hx 0).1.mul_right (hx 0).2)
    have hUp : Commute (U : E) x := by
      rw [hU]
      exact zeroCornerCompletion_commutes (R 0) (R 1) (R 2) x
        (hx 0).1.symm (hx 0).2.symm (hx 1).1.symm (hx 1).2.symm
        (hx 2).1.symm (hx 2).2.symm
    have hUstar : Commute (star (U : E)) x := by
      change star (U : E) * x = x * star (U : E)
      calc
        _ = star (U : E) * x * ((U : E) * star (U : E)) := by rw [U.property.2, mul_one]
        _ = star (U : E) * (x * (U : E)) * star (U : E) := by noncomm_ring
        _ = star (U : E) * ((U : E) * x) * star (U : E) := by rw [hUp.eq]
        _ = x * star (U : E) := by rw [← mul_assoc, U.property.1, one_mul]
    fin_cases i
    · change Commute x d₀ ∧ Commute x (star d₀)
      rw [hd₀]
      change Commute x (R 1 * p) ∧ Commute x (star (R 1 * p))
      exact ⟨(hx 1).1.mul_right hxp,
        by simpa only [star_mul, hp] using hxp.mul_right (hx 1).2⟩
    · change Commute x d₁ ∧ Commute x (star d₁)
      rw [hd₁]
      change Commute x ((U : E) * p) ∧ Commute x (star ((U : E) * p))
      exact ⟨hUp.symm.mul_right hxp,
        by simpa only [star_mul, hp] using hxp.mul_right hUstar.symm⟩

/-- The common-range row is now constructed from the buffer. The only
completion input is the actual connected cocycle to one shared reference. -/
lemma exists_connected_encoded_comparison_of_buffer [Nontrivial E]
    (R : Fin 3 → E)
    (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (b a c : Fin 2 → E)
    (hb : ∀ i j, star (b i) * b j = if i = j then 1 else 0)
    (hbs : (∑ i, b i * star (b i)) = 1)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1)
    (hc : ∀ i j, star (c i) * c j = if i = j then 1 else 0)
    (hcs : (∑ i, c i * star (c i)) = 1)
    (har : bergRowsCommute a R) (hcr : bergRowsCommute c R)
    (u v : unitary E) (hu : Joined (1 : unitary E) u) (hv : Joined (1 : unitary E) v)
    (hua : ∀ j, (u : E) * a j = b j) (hvc : ∀ j, (v : E) * c j = b j)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : unitary E, Joined (1 : unitary E) w ∧
      ∀ i ≤ m, ‖(w : E) * (a 0 ^ i * a 1) * star (w : E) -
        (c 0 ^ i * c 1)‖ < ε := by
  let r : Fin 2 → E := fun i => R i.castSucc
  have hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0 := by
    intro i j
    simpa only [r, Fin.castSucc_inj] using hR i.castSucc j.castSucc
  obtain ⟨hp0, d, hd, hds, hdc⟩ := exists_buffer_shrink_range_pair R hR
  exact exists_connected_forward_shrink_comparison r b a c d hr hb hbs ha has hc hcs
    (fun i j => har i j.castSucc) (fun i j => hcr i j.castSucc)
    u v hu hv hua hvc hp0 hd hds
    (fun i j => hdc (a i) (har i) j) (fun i j => hdc (c i) (hcr i) j) m ε hε

end WeakPureInfiniteness

end

end OAI
