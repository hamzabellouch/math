import OAI.Analysis.PureInfiniteness.ExactFiniteAbelianization

namespace OAI

/-! Finite iteration of the one-coefficient compression, as in the first
paragraph of KR02 Lemma 7.12. Previously compressed coefficients are included
among the commuting elements fixed by the next compression. -/

noncomputable section

namespace WeakPureInfiniteness

variable {D : Type*} [NonUnitalCStarAlgebra D]

lemma compression_product (v w x : D) :
    star (v * w) * x * (v * w) = star w * (star v * x * v) * w := by
  simp only [star_mul, mul_assoc]

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I] [DecidableEq I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem ultrapower_finite_family_abelianization (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (n : ℕ) (b : Fin n → N) (hb : ∀ j, 0 ≤ b j) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ (∀ i, star v * a i * v = a i) ∧
      (∀ i j, Commute (a i) (star v * b j * v)) ∧
      ∀ j k, Commute (star v * b j * v) (star v * b k * v) := by
  classical
  induction n with
  | zero =>
    obtain ⟨v, hv, he⟩ := ultrapower_finite_abelianization_exact U hP a ha hc 0
      (by simp [IsSelfAdjoint])
    exact ⟨v, hv, fun i => (he i).1, fun _ j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨v, hv, hfix, hcom, hpair⟩ := ih (fun j => b j.castSucc) (fun j => hb j.castSucc)
    let c : I ⊕ Fin n → N := Sum.elim a (fun j => star v * b j.castSucc * v)
    have hcp : ∀ j, 0 ≤ c j := by
      intro j
      cases j with
      | inl i => exact ha i
      | inr j => exact star_left_conjugate_nonneg (hb j.castSucc) v
    have hcc : ∀ j k, Commute (c j) (c k) := by
      intro j k
      cases j with
      | inl i =>
        cases k with
        | inl k => exact hc i k
        | inr k => exact hcom i k
      | inr j =>
        cases k with
        | inl i => exact (hcom i j).symm
        | inr k => exact hpair j k
    let z := star v * b (Fin.last n) * v
    have hzp : 0 ≤ z := star_left_conjugate_nonneg (hb (Fin.last n)) v
    obtain ⟨w, hw, he⟩ := ultrapower_finite_abelianization_exact U hP c hcp hcc z hzp.isSelfAdjoint
    have hnew (j : I ⊕ Fin n) : Commute (c j) (star w * z * w) := (he j).2.2
    have hold (j : Fin n) : star (v * w) * b j.castSucc * (v * w) =
        star v * b j.castSucc * v := by
      rw [compression_product]
      exact (he (.inr j)).1
    have hlast : star (v * w) * b (Fin.last n) * (v * w) = star w * z * w :=
      compression_product v w _
    refine ⟨v * w, (norm_mul_le v w).trans ?_, ?_, ?_, ?_⟩
    · nlinarith [norm_nonneg v, norm_nonneg w]
    · intro i
      rw [compression_product, hfix i]
      exact (he (.inl i)).1
    · intro i j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hlast]
        exact hnew (.inl i)
      · rw [hold]
        exact hcom i j
    · intro j k
      refine Fin.lastCases ?_ (fun j => ?_) j
      · refine Fin.lastCases ?_ (fun k => ?_) k
        · exact Commute.refl _
        · rw [hlast, hold]
          exact (hnew (.inr k)).symm
      · refine Fin.lastCases ?_ (fun k => ?_) k
        · rw [hold, hlast]
          exact hnew (.inr j)
        · rw [hold, hold]
          exact hpair j k

end WeakPureInfiniteness

end

end OAI
