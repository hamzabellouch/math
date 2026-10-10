import OAI.NumberTheory.Jacobsthal.Harmonic.AuxiliaryPolynomialLifting

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def residueSlopes (P : Finset ℕ) (T : P → Finset ℤ) (p : P) : Finset (ZMod p.val) := by
  classical
  exact (T p).image (fun s : ℤ => (s : ZMod p.val))

theorem residueSlopes_card_le (P : Finset ℕ) (T : P → Finset ℤ) (p : P) :
    (residueSlopes P T p).card ≤ (T p).card := by
  classical
  exact Finset.card_image_le

theorem exists_integer_slope_polynomial (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : P → Finset ℤ) (a : P → ℤ) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s ∈ T p,
        lineSub (Int.castRingHom (ZMod p.val)) (a p : ZMod p.val) (s : ZMod p.val) Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((D : ℝ)+2)*
        (∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ)) := by
  classical
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog⟩ := exists_small_line_polynomial P hP
    (residueSlopes P T) (fun p => (a p : ZMod p.val)) D
  refine ⟨Q,H,hQ,hD,hH,hcoeff,?_,?_⟩
  · intro p s hs
    apply hline p ⟨(s : ZMod p.val),?_⟩
    exact Finset.mem_image.mpr ⟨s,hs,rfl⟩
  · have hc : logarithmicCost P (residueSlopes P T) ≤
        ∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ) :=
      logarithmicCost_le_budget P hP (residueSlopes P T) (fun p => ((T p).card : ℝ))
        (fun p => by exact_mod_cast residueSlopes_card_le P T p)
    exact hlog.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by positivity)))

def IntegerLineIncidence (P : Finset ℕ) (T : P → Finset ℤ)
    (a : P → ℤ) (x y : ℤ) (p : P) : Prop :=
  ∃ s ∈ T p, (y : ZMod p.val) = (a p : ZMod p.val)-(s : ZMod p.val)*(x : ZMod p.val)

theorem exists_integer_auxiliary_polynomial_lifting (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (T : P → Finset ℤ) (a : P → ℤ) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s ∈ T p,
        lineSub (Int.castRingHom (ZMod p.val)) (a p : ZMod p.val) (s : ZMod p.val) Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((D : ℝ)+2)*
        (∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ)) ∧
      ∀ (S : ℝ) (x y : ℤ), (0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) →
        (0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) →
        ∀ (I : Finset ℕ) (hIP : I ⊆ P),
          (∀ p : I, IntegerLineIncidence P T a x y ⟨p.val,hIP p.property⟩) →
          logarithmicValueBudget D H S < ∑ p ∈ I, Real.log (p : ℝ) →
          MvPolynomial.eval ![x,y] Q = 0 := by
  classical
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog⟩ :=
    exists_integer_slope_polynomial P (fun p hp => (hP p hp).pos) T a D
  refine ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog,?_⟩
  intro S x y hx hy I hIP hinc hlarge
  unfold IntegerLineIncidence at hinc
  choose s hsmem hs using hinc
  apply value_zero_of_log_prime_budget Q D H hD hcoeff hH S x y hx hy I
    (fun p hp => hP p (hIP hp))
    (fun p : I => (a ⟨p.val,hIP p.property⟩ : ZMod p.val))
    (fun p : I => (s p : ZMod p.val))
  · exact fun p => hline ⟨p.val,hIP p.property⟩ (s p) (hsmem p)
  · exact hs
  · exact hlarge

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
