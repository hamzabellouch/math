import OAI.InformationTheory.QuantumCircuit.ProductState

namespace OAI

/-! Normalized local factors as product-state inputs. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

def productVector {N : ℕ} (a : Fin N → Bit → ℂ) : State N :=
  WithLp.toLp 2 (fun x => ∏ i, a i (x i))

lemma productVector_norm {N : ℕ} (a : Fin N → Bit → ℂ)
    (ha : ∀ i, ∑ b, Complex.normSq (a i b) = 1) : ‖productVector a‖ = 1 := by
  have hs : ‖productVector a‖^2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ x : Word N, ‖∏ i, a i (x i)‖^2) = 1
    simp only [norm_prod, ← Finset.prod_pow, ← Complex.normSq_eq_norm_sq]
    rw [← Fintype.prod_sum (fun i b => Complex.normSq (a i b))]
    simp [ha]
  nlinarith [norm_nonneg (productVector a)]

lemma productVector_projector {N : ℕ} (a : Fin N → Bit → ℂ) :
    pureProjector (productVector a) = tensorMatrix (fun i => rankOne (a i)) := by
  ext x y
  change (∏ i, a i (x i)) * star (∏ i, a i (y i)) =
    ∏ i, a i (x i) * star (a i (y i))
  rw [Finset.prod_mul_distrib, star_prod]

def ProductInput.ofFactors {N : ℕ} (a : Fin N → Bit → ℂ)
    (ha : ∀ i, ∑ b, Complex.normSq (a i b) = 1) : ProductInput N where
  state := productVector a
  norm_state := productVector_norm a ha
  test := ⟨Finset.univ, a, fun i _ => ha i⟩
  full_support := rfl
  projector := by
    rw [productVector_projector]
    simp [Count.zero]

end QAC

end

end OAI
