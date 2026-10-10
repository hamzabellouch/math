import OAI.Analysis.KadisonKastler.FiniteSignFourthMoment
import OAI.Analysis.KadisonKastler.FiniteAveraging
import OAI.Analysis.KadisonKastler.TracialProducts

namespace OAI

/-! # Balanced two-sided unitary orbit families

Independent equal-weight left and right conjugation averages control the
respective covariances of the Cartesian-product orbit family. Its common
pairing is unchanged by an operator commuting with both unitary actions.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A I J : Type*} [CStarAlgebra A]
  [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The finite two-sided orbit, indexed by independent choices. -/
def twoSidedOrbit (d : I → unitary A) (e : J → unitary A) (a : A) (ij : I × J) : A :=
  (d ij.1 : A) * a * (e ij.2 : A)

private theorem twoSidedUnitary_left_square (u v : unitary A) (a : A) :
    ((u : A) * a * (v : A)) * star ((u : A) * a * (v : A)) =
      (u : A) * (a * star a) * star (u : A) := by
  calc
    _ = ((u : A) * a) * ((v : A) * star (v : A)) * (star a * star (u : A)) := by
      simp only [star_mul]
      noncomm_ring
    _ = _ := by rw [Unitary.mul_star_self_of_mem v.property]; simp [mul_assoc]

private theorem twoSidedUnitary_right_square (u v : unitary A) (a : A) :
    star ((u : A) * a * (v : A)) * ((u : A) * a * (v : A)) =
      star (v : A) * (star a * a) * (v : A) := by
  calc
    _ = (star (v : A) * star a) * (star (u : A) * (u : A)) * (a * (v : A)) := by
      simp only [star_mul]
      noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem u.property]; simp [mul_assoc]

omit [Nonempty I] in
private theorem finiteAverage_product_fst (f : I → A) :
    finiteAverage (fun ij : I × J => f ij.1) = finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    ← Finset.smul_sum, smul_smul]
  congr 1
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  calc
    _ = (Fintype.card I : ℂ)⁻¹ * ((Fintype.card J : ℂ)⁻¹ * Fintype.card J) := by ring
    _ = _ := by simp [Fintype.card_ne_zero]

omit [Nonempty J] in
private theorem finiteAverage_product_snd (f : J → A) :
    finiteAverage (fun ij : I × J => f ij.2) = finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  simp [Fintype.card_prod, mul_inv_rev, Fintype.card_ne_zero]

private theorem finiteSignLeftCovariance_eq_finiteAverage {K : Type*} [Fintype K]
    (a : K → A) :
    finiteSignLeftCovariance a = finiteAverage (fun k => a k * star (a k)) := by
  simp only [finiteSignLeftCovariance, finiteAverage, ← Complex.coe_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

private theorem finiteSignRightCovariance_eq_finiteAverage {K : Type*} [Fintype K]
    (a : K → A) :
    finiteSignRightCovariance a = finiteAverage (fun k => star (a k) * a k) := by
  simp only [finiteSignRightCovariance, finiteAverage, ← Complex.coe_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

omit [Nonempty I] in
/-- The right randomization disappears from the left covariance. -/
theorem twoSidedOrbit_left_covariance (d : I → unitary A) (e : J → unitary A) (a : A) :
    finiteSignLeftCovariance (twoSidedOrbit d e a) =
      finiteAverage (fun i => (d i : A) * (a * star a) * star (d i : A)) := by
  rw [finiteSignLeftCovariance_eq_finiteAverage]
  have hp : (fun ij : I × J => twoSidedOrbit d e a ij * star (twoSidedOrbit d e a ij)) =
      fun ij : I × J => (d ij.1 : A) * (a * star a) * star (d ij.1 : A) := by
    funext ij
    exact twoSidedUnitary_left_square _ _ _
  rw [hp]
  exact finiteAverage_product_fst (A := A) (I := I) (J := J)
    (fun i => (d i : A) * (a * star a) * star (d i : A))

omit [Nonempty J] in
/-- The left randomization disappears from the right covariance. -/
theorem twoSidedOrbit_right_covariance (d : I → unitary A) (e : J → unitary A) (a : A) :
    finiteSignRightCovariance (twoSidedOrbit d e a) =
      finiteAverage (fun j => star (e j : A) * (star a * a) * (e j : A)) := by
  rw [finiteSignRightCovariance_eq_finiteAverage]
  have hp : (fun ij : I × J => star (twoSidedOrbit d e a ij) * twoSidedOrbit d e a ij) =
      fun ij : I × J => star (e ij.2 : A) * (star a * a) * (e ij.2 : A) := by
    funext ij
    exact twoSidedUnitary_right_square _ _ _
  rw [hp]
  exact finiteAverage_product_snd (A := A) (I := I) (J := J)
    (fun j => star (e j : A) * (star a * a) * (e j : A))

omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Each two-sided orbit point has exactly the original tracial two-norm. -/
theorem twoSidedOrbit_twoNorm (τ : FaithfulTracialState A)
    (d : I → unitary A) (e : J → unitary A) (a : A) (ij : I × J) :
    traceTwoNorm τ (twoSidedOrbit d e a ij) = traceTwoNorm τ a := by
  simp only [twoSidedOrbit, traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commutation lets a common unitary action pass through a pairing. -/
private theorem pairing_unitary_of_commute (V : H →L[ℂ] H)
    (u : unitary (H →L[ℂ] H)) (hu : Commute V (u : H →L[ℂ] H)) (x y : H) :
    inner ℂ (V ((u : H →L[ℂ] H) x)) ((u : H →L[ℂ] H) y) = inner ℂ (V x) y := by
  have he := congrArg (fun T : H →L[ℂ] H => T x) hu.eq
  change V ((u : H →L[ℂ] H) x) = (u : H →L[ℂ] H) (V x) at he
  rw [he]
  exact Unitary.inner_map_map u _ _

omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- A bimodular operator has the same pairing at every two-sided orbit point. -/
theorem twoSidedOrbit_pairing (Φ : A →ₗ[ℂ] H) (V : H →L[ℂ] H)
    (d : I → unitary A) (e : J → unitary A)
    (L : I → unitary (H →L[ℂ] H)) (R : J → unitary (H →L[ℂ] H))
    (hL : ∀ i x, Φ ((d i : A) * x) = (L i : H →L[ℂ] H) (Φ x))
    (hR : ∀ j x, Φ (x * (e j : A)) = (R j : H →L[ℂ] H) (Φ x))
    (hVL : ∀ i, Commute V (L i : H →L[ℂ] H))
    (hVR : ∀ j, Commute V (R j : H →L[ℂ] H))
    (a b : A) (ij : I × J) :
    inner ℂ (V (Φ (twoSidedOrbit d e a ij))) (Φ (twoSidedOrbit d e b ij)) =
      inner ℂ (V (Φ a)) (Φ b) := by
  simp only [twoSidedOrbit, hR, hL]
  rw [pairing_unitary_of_commute V (R ij.2) (hVR ij.2)]
  exact pairing_unitary_of_commute V (L ij.1) (hVL ij.1) _ _

omit [Nonempty I] in
private theorem finiteSignLeftCovariance_reindex {K : Type*} [Fintype K]
    (σ : K ≃ I) (a : I → A) :
    finiteSignLeftCovariance (fun k => a (σ k)) = finiteSignLeftCovariance a := by
  unfold finiteSignLeftCovariance
  rw [Fintype.card_congr σ]
  congr 1
  exact σ.sum_comp (fun i => a i * star (a i))

omit [Nonempty I] in
private theorem finiteSignRightCovariance_reindex {K : Type*} [Fintype K]
    (σ : K ≃ I) (a : I → A) :
    finiteSignRightCovariance (fun k => a (σ k)) = finiteSignRightCovariance a := by
  unfold finiteSignRightCovariance
  rw [Fintype.card_congr σ]
  congr 1
  exact σ.sum_comp (fun i => star (a i) * a i)

/-- Separate finite averages yield exactly the finite families used by the
bounded-ball test, with an ordinary `Fin n` index. -/
theorem exists_balanced_orbit_families (τ : FaithfulTracialState A)
    (Φ : A →ₗ[ℂ] H) (V : H →L[ℂ] H)
    (d : I → unitary A) (e : J → unitary A)
    (L : I → unitary (H →L[ℂ] H)) (R : J → unitary (H →L[ℂ] H))
    (hL : ∀ i x, Φ ((d i : A) * x) = (L i : H →L[ℂ] H) (Φ x))
    (hR : ∀ j x, Φ (x * (e j : A)) = (R j : H →L[ℂ] H) (Φ x))
    (hVL : ∀ i, Commute V (L i : H →L[ℂ] H))
    (hVR : ∀ j, Commute V (R j : H →L[ℂ] H))
    (a b : A) (ha : traceTwoNorm τ a ≤ 1) (hb : traceTwoNorm τ b ≤ 1)
    (hQa : traceTwoNorm τ (finiteAverage (fun j => star (e j : A) * (star a * a) * (e j : A))) ≤ 2)
    (hLa : traceTwoNorm τ (finiteAverage (fun i => (d i : A) * (a * star a) * star (d i : A))) ≤ 2)
    (hQb : traceTwoNorm τ (finiteAverage (fun j => star (e j : A) * (star b * b) * (e j : A))) ≤ 2)
    (hLb : traceTwoNorm τ (finiteAverage (fun i => (d i : A) * (b * star b) * star (d i : A))) ≤ 2) :
    ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → A,
      (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
      (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
      traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
      (∀ i, inner ℂ (V (Φ (f i))) (Φ (g i)) = inner ℂ (V (Φ a)) (Φ b)) := by
  let σ : Fin (Fintype.card (I × J)) ≃ I × J := (Fintype.equivFin (I × J)).symm
  let f : Fin (Fintype.card (I × J)) → A := fun i => twoSidedOrbit d e a (σ i)
  let g : Fin (Fintype.card (I × J)) → A := fun i => twoSidedOrbit d e b (σ i)
  refine ⟨Fintype.card (I × J), Fintype.card_pos, f, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (twoSidedOrbit_twoNorm τ d e a (σ i)).le.trans ha
  · intro i
    exact (twoSidedOrbit_twoNorm τ d e b (σ i)).le.trans hb
  · change traceTwoNorm τ (finiteSignRightCovariance (fun i => twoSidedOrbit d e a (σ i))) ≤ 2
    rw [finiteSignRightCovariance_reindex, twoSidedOrbit_right_covariance]
    exact hQa
  · change traceTwoNorm τ (finiteSignLeftCovariance (fun i => twoSidedOrbit d e a (σ i))) ≤ 2
    rw [finiteSignLeftCovariance_reindex, twoSidedOrbit_left_covariance]
    exact hLa
  · change traceTwoNorm τ (finiteSignRightCovariance (fun i => twoSidedOrbit d e b (σ i))) ≤ 2
    rw [finiteSignRightCovariance_reindex, twoSidedOrbit_right_covariance]
    exact hQb
  · change traceTwoNorm τ (finiteSignLeftCovariance (fun i => twoSidedOrbit d e b (σ i))) ≤ 2
    rw [finiteSignLeftCovariance_reindex, twoSidedOrbit_left_covariance]
    exact hLb
  · intro i
    exact twoSidedOrbit_pairing Φ V d e L R hL hR hVL hVR a b (σ i)

end

end KadisonKastler

end OAI
