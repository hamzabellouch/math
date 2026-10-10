import Mathlib
import OAI.Probability.ParisiFinite.RestrictLeft

namespace OAI

/-! Cost State. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
namespace SKQAOA

def costState (n : ℕ) (J : Disorder n) (γ : ℝ) : State n :=
  (evolution γ (cost n J)).mulVec (plus n)

theorem costState_apply (n : ℕ) (J : Disorder n) (γ : ℝ) (σ : Configuration n) :
    costState n J γ σ = Complex.exp (-(γ : ℂ) * Complex.I * (hamiltonian n J σ : ℂ)) *
      ((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℝ) := by
  simp [costState, cost_evolution_eq_diagonal, Matrix.mulVec_diagonal, plus]

theorem plus_squared (n : ℕ) :
    (((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℝ) : ℂ) ^ 2 = ((2 : ℂ)^n)⁻¹ := by
  have he : ((Real.sqrt ((2 : ℝ)^n))⁻¹)^2 = ((2 : ℝ)^n)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [← Complex.ofReal_pow, he, Complex.ofReal_inv, Complex.ofReal_pow]
  rfl

def phaseCoeff (n : ℕ) (γ : ℝ) (σ τ : Configuration n) (e : Edge n) : ℂ :=
  (γ : ℂ) * Complex.I * ((skCoeff n σ e - skCoeff n τ e : ℝ) : ℂ)

theorem phase_sum (n : ℕ) (J : Disorder n) (γ : ℝ) (σ τ : Configuration n) :
    ∑ e, phaseCoeff n γ σ τ e * (J e : ℂ) =
      (γ : ℂ) * Complex.I * ((hamiltonian n J σ : ℂ) - (hamiltonian n J τ : ℂ)) := by
  simp only [hamiltonian_eq_coeff, Complex.ofReal_sum, Complex.ofReal_mul,
    ← Finset.sum_sub_distrib, Finset.mul_sum, phaseCoeff, Complex.ofReal_sub]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem costState_pair (n : ℕ) (J : Disorder n) (γ : ℝ) (σ τ : Configuration n) :
    star (costState n J γ σ) * costState n J γ τ =
      ((2 : ℂ)^n)⁻¹ * Complex.exp (∑ e, phaseCoeff n γ σ τ e * (J e : ℂ)) := by
  rw [costState_apply, costState_apply, star_mul]
  have hs : star (Complex.exp (-(γ : ℂ) * Complex.I * (hamiltonian n J σ : ℂ))) =
      Complex.exp ((γ : ℂ) * Complex.I * (hamiltonian n J σ : ℂ)) := by
    simp [← Complex.exp_conj]
  rw [hs]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [phase_sum, mul_sub, Complex.exp_sub]
  have hm : Complex.exp (-(γ : ℂ) * Complex.I * (hamiltonian n J τ : ℂ)) =
      (Complex.exp ((γ : ℂ) * Complex.I * (hamiltonian n J τ : ℂ)))⁻¹ := by
    rw [neg_mul, neg_mul, Complex.exp_neg]
  rw [hm, div_eq_mul_inv]
  have hp := plus_squared n
  calc
    _ = ((((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℝ) : ℂ)^2) *
      (Complex.exp ((γ : ℂ) * Complex.I * (hamiltonian n J σ : ℂ)) *
        (Complex.exp ((γ : ℂ) * Complex.I * (hamiltonian n J τ : ℂ)))⁻¹) := by ring
    _ = _ := by rw [hp]

theorem integrable_coord_costState_pair (n : ℕ) (γ : ℝ) (e : Edge n) (σ τ : Configuration n) :
    Integrable (fun J : Disorder n => (J e : ℂ) *
      (star (costState n J γ σ) * costState n J γ τ)) (disorderLaw n) := by
  simp_rw [costState_pair]
  have h := (GaussianFourier.integrable_coord_exp_sum (phaseCoeff n γ σ τ) e).const_mul
    (((2 : ℂ)^n)⁻¹)
  change Integrable _ (GaussianFourier.law (Edge n))
  convert h using 1
  funext J
  ring

 
theorem integral_coord_costState_pair (n : ℕ) (γ : ℝ) (e : Edge n) (σ τ : Configuration n) :
    (∫ J : Disorder n, (J e : ℂ) *
      (star (costState n J γ σ) * costState n J γ τ) ∂disorderLaw n) =
      ((2 : ℂ)^n)⁻¹ * phaseCoeff n γ σ τ e *
        Complex.exp (∑ f, phaseCoeff n γ σ τ f ^ 2 / 2) := by
  simp_rw [costState_pair]
  have he : (fun J : Disorder n => (J e : ℂ) *
      (((2 : ℂ)^n)⁻¹ * Complex.exp (∑ f, phaseCoeff n γ σ τ f * (J f : ℂ)))) =
      fun J => ((2 : ℂ)^n)⁻¹ * ((J e : ℂ) *
        Complex.exp (∑ f, phaseCoeff n γ σ τ f * (J f : ℂ))) := by
    funext J
    ring
  rw [he, integral_const_mul]
  change _ * (∫ J : Disorder n, _ ∂GaussianFourier.law (Edge n)) = _
  rw [GaussianFourier.integral_coord_exp_sum]
  ring

end SKQAOA

namespace SKQAOA

def flipAt {n : ℕ} (σ : Configuration n) (i : Fin n) : Configuration n :=
  Function.update σ i (!(σ i))

@[simp] theorem flipAt_self {n : ℕ} (σ : Configuration n) (i : Fin n) :
    flipAt σ i i = !(σ i) := Function.update_self _ _ _

@[simp] theorem flipAt_ne {n : ℕ} (σ : Configuration n) (i j : Fin n) (h : j ≠ i) :
    flipAt σ i j = σ j := Function.update_of_ne h _ _

@[simp] theorem spin_flipAt_self {n : ℕ} (σ : Configuration n) (i : Fin n) :
    spin (flipAt σ i) i = -spin σ i := by
  cases h : σ i <;> simp [spin, h]

@[simp] theorem spin_flipAt_ne {n : ℕ} (σ : Configuration n) (i j : Fin n) (h : j ≠ i) :
    spin (flipAt σ i) j = spin σ j := by simp [spin, flipAt_ne, h]

@[simp] theorem pauliZ_mulVec {n : ℕ} (i : Fin n) (ψ : State n) (σ : Configuration n) :
    (pauliZ i).mulVec ψ σ = (spin σ i : ℂ) * ψ σ := by
  simp [pauliZ, Matrix.mulVec_diagonal]

@[simp] theorem pauliX_mulVec {n : ℕ} (i : Fin n) (ψ : State n) (σ : Configuration n) :
    (pauliX i).mulVec ψ σ = ψ (flipAt σ i) := by
  have he : pauliX i σ = fun τ => if τ = flipAt σ i then (1 : ℂ) else 0 := by
    funext τ
    unfold pauliX
    by_cases h : τ = flipAt σ i
    · have h' : σ = Function.update τ i (!(τ i)) := (flip_eq_iff i σ τ).mpr h
      simp only [ite_eq_left h, ite_eq_left h']
    · have h' : σ ≠ Function.update τ i (!(τ i)) := fun he => h ((flip_eq_iff i σ τ).mp he)
      simp only [ite_eq_right h, ite_eq_right h']
  change (∑ τ, pauliX i σ τ * ψ τ) = _
  rw [he]
  simp

theorem pauliY_eq {n : ℕ} (i : Fin n) :
    pauliY i = Complex.I • (pauliX i * pauliZ i) := by
  rw [pauliY, TwoState.y, TensorMatrix.local_smul, TensorMatrix.local_mul,
    ← pauliX_eq_atSite, ← pauliZ_eq_atSite]

@[simp] theorem pauliY_mulVec {n : ℕ} (i : Fin n) (ψ : State n) (σ : Configuration n) :
    (pauliY i).mulVec ψ σ = -Complex.I * (spin σ i : ℂ) * ψ (flipAt σ i) := by
  rw [pauliY_eq, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, pauliX_mulVec, pauliZ_mulVec,
    spin_flipAt_self, Complex.ofReal_neg]
  ring

theorem overlapSum_flipAt {n : ℕ} (σ : Configuration n) (i : Fin n) :
    overlapSum σ (flipAt σ i) = (n : ℝ) - 2 := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  unfold overlapSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [spin_flipAt_self, mul_neg, ← sq, spin_sq]
  have he : (∑ j ∈ Finset.univ.erase i, spin σ j * spin (flipAt σ i) j) = (n : ℝ)-1 := by
    calc
      _ = ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [spin_flipAt_ne _ _ _ (Finset.ne_of_mem_erase hj), ← sq, spin_sq]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub hn, Nat.cast_one]
  rw [he]
  ring

theorem phaseCoeff_flip_edge_left {n : ℕ} (γ : ℝ) (σ : Configuration n) (e : Edge n) :
    phaseCoeff n γ σ (flipAt σ e.1.1) e =
      2 * (γ : ℂ) * Complex.I * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
        (spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ) := by
  unfold phaseCoeff skCoeff
  rw [spin_flipAt_self, spin_flipAt_ne _ _ _ (ne_of_gt e.2)]
  push_cast
  ring

theorem phaseCoeff_flip_edge_right {n : ℕ} (γ : ℝ) (σ : Configuration n) (e : Edge n) :
    phaseCoeff n γ σ (flipAt σ e.1.2) e =
      2 * (γ : ℂ) * Complex.I * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
        (spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ) := by
  unfold phaseCoeff skCoeff
  rw [spin_flipAt_self, spin_flipAt_ne _ _ _ (ne_of_lt e.2)]
  push_cast
  ring

@[simp] theorem phaseCoeff_self (n : ℕ) (γ : ℝ) (σ : Configuration n) (e : Edge n) :
    phaseCoeff n γ σ σ e = 0 := by simp [phaseCoeff]

@[simp] theorem phaseCoeff_flip_both {n : ℕ} (γ : ℝ) (σ : Configuration n) (e : Edge n) :
    phaseCoeff n γ σ (flipAt (flipAt σ e.1.1) e.1.2) e = 0 := by
  unfold phaseCoeff skCoeff
  rw [spin_flipAt_self, spin_flipAt_ne _ _ _ (ne_of_lt e.2), spin_flipAt_self,
    spin_flipAt_ne _ _ _ (ne_of_gt e.2)]
  simp

 
theorem phaseCoeff_square_sum_flip {n : ℕ} (hn : 0 < n) (γ : ℝ)
    (σ : Configuration n) (i : Fin n) :
    (∑ e, phaseCoeff n γ σ (flipAt σ i) e ^ 2 / 2) =
      ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ) := by
  have he : (∑ e, phaseCoeff n γ σ (flipAt σ i) e ^ 2 / 2) =
      ((-γ^2 / 2 : ℝ) : ℂ) *
        ((∑ e, (skCoeff n σ e - skCoeff n (flipAt σ i) e)^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [phaseCoeff, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat, mul_pow, Complex.I_sq]
    ring
  rw [he, coeff_increment hn, overlapSum_flipAt]
  push_cast
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

end SKQAOA

namespace SKQAOA

 
theorem integrable_coord_quad_transition (n : ℕ) (γ : ℝ) (e : Edge n) (A : Operator n)
    (a : Configuration n → ℂ) (f : Configuration n → Configuration n)
    (hA : ∀ (ψ : State n) σ, A.mulVec ψ σ = a σ * ψ (f σ)) :
    Integrable (fun J : Disorder n => (J e : ℂ) * quad (costState n J γ) A) (disorderLaw n) := by
  have he : (fun J : Disorder n => (J e : ℂ) * quad (costState n J γ) A) =
      fun J => ∑ σ, a σ * ((J e : ℂ) *
        (star (costState n J γ σ) * costState n J γ (f σ))) := by
    funext J
    simp only [quad, dotProduct, hA, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [he]
  exact integrable_finsetSum _ (fun σ _ =>
    (integrable_coord_costState_pair n γ e σ (f σ)).const_mul (a σ))

 
theorem integral_coord_quad_transition (n : ℕ) (γ : ℝ) (e : Edge n) (A : Operator n)
    (a : Configuration n → ℂ) (f : Configuration n → Configuration n)
    (hA : ∀ (ψ : State n) σ, A.mulVec ψ σ = a σ * ψ (f σ)) :
    (∫ J : Disorder n, (J e : ℂ) * quad (costState n J γ) A ∂disorderLaw n) =
      ∑ σ, a σ * (((2 : ℂ)^n)⁻¹ * phaseCoeff n γ σ (f σ) e *
        Complex.exp (∑ d, phaseCoeff n γ σ (f σ) d ^ 2 / 2)) := by
  have he : (fun J : Disorder n => (J e : ℂ) * quad (costState n J γ) A) =
      fun J => ∑ σ, a σ * ((J e : ℂ) *
        (star (costState n J γ σ) * costState n J γ (f σ))) := by
    funext J
    simp only [quad, dotProduct, hA, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [he, integral_finsetSum _ (fun σ _ =>
    (integrable_coord_costState_pair n γ e σ (f σ)).const_mul (a σ))]
  simp_rw [integral_const_mul, integral_coord_costState_pair]

 
theorem integral_coord_ZZ {n : ℕ} (γ : ℝ) (e : Edge n) :
    (∫ J : Disorder n, (J e : ℂ) *
      quad (costState n J γ) (pauliZ e.1.1 * pauliZ e.1.2) ∂disorderLaw n) = 0 := by
  rw [integral_coord_quad_transition n γ e _
    (fun σ => (spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ)) id (by
      intro ψ σ
      simp only [← Matrix.mulVec_mulVec, pauliZ_mulVec, id_eq]
      ring)]
  simp

 
theorem integral_coord_YY {n : ℕ} (γ : ℝ) (e : Edge n) :
    (∫ J : Disorder n, (J e : ℂ) *
      quad (costState n J γ) (pauliY e.1.1 * pauliY e.1.2) ∂disorderLaw n) = 0 := by
  rw [integral_coord_quad_transition n γ e _
    (fun σ => -(spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ))
    (fun σ => flipAt (flipAt σ e.1.1) e.1.2) (by
      intro ψ σ
      simp only [← Matrix.mulVec_mulVec, pauliY_mulVec,
        spin_flipAt_ne _ _ _ (ne_of_gt e.2)]
      calc
        _ = Complex.I^2 * (spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ) *
            ψ (flipAt (flipAt σ e.1.1) e.1.2) := by ring
        _ = _ := by rw [Complex.I_sq]; ring)]
  simp

 
theorem sum_configuration_normalized (n : ℕ) (c : ℂ) :
    (∑ _σ : Configuration n, ((2 : ℂ)^n)⁻¹ * c) = c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_mul]

theorem integral_coord_YZ {n : ℕ} (γ : ℝ) (e : Edge n) :
    (∫ J : Disorder n, (J e : ℂ) *
      quad (costState n J γ) (pauliY e.1.1 * pauliZ e.1.2) ∂disorderLaw n) =
      2 * (γ : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
        Complex.exp ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le e.1.1.val) e.1.1.isLt
  rw [integral_coord_quad_transition n γ e _
    (fun σ => -Complex.I * (spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ))
    (fun σ => flipAt σ e.1.1) (by
      intro ψ σ
      simp only [← Matrix.mulVec_mulVec, pauliY_mulVec, pauliZ_mulVec,
        spin_flipAt_ne _ _ _ (ne_of_gt e.2)]
      ring)]
  simp_rw [phaseCoeff_flip_edge_left, phaseCoeff_square_sum_flip hn]
  calc
    _ = ∑ _σ : Configuration n, ((2 : ℂ)^n)⁻¹ *
        (2 * (γ : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
          Complex.exp ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      have hi : (spin σ e.1.1 : ℂ)^2 = 1 := by exact_mod_cast spin_sq σ e.1.1
      have hj : (spin σ e.1.2 : ℂ)^2 = 1 := by exact_mod_cast spin_sq σ e.1.2
      calc
        _ = ((2 : ℂ)^n)⁻¹ * (2 * (γ : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
          Complex.exp ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ)) *
          (-Complex.I^2) * (spin σ e.1.1 : ℂ)^2 * (spin σ e.1.2 : ℂ)^2 := by ring
        _ = _ := by rw [hi, hj, Complex.I_sq]; ring
    _ = _ := sum_configuration_normalized n _

theorem integral_coord_ZY {n : ℕ} (γ : ℝ) (e : Edge n) :
    (∫ J : Disorder n, (J e : ℂ) *
      quad (costState n J γ) (pauliZ e.1.1 * pauliY e.1.2) ∂disorderLaw n) =
      2 * (γ : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
        Complex.exp ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le e.1.1.val) e.1.1.isLt
  rw [integral_coord_quad_transition n γ e _
    (fun σ => -Complex.I * (spin σ e.1.1 : ℂ) * (spin σ e.1.2 : ℂ))
    (fun σ => flipAt σ e.1.2) (by
      intro ψ σ
      simp only [← Matrix.mulVec_mulVec, pauliY_mulVec, pauliZ_mulVec]
      ring)]
  simp_rw [phaseCoeff_flip_edge_right, phaseCoeff_square_sum_flip hn]
  calc
    _ = ∑ _σ : Configuration n, ((2 : ℂ)^n)⁻¹ *
        (2 * (γ : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
          Complex.exp ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      have hi : (spin σ e.1.1 : ℂ)^2 = 1 := by exact_mod_cast spin_sq σ e.1.1
      have hj : (spin σ e.1.2 : ℂ)^2 = 1 := by exact_mod_cast spin_sq σ e.1.2
      calc
        _ = ((2 : ℂ)^n)⁻¹ * (2 * (γ : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
          Complex.exp ((-2 * γ^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ)) *
          (-Complex.I^2) * (spin σ e.1.1 : ℂ)^2 * (spin σ e.1.2 : ℂ)^2 := by ring
        _ = _ := by rw [hi, hj, Complex.I_sq]; ring
    _ = _ := sum_configuration_normalized n _

end SKQAOA

namespace SKQAOA

theorem integrable_coord_quad (n : ℕ) (γ : ℝ) (e : Edge n) (A : Operator n) :
    Integrable (fun J : Disorder n => (J e : ℂ) * quad (costState n J γ) A) (disorderLaw n) := by
  have he : (fun J : Disorder n => (J e : ℂ) * quad (costState n J γ) A) =
      fun J => ∑ σ, ∑ τ, A σ τ * ((J e : ℂ) *
        (star (costState n J γ σ) * costState n J γ τ)) := by
    funext J
    simp only [quad, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  rw [he]
  exact integrable_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ =>
    (integrable_coord_costState_pair n γ e σ τ).const_mul (A σ τ)))

theorem qaoaState_one (n : ℕ) (J : Disorder n) (γ β : Fin 1 → ℝ) :
    qaoaState n 1 J γ β = (evolution (β 0) (mixer n)).mulVec (costState n J (γ 0)) := by
  simp [qaoaState, circuit, costState, ← Matrix.mulVec_mulVec]

theorem conjugate_mul {n : ℕ} (U A B : Operator n) (hU : U * Uᴴ = 1) :
    Uᴴ * (A*B) * U = (Uᴴ*A*U)*(Uᴴ*B*U) := by
  symm
  calc
    _ = Uᴴ*A*(U*Uᴴ)*B*U := by noncomm_ring
    _ = _ := by rw [hU]; noncomm_ring

theorem quad_qaoaState_one_edge (n : ℕ) (J : Disorder n) (γ β : Fin 1 → ℝ) (e : Edge n) :
    quad (qaoaState n 1 J γ β) (pauliZ e.1.1 * pauliZ e.1.2) =
      (Real.cos (2*β 0) : ℂ)^2 * quad (costState n J (γ 0)) (pauliZ e.1.1 * pauliZ e.1.2) +
      ((Real.cos (2*β 0) : ℂ) * (Real.sin (2*β 0) : ℂ)) *
        quad (costState n J (γ 0)) (pauliZ e.1.1 * pauliY e.1.2) +
      ((Real.sin (2*β 0) : ℂ) * (Real.cos (2*β 0) : ℂ)) *
        quad (costState n J (γ 0)) (pauliY e.1.1 * pauliZ e.1.2) +
      (Real.sin (2*β 0) : ℂ)^2 * quad (costState n J (γ 0)) (pauliY e.1.1 * pauliY e.1.2) := by
  rw [qaoaState_one, quad_mulVec, conjugate_mul _ _ _
    (Unitary.mul_star_self_of_mem (evolution_unitary _ _ (mixer_hermitian n))),
    mixer_conjugate_pauliZ, mixer_conjugate_pauliZ]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, quad_add, quad_smul]
  ring

theorem integrable_coord_qaoaState_one_edge (n : ℕ) (γ β : Fin 1 → ℝ) (e : Edge n) :
    Integrable (fun J : Disorder n => (J e : ℂ) *
      quad (qaoaState n 1 J γ β) (pauliZ e.1.1 * pauliZ e.1.2)) (disorderLaw n) := by
  simp_rw [quad_qaoaState_one_edge, mul_add]
  simp_rw [mul_left_comm (G := ℂ) _ (↑(Real.cos (2*β 0))^2),
    mul_left_comm (G := ℂ) _ (↑(Real.cos (2*β 0)) * ↑(Real.sin (2*β 0))),
    mul_left_comm (G := ℂ) _ (↑(Real.sin (2*β 0)) * ↑(Real.cos (2*β 0))),
    mul_left_comm (G := ℂ) _ (↑(Real.sin (2*β 0))^2)]
  exact ((((integrable_coord_quad n (γ 0) e _).const_mul _).add
    ((integrable_coord_quad n (γ 0) e _).const_mul _)).add
    ((integrable_coord_quad n (γ 0) e _).const_mul _)).add
    ((integrable_coord_quad n (γ 0) e _).const_mul _)

 
theorem integral_coord_qaoaState_one_edge (n : ℕ) (γ β : Fin 1 → ℝ) (e : Edge n) :
    (∫ J : Disorder n, (J e : ℂ) *
      quad (qaoaState n 1 J γ β) (pauliZ e.1.1 * pauliZ e.1.2) ∂disorderLaw n) =
      2 * (γ 0 : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) * (Real.sin (4*β 0) : ℂ) *
        Complex.exp ((-2 * (γ 0)^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ) := by
  simp_rw [quad_qaoaState_one_edge, mul_add]
  simp_rw [mul_left_comm (G := ℂ) _ (↑(Real.cos (2*β 0))^2),
    mul_left_comm (G := ℂ) _ (↑(Real.cos (2*β 0)) * ↑(Real.sin (2*β 0))),
    mul_left_comm (G := ℂ) _ (↑(Real.sin (2*β 0)) * ↑(Real.cos (2*β 0))),
    mul_left_comm (G := ℂ) _ (↑(Real.sin (2*β 0))^2)]
  have hZZ := (integrable_coord_quad n (γ 0) e (pauliZ e.1.1 * pauliZ e.1.2)).const_mul
    ((Real.cos (2*β 0) : ℂ)^2)
  have hZY := (integrable_coord_quad n (γ 0) e (pauliZ e.1.1 * pauliY e.1.2)).const_mul
    ((Real.cos (2*β 0) : ℂ) * (Real.sin (2*β 0) : ℂ))
  have hYZ := (integrable_coord_quad n (γ 0) e (pauliY e.1.1 * pauliZ e.1.2)).const_mul
    ((Real.sin (2*β 0) : ℂ) * (Real.cos (2*β 0) : ℂ))
  have hYY := (integrable_coord_quad n (γ 0) e (pauliY e.1.1 * pauliY e.1.2)).const_mul
    ((Real.sin (2*β 0) : ℂ)^2)
  have hi1 := integral_add ((hZZ.add hZY).add hYZ) hYY
  have hi2 := integral_add (hZZ.add hZY) hYZ
  have hi3 := integral_add hZZ hZY
  simp only [Pi.add_apply] at hi1 hi2 hi3
  rw [hi1, hi2, hi3]
  simp_rw [integral_const_mul]
  rw [integral_coord_ZZ, integral_coord_ZY, integral_coord_YZ, integral_coord_YY]
  have hs : (Real.sin (4*β 0) : ℂ) =
      2 * (Real.sin (2*β 0) : ℂ) * (Real.cos (2*β 0) : ℂ) := by
    rw [show 4*β 0 = 2*(2*β 0) by ring, Real.sin_two_mul]
    push_cast
    rfl
  rw [hs]
  ring

end SKQAOA

namespace SKQAOA

@[simp] theorem quad_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : State n) (A : ι → Operator n) :
    quad ψ (∑ i ∈ s, A i) = ∑ i ∈ s, quad ψ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quad]
  | @insert i s hi ih => simp [hi, ih]

theorem quad_cost (n : ℕ) (J : Disorder n) (ψ : State n) :
    quad ψ (cost n J) = ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
      ∑ e : Edge n, (J e : ℂ) * quad ψ (pauliZ e.1.1 * pauliZ e.1.2) := by
  simp only [cost, quad_smul, quad_finsetSum]

theorem integrable_quad_cost_one (n : ℕ) (γ β : Fin 1 → ℝ) :
    Integrable (fun J : Disorder n => quad (qaoaState n 1 J γ β) (cost n J)) (disorderLaw n) := by
  simp_rw [quad_cost]
  exact (integrable_finsetSum _ (fun e _ => integrable_coord_qaoaState_one_edge n γ β e)).const_mul _

theorem integral_quad_cost_one (n : ℕ) (γ β : Fin 1 → ℝ) :
    (∫ J : Disorder n, quad (qaoaState n 1 J γ β) (cost n J) ∂disorderLaw n) =
      ((Real.sqrt (n : ℝ))⁻¹ : ℂ) * (Fintype.card (Edge n) : ℂ) *
      (2 * (γ 0 : ℂ) * ((Real.sqrt (n : ℝ))⁻¹ : ℂ) * (Real.sin (4*β 0) : ℂ) *
        Complex.exp ((-2 * (γ 0)^2 * ((n : ℝ)-1) / (n : ℝ) : ℝ) : ℂ)) := by
  simp_rw [quad_cost]
  rw [integral_const_mul, integral_finsetSum _ (fun e _ => integrable_coord_qaoaState_one_edge n γ β e)]
  simp_rw [integral_coord_qaoaState_one_edge]
  simp [mul_assoc]

theorem card_edges_real (n : ℕ) :
    2 * (Fintype.card (Edge n) : ℝ) = (n : ℝ) * ((n : ℝ)-1) := by
  have h := sum_symmetric_pairs n (fun _ _ => 1) (by intros; rfl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  nlinarith

 
theorem expectedEnergy_one (n : ℕ) (γ β : Fin 1 → ℝ) :
    expectedEnergy n 1 γ β =
      γ 0 * ((n : ℝ)-1) / (n : ℝ) * Real.sin (4*β 0) *
        Real.exp (-2 * (γ 0)^2 * ((n : ℝ)-1) / (n : ℝ)) := by
  unfold expectedEnergy energyDensity
  change (∫ J : Disorder n, (quad (qaoaState n 1 J γ β) (cost n J)).re / (n : ℝ) ∂disorderLaw n) = _
  have hi : (∫ J : Disorder n, (quad (qaoaState n 1 J γ β) (cost n J)).re ∂disorderLaw n) =
      (∫ J : Disorder n, quad (qaoaState n 1 J γ β) (cost n J) ∂disorderLaw n).re :=
    integral_re (integrable_quad_cost_one n γ β)
  rw [integral_div, hi, integral_quad_cost_one]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
  by_cases hn : n = 0
  · subst n; simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hs2 : ((Real.sqrt (n : ℝ))⁻¹)^2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    calc
      _ = γ 0 * (2 * (Fintype.card (Edge n) : ℝ)) * ((Real.sqrt (n : ℝ))⁻¹)^2 *
          Real.sin (4*β 0) * Real.exp (-2 * (γ 0)^2 * ((n : ℝ)-1)/(n : ℝ)) / (n : ℝ) := by ring
      _ = _ := by rw [hs2, card_edges_real]; field_simp

end SKQAOA

namespace SKQAOA

theorem tendsto_sizeCorrection :
    Tendsto (fun n : ℕ => ((n : ℝ)-1)/(n : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 - 1/(n : ℝ)) atTop (𝓝 (1-0 : ℝ)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
  field_simp

theorem tendsto_expectedEnergy_one (γ β : Fin 1 → ℝ) :
    Tendsto (fun n => expectedEnergy n 1 γ β) atTop
      (𝓝 (γ 0 * Real.sin (4*β 0) * Real.exp (-2 * (γ 0)^2))) := by
  have h := (((tendsto_const_nhds (x := γ 0)).mul tendsto_sizeCorrection).mul
    (tendsto_const_nhds (x := Real.sin (4*β 0)))).mul
    (Real.continuous_exp.tendsto (-2 * (γ 0)^2 * 1) |>.comp
      (tendsto_const_nhds.mul tendsto_sizeCorrection))
  simp only [mul_one] at h
  convert h using 1
  funext n
  rw [expectedEnergy_one]
  simp only [Function.comp_apply, mul_div_assoc]

theorem value_one (γ β : Fin 1 → ℝ) :
    value 1 γ β = γ 0 * Real.sin (4*β 0) * Real.exp (-2 * (γ 0)^2) := by
  exact (tendsto_expectedEnergy_one γ β).limUnder_eq

 
theorem explicit_one_layer_value :
    value 1 (fun _ => 1/2) (fun _ => Real.pi/8) = Real.exp (-1/2) / 2 := by
  rw [value_one]
  norm_num
  rw [show 4*(Real.pi/8) = Real.pi/2 by ring, Real.sin_pi_div_two]
  ring

end SKQAOA

namespace SKGaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 
theorem expected_field_logPartition_le_of_orthogonal {κ : Type*} [Fintype κ]
    (A B : ι → κ → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0)
    (hinc : ∀ i j, (∑ k, (A i k - A j k)^2) ≤ ∑ k, (B i k - B j k)^2) :
    (∫ x, logPartition (field A x) ∂gaussianLaw κ) ≤
      ∫ x, logPartition (field B x) ∂gaussianLaw κ := by
  rw [← integral_reindex_field A logPartition, ← integral_reindex_field B logPartition]
  apply expected_logPartition_le
  · intro i j
    exact ((Fintype.equivFin κ).symm.sum_comp (fun k => A i k * B j k)).trans (hAB i j)
  · intro i j
    exact ((Fintype.equivFin κ).symm.sum_comp (fun k => (A i k - A j k)^2)).le.trans
      ((hinc i j).trans ((Fintype.equivFin κ).symm.sum_comp (fun k => (B i k - B j k)^2)).symm.le)

theorem expected_field_logPartition_le {κ κ₂ : Type*} [Fintype κ] [Fintype κ₂]
    (A : ι → κ → ℝ) (B : ι → κ₂ → ℝ)
    (hinc : ∀ i j, (∑ k, (A i k - A j k)^2) ≤ ∑ k, (B i k - B j k)^2) :
    (∫ x, logPartition (field A x) ∂gaussianLaw κ) ≤
      ∫ x, logPartition (field B x) ∂gaussianLaw κ₂ := by
  rw [← integral_field_inl (κ₂ := κ₂) A logPartition,
    ← integral_field_inr (κ := κ) B logPartition]
  apply expected_field_logPartition_le_of_orthogonal
  · intro i j
    simp [Fintype.sum_sum_type]
  · intro i j
    simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sub_self,
      sq,mul_zero,Finset.sum_const_zero,add_zero,zero_add] using hinc i j

end SKGaussian

namespace SKQAOA
open SKGaussian

 
def pressure (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J, logPartition (fun σ => β * hamiltonian n J σ) ∂disorderLaw n

def freeEnergy (β : ℝ) (n : ℕ) : ℝ := pressure β n / (n : ℝ) / β

def limitingFreeEnergy (β : ℝ) : ℝ := limUnder atTop (freeEnergy β)

theorem field_scale {ι κ : Type*} [Fintype κ] (β : ℝ) (A : ι → κ → ℝ) (J : κ → ℝ) :
    field (fun i k => β * A i k) J = fun i => β * field A J i := by
  funext i
  simp only [field,mul_assoc,Finset.mul_sum]

theorem scaled_increment {ι κ : Type*} [Fintype κ] (β : ℝ) (A : ι → κ → ℝ) (i j : ι) :
    (∑ k, (β*A i k-β*A j k)^2) = β^2 * ∑ k, (A i k-A j k)^2 := by
  simp_rw [← mul_sub,mul_pow]
  rw [Finset.mul_sum]

theorem field_skCoeff (n : ℕ) (J : Disorder n) : field (skCoeff n) J = hamiltonian n J :=
  funext fun σ => (hamiltonian_eq_coeff n J σ).symm

theorem pressure_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun J => logPartition (fun σ => β * hamiltonian n J σ)) (disorderLaw n) := by
  have : IsProbabilityMeasure (disorderLaw n) := by unfold disorderLaw; infer_instance
  apply integrable_logPartition
  intro σ
  simpa only [field,← hamiltonian_eq_coeff,gaussianLaw,disorderLaw] using (integrable_field (skCoeff n) σ).const_mul β

theorem block_partition (β : ℝ) (n m : ℕ) (J : (Edge n ⊕ Edge m) → ℝ) :
    partition (fun σ => β * field (blockCoeff n m) J σ) =
      partition (fun σ => β * hamiltonian n (fun e => J (Sum.inl e)) σ) *
      partition (fun τ => β * hamiltonian m (fun e => J (Sum.inr e)) τ) := by
  let e : (Configuration n × Configuration m) ≃ Configuration (n+m) := Fin.appendEquiv n m
  rw [partition, ← e.sum_comp]
  simp only [Fintype.sum_prod_type, e]
  change (∑ σ : Configuration n, ∑ τ : Configuration m,
    Real.exp (β * field (blockCoeff n m) J (Fin.append σ τ))) = _
  have he (σ : Configuration n) (τ : Configuration m) :
      field (blockCoeff n m) J (Fin.append σ τ) =
      hamiltonian n (fun e => J (Sum.inl e)) σ + hamiltonian m (fun e => J (Sum.inr e)) τ := by
    simp only [field,blockCoeff,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      restrictLeft_append,restrictRight_append]
    rw [← field, ← field]
    rw [field_skCoeff,field_skCoeff]
  simp_rw [he,mul_add,Real.exp_add]
  simp only [partition,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem block_logPartition (β : ℝ) (n m : ℕ) (J : (Edge n ⊕ Edge m) → ℝ) :
    logPartition (fun σ => β * field (blockCoeff n m) J σ) =
      logPartition (fun σ => β * hamiltonian n (fun e => J (Sum.inl e)) σ) +
      logPartition (fun τ => β * hamiltonian m (fun e => J (Sum.inr e)) τ) := by
  rw [logPartition,block_partition,Real.log_mul (partition_pos _).ne' (partition_pos _).ne']
  rfl

theorem expected_block_logPartition (β : ℝ) (n m : ℕ) :
    (∫ J, logPartition (fun σ => β * field (blockCoeff n m) J σ)
      ∂gaussianLaw (Edge n ⊕ Edge m)) = pressure β n + pressure β m := by
  let T : ((Disorder n) × (Disorder m)) ≃ᵐ ((Edge n ⊕ Edge m) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Edge n ⊕ Edge m => ℝ)).symm
  have hp : MeasurePreserving T ((disorderLaw n).prod (disorderLaw m))
      (gaussianLaw (Edge n ⊕ Edge m)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => gaussianReal 0 1)
  rw [← hp.integral_comp' (fun J => logPartition (fun σ => β * field (blockCoeff n m) J σ))]
  simp_rw [block_logPartition]
  change (∫ J, logPartition (fun σ => β * hamiltonian n J.1 σ) +
    logPartition (fun τ => β * hamiltonian m J.2 τ) ∂(disorderLaw n).prod (disorderLaw m)) = _
  have : IsProbabilityMeasure (disorderLaw n) := by unfold disorderLaw; infer_instance
  have : IsProbabilityMeasure (disorderLaw m) := by unfold disorderLaw; infer_instance
  rw [integral_add ((pressure_integrable β n).comp_fst _) ((pressure_integrable β m).comp_snd _)]
  rw [integral_fun_fst (fun J : Disorder n => logPartition (fun σ => β * hamiltonian n J σ)),
    integral_fun_snd (fun J : Disorder m => logPartition (fun σ => β * hamiltonian m J σ))]
  simp [pressure]

theorem pressure_superadditive_pos (β : ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    pressure β n + pressure β m ≤ pressure β (n+m) := by
  have hinc (σ τ : Configuration (n+m)) :
      (∑ k, (β*blockCoeff n m σ k-β*blockCoeff n m τ k)^2) ≤
      ∑ k, (β*skCoeff (n+m) σ k-β*skCoeff (n+m) τ k)^2 := by
    rw [scaled_increment,scaled_increment]
    exact mul_le_mul_of_nonneg_left (blockCoeff_increment hn hm σ τ) (sq_nonneg β)
  have h := expected_field_logPartition_le (fun σ k => β*blockCoeff n m σ k)
    (fun σ k => β*skCoeff (n+m) σ k) hinc
  simp_rw [field_scale,field_skCoeff] at h
  rw [expected_block_logPartition] at h
  exact h

@[simp] theorem pressure_zero (β : ℝ) : pressure β 0 = 0 := by
  simp [pressure,logPartition,partition,hamiltonian]

theorem pressure_superadditive (β : ℝ) (n m : ℕ) :
    pressure β n + pressure β m ≤ pressure β (n+m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  exact pressure_superadditive_pos β hn hm

end SKQAOA

end

end OAI
