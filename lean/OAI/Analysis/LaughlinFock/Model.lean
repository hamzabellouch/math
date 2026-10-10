import Mathlib
import OAI.Analysis.Laughlin.Model

namespace OAI

/-! Model. -/
noncomputable section

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

abbrev Orbital (Q : ℕ) := Fin (Q + 1)
abbrev Occupation (Q : ℕ) := Finset (Orbital Q)
abbrev FockSpace (Q : ℕ) := EuclideanSpace ℂ (Occupation Q)
abbrev FockMatrix (Q : ℕ) := Matrix (Occupation Q) (Occupation Q) ℂ

 
def tensorPairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  _root_.OAI.Laughlin.pairCoefficient Q p i j

 
def pairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  Real.sqrt 2 * tensorPairCoefficient Q p i j

 

def annihilator (Q : ℕ) (j : Orbital Q) : FockMatrix Q := fun A B =>
  if j ∈ B ∧ A = B.erase j then
    (-1 : ℂ) ^ (B.filter (fun i => i < j)).card
  else 0

 

def pairAnnihilator (Q p : ℕ) : FockMatrix Q :=
  ∑ i : Orbital Q, ∑ j : Orbital Q,
    if i < j then
      (pairCoefficient Q p i j : ℂ) • (annihilator Q j * annihilator Q i)
    else 0

 

def hamiltonian (Q : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range (2 * Q - 1),
    (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p

 
abbrev SectorOccupation (Q n : ℕ) := {A : Occupation Q // A.card = n}

 
def sectorHamiltonian (Q n : ℕ) :
    Matrix (SectorOccupation Q n) (SectorOccupation Q n) ℂ :=
  (hamiltonian Q).submatrix Subtype.val Subtype.val

 
def gammaStar : ℝ := 4616733319001 / 10 ^ 14

 
def FockInequality (Q : ℕ) (γ : ℝ) : Prop :=
  (hamiltonian Q * hamiltonian Q - γ • hamiltonian Q).PosSemidef

 

 
theorem pairCoefficient_eq (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p i j =
      if i.val + j.val = p + 1 then
        ((i.val : ℝ) - (j.val : ℝ)) *
          Real.sqrt (((Q.descFactorial i.val : ℝ) * (Q.descFactorial j.val : ℝ) *
            (p.factorial : ℝ)) /
            ((Q : ℝ) * ((2 * Q - 2).descFactorial p : ℝ) *
              (i.val.factorial : ℝ) * (j.val.factorial : ℝ)))
      else 0 := by
  unfold pairCoefficient tensorPairCoefficient Laughlin.pairCoefficient
  split_ifs <;> simp [Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 2 by norm_num),
    mul_comm (Real.sqrt 2)]

 
theorem hamiltonian_posSemidef (Q : ℕ) : (hamiltonian Q).PosSemidef := by
  unfold hamiltonian
  exact Matrix.posSemidef_sum _ (fun p _ => Matrix.posSemidef_conjTranspose_mul_self _)

theorem hamiltonian_isHermitian (Q : ℕ) : (hamiltonian Q).IsHermitian :=
  (hamiltonian_posSemidef Q).isHermitian

 
theorem sectorHamiltonian_posSemidef (Q n : ℕ) :
    (sectorHamiltonian Q n).PosSemidef :=
  (hamiltonian_posSemidef Q).submatrix _

 
theorem gammaStar_gt_one_twenty_fifth : (1 / 25 : ℝ) < gammaStar := by
  norm_num [gammaStar]

 

theorem final_margin_arithmetic :
    (1 : ℝ) - 93527408868499 / 10 ^ 14 - 61 / 4096 -
      1222 * (3 / 10 ^ 6) = gammaStar := by
  norm_num [gammaStar]

 

theorem annihilator_card {Q : ℕ} (j : Orbital Q) (A B : Occupation Q)
    (h : annihilator Q j A B ≠ 0) : A.card + 1 = B.card := by
  by_cases hc : j ∈ B ∧ A = B.erase j
  · rcases hc with ⟨hj, rfl⟩
    exact Finset.card_erase_add_one hj
  · exact (h (by simp [annihilator, hc])).elim

theorem annihilator_entry_eq_zero {Q : ℕ} (j : Orbital Q) (A B : Occupation Q)
    (h : A.card + 1 ≠ B.card) : annihilator Q j A B = 0 := by
  by_contra hh
  exact h (annihilator_card j A B hh)

 
theorem pairAnnihilator_entry_eq_zero {Q : ℕ} (p : ℕ) (A B : Occupation Q)
    (h : A.card + 2 ≠ B.card) : pairAnnihilator Q p A B = 0 := by
  classical
  simp only [pairAnnihilator, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul]
    suffices hc : (annihilator Q j * annihilator Q i) A B = 0 by simp [hc]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro C _
    by_cases hAC : A.card + 1 = C.card
    · have hCB : C.card + 1 ≠ B.card := by omega
      rw [annihilator_entry_eq_zero i C B hCB, mul_zero]
    · rw [annihilator_entry_eq_zero j A C hAC, zero_mul]
  · rfl

 
theorem hamiltonian_entry_eq_zero {Q : ℕ} (A B : Occupation Q)
    (h : A.card ≠ B.card) : hamiltonian Q A B = 0 := by
  classical
  simp only [hamiltonian, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro C _
  by_cases hCA : C.card + 2 = A.card
  · have hCB : C.card + 2 ≠ B.card := by omega
    rw [pairAnnihilator_entry_eq_zero p C B hCB, mul_zero]
  · rw [pairAnnihilator_entry_eq_zero p C A hCA, star_zero, zero_mul]

 

theorem sectorHamiltonian_eq_zero_of_le_one (Q n : ℕ) (hn : n ≤ 1) :
    sectorHamiltonian Q n = 0 := by
  classical
  ext A B
  change hamiltonian Q A.val B.val = 0
  simp only [hamiltonian, Matrix.sum_apply, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro C _
  have hCB : C.card + 2 ≠ B.val.card := by rw [B.property]; omega
  rw [pairAnnihilator_entry_eq_zero p C B.val hCB, mul_zero]

@[simp] theorem sectorHamiltonian_zero_particles (Q : ℕ) :
    sectorHamiltonian Q 0 = 0 := sectorHamiltonian_eq_zero_of_le_one Q 0 (by omega)

@[simp] theorem sectorHamiltonian_one_particle (Q : ℕ) :
    sectorHamiltonian Q 1 = 0 := sectorHamiltonian_eq_zero_of_le_one Q 1 (by omega)

 

theorem sectorHamiltonian_square (Q n : ℕ) :
    (hamiltonian Q * hamiltonian Q).submatrix
        (Subtype.val : SectorOccupation Q n → Occupation Q) Subtype.val =
      sectorHamiltonian Q n * sectorHamiltonian Q n := by
  classical
  ext A B
  change (∑ C : Occupation Q, hamiltonian Q A.val C * hamiltonian Q C B.val) =
    ∑ C : SectorOccupation Q n, hamiltonian Q A.val C.val * hamiltonian Q C.val B.val
  let f : Occupation Q → ℂ := fun C => hamiltonian Q A.val C * hamiltonian Q C B.val
  change ∑ C, f C = ∑ C : SectorOccupation Q n, f C.val
  calc
    _ = ∑ C ∈ Finset.univ.filter (fun C : Occupation Q => C.card = n), f C := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C _ hC
      have hc : A.val.card ≠ C.card := by
        rw [A.property]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using hC
      simp only [f, hamiltonian_entry_eq_zero A.val C hc, zero_mul]
    _ = _ := Finset.sum_subtype _ (by intro C; simp) f

 

theorem sector_inequality_of_fock {Q : ℕ} {γ : ℝ} (h : FockInequality Q γ)
    (n : ℕ) :
    (sectorHamiltonian Q n * sectorHamiltonian Q n - γ • sectorHamiltonian Q n).PosSemidef := by
  have hc := h.submatrix (Subtype.val : SectorOccupation Q n → Occupation Q)
  change ((hamiltonian Q * hamiltonian Q - γ • hamiltonian Q).submatrix
    (Subtype.val : SectorOccupation Q n → Occupation Q) Subtype.val).PosSemidef at hc
  simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
    sectorHamiltonian_square, sectorHamiltonian] using hc

 
theorem gram_quadratic_form {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (ψ : κ → ℂ) :
    star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ) = star (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

 

theorem hamiltonian_quadratic_form (Q : ℕ) (ψ : Occupation Q → ℂ) :
    (star ψ ⬝ᵥ (hamiltonian Q *ᵥ ψ)).re =
      ∑ p ∈ Finset.range (2 * Q - 1), ∑ A : Occupation Q,
        ‖(pairAnnihilator Q p *ᵥ ψ) A‖ ^ 2 := by
  classical
  simp only [hamiltonian, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [gram_quadratic_form]
  simp [dotProduct, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow]

 
theorem occupation_card_le (Q : ℕ) (A : Occupation Q) : A.card ≤ Q + 1 := by
  simpa using Finset.card_le_univ A

 

theorem sector_quadratic_form_decomposition (Q : ℕ) (M : FockMatrix Q)
    (hM : ∀ A B : Occupation Q, A.card ≠ B.card → M A B = 0)
    (ψ : Occupation Q → ℂ) :
    star ψ ⬝ᵥ (M *ᵥ ψ) =
      ∑ n ∈ Finset.range (Q + 2),
        star (fun A : SectorOccupation Q n => ψ A.val) ⬝ᵥ
          (M.submatrix (Subtype.val : SectorOccupation Q n → Occupation Q)
            Subtype.val *ᵥ (fun A : SectorOccupation Q n => ψ A.val)) := by
  classical
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.submatrix_apply]
  have hcard : ∀ A ∈ (Finset.univ : Finset (Occupation Q)),
      A.card ∈ Finset.range (Q + 2) := by
    intro A _
    have := occupation_card_le Q A
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hcard]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_subtype (p := fun A : Occupation Q => A.card = n) _ (by intro A; simp)]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  calc
    _ = ∑ B ∈ Finset.univ.filter (fun B : Occupation Q => B.card = n),
        M A.val B * ψ B := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro B _ hB
      have hAB : A.val.card ≠ B.card := by
        rw [A.property]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using hB
      simp only [hM A.val B hAB, zero_mul]
    _ = _ := Finset.sum_subtype _ (by intro B; simp) _

 

theorem posSemidef_of_sectors {Q : ℕ} {M : FockMatrix Q} (hHerm : M.IsHermitian)
    (hM : ∀ A B : Occupation Q, A.card ≠ B.card → M A B = 0)
    (h : ∀ n : ℕ, n ≤ Q + 1 →
      (M.submatrix (Subtype.val : SectorOccupation Q n → Occupation Q)
        Subtype.val).PosSemidef) : M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro ψ
  rw [sector_quadratic_form_decomposition Q M hM ψ]
  apply Finset.sum_nonneg
  intro n hn
  have hn' : n ≤ Q + 1 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
  exact (h n hn').dotProduct_mulVec_nonneg _

 
theorem gapMatrix_entry_eq_zero {Q : ℕ} (γ : ℝ) (A B : Occupation Q)
    (h : A.card ≠ B.card) :
    (hamiltonian Q * hamiltonian Q - γ • hamiltonian Q) A B = 0 := by
  classical
  simp only [Matrix.sub_apply, Matrix.smul_apply, hamiltonian_entry_eq_zero A B h,
    smul_zero, sub_zero, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro C _
  by_cases hAC : A.card = C.card
  · have hCB : C.card ≠ B.card := by omega
    rw [hamiltonian_entry_eq_zero C B hCB, mul_zero]
  · rw [hamiltonian_entry_eq_zero A C hAC, zero_mul]

 

theorem fock_inequality_iff_sectors (Q : ℕ) (γ : ℝ) :
    FockInequality Q γ ↔ ∀ n : ℕ, n ≤ Q + 1 →
      (sectorHamiltonian Q n * sectorHamiltonian Q n -
        γ • sectorHamiltonian Q n).PosSemidef := by
  classical
  constructor
  · intro h n _
    exact sector_inequality_of_fock h n
  · intro h
    have hHerm : (hamiltonian Q * hamiltonian Q).IsHermitian := by
      simpa only [pow_two] using (hamiltonian_isHermitian Q).pow 2
    apply posSemidef_of_sectors
      (hHerm.sub ((hamiltonian_isHermitian Q).smul (show IsSelfAdjoint γ by rfl)))
      (gapMatrix_entry_eq_zero γ)
    intro n hn
    simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
      sectorHamiltonian_square, sectorHamiltonian] using h n hn
end LaughlinFock
end

end OAI
