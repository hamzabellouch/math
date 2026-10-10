import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.SeriesJets

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {R σ τ ι : Type*} [CommRing R]

 theorem Jet.sum {n : ℕ} (s : Finset ι) {f g : ι → MvPowerSeries σ R}
    (h : ∀ i ∈ s, Jet n (f i) (g i)) : Jet n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  apply Jet.iff_coeff.mpr
  intro e he
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i hi => Jet.iff_coeff.mp (h i hi) e he

 theorem positively_weighted_triple {n : ℕ} {f f' h h' g g' : MvPowerSeries σ R}
    (hf : Jet n f f') (hg : Jet n g g') (h0 : Vanishes 1 h) (h0' : Vanishes 1 h')
    (hh : Jet (n+1) h h') : Jet (n+1) (f*h*g) (f'*h'*g') := by
  change Vanishes (n+1) (f*h*g - f'*h'*g')
  have heq : f*h*g - f'*h'*g' =
      (f-f')*h*g + f'*(h-h')*g + f'*h'*(g-g') := by ring
  rw [heq]
  apply Vanishes.add
  · exact ((Vanishes.mul hf h0).mul_right g).add
      ((Vanishes.mul_left hh f').mul_right g)
  · simpa only [Nat.add_comm, mul_assoc] using (h0'.mul hg).mul_left f'

variable [Fintype ι]

def correctionArguments (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (B : Matrix ι ι (MvPowerSeries σ R)) : τ ⊕ ι → MvPowerSeries σ R
  | .inl t => x t
  | .inr i => ∑ j, B i j * v j

def remainderValue (H : Matrix ι ι (MvPowerSeries (τ ⊕ ι) R))
    (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (B : Matrix ι ι (MvPowerSeries σ R)) : Matrix ι ι (MvPowerSeries σ R) :=
  fun i j => subst (correctionArguments x v B) (H i j)

def correctionOperator (b : Matrix ι ι (MvPowerSeries σ R))
    (H : Matrix ι ι (MvPowerSeries (τ ⊕ ι) R))
    (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (B : Matrix ι ι (MvPowerSeries σ R)) : Matrix ι ι (MvPowerSeries σ R) :=
  -b - B.transpose * remainderValue H x v B * B

 theorem correctionArguments_centered (x : τ → MvPowerSeries σ R)
    (v : ι → MvPowerSeries σ R) (hx : ∀ t, constantCoeff (x t) = 0)
    (hv : ∀ i, Vanishes 2 (v i)) (B : Matrix ι ι (MvPowerSeries σ R)) :
    ∀ z, constantCoeff (correctionArguments x v B z) = 0 := by
  intro z
  cases z with
  | inl t => exact hx t
  | inr i =>
    apply Vanishes.one_iff.mp
    exact (Vanishes.sum Finset.univ (fun j => B i j * v j)
      (fun j _ => (hv j).mul_left (B i j))).mono (by omega)

 theorem correctionArguments_jet (x : τ → MvPowerSeries σ R)
    (v : ι → MvPowerSeries σ R) (hv : ∀ i, Vanishes 2 (v i))
    {n : ℕ} {B B' : Matrix ι ι (MvPowerSeries σ R)}
    (hB : ∀ i j, Jet n (B i j) (B' i j)) :
    ∀ z, Jet (n+2) (correctionArguments x v B z) (correctionArguments x v B' z) := by
  intro z
  cases z with
  | inl t => exact Jet.refl _ _
  | inr i =>
    apply Jet.sum
    intro j _
    change Vanishes (n+2) (B i j * v j - B' i j * v j)
    rw [← sub_mul]
    exact (hB i j).mul (hv j)

variable [Finite σ] [Finite τ]

omit [Finite σ] in
 theorem remainderValue_positive (H : Matrix ι ι (MvPowerSeries (τ ⊕ ι) R))
    (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (hH : ∀ i j, Vanishes 1 (H i j)) (hx : ∀ t, constantCoeff (x t) = 0)
    (hv : ∀ i, Vanishes 2 (v i)) (B : Matrix ι ι (MvPowerSeries σ R)) (i j : ι) :
    Vanishes 1 (remainderValue H x v B i j) := by
  apply Vanishes.one_iff.mpr
  have ha := correctionArguments_centered x v hx hv B
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha
    (Vanishes.one_iff.mp (hH i j))

 theorem remainderValue_jet (H : Matrix ι ι (MvPowerSeries (τ ⊕ ι) R))
    (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (hx : ∀ t, constantCoeff (x t) = 0) (hv : ∀ i, Vanishes 2 (v i))
    {n : ℕ} {B B' : Matrix ι ι (MvPowerSeries σ R)}
    (hB : ∀ i j, Jet n (B i j) (B' i j)) (i j : ι) :
    Jet (n+2) (remainderValue H x v B i j) (remainderValue H x v B' i j) := by
  exact Jet.subst (correctionArguments_centered x v hx hv B)
    (correctionArguments_centered x v hx hv B') (correctionArguments_jet x v hv hB) (H i j)

 theorem correctionOperator_contracts (b : Matrix ι ι (MvPowerSeries σ R))
    (H : Matrix ι ι (MvPowerSeries (τ ⊕ ι) R))
    (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (hH : ∀ i j, Vanishes 1 (H i j)) (hx : ∀ t, constantCoeff (x t) = 0)
    (hv : ∀ i, Vanishes 2 (v i))
    {n : ℕ} {B B' : Matrix ι ι (MvPowerSeries σ R)}
    (hB : ∀ i j, Jet n (B i j) (B' i j)) (i j : ι) :
    Jet (n+1) (correctionOperator b H x v B i j) (correctionOperator b H x v B' i j) := by
  classical
  simp only [correctionOperator, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  apply Jet.sub (Jet.refl _ _)
  apply Jet.sum
  intro l _
  apply Jet.sum
  intro k _
  exact positively_weighted_triple (hB k i) (hB l j)
    (remainderValue_positive H x v hH hx hv B k l)
    (remainderValue_positive H x v hH hx hv B' k l)
    ((remainderValue_jet H x v hx hv hB k l).mono (by omega))

theorem exists_correction_matrix (b : Matrix ι ι (MvPowerSeries σ R))
    (H : Matrix ι ι (MvPowerSeries (τ ⊕ ι) R))
    (x : τ → MvPowerSeries σ R) (v : ι → MvPowerSeries σ R)
    (hH : ∀ i j, Vanishes 1 (H i j)) (hx : ∀ t, constantCoeff (x t) = 0)
    (hv : ∀ i, Vanishes 2 (v i)) :
    ∃ B : Matrix ι ι (MvPowerSeries σ R), B = -b - B.transpose * remainderValue H x v B * B := by
  let T : ((ι × ι) → MvPowerSeries σ R) → ((ι × ι) → MvPowerSeries σ R) :=
    fun B ij => correctionOperator b H x v (fun i j => B (i,j)) ij.1 ij.2
  have hT : ∀ n f g, Close n f g → Close (n+1) (T f) (T g) := by
    intro n f g hfg ij e he
    exact Jet.iff_coeff.mp (correctionOperator_contracts b H x v hH hx hv
      (fun i j => Jet.iff_coeff.mpr (hfg (i,j))) ij.1 ij.2) e he
  refine ⟨fun i j => fixedPoint T (i,j), ?_⟩
  funext i j
  exact (congrFun (fixedPoint_eq T hT) (i,j)).symm

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
