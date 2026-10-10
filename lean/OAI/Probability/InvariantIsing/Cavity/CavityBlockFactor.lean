import OAI.Probability.InvariantIsing.Core.Model
import OAI.Probability.InvariantIsing.Core.Ward

namespace OAI

/-! Exact finite-volume algebra for the coupled cavity comparison.  The
spectral coupling and its Gaussian limit are separate source obligations. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityQuadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, y i * A i j * y j

def cavityLogFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin d → ℝ) (ε : Spin n) : ℝ :=
  cavityQuadratic K y + (∑ i, ∑ j, y i * L i j * spinValue (ε j)) +
    cavityQuadratic C (fun j => spinValue (ε j))

lemma cavityQuadratic_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    cavityQuadratic (A - B) y = cavityQuadratic A y - cavityQuadratic B y := by
  simp only [cavityQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- The exact exponent difference in `cav:factor`, with no commutativity
assumption on the two symmetric special-coordinate blocks. -/
theorem cavity_block_factor {d n : ℕ} (A A0 : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin d → ℝ) (ε : Spin n) :
    (1 / 2 : ℝ) * (∑ i : Fin d ⊕ Fin n, ∑ j : Fin d ⊕ Fin n,
      Sum.elim y (fun a => spinValue (ε a)) i *
        (Matrix.fromBlocks A L L.transpose C) i j *
        Sum.elim y (fun a => spinValue (ε a)) j) - cavityQuadratic A0 y =
      cavityLogFactor (A - A0) L C y ε := by
  have hcross : (∑ j : Fin n, ∑ i : Fin d, spinValue (ε j) * L i j * y i) =
      ∑ i : Fin d, ∑ j : Fin n, y i * L i j * spinValue (ε j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring_nf
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Finset.sum_add_distrib]
  rw [hcross]
  unfold cavityLogFactor
  rw [cavityQuadratic_sub]
  unfold cavityQuadratic
  ring_nf

/-- The base Gibbs law times the independent uniform probability on the
cavity cube, evaluated on the positive cavity factor. -/
def cavityFactorMean {N n : ℕ} (H : Spin N → ℝ) (V : Spin N → Spin n → ℝ) : ℝ :=
  (Fintype.card (Spin n) : ℝ)⁻¹ *
    ∑ σ, (Real.exp (H σ) / ∑ τ, Real.exp (H τ)) * ∑ ε, Real.exp (V σ ε)

lemma cavityFactorMean_eq_gibbsAverage {N n : ℕ} (H : Spin N → ℝ)
    (V : Spin N → Spin n → ℝ) :
    cavityFactorMean H V = gibbsAverage (fun _ => 1) H
      (fun σ => (Fintype.card (Spin n) : ℝ)⁻¹ * ∑ ε, Real.exp (V σ ε)) := by
  simp only [cavityFactorMean, gibbsAverage, finiteGibbs, finitePartition, one_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring_nf

lemma cavityFactorMean_eq_ratio {N n : ℕ} (H : Spin N → ℝ)
    (V : Spin N → Spin n → ℝ) :
    cavityFactorMean H V = (Fintype.card (Spin n) : ℝ)⁻¹ *
      ((∑ x : Spin N × Spin n, Real.exp (H x.1 + V x.1 x.2)) /
        ∑ σ, Real.exp (H σ)) := by
  unfold cavityFactorMean
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  congr 1
  simp only [Fintype.sum_prod_type, Real.exp_add, Finset.mul_sum]

lemma cavityFactorMean_pos {N n : ℕ} (H : Spin N → ℝ) (V : Spin N → Spin n → ℝ) :
    0 < cavityFactorMean H V := by
  rw [cavityFactorMean_eq_ratio]
  have hc : (0 : ℝ) < Fintype.card (Spin n) := by exact_mod_cast Fintype.card_pos
  exact mul_pos (inv_pos.mpr hc) (div_pos (sum_exp_pos _) (sum_exp_pos H))

/-- Exact finite log-partition increment for probability-normalized
partition functions, at the base endpoint of the cavity interpolation. -/
theorem logPartition_cavity_increment {N n : ℕ} (H : Spin N → ℝ)
    (V : Spin N → Spin n → ℝ) :
    logPartition (fun x : Spin N × Spin n => H x.1 + V x.1 x.2) - logPartition H =
      Real.log (cavityFactorMean H V) := by
  have hN : (Fintype.card (Spin N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card (Spin n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfull := (sum_exp_pos (fun x : Spin N × Spin n => H x.1 + V x.1 x.2)).ne'
  have hbase := (sum_exp_pos H).ne'
  rw [logPartition_eq, logPartition_eq, cavityFactorMean_eq_ratio,
    Real.log_mul (inv_ne_zero hn) (div_ne_zero hfull hbase), Real.log_inv,
    Real.log_div hfull hbase]
  simp only [Fintype.card_prod, Nat.cast_mul]
  rw [Real.log_mul hN hn]
  ring_nf

theorem logPartition_cavityBlock_increment {N d n : ℕ} (H : Spin N → ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y : Spin N → Fin d → ℝ) :
    logPartition (fun x : Spin N × Spin n => H x.1 + cavityLogFactor K L C (y x.1) x.2) -
      logPartition H = Real.log (cavityFactorMean H (fun σ ε => cavityLogFactor K L C (y σ) ε)) :=
  logPartition_cavity_increment (N := N) (n := n) H
    (fun σ ε => cavityLogFactor K L C (y σ) ε)

end InvariantIsing

end

end OAI
