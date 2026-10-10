import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorPromise

namespace OAI

/-! Identification of the encoded source's original swap-form variational
energy with the complete finite matrix used by all mediator stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

def SquareLatticeHeisenberg.bonds (d : SquareLatticeHeisenberg) :
    MediatorIteration.Bonds d.vertices d.edges where
  left := d.left
  right := d.right
  weight := d.coefficient

theorem sourceSpinMass_norm_sq {n : ℕ} (p : MediatorLowSpace n) :
    sourceSpinMass (fun s => p s) = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [sourceSpinMass, Complex.normSq_eq_norm_sq]

theorem sourceGraphMatrix_action (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    d.bonds.matrix *ᵥ u = sourceHamiltonian d u := by
  unfold MediatorIteration.Bonds.matrix SquareLatticeHeisenberg.bonds sourceGraphMatrix
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, sourceHeisenbergMatrix_mulVec,
    ]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_ratCast]
  rfl

theorem sourceGraphMatrix_form (d : SquareLatticeHeisenberg)
    (p : MediatorLowSpace d.vertices) :
    ⟪p, spinMatrixOperator d.bonds.matrix p⟫_ℝ = sourceHamiltonianForm d (fun s => p s) := by
  rw [HubbardGlobal.euclidean_real_inner, sourceHamiltonianForm_eq_expectation]
  have hact : spinMatrixOperator d.bonds.matrix p =
      WithLp.toLp 2 (sourceHamiltonian d (fun s => p s)) := by
    ext s
    exact congrFun (sourceGraphMatrix_action d (fun s => p s)) s
  rw [hact, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [RCLike.inner_apply, mul_comm]
  rfl

/-- The mediator input is the actual source energy in the published promise. -/
theorem sourceMatrixBottom_eq_realSource (d : SquareLatticeHeisenberg) :
    sourceMatrixBottom d.vertices d.bonds.matrix = realSourceGroundEnergy d := by
  obtain ⟨p, hp, hb, hmin⟩ := sourceMatrixBottom_minimizer d.vertices d.bonds.matrix
  have hmass : sourceSpinMass (fun s => p s) = 1 := by rw [sourceSpinMass_norm_sq, hp]; norm_num
  apply le_antisymm
  · apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    let q : MediatorLowSpace d.vertices := WithLp.toLp 2 u
    have hq : ‖q‖ = 1 := by
      have hs : ‖q‖ ^ 2 = 1 := (sourceSpinMass_norm_sq q).symm.trans hu
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hs)
    rw [hb]
    simpa only [sourceGraphMatrix_form, q] using hmin q hq
  · rw [hb, sourceGraphMatrix_form]
    exact realSourceGroundEnergy_le_trial d (fun s => p s) hmass

theorem source_three_stage_bottom (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(d.coefficient e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(d.coefficient e : ℝ)|) :
    |sourceMatrixBottom (d.vertices + d.edges * 2 + d.edges * 2 * 2 +
        (d.edges * 2 + d.edges * 2 * 2) * 2)
      (MediatorIteration.finalGraph d.bonds W G).matrix +
        (MediatorIteration.offset d.bonds W G : ℝ) - realSourceGroundEnergy d| ≤ 3 / (512 * G) := by
  rw [← sourceMatrixBottom_eq_realSource]
  exact MediatorIteration.three_stage_bottom d.bonds d.edge_ne hW hG hJ hJl

end ContinuumCoulomb

end

end OAI
