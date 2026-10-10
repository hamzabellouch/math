import OAI.Analysis.Laughlin.Pair.FactorLimit
import OAI.Analysis.Laughlin.Fock.Hamiltonian
import Mathlib.Topology.Instances.Matrix

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

abbrev Occupations (L : ℕ) := Finset (Fin (L+1))

noncomputable def pairMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    Matrix (Occupations L) (Occupations L) ℂ := fun A B =>
  ∑ i, ∑ j, c i j * (occupationBasis L).repr
    (annihilate j (annihilate i (occupationBasis L B))) A

noncomputable def planarCoefficient (p i j : ℕ) : ℂ :=
  ((pairLimitCoefficient p i j / Real.sqrt (2 : ℕ) : ℝ) : ℂ)

noncomputable def sphereCoefficient (Q p i j : ℕ) : ℂ :=
  ((modeFactor Q i * modeFactor Q j * pairFactor Q p *
    pairLimitCoefficient p i j / Real.sqrt 2 : ℝ) : ℂ)

theorem sphereCoefficient_eq (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (i j : Fin (Q+1)) :
    sphereCoefficient Q p i.val j.val = ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [sphereCoefficient,pairCoefficient_conjugation Q p hQ hp]

theorem sphereCoefficient_tendsto (p i j : ℕ) :
    Tendsto (fun Q => sphereCoefficient Q p i j) atTop (𝓝 (planarCoefficient p i j)) := by
  have h := ((((modeFactor_tendsto i).mul (modeFactor_tendsto j)).mul
    (pairFactor_tendsto p)).mul_const (pairLimitCoefficient p i j)).div_const (Real.sqrt 2)
  simpa only [one_mul,sphereCoefficient,planarCoefficient,Nat.cast_ofNat,Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

noncomputable def planarPairMatrix (L p : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  pairMatrix L (fun i j => planarCoefficient p i.val j.val)

noncomputable def spherePairMatrix (L Q p : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  pairMatrix L (fun i j => sphereCoefficient Q p i.val j.val)

theorem spherePairMatrix_tendsto (L p : ℕ) (A B : Occupations L) :
    Tendsto (fun Q => spherePairMatrix L Q p A B) atTop
      (𝓝 (planarPairMatrix L p A B)) := by
  unfold spherePairMatrix planarPairMatrix pairMatrix
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (sphereCoefficient_tendsto p i.val j.val).mul_const _

noncomputable def planarHamiltonian (L : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  ∑ p ∈ Finset.range (2*L+1), (planarPairMatrix L p)ᴴ * planarPairMatrix L p

noncomputable def sphereHamiltonian (L Q : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  ∑ p ∈ Finset.range (2*L+1), (spherePairMatrix L Q p)ᴴ * spherePairMatrix L Q p

theorem sphereHamiltonian_tendsto (L : ℕ) (A B : Occupations L) :
    Tendsto (fun Q => sphereHamiltonian L Q A B) atTop (𝓝 (planarHamiltonian L A B)) := by
  simp only [sphereHamiltonian,planarHamiltonian,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply tendsto_finsetSum
  intro p hp
  apply tendsto_finsetSum
  intro C hC
  exact ((spherePairMatrix_tendsto L p C A).star).mul (spherePairMatrix_tendsto L p C B)

noncomputable def pairEnergy (L : ℕ)
    (P : ℕ → Matrix (Occupations L) (Occupations L) ℂ) (x : Occupations L → ℂ) : ℝ :=
  ∑ p ∈ Finset.range (2*L+1), ∑ A, ‖(P p *ᵥ x) A‖^2

noncomputable def squareNorm (L : ℕ) (H : Matrix (Occupations L) (Occupations L) ℂ)
    (x : Occupations L → ℂ) : ℝ := ∑ A, ‖(H *ᵥ x) A‖^2

theorem sphere_pairEnergy_tendsto (L : ℕ) (x : Occupations L → ℂ) :
    Tendsto (fun Q => pairEnergy L (spherePairMatrix L Q) x) atTop
      (𝓝 (pairEnergy L (planarPairMatrix L) x)) := by
  unfold pairEnergy
  apply tendsto_finsetSum
  intro p hp
  apply tendsto_finsetSum
  intro A hA
  apply Filter.Tendsto.pow
  apply Filter.Tendsto.norm
  simp only [Matrix.mulVec,dotProduct]
  apply tendsto_finsetSum
  intro B hB
  exact (spherePairMatrix_tendsto L p A B).mul_const (x B)

theorem sphere_squareNorm_tendsto (L : ℕ) (x : Occupations L → ℂ) :
    Tendsto (fun Q => squareNorm L (sphereHamiltonian L Q) x) atTop
      (𝓝 (squareNorm L (planarHamiltonian L) x)) := by
  unfold squareNorm
  apply tendsto_finsetSum
  intro A hA
  apply Filter.Tendsto.pow
  apply Filter.Tendsto.norm
  simp only [Matrix.mulVec,dotProduct]
  apply tendsto_finsetSum
  intro B hB
  exact (sphereHamiltonian_tendsto L A B).mul_const (x B)

theorem endpoint_of_sphere_blocks (L : ℕ) (γstar : ℝ) (hγstar : 0 < γstar)
    (x : Occupations L → ℂ)
    (hSphere : ∀ γ : ℝ, 0 < γ → γ < γstar → ∀ᶠ Q : ℕ in atTop,
      γ * pairEnergy L (spherePairMatrix L Q) x ≤ squareNorm L (sphereHamiltonian L Q) x) :
    γstar * pairEnergy L (planarPairMatrix L) x ≤ squareNorm L (planarHamiltonian L) x := by
  have hGap (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < γstar) :
      γ * pairEnergy L (planarPairMatrix L) x ≤ squareNorm L (planarHamiltonian L) x :=
    le_of_tendsto_of_tendsto ((sphere_pairEnergy_tendsto L x).const_mul γ)
      (sphere_squareNorm_tendsto L x) (hSphere γ hγ hγ')
  by_contra hn
  have hlt : squareNorm L (planarHamiltonian L) x <
      γstar * pairEnergy L (planarPairMatrix L) x := lt_of_not_ge hn
  have hE : 0 < pairEnergy L (planarPairMatrix L) x := by
    have hS : 0 ≤ squareNorm L (planarHamiltonian L) x :=
      Finset.sum_nonneg (fun A hA => sq_nonneg _)
    nlinarith
  obtain ⟨γ,hγ,hγ'⟩ := exists_between (div_lt_iff₀ hE |>.mpr hlt)
  have hS : 0 ≤ squareNorm L (planarHamiltonian L) x :=
    Finset.sum_nonneg (fun A hA => sq_nonneg _)
  have hγpos : 0 < γ := lt_of_le_of_lt (div_nonneg hS hE.le) hγ
  have hc := hGap γ hγpos hγ'
  have hd := (div_lt_iff₀ hE).mp hγ
  linarith

end Laughlin.Planar

end OAI
