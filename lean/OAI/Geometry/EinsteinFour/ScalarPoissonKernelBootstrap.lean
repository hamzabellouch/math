import OAI.Geometry.EinsteinFour.ScalarPoissonKernelLocalRegularity
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMultiplier

namespace OAI

/-! Integer-order elliptic bootstrap from the actual distributional
commutator and the proved small-coefficient H2 regularity theorem. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

private theorem scalar_derivative_fourier (i : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i u = (2 * Real.pi * Complex.I) •
      fourierMultiplierCLM ℂ (fun x : V => (x i : ℂ)) u := by
  rw [scalarCoordinateDerivative, lineDeriv_eq_fourierMultiplierCLM]
  apply congrArg (fun a : V → ℂ => (2 * Real.pi * Complex.I) • fourierMultiplierCLM ℂ a u)
  funext x
  simp only [EuclideanSpace.inner_basisFun_real]

/-- Coordinate derivatives commute for every tempered distribution. -/
theorem scalarCoordinateDerivative_commute (i j : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative j u) =
      scalarCoordinateDerivative j (scalarCoordinateDerivative i u) := by
  simp_rw [scalar_derivative_fourier, map_smul, smul_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop) (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop) (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop)]
  apply congrArg (fun a : V → ℂ =>
    ((2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)) • fourierMultiplierCLM ℂ a u)
  funext x
  simp only [Pi.mul_apply, mul_comm]

private theorem scalar_derivative_add (k : Fin 4) (u v : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (u + v) =
      scalarCoordinateDerivative k u + scalarCoordinateDerivative k v :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)).map_add u v

private theorem scalar_derivative_sub (k : Fin 4) (u v : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (u - v) =
      scalarCoordinateDerivative k u - scalarCoordinateDerivative k v :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)).map_sub u v

private theorem scalar_derivative_real_smul (k : Fin 4) (c : ℝ) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (c • u) = c • scalarCoordinateDerivative k u :=
  (LineDeriv.lineDerivOpCLM ℝ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)).map_smul c u

private theorem scalar_derivative_sum (k : Fin 4) (u : Fin 4 → 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (∑ i, u i) = ∑ i, scalarCoordinateDerivative k (u i) :=
  map_sum (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)) u Finset.univ

private theorem scalar_derivative_laplacian (k : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (Δ u) = Δ (scalarCoordinateDerivative k u) := by
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ),
    TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
  change scalarCoordinateDerivative k (∑ i : Fin 4,
    scalarCoordinateDerivative i (scalarCoordinateDerivative i u)) =
      ∑ i : Fin 4, scalarCoordinateDerivative i
        (scalarCoordinateDerivative i (scalarCoordinateDerivative k u))
  rw [scalar_derivative_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarCoordinateDerivative_commute k i, scalarCoordinateDerivative_commute k i]

private theorem scalar_derivative_helmholtz (k : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (normalizedScalarHelmholtz u) =
      normalizedScalarHelmholtz (scalarCoordinateDerivative k u) := by
  rw [normalizedScalarHelmholtz, normalizedScalarHelmholtz,
    scalar_derivative_sub, scalar_derivative_real_smul, scalar_derivative_laplacian]

/-- Exact first commutator of the variable-coefficient operator. -/
theorem scalarPerturbedOperator_derivative (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (k : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (scalarPerturbedOperator a b u) =
      scalarPerturbedOperator a b (scalarCoordinateDerivative k u) +
        (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (D k (a i j))
          (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) +
        ∑ i : Fin 4, smulLeftCLM ℂ (D k (b i)) (scalarCoordinateDerivative i u) := by
  have hcomm (i j : Fin 4) :
      scalarCoordinateDerivative k (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) =
        scalarCoordinateDerivative i (scalarCoordinateDerivative j (scalarCoordinateDerivative k u)) := by
    rw [scalarCoordinateDerivative_commute k i, scalarCoordinateDerivative_commute k j]
  have hcomm1 (i : Fin 4) : scalarCoordinateDerivative k (scalarCoordinateDerivative i u) =
      scalarCoordinateDerivative i (scalarCoordinateDerivative k u) :=
    scalarCoordinateDerivative_commute k i u
  simp only [scalarPerturbedOperator, scalar_derivative_add, scalar_derivative_helmholtz,
    scalar_derivative_sum, scalarCoordinateDerivative_multiplier, scalarSchwartzCoordinateDerivative,
    hcomm, hcomm1,
    Finset.sum_add_distrib]
  abel

private theorem scalar_sobolev_nat_step (n : ℕ) (u : 𝓢'(V, ℂ)) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 u ↔ MemSobolev (n : ℝ) 2 u ∧
      ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
  simpa only [Nat.cast_add, Nat.cast_one] using scalar_memSobolev_succ_iff (n : ℝ) u

private theorem scalar_sobolev_sum (n : ℕ) (u : Fin 4 → 𝓢'(V, ℂ))
    (hu : ∀ i, MemSobolev (n : ℝ) 2 (u i)) :
    MemSobolev (n : ℝ) 2 (∑ i : Fin 4, u i) := by
  have hs (s : Finset (Fin 4)) : MemSobolev (n : ℝ) 2 (∑ i ∈ s, u i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ (n : ℝ) 2
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (hu i).add ih
  exact hs Finset.univ

/-- Every integer Sobolev order of the right-hand side gives two additional
orders for the original L2 solution. -/
theorem scalar_small_elliptic_integer_regularity
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (n : ℕ) (u f : 𝓢'(V, ℂ)) (hu : MemSobolev 0 2 u)
    (hf : MemSobolev (n : ℝ) 2 f) (heq : scalarPerturbedOperator a b u = f) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 u := by
  induction n generalizing u f with
  | zero =>
      obtain ⟨u, rfl⟩ := memSobolev_zero_iff.mp hu
      obtain ⟨f, rfl⟩ := memSobolev_zero_iff.mp (by simpa only [Nat.cast_zero] using hf)
      simpa using scalar_small_elliptic_gain_two a b δ hδ ha ha1 ha2 hb hb1 hsmall u f heq
  | succ n ih =>
      have hfstep := (scalar_sobolev_nat_step n f).mp hf
      have hu2 := ih u f hu hfstep.1 heq
      have hustep := (scalar_sobolev_nat_step (n + 1) u).mp hu2
      have hD (k : Fin 4) := (scalar_sobolev_nat_step n (scalarCoordinateDerivative k u)).mp
        (hustep.2 k)
      have hderiv (k : Fin 4) :
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (scalarCoordinateDerivative k u) := by
        let A : 𝓢'(V, ℂ) := ∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (D k (a i j))
          (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))
        let B : 𝓢'(V, ℂ) := ∑ i : Fin 4, smulLeftCLM ℂ (D k (b i))
          (scalarCoordinateDerivative i u)
        have hA : MemSobolev (n : ℝ) 2 A := by
          apply scalar_sobolev_sum n
          intro i
          apply scalar_sobolev_sum n
          intro j
          exact scalar_memSobolev_schwartz_multiplier n _ _ ((hD j).2 i)
        have hB : MemSobolev (n : ℝ) 2 B := by
          apply scalar_sobolev_sum n
          intro i
          exact scalar_memSobolev_schwartz_multiplier n _ _ (hD i).1
        have hEq : scalarPerturbedOperator a b (scalarCoordinateDerivative k u) =
            scalarCoordinateDerivative k f - A - B := by
          calc
            _ = (scalarPerturbedOperator a b (scalarCoordinateDerivative k u) + A + B) - A - B := by abel
            _ = _ := by rw [← scalarPerturbedOperator_derivative, heq]
        exact ih _ _ ((hustep.2 k).mono (by positivity)) ((hfstep.2 k).sub hA |>.sub hB) hEq
      simpa only [Nat.add_assoc] using
        (scalar_sobolev_nat_step (n + 2) u).mpr ⟨hu2, hderiv⟩

end
end PositiveEinsteinFour.Geometry

end OAI
