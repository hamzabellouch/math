import OAI.AlgebraicGeometry.PlaneCurves.ExponentMatrices

namespace OAI

/-!
# Local holomorphic jets and finite jet noncancellation
-/

section

/-! Holomorphy on the common local disk follows directly from the checked
normal convergence of the actual finite exponential sums. This avoids requiring
a global-entire theorem when only the source's fixed chart is used. -/

noncomputable section
open Filter Topology

namespace Nagata.Workers.W11

open Nagata.W07 Nagata.W22

/-- For sufficiently small positive parameters the literal normalized theta
series is holomorphic on the fixed unit disk. The proof takes the locally
uniform limit of its actual finite sums of entire exponential functions. -/
theorem eventually_differentiableOn_normalizedThetaSeries_disk
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ᶠ t in l, DifferentiableOn ℂ (normalizedThetaSeries n a K ε (τ t))
      {x : ℂ | ‖x‖ < 1} := by
  have hsum := eventually_normalizedThetaSeries_partialSums
    (K := K) (R := 1) ha han hε zero_le_one hτ hτpos
  apply hsum.mono
  intro t ht
  have hlocal := (ht.mono (show {x : ℂ | ‖x‖ < 1} ⊆ {x : ℂ | ‖x‖ ≤ 1}
    from fun x hx => (show ‖x‖ < 1 from hx).le)).tendstoLocallyUniformlyOn
  have hfinite : ∀ S : Finset ℤ, DifferentiableOn ℂ
      (fun x => ∑ p ∈ S, normalizedThetaTerm n a K ε (τ t) p x)
      {x : ℂ | ‖x‖ < 1} := by
    intro S
    apply DifferentiableOn.fun_sum
    intro p _
    have hd : Differentiable ℂ (normalizedThetaTerm n a K ε (τ t) p) := by
      unfold normalizedThetaTerm
      exact (differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp
    exact hd.differentiableOn
  exact hlocal.differentiableOn (Eventually.of_forall hfinite)
    (isOpen_lt continuous_norm continuous_const)

end Nagata.Workers.W11

end
end

section

/-!
# Actual mixed derivatives of separated local scalar expressions
-/

noncomputable section
open Filter Topology

namespace Nagata.Workers.W11

open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents

/-- First take `b` derivatives in `y`, then `ell` derivatives in `x`, at the
origin, exactly as in the source's jet rows. -/
def mixedJetAtZero (F : ℂ → ℂ → ℂ) (ell b : ℕ) : ℂ :=
  iteratedDeriv ell (fun x => iteratedDeriv b (F x) 0) 0

/-- The separated-variable formula, including zero derivative orders and zero
frequencies, holds for actual derivatives. -/
theorem mixedJetAtZero_separated (f : ℂ → ℂ) (j : ℂ) (ell b : ℕ) :
    mixedJetAtZero (fun x y => f x * Complex.exp (j * y)) ell b =
      iteratedDeriv ell f 0 * j ^ b := by
  have hy : (fun x => iteratedDeriv b (fun y => f x * Complex.exp (j * y)) 0) =
      fun x => f x * j ^ b := by
    funext x
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
    simp
  unfold mixedJetAtZero
  rw [hy, iteratedDeriv_mul_const_field]

/-- Genuine mixed-derivative matrix on the source's fixed row and column types. -/
def separatedJetMatrix (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ) :
    Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ :=
  fun row col => mixedJetAtZero
    (fun x y => coeff col x * Complex.exp ((col.val.1 : ℂ) * y))
    row.2.val row.1.val

/-- Coefficient derivative convergence implies entrywise convergence of the
actual mixed-derivative matrix to `B0`. -/
theorem tendsto_separatedJetMatrix_entries
    {α : Type*} {l : Filter α} (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (coeff : α → Column d (m : ℤ) a delta → ℂ → ℂ)
    (hcoeff : ∀ col ell, Tendsto (fun t => iteratedDeriv ell (coeff t col) 0) l
      (𝓝 ((col.val.2 : ℂ) ^ ell))) :
    ∀ row col, Tendsto (fun t => separatedJetMatrix d q m a delta (coeff t) row col)
      l (𝓝 (B0 d q m a delta row col)) := by
  intro row col
  simpa only [separatedJetMatrix, mixedJetAtZero_separated, B0] using
    (hcoeff col row.2.val).mul_const ((col.val.1 : ℂ) ^ row.1.val)

end Nagata.Workers.W11

end
end

section

/-! Mixed jets depend only on the genuine local germ on a neighborhood of the
origin. This connects a local chart identity with the finite jet conditions. -/

open Filter Topology

namespace Nagata.Workers.W11

/-- Equality on a genuine neighborhood in ℂ² implies equality of every mixed
iterated derivative at the origin. No global identity is required. -/
theorem mixedJetAtZero_congr_of_eventuallyEq
    {F G : ℂ → ℂ → ℂ} (ell b : ℕ)
    (h : ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0), F z.1 z.2 = G z.1 z.2) :
    mixedJetAtZero F ell b = mixedJetAtZero G ell b := by
  have hp : ∀ᶠ z : ℂ × ℂ in (𝓝 0) ×ˢ (𝓝 0), F z.1 z.2 = G z.1 z.2 := by
    simpa only [nhds_prod_eq] using h
  have hi : (fun x => iteratedDeriv b (F x) 0) =ᶠ[𝓝 0]
      (fun x => iteratedDeriv b (G x) 0) :=
    hp.curry.mono fun x hx => Filter.EventuallyEq.iteratedDeriv_eq b hx
  exact Filter.EventuallyEq.iteratedDeriv_eq ell hi

/-- A scalar expression vanishing on a chart neighborhood has all its prescribed
mixed jets zero. This is valid for each finite jet order independently. -/
theorem mixedJetAtZero_eq_zero_of_locally_zero
    {F : ℂ → ℂ → ℂ} (ell b : ℕ)
    (h : ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0), F z.1 z.2 = 0) :
    mixedJetAtZero F ell b = 0 := by
  have heq := mixedJetAtZero_congr_of_eventuallyEq (G := fun _ _ => 0) ell b h
  simpa [mixedJetAtZero] using heq

end Nagata.Workers.W11

end

section

/-!
# Actual finite scalar sums and their mixed jets

This is the analytic linearity bridge from the source's finite scalar expression
`H_F(x,y) = Σ coefficient_j(x) exp(j y)` to matrix multiplication. Smoothness
of the coefficient functions is explicit; totalized derivatives are not silently
treated as linear on arbitrary, possibly nondifferentiable functions.
-/

noncomputable section
open Filter Topology

namespace Nagata.Workers.W11

/-- Actual mixed derivatives commute with the finite scalar expansion when the
coefficient functions have the required derivatives. -/
theorem mixedJetAtZero_separated_sum {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (j c : ι → ℂ) (ell b : ℕ)
    (hf : ∀ i, ContDiffAt ℂ ell (f i) 0) :
    mixedJetAtZero (fun x y => ∑ i, c i * f i x * Complex.exp (j i * y)) ell b =
      ∑ i, c i * (iteratedDeriv ell (f i) 0 * j i ^ b) := by
  have hy : (fun x => iteratedDeriv b
      (fun y => ∑ i, c i * f i x * Complex.exp (j i * y)) 0) =
      fun x => ∑ i, c i * f i x * j i ^ b := by
    funext x
    rw [iteratedDeriv_fun_sum (I := Finset.univ)
      (f := fun i y => c i * f i x * Complex.exp (j i * y))
      (fun i _ => (contDiffAt_const.mul (contDiffAt_const.mul contDiffAt_id).cexp))]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
    simp
  unfold mixedJetAtZero
  rw [hy, iteratedDeriv_fun_sum (I := Finset.univ)
    (f := fun i x => c i * f i x * j i ^ b)
    (fun i _ => (contDiffAt_const.mul (hf i)).mul contDiffAt_const)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field, mul_assoc]

open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents

/-- Multiplying the actual mixed-derivative matrix by coefficients is exactly
the mixed jet of their finite scalar combination. -/
theorem separatedJetMatrix_mulVec_eq_mixedJet
    (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ)
    (v : Column d (m : ℤ) a delta → ℂ) (row : JetIndex q m)
    (hcoeff : ∀ col, ContDiffAt ℂ row.2.val (coeff col) 0) :
    (separatedJetMatrix d q m a delta coeff).mulVec v row =
      mixedJetAtZero (fun x y => ∑ col, v col * coeff col x *
        Complex.exp ((col.val.1 : ℂ) * y)) row.2.val row.1.val := by
  rw [mixedJetAtZero_separated_sum _ _ _ _ _ hcoeff]
  simp only [Matrix.mulVec, dotProduct, separatedJetMatrix, mixedJetAtZero_separated]
  apply Finset.sum_congr rfl
  intro col _
  exact mul_comm _ _

/-- Consequently the entire source-shaped finite jet system vanishes exactly
when the actual scalar combination has all its prescribed mixed jets zero. -/
theorem separatedJetMatrix_kernel_iff_mixedJets
    (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ)
    (v : Column d (m : ℤ) a delta → ℂ)
    (hcoeff : ∀ row : JetIndex q m, ∀ col, ContDiffAt ℂ row.2.val (coeff col) 0) :
    (separatedJetMatrix d q m a delta coeff).mulVec v = 0 ↔
      ∀ row : JetIndex q m, mixedJetAtZero (fun x y => ∑ col,
        v col * coeff col x * Complex.exp ((col.val.1 : ℂ) * y))
        row.2.val row.1.val = 0 := by
  constructor
  · intro hv row
    rw [← separatedJetMatrix_mulVec_eq_mixedJet d q m a delta coeff v row (hcoeff row)]
    exact congrFun hv row
  · intro hv
    funext row
    rw [separatedJetMatrix_mulVec_eq_mixedJet d q m a delta coeff v row (hcoeff row)]
    exact hv row

end Nagata.Workers.W11

end
end

section

/-!
# Contradiction for the actual finite exponent and jet index sets
-/

noncomputable section
open Filter Topology

namespace Nagata.Workers.W11

open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents

/-- On the manuscript's actual finite index types, its numerical parameter
hypotheses and entrywise convergence give eventual injectivity. -/
theorem eventually_injective_finite_jet_matrix
    {α : Type*} {l : Filter α}
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (B : α → Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hB : ∀ row col, Tendsto (fun t => B t row col) l
      (𝓝 ((col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val))) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  classical
  exact eventually_injective_of_injective_limit (B₀ := B0 d q m a delta) hB
    (B0_mulVec_injective d q m rho a delta lam ha hm hrho hdelta hlam hlam1
      hratio hslack hcoef hmargin)

/-- The fixed-index matrix contradiction under the stated numerical and kernel
hypotheses. No regular choice of kernel vector is required. -/
theorem finite_jet_matrix_contradiction
    {α : Type*} {l : Filter α} [NeBot l]
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (B : α → Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hB : ∀ row col, Tendsto (fun t => B t row col) l
      (𝓝 ((col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val)))
    (hkernel : ∀ᶠ t in l, ∃ v : Column d (m : ℤ) a delta → ℂ,
      v ≠ 0 ∧ (B t).mulVec v = 0) : False := by
  classical
  exact not_eventually_nonzero_kernel_of_injective_limit
    (B₀ := B0 d q m a delta) hB
    (B0_mulVec_injective d q m rho a delta lam ha hm hrho hdelta hlam hlam1
      hratio hslack hcoef hmargin) hkernel

end Nagata.Workers.W11

end
end

end OAI
