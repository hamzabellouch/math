import OAI.AlgebraicGeometry.PlaneCurves.ThetaLimits

namespace OAI

/-!
# Theta jet matrices and their basis data
-/

section

noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents

/-- The actual mixed-derivative matrix of all three scalar coefficient branches.
The `marks` are offsets `aᵢ = x₀ - xᵢ` in `(0,1)`, as in §03's product limit;
they are not the original point exponents `xᵢ`. -/
def thetaJetMatrix (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (marks : Fin 9 → ℝ) (τ : ℝ) :
    Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ :=
  separatedJetMatrix d q m a delta
    (Nagata.W22.basisCoefficient d (m : ℤ) a delta marks τ)

/-- Entrywise convergence of the literal theta jet matrix, with no assumed
derivative convergence: that input is discharged by the scalar analytic theorem. -/
theorem tendsto_thetaJetMatrix_entries
    {α : Type*} {l : Filter α} {τ : α → ℝ}
    (d : ℤ) (q m : ℕ) (a delta : ℝ) (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ row col, Tendsto (fun t => thetaJetMatrix d q m a delta marks (τ t) row col)
      l (𝓝 (B0 d q m a delta row col)) := by
  exact tendsto_separatedJetMatrix_entries d q m a delta
    (fun t => Nagata.W22.basisCoefficient d (m : ℤ) a delta marks (τ t))
    (Nagata.W22.tendsto_iteratedDeriv_basisCoefficient_zero hmarks hmarksone hτ hτpos)

/-- The literal finite scalar expression for a coefficient vector. -/
def thetaScalarCombination (d : ℤ) (m : ℕ) (a delta : ℝ)
    (marks : Fin 9 → ℝ) (τ : ℝ) (v : Column d (m : ℤ) a delta → ℂ)
    (x y : ℂ) : ℂ :=
  ∑ col, v col * Nagata.W22.basisCoefficient d (m : ℤ) a delta marks τ col x *
    Complex.exp ((col.val.1 : ℂ) * y)

/-- The actual finite scalar expansion is linear in its coefficients. -/
def thetaScalarCombinationLinear (d : ℤ) (m : ℕ) (a delta : ℝ)
    (marks : Fin 9 → ℝ) (τ : ℝ) :
    (Column d (m : ℤ) a delta → ℂ) →ₗ[ℂ] (ℂ → ℂ → ℂ) where
  toFun := thetaScalarCombination d m a delta marks τ
  map_add' v w := by
    funext x y
    simp [thetaScalarCombination, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext x y
    simp [thetaScalarCombination, Finset.mul_sum, mul_assoc]

/-- Jet determination of a coefficient vector implies noncancellation of the
actual finite scalar expansion as a function, without assuming a basis. -/
theorem thetaScalarCombination_injective_of_jets
    (d : ℤ) (q m : ℕ) (a delta : ℝ) (marks : Fin 9 → ℝ) (τ : ℝ)
    (hjets : ∀ v : Column d (m : ℤ) a delta → ℂ,
      (∀ row : JetIndex q m,
        mixedJetAtZero (thetaScalarCombination d m a delta marks τ v)
          row.2.val row.1.val = 0) → v = 0) :
    Function.Injective (thetaScalarCombination d m a delta marks τ) := by
  apply (LinearMap.ker_eq_bot (f := thetaScalarCombinationLinear d m a delta marks τ)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hjets v
  intro row
  change thetaScalarCombination d m a delta marks τ v = 0 at hv
  rw [hv]
  simp [mixedJetAtZero]

/-- For sufficiently small parameters the actual scalar expression has zero
prescribed mixed jets iff its coefficient vector is a theta-matrix kernel
vector. The differentiability needed for finite-sum linearity is discharged. -/
theorem eventually_thetaJetMatrix_kernel_iff_mixedJets
    {α : Type*} {l : Filter α} {τ : α → ℝ}
    (d : ℤ) (q m : ℕ) (a delta : ℝ) (marks : Fin 9 → ℝ)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ᶠ t in l, ∀ v : Column d (m : ℤ) a delta → ℂ,
      (thetaJetMatrix d q m a delta marks (τ t)).mulVec v = 0 ↔
      ∀ row : JetIndex q m,
        mixedJetAtZero (thetaScalarCombination d m a delta marks (τ t) v)
          row.2.val row.1.val = 0 := by
  have hs := Nagata.W22.eventually_contDiffAt_basisCoefficient
    (d := d) (m := (m : ℤ)) (ρ := a) (Δ := delta) marks hτ hτpos
  exact hs.mono fun t ht v => separatedJetMatrix_kernel_iff_mixedJets
    d q m a delta (Nagata.W22.basisCoefficient d (m : ℤ) a delta marks (τ t)) v
    (fun row col => ht col row.2.val)

end Nagata.Workers.W11

end
end

section

/-!
# Literal theta-coefficient jet matrix
-/

noncomputable section
open Filter Topology

namespace Nagata.Workers.W11

open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents

theorem eventually_injective_thetaJetMatrix
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective (thetaJetMatrix d q m a delta marks τ).mulVec := by
  classical
  apply eventually_injective_finite_jet_matrix d q m rho a delta lam
    ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin
    (thetaJetMatrix d q m a delta marks)
  exact tendsto_thetaJetMatrix_entries d q m a delta marks hmarks hmarksone
    (tendsto_id.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin

theorem thetaJetMatrix_kernel_contradiction
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hkernel : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ v : Column d (m : ℤ) a delta → ℂ,
      v ≠ 0 ∧ (thetaJetMatrix d q m a delta marks τ).mulVec v = 0) : False := by
  have hinj := eventually_injective_thetaJetMatrix d q m rho a delta lam
    ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin marks hmarks hmarksone
  obtain ⟨τ, ht, v, hv, hzero⟩ := (hinj.and hkernel).exists
  exact hv (ht (by simpa only [Matrix.mulVec_zero] using hzero))

/-- For sufficiently small positive parameters, the literal scalar combination
can have all prescribed mixed jets zero only when every coefficient is zero.
This result contains no assumed smoothness, derivative convergence or rank. -/
theorem eventually_thetaScalarCombination_jet_injective
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ v : Column d (m : ℤ) a delta → ℂ,
      (∀ row : JetIndex q m,
        mixedJetAtZero (thetaScalarCombination d m a delta marks τ v)
          row.2.val row.1.val = 0) → v = 0 := by
  have hi := eventually_injective_thetaJetMatrix d q m rho a delta lam
    ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin marks hmarks hmarksone
  have he := eventually_thetaJetMatrix_kernel_iff_mixedJets d q m a delta marks
    (tendsto_id.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
  exact (hi.and he).mono fun τ hτ v hv => hτ.1
    (by simpa only [id_eq, Matrix.mulVec_zero] using (hτ.2 v).mpr hv)

/-- Noncancellation of the actual scalar column expansion for sufficiently
small positive parameters: distinct coefficient vectors define distinct
functions of the two local variables. -/
theorem eventually_thetaScalarCombination_injective
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      Function.Injective (thetaScalarCombination d m a delta marks τ) :=
  (eventually_thetaScalarCombination_jet_injective d q m rho a delta lam
    ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin marks hmarks hmarksone).mono
    fun τ hτ => thetaScalarCombination_injective_of_jets d q m a delta marks τ hτ

end Nagata.Workers.W11

end
end

end OAI
