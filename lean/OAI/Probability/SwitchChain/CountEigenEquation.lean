import OAI.Probability.SwitchChain.CountEigenvalue
import OAI.Probability.SwitchChain.CountCovering

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CountEigenvalue

theorem count_eigenvalue_le_two
    {ι : Type*} [Fintype ι] (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι) (b : ι → ℕ → ℝ) (lam : ℝ)
    (hne : ∃ i, ∃ s t : Fin (m + 1), b i s.val ≠ b i t.val)
    (heig : ∀ i t, t ≤ m →
      (lam - 1) * b i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b (left i) y + b (right i) (m - t - y))) : lam ≤ 2 := by
  apply eigenvalue_le_two_of_adjacent_coupling
    (fun i (t : Fin (m + 1)) => b i t.val) lam hne
  intro i t hmax
  let s := m - (t.val + 1)
  have htotal : s + 1 = m - t.val := by dsimp [s]; omega
  have hleft : ∀ u ≤ s,
      |b (left i) (u + 1) - b (left i) u| ≤
        |b i (t.val + 1) - b i t.val| := by
    intro u hu
    have hum : u < m := by dsimp [s] at hu; have := t.isLt; omega
    exact hmax (left i) ⟨u, hum⟩
  have hright : ∀ u ≤ s,
      |b (right i) (u + 1) - b (right i) u| ≤
        |b i (t.val + 1) - b i t.val| := by
    intro u hu
    have hum : u < m := by dsimp [s] at hu; have := t.isLt; omega
    exact hmax (right i) ⟨u, hum⟩
  have hcover := CountCoupling.pairExpectation_adjacent_sum_bound
    (α (left i)) (α (right i)) s (b (left i)) (b (right i))
    |b i (t.val + 1) - b i t.val| hleft hright
  rw [htotal] at hcover
  change |(lam - 1) * (b i (t.val + 1) - b i t.val)| ≤
    |b i (t.val + 1) - b i t.val|
  rw [mul_sub, heig i (t.val + 1) (by have := t.isLt; omega),
    heig i t.val (by have := t.isLt; omega)]
  simpa only [s, abs_sub_comm] using hcover

theorem count_eigenvalue_le_two_of_centered
    {ι : Type*} [Fintype ι] (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι) (b : ι → ℕ → ℝ)
    (p : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t.val = 0)
    (hne : ∃ i, ∃ t : Fin (m + 1), b i t.val ≠ 0)
    (heig : ∀ i t, t ≤ m →
      (lam - 1) * b i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b (left i) y + b (right i) (m - t - y))) : lam ≤ 2 := by
  exact count_eigenvalue_le_two m α left right b lam
    (exists_nonconstant_of_centered (fun i (t : Fin (m + 1)) => b i t.val)
      p hmass hcenter hne) heig

theorem count_operator_quadratic_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι)
    (b : E → ι → ℕ → ℝ) (p : ι → Fin (m + 1) → ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ x i, ∑ t, p i t * b x i t.val = 0)
    (hdetect : ∀ x, x ≠ 0 → ∃ i, ∃ t : Fin (m + 1), b x i t.val ≠ 0)
    (heig : ∀ (lam : ℝ) (x : E), T x = lam • x → ∀ i t, t ≤ m →
      (lam - 1) * b x i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b x (left i) y + b x (right i) (m - t - y))) :
    ∀ x : E, ⟪x, T x⟫ ≤ 2 * ‖x‖ ^ 2 := by
  classical
  let basis := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (basis i) = ev i • basis i :=
    hT.apply_eigenvectorBasis rfl i
  have hev (i : Fin (Module.finrank ℝ E)) : ev i ≤ 2 := by
    apply count_eigenvalue_le_two_of_centered m α left right (b (basis i)) p (ev i)
      hmass (hcenter (basis i))
    · apply hdetect
      intro hz
      have hn := basis.orthonormal.1 i
      rw [hz, norm_zero] at hn
      norm_num at hn
    · exact heig (ev i) (basis i) (hbe i)
  intro x
  rw [← basis.sum_inner_mul_inner x (T x), ← basis.sum_sq_inner_right x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪basis i, T x⟫ = ev i * ⟪basis i, x⟫ := by
    rw [← hT (basis i) x, hbe, inner_smul_left]
    simp
  rw [hcoord, real_inner_comm x (basis i)]
  have hi := hev i
  nlinarith [sq_nonneg ⟪basis i, x⟫]

end Problem315.CountEigenvalue

end

end OAI
