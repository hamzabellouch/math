import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSplitSupply
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelCollision
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelSeparation
import OAI.NumberTheory.Ostmann.Quadratic.RootPopulationBudget

namespace OAI

/-! # The large nonexceptional quadratic populations are impossible

The collision estimate uses the integer prime cutoff and the quadratic
split-prime estimate. Root equations, separation, and population sizes
supply its geometric hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem small_kernel_le_split_cutoff (η L : ℝ) (u : ℤ)
    (hη : η ≤ 1 / 1000) (hL : 0 ≤ L)
    (hu : (u.natAbs : ℝ) ≤ Real.exp (η * L)) :
    u.natAbs ≤ kernelSplitCutoff η L := by
  apply Nat.le_floor
  apply hu.trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hη hL
  nlinarith

theorem small_kernel_product_bounds (η L : ℝ) (m : ℕ) (u v : ℤ)
    (hm : 0 < m) (hu : u ≠ 0) (hv : v ≠ 0)
    (hL : 1000 ≤ L) (hη : η ≤ 1 / 1000)
    (hmupper : (m : ℝ) ≤ Real.exp (η * L))
    (huupper : (u.natAbs : ℝ) ≤ Real.exp (η * L))
    (hvupper : (v.natAbs : ℝ) ≤ Real.exp (η * L)) :
    ((u * v).natAbs : ℝ) ≤ Real.exp (2 * η * L) ∧
      0 < 2 * m * u.natAbs * v.natAbs ∧
      (u * v).natAbs ∣ 2 * m * u.natAbs * v.natAbs ∧
      Real.log (2 * m * u.natAbs * v.natAbs : ℕ) ≤ L := by
  have hu0 : 0 < u.natAbs := Int.natAbs_pos.mpr hu
  have hv0 : 0 < v.natAbs := Int.natAbs_pos.mpr hv
  have hp : (u.natAbs : ℝ) * v.natAbs ≤ Real.exp (2 * η * L) := by
    calc
      _ ≤ Real.exp (η * L) * Real.exp (η * L) :=
        mul_le_mul huupper hvupper (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨by simpa only [Int.natAbs_mul, Nat.cast_mul] using hp, by positivity, ?_, ?_⟩
  · rw [Int.natAbs_mul]
    exact ⟨2 * m, by ring⟩
  · have hsize : (2 * m * u.natAbs * v.natAbs : ℕ) ≤ (2 : ℝ) * Real.exp (3 * η * L) := by
      push_cast
      calc
        _ = 2 * ((m : ℝ) * (u.natAbs * v.natAbs)) := by ring
        _ ≤ 2 * (Real.exp (η * L) * Real.exp (2 * η * L)) := by
          gcongr
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    have hpos : (0 : ℝ) < (2 * m * u.natAbs * v.natAbs : ℕ) := by positivity
    have hl := Real.log_le_log hpos hsize
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hl
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have heta := mul_le_mul_of_nonneg_right hη (show 0 ≤ L by linarith)
    linarith

/-- For all sufficiently large scales, two separated prime-difference
populations cannot both exceed the split cutoff while carrying small,
nonexceptional squarefree kernels about one reduced rational center. -/
theorem no_large_nonexceptional_quadratic_populations (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ η L₁ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₁ ∧
      ∀ L : ℝ, L₁ ≤ L → ∀ (S T : Finset ℤ) (rootS rootT : ℤ → ℕ)
        (m : ℕ) (h u v : ℤ),
        0 < m → h.natAbs.Coprime m → u ≠ 0 → v ≠ 0 →
        Squarefree u.natAbs → Squarefree v.natAbs →
        (m : ℝ) ≤ Real.exp (η * L) →
        (u.natAbs : ℝ) ≤ Real.exp (η * L) →
        (v.natAbs : ℝ) ≤ Real.exp (η * L) →
        (∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h) →
        (∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        u * v ∉ pageKernelExclusion P (kernelConductorCutoff η L) (L ^ (100 : ℕ)) →
        kernelSplitCutoff η L ≤ S.card → kernelSplitCutoff η L ≤ T.card → False := by
  obtain ⟨η, L₀, hηpos, hη, hL₀, hsupply⟩ := quadratic_split_supply P H hSiegel
  let L₁ := max L₀ (max 1000 (50 * (C + 1) + 1))
  refine ⟨η, L₁, hηpos, hη, lt_of_lt_of_le hL₀ (le_max_left _ _), ?_⟩
  intro L hL S T rootS rootT m h u v hm hred hu hv husf hvsf hmupper huupper hvupper
    hS hT hspanS hspanT hcross hout hScard hTcard
  have hLbase : L₀ ≤ L := (le_max_left _ _).trans hL
  have h1000 : 1000 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hlarge : 50 * (C + 1) + 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hQ := (kernelSplitCutoff_bounds η L hη (by linarith)).1
  have hSnon : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hQ hScard)
  have hTnon : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hQ hTcard)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le hQ hScard)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (lt_of_lt_of_le hQ hTcard)
  have hucut := small_kernel_le_split_cutoff η L u hη (by linarith) huupper
  have hcop : u.natAbs.Coprime v.natAbs := quadratic_kernels_coprime m h x y u v
    (rootS x) (rootT y) hu hred (hS x hx) (hT y hy) (hcross x hx y hy).1
    (hucut.trans_lt (hcross x hx y hy).2)
  have hsf : Squarefree (u * v).natAbs := by
    rw [Int.natAbs_mul]
    exact squarefree_mul_iff.mpr ⟨Nat.coprime_iff_isRelPrime.mp hcop, husf, hvsf⟩
  have hb := small_kernel_product_bounds η L m u v hm hu hv h1000 hη hmupper huupper hvupper
  have hmass := hsupply L hLbase (u * v) (2 * m * u.natAbs * v.natAbs)
    hsf (mul_ne_zero hu hv) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hout
  have hmertens : (1 / 2 - 5 * η) * L - (C + 1) ≤
      ∑ p ∈ Nat.primesLE (kernelSplitCutoff η L), Real.log (p : ℝ) / (p : ℝ) := by
    have hlo := kernelSplitCutoff_log_lower η L hη (by linarith)
    have hm' := hM (kernelSplitCutoff η L) hQ
    linarith
  have hd := naturalRootDiameter_bounds m L η hm (by linarith) hmupper
  have hbudget := root_population_collision_budget m (kernelSplitCutoff η L) S.card T.card
    L η hm hQ h1000 hη hmupper hScard hTcard
  have hcontr := quadratic_kernel_collision_bound (Nat.primesLE (kernelSplitCutoff η L))
    S T hSnon hTnon rootS rootT m (naturalRootDiameter m L) (naturalRootDiameter m L)
    hm hd.1 hd.1 h u v hu hv hS hT (Real.exp L) hspanS hspanT
    (naturalRootDiameter_dominates m L u hm hu)
    (naturalRootDiameter_dominates m L v hm hv)
    (fun x hx y hy => (hcross x hx y hy).1) L η (C + 1)
    (fun _ hp => Nat.prime_of_mem_primesLE hp)
    (fun p hp x hx y hy => (Nat.le_of_mem_primesLE hp).trans_lt (hcross x hx y hy).2)
    (by linarith) hη hmertens hmass (by simpa only [two_mul] using hbudget)
  linarith

end Ostmann

end OAI
