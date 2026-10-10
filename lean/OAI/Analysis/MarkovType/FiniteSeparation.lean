import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {ι κ : Type*} [sectionFintypeι : Fintype ι] [Fintype κ]

def finiteL1 (x : ι → ℝ) : ℝ := ∑ i, |x i|

theorem finiteL1_nonneg (x : ι → ℝ) : 0 ≤ finiteL1 x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

@[simp] theorem finiteL1_zero : finiteL1 (0 : ι → ℝ) = 0 := by
  simp [finiteL1]

@[simp] theorem finiteL1_single [DecidableEq ι] (i : ι) (a : ℝ) :
    finiteL1 (Pi.single i a) = |a| := by
  classical
  unfold finiteL1
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [Pi.single_eq_of_ne hji]

theorem continuous_finiteL1 : Continuous (finiteL1 : (ι → ℝ) → ℝ) := by
  unfold finiteL1
  fun_prop

theorem convex_finiteL1_lt (ε : ℝ) :
    Convex ℝ {x : ι → ℝ | finiteL1 x < ε} := by
  intro x hx y hy a b ha hb hab
  change finiteL1 (a • x + b • y) < ε
  calc
    finiteL1 (a • x + b • y)
        ≤ ∑ i, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x i) (b * y i)
    _ = a * finiteL1 x + b * finiteL1 y := by
      simp only [finiteL1, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * max (finiteL1 x) (finiteL1 y) + b * max (finiteL1 x) (finiteL1 y) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max (finiteL1 x) (finiteL1 y) := by rw [← add_mul, hab, one_mul]
    _ < ε := max_lt hx hy

def finiteMixtures (v : κ → ι → ℝ) : Set (ι → ℝ) :=
  {x | ∃ w : κ → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
    ∀ i, x i = ∑ j, w j * v j i}

omit sectionFintypeι in
theorem mem_finiteMixtures [Fintype ι] (v : κ → ι → ℝ) (j : κ) :
    v j ∈ finiteMixtures v := by
  classical
  refine ⟨fun k => if k = j then 1 else 0, ?_, ?_, ?_⟩
  · intro k
    change 0 ≤ if k = j then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · simp
  · intro i
    simp

omit sectionFintypeι in
theorem convex_finiteMixtures [Fintype ι] (v : κ → ι → ℝ) : Convex ℝ (finiteMixtures v) := by
  rintro x ⟨wx, hwx, hsx, hex⟩ y ⟨wy, hwy, hsy, hey⟩ a b ha hb hab
  refine ⟨fun j => a * wx j + b * wy j, ?_, ?_, ?_⟩
  · intro j
    exact add_nonneg (mul_nonneg ha (hwx j)) (mul_nonneg hb (hwy j))
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsx, hsy, mul_one, hab]
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hex i, hey i,
      add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

theorem continuousLinearMap_pi_expansion [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  classical
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    f x = f (∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ)) := congrArg f hx
    _ = ∑ i, f (Pi.single i 1) * x i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm]

theorem exists_finite_mixture_l1_lt [Nonempty κ] (v : κ → ι → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hdual : ∀ a : ι → ℝ, (∀ i, |a i| ≤ 1) →
      ∃ j, |∑ i, a i * v j i| < ε) :
    ∃ w : κ → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∑ i, |∑ j, w j * v j i|) < ε := by
  classical
  have hinter : ∃ x : ι → ℝ, finiteL1 x < ε ∧ x ∈ finiteMixtures v := by
    by_contra hn
    have hdisj : Disjoint {x : ι → ℝ | finiteL1 x < ε} (finiteMixtures v) := by
      rw [Set.disjoint_left]
      intro x hx hy
      exact hn ⟨x, hx, hy⟩
    obtain ⟨f, u, hopen, hsep⟩ := geometric_hahn_banach_open
      (convex_finiteL1_lt (ι := ι) ε)
      (isOpen_lt continuous_finiteL1 continuous_const)
      (convex_finiteMixtures v) hdisj
    have hu : 0 < u := by
      have h := hopen 0 (by simpa using hε)
      simpa using h
    let a : ι → ℝ := fun i => f (Pi.single i 1)
    have hrep (x : ι → ℝ) : f x = ∑ i, a i * x i :=
      continuousLinearMap_pi_expansion f x
    have ha_nonzero : ∃ i, a i ≠ 0 := by
      by_contra ha
      have haz : ∀ i, a i = 0 := by simpa using ha
      have hfzero (x : ι → ℝ) : f x = 0 := by simp [hrep x, haz]
      have hj := hsep (v (Classical.choice ‹Nonempty κ›))
        (mem_finiteMixtures v (Classical.choice ‹Nonempty κ›))
      rw [hfzero] at hj
      exact (not_le_of_gt hu) hj
    obtain ⟨i₁, hi₁⟩ := ha_nonzero
    let : Nonempty ι := ⟨i₁⟩
    obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i : ι => |a i|) Finset.univ_nonempty
    let M : ℝ := |a i₀|
    have hM : 0 < M := lt_of_lt_of_le (abs_pos.mpr hi₁) (hmax i₁ (Finset.mem_univ _))
    have hbound (i : ι) : |a i| ≤ M := hmax i (Finset.mem_univ _)
    have hεM : ε * M ≤ u := by
      by_contra hnM
      have huM : u / M < ε := (div_lt_iff₀ hM).mpr (lt_of_not_ge hnM)
      let r : ℝ := (u / M + ε) / 2
      have hr : 0 < r := by dsimp [r]; positivity
      have hrε : r < ε := by dsimp [r]; linarith
      have hurM : u < r * M := by
        have hud : u / M < r := by dsimp [r]; linarith
        exact (div_lt_iff₀ hM).mp hud
      by_cases hai : 0 ≤ a i₀
      · have hMval : a i₀ = M := by dsimp [M]; rw [abs_of_nonneg hai]
        have hx : finiteL1 (Pi.single i₀ r) < ε := by
          simpa only [finiteL1_single, abs_of_pos hr] using hrε
        have hf := hopen (Pi.single i₀ r) hx
        have heval : f (Pi.single i₀ r) = r * M := by
          rw [hrep]
          simp [Pi.single_apply, hMval, mul_comm]
        rw [heval] at hf
        exact (lt_asymm hf hurM)
      · have hMval : a i₀ = -M := by
          dsimp [M]
          rw [abs_of_neg (lt_of_not_ge hai)]
          ring
        have hx : finiteL1 (Pi.single i₀ (-r)) < ε := by
          simpa only [finiteL1_single, abs_neg, abs_of_pos hr] using hrε
        have hf := hopen (Pi.single i₀ (-r)) hx
        have heval : f (Pi.single i₀ (-r)) = r * M := by
          rw [hrep]
          simp [Pi.single_apply, hMval, mul_comm]
        rw [heval] at hf
        exact (lt_asymm hf hurM)
    obtain ⟨j, hj⟩ := hdual (fun i => a i / M) (fun i => by
      rw [abs_div, abs_of_pos hM]
      exact (div_le_one hM).mpr (hbound i))
    have hsum : (∑ i, (a i / M) * v j i) = f (v j) / M := by
      rw [hrep]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum, abs_div, abs_of_pos hM] at hj
    have hsmall : |f (v j)| < ε * M := (div_lt_iff₀ hM).mp hj
    have hlarge : u ≤ f (v j) := hsep (v j) (mem_finiteMixtures v j)
    exact (not_lt_of_ge (hεM.trans (hlarge.trans (le_abs_self _)))) hsmall
  obtain ⟨x, hx, w, hw, hs, he⟩ := hinter
  refine ⟨w, hw, hs, ?_⟩
  simpa only [finiteL1, he] using hx

end MarkovSuperreflexivity

end OAI
