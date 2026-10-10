import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFactorization

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

noncomputable def kernelRootResidues (m : ℕ) (u h : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter
    (fun r => (u : ZMod m) * (r : ZMod m) ^ 2 = -(h : ZMod m))

@[simp] theorem mem_kernelRootResidues {m r : ℕ} {u h : ℤ} :
    r ∈ kernelRootResidues m u h ↔
      r < m ∧ (u : ZMod m) * (r : ZMod m) ^ 2 = -(h : ZMod m) := by
  classical
  simp only [kernelRootResidues, Finset.mem_filter, Finset.mem_range]

theorem squareFactor_mod_mem_kernelRootResidues {m : ℕ} (hm : 0 < m)
    {u h x : ℤ} {t : ℕ} (heq : (m : ℤ) * x - h = u * (t : ℤ) ^ 2) :
    t % m ∈ kernelRootResidues m u h := by
  rw [mem_kernelRootResidues]
  refine ⟨Nat.mod_lt _ hm, ?_⟩
  have hc := congrArg (fun z : ℤ => (z : ZMod m)) heq
  simpa using hc.symm

theorem kernel_population_le_quotient_interval
    (S : Finset ℤ) {m : ℕ} (hm : 0 < m) {u h : ℤ}
    (t : ℤ → ℕ) (lo hi : ℕ)
    (heq : ∀ x ∈ S, (m : ℤ) * x - h = u * (t x : ℤ) ^ 2)
    (hrange : ∀ x ∈ S, lo ≤ t x ∧ t x ≤ hi) :
    S.card ≤ (kernelRootResidues m u h).card * (hi / m + 1 - lo / m) := by
  classical
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcard := Finset.card_le_card_of_injOn
    (s := S) (t := (kernelRootResidues m u h) ×ˢ Finset.Icc (lo / m) (hi / m))
    (fun x : ℤ => (t x % m, t x / m))
    (fun x hx => Finset.mem_product.mpr
      ⟨squareFactor_mod_mem_kernelRootResidues hm (heq x hx),
        Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (hrange x hx).1,
          Nat.div_le_div_right (hrange x hx).2⟩⟩) ?_
  · simpa only [Finset.card_product, Nat.card_Icc] using hcard
  · intro x hx y hy he
    have hmod := congrArg Prod.fst he
    have hdiv := congrArg Prod.snd he
    have ht : t x = t y := by
      have hx := Nat.mod_add_div (t x) m
      have hy := Nat.mod_add_div (t y) m
      dsimp at hmod hdiv
      rw [hmod, hdiv] at hx
      exact hx.symm.trans hy
    have hlin : (m : ℤ) * x = m * y := by
      have hx := heq x hx
      have hy := heq y hy
      rw [ht] at hx
      linarith
    exact mul_left_cancel₀ hmz hlin

theorem kernel_population_le_diameter
    (S : Finset ℤ) {m : ℕ} (hm : 0 < m) {u h : ℤ}
    (t : ℤ → ℕ) (lo hi : ℕ)
    (heq : ∀ x ∈ S, (m : ℤ) * x - h = u * (t x : ℤ) ^ 2)
    (hrange : ∀ x ∈ S, lo ≤ t x ∧ t x ≤ hi) :
    S.card ≤ (kernelRootResidues m u h).card * ((hi - lo) / m + 2) := by
  apply (kernel_population_le_quotient_interval S hm t lo hi heq hrange).trans
  apply Nat.mul_le_mul_left
  by_cases hlo : lo ≤ hi
  · have hb := Nat.add_div_le_div_add_div_add_one lo (hi - lo) m
    rw [Nat.add_sub_of_le hlo] at hb
    apply Nat.sub_le_iff_le_add.mpr
    calc
      hi / m + 1 ≤ (lo / m + (hi - lo) / m + 1) + 1 := Nat.add_le_add_right hb 1
      _ = (hi - lo) / m + 2 + lo / m := by omega
  · have hh : hi / m ≤ lo / m := Nat.div_le_div_right (by omega)
    have hb : hi / m + 1 - lo / m ≤ 1 := Nat.sub_le_iff_le_add.mpr (by omega)
    apply hb.trans
    exact Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_left 2 _)

theorem nonnegative_square_diameter {s t D : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hbound : |s ^ 2 - t ^ 2| ≤ D) : |s - t| ≤ Real.sqrt D := by
  apply (Real.le_sqrt (abs_nonneg _) hD).mpr
  have hab : |s ^ 2 - t ^ 2| = |s - t| * (s + t) := by
    rw [← abs_of_nonneg (add_nonneg hs ht), ← abs_mul]
    congr 1
    ring
  have hst : |s - t| ≤ s + t := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hab] at hbound
  nlinarith [mul_le_mul_of_nonneg_left hst (abs_nonneg (s - t))]

theorem kernel_squareFactor_diameter {m u h x y : ℤ} {s t : ℕ} {X : ℝ}
    (hu : u ≠ 0) (hX : 0 ≤ X)
    (hx : m * x - h = u * (s : ℤ) ^ 2)
    (hy : m * y - h = u * (t : ℤ) ^ 2)
    (hd : |(x : ℝ) - (y : ℝ)| ≤ X) :
    |(s : ℝ) - (t : ℝ)| ≤ Real.sqrt (|(m : ℝ)| * X / |(u : ℝ)|) := by
  have hur : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have hupos : 0 < |(u : ℝ)| := abs_pos.mpr hur
  apply nonnegative_square_diameter (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (div_nonneg (mul_nonneg (abs_nonneg _) hX) hupos.le)
  have hxr : (m : ℝ) * x - h = u * (s : ℝ) ^ 2 := by exact_mod_cast hx
  have hyr : (m : ℝ) * y - h = u * (t : ℝ) ^ 2 := by exact_mod_cast hy
  have hdiff : (u : ℝ) * ((s : ℝ) ^ 2 - (t : ℝ) ^ 2) =
      (m : ℝ) * ((x : ℝ) - (y : ℝ)) := by nlinarith [hxr, hyr]
  apply (le_div_iff₀ hupos).mpr
  have ha := congrArg abs hdiff
  rw [abs_mul, abs_mul] at ha
  calc
    |(s : ℝ) ^ 2 - (t : ℝ) ^ 2| * |(u : ℝ)| =
      |(m : ℝ)| * |(x : ℝ) - (y : ℝ)| := by nlinarith [ha]
    _ ≤ |(m : ℝ)| * X := mul_le_mul_of_nonneg_left hd (abs_nonneg _)

end Ostmann.QuadraticCenter

end OAI
