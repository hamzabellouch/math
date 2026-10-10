import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingLimits

namespace OAI

/-!
# Centralizer limits of normalized shearing trajectories

Uniform control before the first shearing time bounds the quadratic
coefficient. Since the shearing times diverge, the diagonal disturbance
vanishes. Every convergent terminal matrix therefore lies in the root
centralizer. These conclusions use actual special-linear matrices.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma root_conjugation_pivot {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 i j - g.1 i j =
      t * (g.1 j j - g.1 i i) - t ^ 2 * g.1 j i := by
  rw [root_conjugation_entry]
  simp only [ite_true, and_self]
  ring

lemma root_shearing_quadratic_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) {t a : ℝ} (ht : 0 ≤ t)
    (hsmall : ∀ u ∈ Icc 0 t, rootShearSize hij g u ≤ a) :
    |t ^ 2 * g.1 j i| ≤ 6 * a := by
  let f : ℝ → ℝ := fun u =>
    (Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).1 i j - g.1 i j
  have h1 : |f t| ≤ a :=
    (entry_sub_le_rootShearSize hij g t i j).trans (hsmall t ⟨ht, le_rfl⟩)
  have h2 : |f (t / 2)| ≤ a :=
    (entry_sub_le_rootShearSize hij g (t / 2) i j).trans
      (hsmall (t / 2) ⟨by linarith, by linarith⟩)
  have he : t ^ 2 * g.1 j i = 4 * f (t / 2) - 2 * f t := by
    have hf (u : ℝ) : f u = u * (g.1 j j - g.1 i i) - u ^ 2 * g.1 j i :=
      root_conjugation_pivot hij g u
    rw [hf, hf]
    ring
  rw [he]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma root_shearing_linear_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) {t a : ℝ} (ht : 0 < t)
    (hsmall : ∀ u ∈ Icc 0 t, rootShearSize hij g u ≤ a) :
    |t * g.1 j i| ≤ 6 * a / t := by
  apply (le_div_iff₀ ht).mpr
  have he : |t * g.1 j i| * t = |t ^ 2 * g.1 j i| := by
    simp only [abs_mul, abs_pow, abs_of_pos ht]
    ring
  rw [he]
  exact root_shearing_quadratic_bound hij g ht.le hsmall

/-- The diagonal perturbation tends to zero on a diverging normalized
shearing interval. -/
lemma tendsto_root_shearing_linear_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (t : ℕ → ℝ) (ht : ∀ m, 0 < t m)
    (htop : Tendsto t atTop atTop) (a : ℝ)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a) :
    Tendsto (fun m => t m * (g m).1 j i) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro m
    simpa only [Real.norm_eq_abs] using
      root_shearing_linear_bound hij (g m) (ht m) (hsmall m)
  · exact tendsto_const_nhds.div_atTop htop

/-- Every terminal limit of a uniformly bounded normalized shearing
interval centralizes the original root subgroup. -/
theorem rootShearLimit_centralizes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    (a : ℝ) (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-t m)) atTop (𝓝 h)) :
    ∀ u : ℝ, h * Matrix.SpecialLinearGroup.transvection hij u =
      Matrix.SpecialLinearGroup.transvection hij u * h := by
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.1 r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).1 r s) atTop
      (𝓝 ((1 : G n).1 r s)) :=
    (hcont r s).tendsto _ |>.comp hg
  have hhentry (r s : Fin n) : Tendsto (fun m =>
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 r s) atTop (𝓝 (h.1 r s)) :=
    (hcont r s).tendsto _ |>.comp hlim
  have hlinear := tendsto_root_shearing_linear_zero hij g t ht htop a hsmall
  apply (commutes_root_one_iff_all hij h).mp
  apply (commutes_root_one_iff hij h).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 r i) =
        (fun m => (g m).1 r i) := by
      funext m
      simp [root_conjugation_entry, hr, hij]
    have hzero : Tendsto (fun m => (g m).1 r i) atTop (𝓝 0) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hr] using hgentry r i
    exact tendsto_nhds_unique (he ▸ hhentry r i) hzero
  · intro s hs
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 j s) =
        (fun m => (g m).1 j s) := by
      funext m
      simp [root_conjugation_entry, hs, hij.symm]
    have hzero : Tendsto (fun m => (g m).1 j s) atTop (𝓝 0) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (Ne.symm hs)] using hgentry j s
    exact tendsto_nhds_unique (he ▸ hhentry j s) hzero
  · have hdiag_i : h.1 i i = 1 := by
      have hconv := (hgentry i i).add hlinear
      have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).1 i i) =
          (fun m => (g m).1 i i + t m * (g m).1 j i) := by
        funext m
        simp [root_conjugation_entry, hij]
      have hone : Tendsto (fun m => (g m).1 i i + t m * (g m).1 j i) atTop (𝓝 1) := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, add_zero] using hconv
      exact tendsto_nhds_unique (he ▸ hhentry i i) hone
    have hdiag_j : h.1 j j = 1 := by
      have hconv := (hgentry j j).sub hlinear
      have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).1 j j) =
          (fun m => (g m).1 j j - t m * (g m).1 j i) := by
        funext m
        simp [root_conjugation_entry, hij.symm]
      have hone : Tendsto (fun m => (g m).1 j j - t m * (g m).1 j i) atTop (𝓝 1) := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, sub_zero] using hconv
      exact tendsto_nhds_unique (he ▸ hhentry j j) hone
    exact hdiag_i.trans hdiag_j.symm

end DukePrimeDegree

end OAI
