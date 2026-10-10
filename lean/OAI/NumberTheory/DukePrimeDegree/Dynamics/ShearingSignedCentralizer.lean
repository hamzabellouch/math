import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingBoundedLimit

namespace OAI

/-!
# Limits for shearing times of either sign

Annular return selection can produce positive or negative root times.
Bounds on the symmetric interval and divergence of the absolute times
suffice for the centralizer conclusion, without a sign assumption.
-/

noncomputable section
open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma signed_root_shearing_quadratic_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t a : ℝ)
    (hsmall : ∀ u : ℝ, |u| ≤ |t| → rootShearSize hij g u ≤ a) :
    |t ^ 2 * g.val j i| ≤ 6 * a := by
  let f : ℝ → ℝ := fun u =>
    (Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).val i j - g.val i j
  have h1 : |f t| ≤ a :=
    (entry_sub_le_rootShearSize hij g t i j).trans (hsmall t le_rfl)
  have hh : |t / 2| ≤ |t| := by
    rw [abs_div]
    norm_num
  have h2 : |f (t / 2)| ≤ a :=
    (entry_sub_le_rootShearSize hij g (t / 2) i j).trans (hsmall (t / 2) hh)
  have he : t ^ 2 * g.val j i = 4 * f (t / 2) - 2 * f t := by
    have hf (u : ℝ) : f u = u * (g.val j j - g.val i i) - u ^ 2 * g.val j i :=
      root_conjugation_pivot hij g u
    rw [hf, hf]
    ring
  rw [he]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma signed_root_shearing_linear_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t a : ℝ) (ht : t ≠ 0)
    (hsmall : ∀ u : ℝ, |u| ≤ |t| → rootShearSize hij g u ≤ a) :
    |t * g.val j i| ≤ 6 * a / |t| := by
  apply (le_div_iff₀ (abs_pos.mpr ht)).mpr
  have he : |t * g.val j i| * |t| = |t ^ 2 * g.val j i| := by
    simp only [abs_mul, abs_pow]
    ring
  rw [he]
  exact signed_root_shearing_quadratic_bound hij g t a hsmall

lemma tendsto_signed_root_shearing_linear_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop) (a : ℝ)
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ a) :
    Tendsto (fun m => t m * (g m).val j i) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro m
    simpa only [Real.norm_eq_abs] using
      signed_root_shearing_linear_bound hij (g m) (t m) a (ht m) (hsmall m)
  · exact tendsto_const_nhds.div_atTop htop

theorem rootShearLimit_signed_centralizes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a : ℝ) (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ a)
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
  have hlinear := tendsto_signed_root_shearing_linear_zero hij g t ht htop a hsmall
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

end

end OAI
