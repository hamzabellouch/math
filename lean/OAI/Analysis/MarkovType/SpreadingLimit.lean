import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

namespace SpreadingLimit

section PointwiseLimit

variable {E Y : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (L : ℕ → E →ₗ[ℝ] Y)
  (hCauchy : ∀ x, CauchySeq (fun n => ‖L n x‖))

def normLimit (x : E) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete (hCauchy x))

theorem tendsto_normLimit (x : E) :
    Tendsto (fun n => ‖L n x‖) atTop (𝓝 (normLimit L hCauchy x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hCauchy x))

theorem normLimit_add_le (x y : E) :
    normLimit L hCauchy (x + y) ≤ normLimit L hCauchy x + normLimit L hCauchy y := by
  apply le_of_tendsto_of_tendsto' (tendsto_normLimit L hCauchy (x + y))
    ((tendsto_normLimit L hCauchy x).add (tendsto_normLimit L hCauchy y))
  intro n
  simpa only [map_add] using norm_add_le (L n x) (L n y)

theorem normLimit_smul (r : ℝ) (x : E) :
    normLimit L hCauchy (r • x) = ‖r‖ * normLimit L hCauchy x := by
  have h : Tendsto (fun n => ‖L n (r • x)‖) atTop
      (𝓝 (‖r‖ * normLimit L hCauchy x)) := by
    simpa only [map_smul, norm_smul] using
      (tendsto_const_nhds.mul (tendsto_normLimit L hCauchy x))
  exact tendsto_nhds_unique (tendsto_normLimit L hCauchy (r • x)) h

def limitSeminorm : Seminorm ℝ E :=
  Seminorm.of (normLimit L hCauchy) (normLimit_add_le L hCauchy)
    (normLimit_smul L hCauchy)

@[simp] theorem limitSeminorm_apply (x : E) :
    limitSeminorm L hCauchy x = normLimit L hCauchy x := rfl

theorem tendsto_limitSeminorm (x : E) :
    Tendsto (fun n => ‖L n x‖) atTop (𝓝 (limitSeminorm L hCauchy x)) :=
  tendsto_normLimit L hCauchy x

theorem limitSeminorm_le (x : E) (b : ℝ)
    (hb : ∀ᶠ n in atTop, ‖L n x‖ ≤ b) :
    limitSeminorm L hCauchy x ≤ b :=
  le_of_tendsto (tendsto_limitSeminorm L hCauchy x) hb

theorem le_limitSeminorm_of_error (x : E) (b : ℝ) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, b - error n ≤ ‖L n x‖) :
    b ≤ limitSeminorm L hCauchy x := by
  have h := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub herror) (tendsto_limitSeminorm L hCauchy x) hb
  simpa only [sub_zero] using h

theorem limitSeminorm_le_limitSeminorm_of_error (x y : E) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hxy : ∀ᶠ n in atTop, ‖L n x‖ ≤ ‖L n y‖ + error n) :
    limitSeminorm L hCauchy x ≤ limitSeminorm L hCauchy y := by
  have h := le_of_tendsto_of_tendsto (tendsto_limitSeminorm L hCauchy x)
    ((tendsto_limitSeminorm L hCauchy y).add herror) hxy
  simpa only [add_zero] using h

theorem limitSeminorm_eq_of_error (x y : E) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hxy : ∀ᶠ n in atTop, |‖L n x‖ - ‖L n y‖| ≤ error n) :
    limitSeminorm L hCauchy x = limitSeminorm L hCauchy y := by
  apply le_antisymm
  · apply limitSeminorm_le_limitSeminorm_of_error L hCauchy x y error herror
    filter_upwards [hxy] with n hn
    have h := (abs_le.mp hn).2
    linarith
  · apply limitSeminorm_le_limitSeminorm_of_error L hCauchy y x error herror
    filter_upwards [hxy] with n hn
    have h := (abs_le.mp hn).1
    linarith

end PointwiseLimit

theorem coordinate_lower_of_prefix (p : Seminorm ℝ C00) (d : ℝ) (hd : 0 ≤ d)
    (hprefix : ∀ x r, d * |prefixCut x r| ≤ p x) (x : C00) (i : ℕ) :
    (d / 2) * |x i| ≤ p x := by
  have hcoord : |x i| ≤ |prefixCut x (i + 1)| + |prefixCut x i| := by
    calc
      |x i| = |prefixCut x (i + 1) + -(prefixCut x i)| := by
        rw [prefixCut_succ]
        congr 1
        ring
      _ ≤ |prefixCut x (i + 1)| + |-(prefixCut x i)| := abs_add_le _ _
      _ = |prefixCut x (i + 1)| + |prefixCut x i| := by rw [abs_neg]
  have hmul := mul_le_mul_of_nonneg_left hcoord hd
  have h0 := hprefix x i
  have h1 := hprefix x (i + 1)
  nlinarith

theorem definite_of_prefix (p : Seminorm ℝ C00) (d : ℝ) (hd : 0 < d)
    (hprefix : ∀ x r, d * |prefixCut x r| ≤ p x) :
    ∀ x, p x = 0 → x = 0 := by
  intro x hx
  ext i
  have h := coordinate_lower_of_prefix p d hd.le hprefix x i
  rw [hx] at h
  have ha : |x i| = 0 := by
    have hnonneg := abs_nonneg (x i)
    nlinarith
  exact abs_eq_zero.mp ha

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (L : ℕ → C00 →ₗ[ℝ] Y)
  (hCauchy : ∀ x, CauchySeq (fun n => ‖L n x‖))

theorem limitSeminorm_prefix_lower (d : ℝ) (error : C00 → ℕ → ℝ)
    (herror : ∀ x, Tendsto (error x) atTop (𝓝 0))
    (hprefix : ∀ x r, ∀ᶠ n in atTop,
      d * |prefixCut x r| - error x n ≤ ‖L n x‖) :
    ∀ x r, d * |prefixCut x r| ≤ limitSeminorm L hCauchy x := by
  intro x r
  exact le_limitSeminorm_of_error L hCauchy x (d * |prefixCut x r|)
    (error x) (herror x) (hprefix x r)

theorem limitSeminorm_spreading
    (hosc : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, ∃ error : ℕ → ℝ,
        Tendsto error atTop (𝓝 0) ∧
        ∀ᶠ n in atTop,
          |‖L n (C00.place ι a)‖ - ‖L n (C00.ofArray a)‖| ≤ error n) :
    ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ,
        limitSeminorm L hCauchy (C00.place ι a) =
          limitSeminorm L hCauchy (C00.ofArray a) := by
  intro m ι hι a
  obtain ⟨error, herror, hbound⟩ := hosc ι hι a
  exact limitSeminorm_eq_of_error L hCauchy (C00.place ι a)
    (C00.ofArray a) error herror hbound

end SpreadingLimit

end MarkovSuperreflexivity

end

end OAI
