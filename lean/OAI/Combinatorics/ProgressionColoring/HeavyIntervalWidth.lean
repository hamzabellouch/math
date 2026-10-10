import OAI.Combinatorics.ProgressionColoring.Dichotomy
import OAI.Combinatorics.ProgressionColoring.ClosestReturnEstimates
import OAI.Combinatorics.ProgressionColoring.ResidueFiber
import OAI.Combinatorics.ProgressionColoring.LabelFiber
import Mathlib.Tactic.FieldSimp

namespace OAI

/-!
# Drift relative to every heavy label interval

All occurrences of a label are in one residue class modulo the primitive
return denominator. Packing these actual occurrence indices gives at least
`card - 1` periods between the extreme visits. Their representatives alone
then determine the real accumulated drift: the integral discrepancy is too
small to be nonzero. No assertion about the path between the visits is used.
-/

universe uIndex uB

namespace QuantitativeVanDerWaerden

/-- At indices differing by `c` denominator periods, the rational numerator
disappears modulo integers and only `c` times the drift remains. -/
theorem rational_path_period_difference {ι : Type uIndex} {h a b c : ℕ}
    (Y : ℕ → ι → ℝ) (A v : ι → ℝ) (s : ι → ℤ)
    (hh : 0 < h) (hab : a ≤ b) (hspan : b - a = c * h)
    (hpath : ∀ n i, ∃ z : ℤ,
      Y n i - A i - (n : ℝ) / h * ((s i : ℝ) + v i) = z) (i : ι) :
    ∃ z : ℤ, (Y b i - Y a i) - (c : ℝ) * v i = z := by
  obtain ⟨za, hza⟩ := hpath a i
  obtain ⟨zb, hzb⟩ := hpath b i
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hspanR : (b : ℝ) - a = (c : ℝ) * h := by
    have hs : ((b - a : ℕ) : ℝ) = (c : ℝ) * h := by exact_mod_cast hspan
    simpa only [Nat.cast_sub hab] using hs
  have hquot : (b : ℝ) / h - (a : ℝ) / h = c := by
    rw [← sub_div, hspanR, mul_div_cancel_right₀ _ hhR]
  have hscale : (b : ℝ) / h * ((s i : ℝ) + v i) -
      (a : ℝ) / h * ((s i : ℝ) + v i) = (c : ℝ) * ((s i : ℝ) + v i) := by
    rw [← sub_mul, hquot]
  refine ⟨(c : ℤ) * s i + zb - za, ?_⟩
  push_cast
  nlinarith

/-- A heavy set of occurrences in one residue class controls the common drift
by the actual width of every one of its coordinate intervals. -/
theorem heavy_fiber_relative_width {ι : Type uIndex} {J : Finset ℕ} {k h : ℕ}
    {M H : ℝ} (Y : ℕ → ι → ℝ) (A v L : ι → ℝ) (s : ι → ℤ)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < J.card) (hh : 0 < h)
    (hbound : ∀ j ∈ J, j < k)
    (hcongr : ∀ a ∈ J, ∀ b ∈ J, (h : ℤ) ∣ (b : ℤ) - a)
    (hpath : ∀ n i, ∃ z : ℤ,
      Y n i - A i - (n : ℝ) / h * ((s i : ℝ) + v i) = z)
    (hbox : ∀ a ∈ J, ∀ b ∈ J, ∀ i, |Y b i - Y a i| ≤ L i)
    (hwidth : ∀ i, L i ≤ 2 * H)
    (hdrift : ∀ i, |v i| ≤ 4 * M * H / (k : ℝ))
    (hsmall : 2 * H + 4 * M * H / (h : ℝ) < 1) :
    ∀ i, |v i| ≤ (2 * M / (k : ℝ)) * L i := by
  obtain ⟨hcard, _, _, hk⟩ := heavy_card_estimates hM hscale hheavy
  have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc, hcount, hspan, hspanbound⟩ :=
    residue_fiber_span J hJ hh hcard hcongr hbound
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hcountR : (J.card : ℝ) - 1 ≤ c := by
    have hcast : ((J.card - 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast hcount
    simpa only [Nat.cast_sub (by omega : 1 ≤ J.card), Nat.cast_one] using hcast
  have hclower : (k : ℝ) / (2 * M) ≤ c :=
    (heavy_card_div_lower hM hscale hheavy).trans hcountR
  have hspanR : (c : ℝ) * h ≤ k := by exact_mod_cast hspanbound.le
  have hmin := J.min'_mem hJ
  have hmax := J.max'_mem hJ
  have hminmax : J.min' hJ ≤ J.max' hJ := J.min'_le _ hmax
  intro i
  have hphase := rational_path_period_difference Y A v s hh hminmax hspan hpath i
  have hprod : |(c : ℝ) * v i| ≤ 4 * M * H / (h : ℝ) := by
    rw [abs_mul, abs_of_nonneg hcR]
    apply (le_div_iff₀ hhR).2
    calc
      ((c : ℝ) * |v i|) * h = ((c : ℝ) * h) * |v i| := by ring
      _ ≤ (k : ℝ) * |v i| := mul_le_mul_of_nonneg_right hspanR (abs_nonneg _)
      _ ≤ 4 * M * H := by
        have hv := (le_div_iff₀ hkR).mp (hdrift i)
        simpa only [mul_comm] using hv
  apply heavy_interval_relative_drift hkR hM hclower hphase
    (hbox _ hmin _ hmax i) hprod
  linarith [hwidth i]

/-- Apply the endpoint argument to the actual occurrence fiber of any heavy
label, including labels different from the one that supplied the return. -/
theorem heavy_label_relative_width {ι : Type uIndex} {B : Type uB} {k h j : ℕ}
    {M H : ℝ} (Y : ℕ → ι → ℝ) (A v : ι → ℝ) (s : ι → ℤ)
    (label : ℕ → B) (width : B → ι → ℝ)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (labelFiber k label (label j)).card) (hh : 0 < h)
    (hcongr : ∀ a, a < k → ∀ b, b < k → label a = label b →
      (h : ℤ) ∣ (b : ℤ) - a)
    (hpath : ∀ n i, ∃ z : ℤ,
      Y n i - A i - (n : ℝ) / h * ((s i : ℝ) + v i) = z)
    (hbox : ∀ a, a < k → ∀ b, b < k → label a = label b →
      ∀ i, |Y b i - Y a i| ≤ width (label a) i)
    (hwidth : ∀ i, width (label j) i ≤ 2 * H)
    (hdrift : ∀ i, |v i| ≤ 4 * M * H / (k : ℝ))
    (hsmall : 2 * H + 4 * M * H / (h : ℝ) < 1) :
    ∀ i, |v i| ≤ (2 * M / (k : ℝ)) * width (label j) i := by
  apply heavy_fiber_relative_width Y A v (width (label j)) s hM hscale hheavy hh
  · intro n hn
    exact (mem_labelFiber.mp hn).1
  · intro a ha b hb
    obtain ⟨ha, hla⟩ := mem_labelFiber.mp ha
    obtain ⟨hb, hlb⟩ := mem_labelFiber.mp hb
    exact hcongr a ha b hb (hla.trans hlb.symm)
  · exact hpath
  · intro a ha b hb i
    obtain ⟨ha, hla⟩ := mem_labelFiber.mp ha
    obtain ⟨hb, hlb⟩ := mem_labelFiber.mp hb
    simpa only [hla] using hbox a ha b hb (hla.trans hlb.symm) i
  · exact hwidth
  · exact hdrift
  · exact hsmall

end QuantitativeVanDerWaerden

end OAI
