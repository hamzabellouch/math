import Mathlib.Algebra.Order.Field.GeomSum
import OAI.NumberTheory.Jacobsthal.Partitions.SourceAllInverseBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMeshTail

open _root_.Finset

theorem quadratic_exp_majorant {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    r^2*Real.exp (-c*r) ≤ (8/c^2)*Real.exp (-c*r/2) := by
  have h := Real.pow_div_factorial_le_exp (x := c*r/2) (by positivity) 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_one,Nat.cast_ofNat] at h
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  have hp : r^2 ≤ (8/c^2)*Real.exp (c*r/2) := by
    have hh : r^2 ≤ 8*Real.exp (c*r/2)/c^2 := (le_div_iff₀ hc2).mpr (by nlinarith [h])
    convert hh using 1; ring
  calc
    _ ≤ ((8/c^2)*Real.exp (c*r/2))*Real.exp (-c*r) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

noncomputable def envelope (c K t : ℝ) : ℝ :=
  (8/c^2)*Real.exp (-c*K/4)*Real.exp (-c*t/4)

theorem reward_le_envelope {c r K t : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hK : K ≤ r) (ht : t ≤ r) : r^2*Real.exp (-c*r) ≤ envelope c K t := by
  refine (quadratic_exp_majorant hc hr).trans ?_
  unfold envelope
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exponential_mesh_sum {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (N : ℕ) :
    (∑ j ∈ range N,h*Real.exp (-a*((j:ℝ)*h))) ≤ h+1/a := by
  let e := Real.exp (-a*h)
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hg : (∑ j ∈ range N,e^j) ≤ 1/(1-e) := by
    simpa only [Nat.Ico_zero_eq_range,pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m:=0) (n:=N) he0.le he1)
  have heq : (∑ j ∈ range N,h*Real.exp (-a*((j:ℝ)*h))) = h*(∑ j ∈ range N,e^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [e]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hbasic : (1+a*h)*e ≤ 1 := by
    calc
      _ ≤ Real.exp (a*h)*e := mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp (a*h)) he0.le
      _ = _ := by dsimp [e]; rw [← Real.exp_add]; simp
  have hInv : a*(1/a) = 1 := by field_simp
  have hden : 0 < 1-e := by linarith
  have hlast : h/(1-e) ≤ h+1/a := by
    apply (div_le_iff₀ hden).mpr
    have hinv0 : 0 < 1/a := one_div_pos.mpr ha
    have hm := mul_le_mul_of_nonneg_left hbasic hinv0.le
    nlinarith
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hg hh.le).trans (by simpa only [mul_one_div] using hlast)

theorem envelope_mesh_sum {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1) (K : ℝ) (N : ℕ) :
    (∑ j ∈ range N,h*envelope c K ((j:ℝ)*h)) ≤
      (8/c^2)*(1+4/c)*Real.exp (-c*K/4) := by
  have hb := exponential_mesh_sum (a:=c/4) (by positivity) hh N
  have heq : (∑ j ∈ range N,h*envelope c K ((j:ℝ)*h)) =
      ((8/c^2)*Real.exp (-c*K/4))*(∑ j ∈ range N,h*Real.exp (-(c/4)*((j:ℝ)*h))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold envelope
    rw [show -(c/4)*((j:ℝ)*h) = -c*((j:ℝ)*h)/4 by ring]
    ring
  rw [heq]
  have hconst : 0 ≤ (8/c^2)*Real.exp (-c*K/4) := by positivity
  calc
    _ ≤ ((8/c^2)*Real.exp (-c*K/4))*(h+1/(c/4)) := mul_le_mul_of_nonneg_left hb hconst
    _ ≤ ((8/c^2)*Real.exp (-c*K/4))*(1+4/c) := by
      apply mul_le_mul_of_nonneg_left _ hconst
      have he : 1/(c/4) = 4/c := by ring
      rw [he]
      linarith
    _ = _ := by ring

end NumberTheoryLean.ExponentialMeshTail

end

section

namespace NumberTheoryLean.PrimeExponentialTail

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins PrimeCompactWeights ExponentialMeshTail DerivativeWeights

variable {w ell S : ℝ} {start : Node}

noncomputable def tailReward (c K : ℝ) : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => if K < h.node.gap then
      ENNReal.ofReal (h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio) else 0

theorem grid_above {m : ℕ} (hm : 1 ≤ m) (S : ℝ) :
    S < point m (⌈S*(m:ℝ)⌉₊+1) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hceil := Nat.le_ceil (S*(m:ℝ))
  unfold point
  apply (lt_div_iff₀ hm0).mpr
  push_cast
  linarith

theorem actual_tail_bin_envelope {c K : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m)
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : ell ≤ start.cutoff) (hsS : start.ratio ≤ S)
    (z : ChainState w ell S start) :
    tailReward c K z ≤ ∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),
      ENNReal.ofReal (envelope c K (point m j))*(bin m j).indicator inverseWeight z := by
  classical
  cases z with
  | none => exact zero_le
  | some h =>
    by_cases hh : K < h.node.gap
    · have hg : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
      have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
      have hs0 := (valid_pos hv).le
      have hS : h.node.ratio ≤ S := terminal_ratio_le hsS h.admissible
      obtain ⟨j,hj,hcell⟩ := finite_grid_cover hm hs0 (hS.trans_lt (grid_above hm S))
      have hmem : some h ∈ bin m j := (mem_bin h m j).mpr hcell
      have hratio : point m j ≤ h.node.gap := hcell.1.trans (history_ratio_le_gap hell hr hs hcons hcut h)
      have hreward := reward_le_envelope hc hg.le hh.le hratio
      have hφ := weight_pos hv
      have hterm : tailReward c K (some h) ≤
          ENNReal.ofReal (envelope c K (point m j))*(bin m j).indicator inverseWeight (some h) := by
        rw [indicator_of_mem hmem]
        change (if K < h.node.gap then _ else _) ≤ ENNReal.ofReal _*ENNReal.ofReal _
        rw [ite_eq_left hh,← ENNReal.ofReal_mul (by unfold envelope; positivity)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_one_div] using div_le_div_of_nonneg_right hreward hφ.le
      exact hterm.trans (Finset.single_le_sum (s:=range (⌈S*(m:ℝ)⌉₊+1)) (a:=j)
        (f:=fun k => ENNReal.ofReal (envelope c K (point m k))*(bin m k).indicator inverseWeight (some h))
        (fun _ _ => zero_le) (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hj))
    · simp only [tailReward,ite_eq_right hh]
      exact zero_le

theorem actual_tail_integral_bins {c K : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m)
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : ell ≤ start.cutoff) (hsS : start.ratio ≤ S) (n : ℕ) :
    (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      ∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),ENNReal.ofReal (envelope c K (point m j))*inverseBin w ell S start m n j := by
  calc
    _ ≤ ∫⁻ z,∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),
        ENNReal.ofReal (envelope c K (point m j))*(bin m j).indicator inverseWeight z ∂pathLaw w ell S start n :=
      lintegral_mono (actual_tail_bin_envelope hc hm hell hr hs hcons hcut hsS)
    _ = _ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator (bin_measurable m j)]
        rfl
      · intro j _hj
        exact measurable_const.mul ((measurable_of_countable inverseWeight).indicator (bin_measurable m j))

theorem actual_tail_from_inverse_bins {c K C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    {m : ℕ} (hm : 1 ≤ m) (hm1 : width m ≤ 1)
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : ell ≤ start.cutoff) (hsS : start.ratio ≤ S) (n : ℕ)
    (hbins : ∀ j,inverseBin w ell S start m n j ≤ ENNReal.ofReal (C*width m)) :
    (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4)) := by
  have hh := width_pos hm
  refine (actual_tail_integral_bins hc hm hell hr hs hcons hcut hsS n).trans ?_
  calc
    _ ≤ ∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),ENNReal.ofReal (envelope c K (point m j))*ENNReal.ofReal (C*width m) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbins j) zero_le)
    _ = ENNReal.ofReal (C*(∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),width m*envelope c K (point m j))) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [← ENNReal.ofReal_mul (by unfold envelope; positivity)]
        congr 1
        ring
      · intro j _hj
        unfold envelope
        positivity
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have he : ∀ j : ℕ,point m j = (j:ℝ)*width m := by intro j; unfold point width; ring
      simp only [he]
      have h := envelope_mesh_sum hc hh hm1 K (⌈S*(m:ℝ)⌉₊+1)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hC

end NumberTheoryLean.PrimeExponentialTail

end

end Erdos970

end OAI
