import OAI.AlgebraicGeometry.PlaneCurves.InfiniteProducts
import OAI.AlgebraicGeometry.PlaneCurves.JetGerms

namespace OAI

/-!
# Marked theta products and scalar-basis degeneration
-/

section

/-! Degeneration of the actual theta product in the common logarithmic chart. -/
noncomputable section
open Filter Topology

namespace Nagata.W22
open Nagata.W21

/-- One half of the theta product, after substituting a shrinking center. -/
def scaledThetaPositive (a : ℝ) (δ : ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  thetaPositive (τ : ℂ) (((τ ^ a : ℝ) : ℂ) * Complex.exp (δ * x))

/-- The nonconstant product factors have one summable geometric majorant on a disk. -/
theorem scaledThetaPositive_factor_norm_le {a τ R : ℝ} {δ x : ℂ}
    (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hδ : ‖δ‖ ≤ 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (t : ℕ) :
    ‖-((τ : ℂ) ^ t * (((τ ^ a : ℝ) : ℂ) * Complex.exp (δ * x)))‖ ≤
      (1 / 2 : ℝ) ^ t * (τ ^ a * Real.exp R) := by
  have he : ‖Complex.exp (δ * x)‖ ≤ Real.exp R := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right hδ hR).trans_eq (one_mul R))
  simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hτ, abs_of_nonneg (Real.rpow_nonneg hτ _)]
  exact mul_le_mul (pow_le_pow_left₀ hτ hτhalf t)
    (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hτ _))
    (mul_nonneg (Real.rpow_nonneg hτ _) (norm_nonneg _)) (by positivity)

/-- Each half-product tends uniformly to one on a fixed disk when `a>0`. -/
theorem tendstoUniformlyOn_scaledThetaPositive
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a R : ℝ} {δ : ℂ}
    (ha : 0 < a) (hδ : ‖δ‖ ≤ 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoUniformlyOn (fun j => scaledThetaPositive a δ (τ j)) (fun _ => 1)
      l {x : ℂ | ‖x‖ ≤ R} := by
  let u : α → ℕ → ℂ → ℂ := fun j t x =>
    -((τ j : ℂ) ^ t * (((τ j ^ a : ℝ) : ℂ) * Complex.exp (δ * x)))
  let B : α → ℝ := fun j => 2 * (τ j ^ a * Real.exp R)
  have hp := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp hτ
  have hB : Tendsto B l (𝓝 0) := by
    simpa only [B, Function.comp_def, Real.zero_rpow ha.ne', zero_mul, mul_zero] using
      (hp.mul_const (Real.exp R)).const_mul 2
  have hhalf : ∀ᶠ j in l, τ j < 1 / 2 := hτ.eventually (gt_mem_nhds (by norm_num))
  have hg : Summable (fun t : ℕ => (1 / 2 : ℝ) ^ t) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∀ᶠ j in l, ∀ x ∈ {x : ℂ | ‖x‖ ≤ R}, Summable (fun t => ‖u j t x‖) := by
    filter_upwards [hτpos, hhalf] with j hj hh x hx
    exact (hg.mul_right (τ j ^ a * Real.exp R)).of_nonneg_of_le (fun t => norm_nonneg _)
      (fun t => scaledThetaPositive_factor_norm_le hj.le hh.le hδ hR hx t)
  have hbound : ∀ᶠ j in l, ∀ x ∈ {x : ℂ | ‖x‖ ≤ R}, (∑' t, ‖u j t x‖) ≤ B j := by
    filter_upwards [hτpos, hhalf, hsum] with j hj hh hs x hx
    calc
      _ ≤ ∑' t : ℕ, (1 / 2 : ℝ) ^ t * (τ j ^ a * Real.exp R) :=
        (hs x hx).tsum_le_tsum
          (fun t => scaledThetaPositive_factor_norm_le hj.le hh.le hδ hR hx t)
          (hg.mul_right _)
      _ = B j := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num [B]
  have h := Nagata.W03.tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le hB hsum hbound
  unfold scaledThetaPositive thetaPositive
  simpa only [u, sub_eq_add_neg] using h

/-- Local-uniform version of the same actual half-product degeneration. -/
theorem tendstoLocallyUniformlyOn_scaledThetaPositive
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : ℝ} {δ : ℂ}
    (ha : 0 < a) (hδ : ‖δ‖ ≤ 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => scaledThetaPositive a δ (τ j))
      (fun _ => 1) l Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro S hS hSc
  obtain ⟨R, hR⟩ := hSc.exists_bound_of_continuousOn (f := fun x : ℂ => x) continuous_id.continuousOn
  apply (tendstoUniformlyOn_scaledThetaPositive ha hδ (le_max_right R 0) hτ hτpos).mono
  intro x hx
  exact (hR x hx).trans (le_max_left R 0)

/-- The actual theta product evaluated at the shrinking center. -/
def shiftedThetaProduct (a : ℝ) (τ : ℝ) (x : ℂ) : ℂ :=
  thetaProduct (τ : ℂ) (((τ ^ a : ℝ) : ℂ) * Complex.exp x)

/-- The two source halves after the common-chart substitution. -/
theorem shiftedThetaProduct_eq_halves {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (x : ℂ) :
    shiftedThetaProduct a τ x = scaledThetaPositive a 1 τ x *
      scaledThetaPositive (1 - a) (-1) τ x := by
  unfold shiftedThetaProduct thetaProduct scaledThetaPositive
  simp only [one_mul, neg_one_mul, mul_inv_rev, ← Complex.exp_neg]
  congr 2
  rw [Real.rpow_sub hτ, Real.rpow_one, Complex.ofReal_div]
  ring

/-- The complete theta factor tends locally uniformly to one if `0<a<1`. -/
theorem tendstoLocallyUniformlyOn_shiftedThetaProduct
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : ℝ}
    (ha : 0 < a) (haone : a < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => shiftedThetaProduct a (τ j))
      (fun _ => 1) l Set.univ := by
  have hp := tendstoLocallyUniformlyOn_scaledThetaPositive (δ := (1 : ℂ)) ha (by simp) hτ hτpos
  have hm := tendstoLocallyUniformlyOn_scaledThetaPositive (δ := (-1 : ℂ))
    (sub_pos.mpr haone) (by simp) hτ hτpos
  have h := hp.mul₀ hm continuousOn_const continuousOn_const
  apply (show TendstoLocallyUniformlyOn
    (fun j x => scaledThetaPositive a 1 (τ j) x * scaledThetaPositive (1 - a) (-1) (τ j) x)
    (fun _ => (1 : ℂ)) l Set.univ by simpa only [Pi.mul_def, mul_one] using h).congr_inseparable
  filter_upwards [hτpos] with j hj x hx
  exact .of_eq (shiftedThetaProduct_eq_halves hj a x).symm

end Nagata.W22

end
end

section

/-! The actual nine-mark product, its powers, and the positive-degree second
basis block. All convergence assumptions are proved for these explicit functions. -/
noncomputable section
open Filter Topology

namespace Nagata.W22

/-- The product `Π` in the local covering frame, with offsets `aᵢ=x₀−xᵢ`. -/
def markedPi (a : Fin 9 → ℝ) (τ : ℝ) (x : ℂ) : ℂ :=
  ∏ i : Fin 9, shiftedThetaProduct (a i) τ x

/-- Every shifted theta factor is entire in the logarithmic coordinate. -/
theorem shiftedThetaProduct_differentiable {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (a : ℝ) :
    Differentiable ℂ (shiftedThetaProduct a τ) := by
  have ht : ‖(τ : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
  intro x
  have hz : ((τ ^ a : ℝ) : ℂ) * Complex.exp x ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ a).ne') (Complex.exp_ne_zero x)
  exact (Nagata.W21.thetaProduct_differentiableAt ht hz).comp x
    ((Complex.hasDerivAt_exp x).const_mul ((τ ^ a : ℝ) : ℂ)).differentiableAt

/-- The nine-factor product is entire in the logarithmic coordinate. -/
theorem markedPi_differentiable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (a : Fin 9 → ℝ) : Differentiable ℂ (markedPi a τ) := by
  exact Differentiable.fun_finsetProd fun i hi => shiftedThetaProduct_differentiable hτ hτone (a i)

/-- The full product tends locally uniformly to one, with all nine marks present. -/
theorem tendstoLocallyUniformlyOn_markedPi
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : Fin 9 → ℝ}
    (ha : ∀ i, 0 < a i) (haone : ∀ i, a i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => markedPi a (τ j)) (fun _ => 1) l Set.univ := by
  exact Nagata.W03.tendstoLocallyUniformlyOn_finset_prod_one Finset.univ
    (fun i hi => tendstoLocallyUniformlyOn_shiftedThetaProduct (ha i) (haone i) hτ hτpos)

/-- Every fixed nonnegative power of `Π` tends locally uniformly to one. -/
theorem tendstoLocallyUniformlyOn_markedPi_pow
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : Fin 9 → ℝ}
    (ha : ∀ i, 0 < a i) (haone : ∀ i, a i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e : ℕ) :
    TendstoLocallyUniformlyOn (fun j x => markedPi a (τ j) x ^ e) (fun _ => 1) l Set.univ := by
  exact Nagata.W03.tendstoLocallyUniformlyOn_pow_one
    (tendstoLocallyUniformlyOn_markedPi ha haone hτ hτpos) e

/-- The degree-zero tip is retained: the coefficient `Π^e` has jets tending to
those of the constant function one, including its zeroth jet. -/
theorem tendsto_iteratedDeriv_markedPi_pow_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {marks : Fin 9 → ℝ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e c : ℕ) :
    Tendsto (fun j => iteratedDeriv c (fun x => markedPi marks (τ j) x ^ e) 0)
      l (𝓝 ((0 : ℂ) ^ c)) := by
  have hf := tendstoLocallyUniformlyOn_markedPi_pow hmarks hmarksone hτ hτpos e
  have hone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  have hd : ∀ᶠ j in l, DifferentiableOn ℂ (fun x => markedPi marks (τ j) x ^ e) Set.univ := by
    filter_upwards [hτpos, hone] with j hj ho
    exact ((markedPi_differentiable hj ho marks).pow e).differentiableOn
  have h := (tendstoLocallyUniformlyOn_iteratedDeriv hf hd isOpen_univ c).tendsto_at
    (a := (0 : ℂ)) (Set.mem_univ _)
  convert h using 1
  cases c <;> simp [iteratedDeriv_const]

end Nagata.W22

end
end

section

/-! Exact moving-center evaluation of the genuine nine-mark section. -/
noncomputable section
namespace Nagata.W22

/-- The actual nine-mark multiplier section for ray lifts `τ^ξᵢ`. -/
def rayMarkedSection {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (ξ : Fin 9 → ℝ) :=
  Nagata.W08.markedThetaSection
    (τ := (τ : ℂ))
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone)
    (Complex.ofReal_ne_zero.mpr hτ.ne')
    (fun i => ((τ ^ ξ i : ℝ) : ℂ))
    (fun i => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ (ξ i)).ne')

/-- Evaluating the genuine section on the moving exponential chart gives exactly
the scalar nine-factor product used in the jet limit. -/
theorem rayMarkedSection_centered {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ξ : Fin 9 → ℝ) (x₀ : ℝ) (x : ℂ) :
    (rayMarkedSection hτ hτone ξ).val (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      markedPi (fun i => x₀ - ξ i) τ x := by
  have hz : ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ x₀).ne')
      (Complex.exp_ne_zero x)
  unfold rayMarkedSection
  rw [Nagata.W08.markedThetaSection_apply _ _ _ _ hz]
  unfold Nagata.W21.markedThetaProduct markedPi shiftedThetaProduct
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  rw [Real.rpow_sub hτ, Complex.ofReal_div]
  ring

end Nagata.W22

end
end

section

noncomputable section
open Filter Topology
namespace Nagata.W22

/-- The exact second-branch scalar coefficient. -/
def multipliedThetaCoefficient (marks : Fin 9 → ℝ) (n a K : ℝ) (ε : ℂ)
    (e : ℕ) (τ : ℝ) (x : ℂ) : ℂ :=
  markedPi marks τ x ^ e * normalizedThetaSeries n a K ε τ x

/-- The complete positive-degree coefficient block has the required local limit. -/
theorem tendstoLocallyUniformlyOn_multipliedThetaCoefficient
    {α : Type*} {l : Filter α} {τ : α → ℝ} {marks : Fin 9 → ℝ}
    {n a K : ℝ} {ε : ℂ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e : ℕ) :
    TendstoLocallyUniformlyOn (fun j => multipliedThetaCoefficient marks n a K ε e (τ j))
      (fun x => Complex.exp ((K : ℂ) * x)) l Set.univ := by
  have hp := tendstoLocallyUniformlyOn_markedPi_pow hmarks hmarksone hτ hτpos e
  have ht := tendstoLocallyUniformlyOn_normalizedThetaSeries (K := K) ha han hε hτ hτpos
  unfold multipliedThetaCoefficient
  simpa only [Pi.mul_def, one_mul] using hp.mul₀ ht continuousOn_const
    ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)

/-- Derivative limits for the complete positive-degree second block at the jet origin. -/
theorem tendsto_iteratedDeriv_multipliedThetaCoefficient_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {marks : Fin 9 → ℝ}
    {n a K : ℝ} {ε : ℂ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e c : ℕ) :
    Tendsto (fun j => iteratedDeriv c (multipliedThetaCoefficient marks n a K ε e (τ j)) 0)
      l (𝓝 ((K : ℂ) ^ c)) := by
  have hf := tendstoLocallyUniformlyOn_multipliedThetaCoefficient (K := K)
    hmarks hmarksone ha han hε hτ hτpos e
  have hone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  have htheta := Nagata.Workers.W11.eventually_differentiableOn_normalizedThetaSeries_disk
    (K := K) ha han hε hτ hτpos
  have hd : ∀ᶠ j in l, DifferentiableOn ℂ
      (multipliedThetaCoefficient marks n a K ε e (τ j)) {x : ℂ | ‖x‖ < 1} := by
    filter_upwards [hτpos, hone, htheta] with j hj ho ht
    exact (((markedPi_differentiable hj ho marks).pow e).differentiableOn).mul ht
  have h := (tendstoLocallyUniformlyOn_iteratedDeriv
    (hf.mono (Set.subset_univ _)) hd (isOpen_lt continuous_norm continuous_const) c).tendsto_at
    (a := (0 : ℂ)) (by simp)
  simpa only [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one] using h

end Nagata.W22

end
end

section

noncomputable section
open Filter Topology

namespace Nagata.W22
open Nagata.FiniteExponents

/-- Actual scalar expression of every basis column, retaining the degree-zero tip. -/
def basisCoefficient (d m : ℤ) (ρ Δ : ℝ) (marks : Fin 9 → ℝ)
    (τ : ℝ) (col : Column d m ρ Δ) : ℂ → ℂ :=
  let j := col.val.1
  let K := col.val.2
  if j ≤ m then
    normalizedThetaSeries (commonDegree d m : ℝ)
      ((K : ℝ) - firstLower d m j ρ Δ) (K : ℝ) ((-1 : ℂ) ^ (m - j)) τ
  else if 0 < d - 3 * j then
    multipliedThetaCoefficient marks (sourceDegree d j : ℝ)
      ((K : ℝ) - secondLower d j ρ Δ) (K : ℝ) 1 (Int.toNat (j - m)) τ
  else
    fun x => markedPi marks τ x ^ Int.toNat (j - m)

/-- All columns are eventually holomorphic on one fixed disk. This assertion
uses the actual normal convergence and keeps all three source branches. -/
theorem eventually_differentiableOn_basisCoefficient_disk
    {α : Type*} {l : Filter α} {τ : α → ℝ} {d m : ℤ} {ρ Δ : ℝ}
    (marks : Fin 9 → ℝ) (hτ : Tendsto τ l (𝓝 0))
    (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ᶠ t in l, ∀ col : Column d m ρ Δ,
      DifferentiableOn ℂ (basisCoefficient d m ρ Δ marks (τ t) col)
        {x : ℂ | ‖x‖ < 1} := by
  classical
  apply Filter.eventually_all.mpr
  rintro ⟨⟨j, K⟩, hcol⟩
  have hone : ∀ᶠ t in l, τ t < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  change (j, K) ∈ exponentSet d m ρ Δ at hcol
  rcases mem_exponentSet_iff.mp hcol with hfirst | hsecond | hzero
  · rcases hfirst with ⟨hj0, hjm, hlo, hhi⟩
    simp only [basisCoefficient, ite_eq_left hjm]
    exact Nagata.Workers.W11.eventually_differentiableOn_normalizedThetaSeries_disk
      (by linarith) (by linarith) (by simp) hτ hτpos
  · rcases hsecond with ⟨hmj, hjd, hdpos, hlo, hhi⟩
    simp only [basisCoefficient, ite_eq_right (not_le.mpr hmj), ite_eq_left hdpos]
    have ht := Nagata.Workers.W11.eventually_differentiableOn_normalizedThetaSeries_disk
      (n := (sourceDegree d j : ℝ)) (a := (K : ℝ) - secondLower d j ρ Δ)
      (K := (K : ℝ)) (ε := 1) (by linarith) (by linarith) (by simp) hτ hτpos
    filter_upwards [hτpos, hone, ht] with t hpos hone htheta
    exact (((markedPi_differentiable hpos hone marks).pow (Int.toNat (j-m))).differentiableOn).mul htheta
  · rcases hzero with ⟨hmj, hjd, hd0, rfl⟩
    simp only [basisCoefficient, ite_eq_right (not_le.mpr hmj), hd0, lt_self_iff_false, ite_false]
    filter_upwards [hτpos, hone] with t hpos hone
    exact ((markedPi_differentiable hpos hone marks).pow (Int.toNat (j-m))).differentiableOn

/-- Eventual smoothness of every literal column, for the finite-jet linearity bridge. -/
theorem eventually_contDiffAt_basisCoefficient
    {α : Type*} {l : Filter α} {τ : α → ℝ} {d m : ℤ} {ρ Δ : ℝ}
    (marks : Fin 9 → ℝ) (hτ : Tendsto τ l (𝓝 0))
    (hτpos : ∀ᶠ j in l, 0 < τ j) :
    ∀ᶠ j in l, ∀ col : Column d m ρ Δ, ∀ c : ℕ,
      ContDiffAt ℂ c (basisCoefficient d m ρ Δ marks (τ j) col) 0 := by
  filter_upwards [eventually_differentiableOn_basisCoefficient_disk
    (d := d) (m := m) (ρ := ρ) (Δ := Δ) marks hτ hτpos] with j hj col c
  exact ((hj col).contDiffOn (isOpen_lt continuous_norm continuous_const)).contDiffAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds (by simp))

/-- Every genuine scalar coefficient has the expected limiting x-jets. -/
theorem tendsto_iteratedDeriv_basisCoefficient_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {d m : ℤ} {ρ Δ : ℝ}
    {marks : Fin 9 → ℝ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j)
    (col : Column d m ρ Δ) (c : ℕ) :
    Tendsto (fun t => iteratedDeriv c (basisCoefficient d m ρ Δ marks (τ t) col) 0)
      l (𝓝 ((col.val.2 : ℂ) ^ c)) := by
  rcases col with ⟨⟨j, K⟩, hcol⟩
  change (j, K) ∈ exponentSet d m ρ Δ at hcol
  rcases mem_exponentSet_iff.mp hcol with hfirst | hsecond | hzero
  · rcases hfirst with ⟨hj0, hjm, hlo, hhi⟩
    simp only [basisCoefficient, ite_eq_left hjm]
    have hε : ‖(-1 : ℂ) ^ (m - j)‖ = 1 := by simp
    simpa using tendsto_iteratedDeriv_normalizedThetaSeries_zero
      (a := (K : ℝ) - firstLower d m j ρ Δ)
      (n := (commonDegree d m : ℝ)) (K := (K : ℝ))
      (by linarith) (by linarith) hε hτ hτpos c
  · rcases hsecond with ⟨hmj, hjd, hdpos, hlo, hhi⟩
    simp only [basisCoefficient, ite_eq_right (not_le.mpr hmj), ite_eq_left hdpos]
    simpa using tendsto_iteratedDeriv_multipliedThetaCoefficient_zero hmarks hmarksone
      (a := (K : ℝ) - secondLower d j ρ Δ)
      (n := (sourceDegree d j : ℝ)) (K := (K : ℝ))
      (by linarith) (by linarith) (by simp : ‖(1 : ℂ)‖ = 1) hτ hτpos
      (Int.toNat (j - m)) c
  · rcases hzero with ⟨hmj, hjd, hd0, rfl⟩
    simp only [basisCoefficient, ite_eq_right (not_le.mpr hmj), hd0, lt_self_iff_false, ite_false]
    simpa only [Int.cast_zero] using tendsto_iteratedDeriv_markedPi_pow_zero hmarks hmarksone hτ hτpos
      (Int.toNat (j - m)) c

end Nagata.W22

end
end

end OAI
