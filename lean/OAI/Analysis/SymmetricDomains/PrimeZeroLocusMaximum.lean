import Mathlib
import OAI.Analysis.SymmetricDomains.FiberCardAmbientSheets

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem coeff_pow_X_sub_C_pred {r : ℕ} (hr : 0 < r) (b : ℂ) :
    ((Polynomial.X - C b)^r).coeff (r-1) = -(r : ℂ) * b := by
  have he := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin r))
    (fun _ => b) (by simpa using hr)
  simpa [nsmul_eq_mul] using he

theorem norm_finite_average_le_one {X : Type*} (F : Finset X) {r : ℕ}
    (hr : 0 < r) (hcard : F.card = r) (h : X → ℂ)
    (hb : ∀ x ∈ F, ‖h x‖ ≤ 1) : ‖(∑ x ∈ F, h x) / (r : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0:ℝ) < r)).mpr
  calc
    ‖∑ x ∈ F, h x‖ ≤ ∑ x ∈ F, ‖h x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ F, (1:ℝ) := Finset.sum_le_sum hb
    _ = r := by simp [hcard]

theorem extended_fiber_average {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : V → (Fin d → ℂ))
    (hπ : IsProperMap π) (hfin : ∀ y, (π ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ) (hr : 0 < r)
    (hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r)
    {B : Set (Fin d → ℂ)} (hB : IsOpen B) {a : Fin d → ℂ} (ha : a ∈ B)
    (h : V → ℂ) (hh : ContinuousOn h (π ⁻¹' B))
    (hb : ∀ x, π x ∈ B → ‖h x‖ ≤ 1)
    (hholo : ∀ k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin h y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}))
    (b : ℂ) (hcoalesce : ∀ x, π x = a → h x = b) :
    ∃ c : (Fin d → ℂ) → ℂ,
      DifferentiableOn ℂ c B ∧ (∀ y ∈ B, ‖c y‖ ≤ 1) ∧
      (∀ y ∈ B, MvPolynomial.eval y D ≠ 0 →
        c y = (∑ x ∈ (hfin y).toFinset, h x) / (r : ℂ)) ∧ c a = b := by
  classical
  obtain ⟨c,hcd,_,hce,hcq⟩ := extended_fiber_coefficients V π hπ hfin D hD r hcard
    hB ha h hh hb hholo b hcoalesce
  let j : Fin r := ⟨r-1, by omega⟩
  let g := fun y => -(c j y) / (r : ℂ)
  have hgd : DifferentiableOn ℂ g B := by
    dsimp [g]
    convert! (hcd j).neg.mul_const (r : ℂ)⁻¹ using 1
  have hge : ∀ y ∈ B, MvPolynomial.eval y D ≠ 0 →
      g y = (∑ x ∈ (hfin y).toFinset, h x)/(r : ℂ) := by
    intro y hy hDy
    have he := Polynomial.prod_X_sub_C_coeff_card_pred (hfin y).toFinset h
      (by rw [hcard y hDy]; exact hr)
    change -(c j y) / (r : ℂ) = _
    rw [hce j y hy hDy]
    change -((∏ x ∈ (hfin y).toFinset, (X - C (h x))).coeff (r-1))/(r : ℂ) = _
    rw [← hcard y hDy, he, neg_neg]
  have hgb : ∀ y ∈ B, ‖g y‖ ≤ 1 := by
    intro y hy
    let S := {y : Fin d → ℂ | MvPolynomial.eval y D ≠ 0}
    have hdense : Dense S := dense_polynomial_nonzero D hD
    have : (𝓝[S] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense y)
    have ht : Tendsto g (𝓝[S] y) (𝓝 (g y)) :=
      ((hgd y hy).differentiableAt (hB.mem_nhds hy)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht.norm
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB.mem_nhds hy)] with z hzS hzB
    rw [hge z hzB hzS]
    apply norm_finite_average_le_one _ hr (hcard z hzS) h
    intro x hx
    have hxz : π x = z := (hfin z).mem_toFinset.mp hx
    exact hb x (hxz.symm ▸ hzB)
  refine ⟨g,hgd,hgb,hge,?_⟩
  change -(c j a)/(r : ℂ) = b
  rw [hcq j]
  change -(((X - C b)^r).coeff (r-1))/(r : ℂ) = b
  rw [coeff_pow_X_sub_C_pred hr b]
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  field_simp

theorem holomorphic_maximum_subsequence_on_ball {d : ℕ}
    {a : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (F : ℕ → (Fin d → ℂ) → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) (Metric.ball a R))
    (hb : ∀ i y, y ∈ Metric.ball a R → ‖F i y‖ ≤ 1)
    (ha : Tendsto (fun i => F i a) atTop (𝓝 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ y ∈ Metric.ball a R, Tendsto (fun i => F (φ i) y) atTop (𝓝 1) := by
  classical
  let B := Metric.ball a R
  let : LocallyCompactSpace B := Metric.isOpen_ball.locallyCompactSpace
  have he : Equicontinuous (fun i (y : B) => F i y) :=
    equicontinuous_of_bounded_differentiableOn Metric.isOpen_ball F hd hb
  obtain ⟨f,_,_,φ,hφ,hconv⟩ := locally_uniform_subsequence_of_equicontinuous
    (fun i (y : B) => F i y) he (fun i y => hb i y y.property)
  let g : (Fin d → ℂ) → ℂ := fun y => if hy : y ∈ B then f ⟨y,hy⟩ else 0
  have hconv' : TendstoLocallyUniformlyOn (fun i => F (φ i)) g atTop B := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [g, Function.comp_def, Subtype.coe_prop, dite_true] using hconv
  have haB : a ∈ B := Metric.mem_ball_self hR
  have hga : g a = 1 := tendsto_nhds_unique (hconv'.tendsto_at haB) (ha.comp hφ.tendsto_atTop)
  have hge := maximum_propagation_on_ball hR (fun i => F (φ i)) g
    (fun i => hd (φ i)) (fun i => hb (φ i)) hconv' hga
  refine ⟨φ,hφ,fun y hy => ?_⟩
  simpa only [hge hy] using hconv'.tendsto_at hy

theorem unit_disc_finset_sum_eq_card {X : Type*} (F : Finset X) (v : X → ℂ)
    (hv : ∀ x ∈ F, ‖v x‖ ≤ 1) (hs : ∑ x ∈ F, v x = (F.card : ℂ)) :
    ∀ x ∈ F, v x = 1 := by
  have hre : ∑ x ∈ F, (v x).re = ∑ _x ∈ F, (1 : ℝ) := by
    simpa using congrArg Complex.re hs
  have hres : ∀ x ∈ F, (v x).re = 1 :=
    (Finset.sum_eq_sum_iff_of_le (fun x hx => (Complex.re_le_norm (v x)).trans (hv x hx))).mp hre
  intro x hx
  apply Complex.ext
  · simpa using hres x hx
  · have hsq := Complex.sq_norm_sub_sq_re (v x)
    have hnorm := hv x hx
    have hn := norm_nonneg (v x)
    have hi : (v x).im = 0 := by nlinarith [hres x hx, sq_nonneg (v x).im]
    simpa using hi

theorem scalar_maximum_local_of_finite_analytic_map {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π₀ : (Fin n → ℂ) → (Fin d → ℂ))
    (hπ : IsProperMap (fun x : V => π₀ x.val))
    (hπo : IsOpenMap (fun x : V => π₀ x.val))
    (hfin : ∀ y, ((fun x : V => π₀ x.val) ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ) (hr : 0 < r)
    (hsheets : ∀ a, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (A : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen A ∧ a ∈ A ∧ (∀ i, AnalyticOnNhd ℂ (g i) A) ∧
        ∀ y ∈ A, Function.Injective (fun i => g i y) ∧
          ∀ z, (z ∈ V ∧ π₀ z = y) ↔ ∃ i, g i y = z)
    {W : Set V} (hW : IsOpen W) (h : ℕ → V → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    (f : V → ℂ) (hfc : ContinuousOn f W)
    (ht : ∀ x ∈ W, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : V} (hq : q ∈ W) (hfq : f q = 1) : ∀ᶠ x in 𝓝 q, f x = 1 := by
  classical
  let π : V → (Fin d → ℂ) := fun x => π₀ x.val
  obtain ⟨B,hB,hqB,Ω,C,hΩ,hqΩ,hΩW,hC,hΩC,hfiber⟩ :=
    finite_fiber_localization hπ q (hfin (π q)) hW hq
  let H : ℕ → V → ℂ := fun i => Ω.piecewise (h i) (fun _ => h i q)
  have hHhol : ∀ i x, π x ∈ B → ScalarAnalyticAt (H i) x := by
    intro i
    exact scalarAnalyticAt_padded hΩ hC hΩC (fun x hx => hh i x (hΩW hx)) (h i q)
  have hHc : ∀ i, ContinuousOn (H i) (π ⁻¹' B) :=
    fun i x hx => (hHhol i x hx).continuousAt.continuousWithinAt
  have hHb : ∀ i x, π x ∈ B → ‖H i x‖ ≤ 1 := by
    intro i x _
    by_cases hx : x ∈ Ω
    · simpa only [H, piecewise_eq_of_mem Ω (h i) _ hx] using hb i x (hΩW hx)
    · simpa only [H, piecewise_eq_of_notMem Ω (h i) _ hx] using hb i q hq
  have hHq : ∀ i x, π x = π q → H i x = h i q := by
    intro i x hx
    by_cases hxΩ : x ∈ Ω
    · have hxq : x = q := by
        have : x ∈ Ω ∩ π ⁻¹' {π q} := ⟨hxΩ,hx⟩
        rw [hfiber] at this
        exact this
      simp [H, hxq, hqΩ]
    · simp [H, hxΩ]
  have hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r := by
    intro y hy
    obtain ⟨I,g,A,hIr,_,hyA,_,hs⟩ := hsheets y hy
    exact (fiber_card_of_ambient_sheets V π₀ hfin y I (fun i => g i y)
      (hs y hyA).1 (hs y hyA).2).trans hIr
  have hcoef : ∀ i k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin (H i) y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}) := by
    intro i k a ha
    obtain ⟨I,g,A,_,hA,haA,hg,hs⟩ := hsheets a ha.2
    apply fiberPolynomial_coeff_analyticAt_of_sheets V π₀ hfin (H i) I g hA haA hg hs
    intro x hx
    apply hHhol i x
    change π₀ x.val ∈ B
    rw [hx]
    exact ha.1
  choose c hcd hcb hce hcq using fun i => extended_fiber_average V π hπ hfin D hD r hr
    hcard hB hqB (H i) (hHc i) (hHb i) (hcoef i) (h i q) (hHq i)
  obtain ⟨R,hR,hRB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hqB)
  have hcqt : Tendsto (fun i => c i (π q)) atTop (𝓝 1) := by
    have heq : (fun i => c i (π q)) = (fun i => h i q) := funext hcq
    rw [heq]
    simpa only [hfq] using ht q hq
  obtain ⟨φ,hφ,hmax⟩ := holomorphic_maximum_subsequence_on_ball hR c
    (fun i => (hcd i).mono hRB) (fun i y hy => hcb i y (hRB hy)) hcqt
  let F : V → ℂ := Ω.piecewise f (fun _ => f q)
  have hFc : ContinuousOn F (π ⁻¹' B) :=
    continuousOn_padded hπ.continuous hB hΩ hC hΩC (hfc.mono hΩW) (f q)
  have hHt : ∀ x, Tendsto (fun i => H i x) atTop (𝓝 (F x)) := by
    intro x
    by_cases hx : x ∈ Ω
    · simpa only [H,F,piecewise_eq_of_mem Ω _ _ hx] using ht x (hΩW hx)
    · simpa only [H,F,piecewise_eq_of_notMem Ω _ _ hx] using ht q hq
  have hFb : ∀ x, π x ∈ B → ‖F x‖ ≤ 1 := by
    intro x hx
    exact le_of_tendsto (hHt x).norm (Filter.Eventually.of_forall fun i => hHb i x hx)
  have he : EqOn F (fun _ => 1)
      ((π ⁻¹' Metric.ball (π q) R) ∩ (π ⁻¹' {y | MvPolynomial.eval y D ≠ 0})) := by
    intro x hx
    let A := (hfin (π x)).toFinset
    have hsumt : Tendsto (fun i => (∑ z ∈ A, H (φ i) z)/(r : ℂ)) atTop
        (𝓝 ((∑ z ∈ A, F z)/(r : ℂ))) :=
      (tendsto_finsetSum A (fun z _ => (hHt z).comp hφ.tendsto_atTop)).div_const _
    have hsumt' : Tendsto (fun i => (∑ z ∈ A, H (φ i) z)/(r : ℂ)) atTop (𝓝 1) := by
      have heq : (fun i => c (φ i) (π x)) =
          (fun i => (∑ z ∈ A, H (φ i) z)/(r : ℂ)) :=
        funext (fun i => hce (φ i) (π x) (hRB hx.1) hx.2)
      rw [← heq]
      exact hmax (π x) hx.1
    have hsum : (∑ z ∈ A, F z) = (A.card : ℂ) := by
      have heq := tendsto_nhds_unique hsumt hsumt'
      have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
      rw [div_eq_one_iff_eq hrC] at heq
      simpa only [A, hcard (π x) hx.2] using heq
    have hv : ∀ z ∈ A, ‖F z‖ ≤ 1 := by
      intro z hz
      have hzx : π z = π x := (hfin (π x)).mem_toFinset.mp hz
      exact hFb z (hzx.symm ▸ hRB hx.1)
    exact unit_disc_finset_sum_eq_card A F hv hsum x
      ((hfin (π x)).mem_toFinset.mpr rfl)
  have hd : Dense (π ⁻¹' {y | MvPolynomial.eval y D ≠ 0}) :=
    (dense_polynomial_nonzero D hD).preimage hπo
  have hcl : π ⁻¹' Metric.ball (π q) R ⊆
      closure ((π ⁻¹' Metric.ball (π q) R) ∩ (π ⁻¹' {y | MvPolynomial.eval y D ≠ 0})) :=
    fun x hx => (Metric.isOpen_ball.preimage hπ.continuous).inter_closure ⟨hx,hd x⟩
  have he' : EqOn F (fun _ => 1) (π ⁻¹' Metric.ball (π q) R) :=
    he.of_subset_closure (hFc.mono (preimage_mono hRB)) continuousOn_const inter_subset_left hcl
  have hball : π ⁻¹' Metric.ball (π q) R ∈ 𝓝 q :=
    hπ.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hR)
  filter_upwards [hΩ.mem_nhds hqΩ,hball] with x hxΩ hxB
  have := he' hxB
  simpa only [F,piecewise_eq_of_mem Ω f _ hxΩ] using this

theorem prime_zeroLocus_maximum_local {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    {W : Set (MvPolynomial.zeroLocus ℂ I)} (hW : IsOpen W)
    (h : ℕ → MvPolynomial.zeroLocus ℂ I → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    (f : MvPolynomial.zeroLocus ℂ I → ℂ) (hfc : ContinuousOn f W)
    (ht : ∀ x ∈ W, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : MvPolynomial.zeroLocus ℂ I} (hq : q ∈ W) (hfq : f q = 1) :
    ∀ᶠ x in 𝓝 q, f x = 1 := by
  obtain ⟨d, _, g, hg, hgi⟩ := exists_integral_inj_algHom_of_quotient I Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ I (g (MvPolynomial.X j))
  obtain ⟨hπ,hfin⟩ := normalization_proper_finite I g hgi P hP
  have ho := normalization_isOpenMap I g hg hgi P hP
  obtain ⟨D,r,hD,hr,hs⟩ := normalization_analytic_sheets I g hg hgi P hP
  exact scalar_maximum_local_of_finite_analytic_map _ _ hπ ho hfin D hD r hr hs
    hW h hh hb f hfc ht hq hfq

end Release061

end OAI
