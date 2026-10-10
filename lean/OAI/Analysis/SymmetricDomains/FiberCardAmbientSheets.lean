import Mathlib
import OAI.Analysis.SymmetricDomains.ProperEventuallyFiberSubset

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem continuousOn_padded {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (_hπ : Continuous π) {B : Set Y} (_hB : IsOpen B)
    {Ω C : Set X} [DecidablePred (· ∈ Ω)] (hΩ : IsOpen Ω) (hC : IsClosed C)
    (hΩC : Ω = C ∩ π ⁻¹' B) {h : X → ℂ} (hh : ContinuousOn h Ω) (b : ℂ) :
    ContinuousOn (Ω.piecewise h (fun _ => b)) (π ⁻¹' B) := by
  classical
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hxΩ : x ∈ Ω
  · have he : Ω.piecewise h (fun _ => b) =ᶠ[𝓝 x] h :=
      by
        filter_upwards [hΩ.mem_nhds hxΩ] with z hz
        exact piecewise_eq_of_mem Ω h _ hz
    exact ((hh x hxΩ).continuousAt (hΩ.mem_nhds hxΩ)).congr_of_eventuallyEq he
  · have hxC : x ∉ C := fun hc => hxΩ (hΩC.symm ▸ ⟨hc, hx⟩)
    have he : Ω.piecewise h (fun _ => b) =ᶠ[𝓝 x] (fun _ => b) := by
      filter_upwards [hC.isOpen_compl.mem_nhds hxC] with z hz
      exact piecewise_eq_of_notMem Ω h _ (fun h => hz ((hΩC ▸ h).1))
    exact continuousAt_const.congr_of_eventuallyEq he

theorem proper_eventually_fiber_values_close {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (hπ : IsProperMap π) {a : Y} {B : Set Y} (hB : IsOpen B) (ha : a ∈ B)
    (h : X → ℂ) (hh : ContinuousOn h (π ⁻¹' B)) (b : ℂ)
    (hfiber : ∀ x, π x = a → h x = b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 a, ∀ x, π x = y → dist (h x) b < ε := by
  have hO : IsOpen ((π ⁻¹' B) ∩ h ⁻¹' Metric.ball b ε) :=
    hh.isOpen_inter_preimage (hB.preimage hπ.continuous) Metric.isOpen_ball
  have haO : π ⁻¹' {a} ⊆ (π ⁻¹' B) ∩ h ⁻¹' Metric.ball b ε := by
    intro x hx
    refine ⟨?_, ?_⟩
    · change π x ∈ B
      change π x = a at hx
      rwa [hx]
    · change dist (h x) b < ε
      rw [hfiber x hx, dist_self]
      exact hε
  exact (proper_eventually_fiber_subset hπ hO haO).mono fun _ hy x hx => (hy x hx).2

theorem extended_fiber_coefficients {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : V → (Fin d → ℂ))
    (hπ : IsProperMap π) (hfin : ∀ y, (π ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ)
    (hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r)
    {B : Set (Fin d → ℂ)} (hB : IsOpen B) {a : Fin d → ℂ} (ha : a ∈ B)
    (h : V → ℂ) (hh : ContinuousOn h (π ⁻¹' B))
    (hb : ∀ x, π x ∈ B → ‖h x‖ ≤ 1)
    (hholo : ∀ k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin h y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}))
    (b : ℂ) (hcoalesce : ∀ x, π x = a → h x = b) :
    ∃ c : Fin r → (Fin d → ℂ) → ℂ,
      (∀ j, DifferentiableOn ℂ (c j) B) ∧
      (∀ j y, y ∈ B → ‖c j y‖ ≤ (2 : ℝ)^r) ∧
      (∀ j y, y ∈ B → MvPolynomial.eval y D ≠ 0 →
        c j y = (fiberPolynomial π hfin h y).coeff j) ∧
      ∀ j, c j a = ((Polynomial.X - C b)^r).coeff j := by
  classical
  have hbound : ∀ k y, y ∈ B \ {y | MvPolynomial.eval y D = 0} →
      ‖(fiberPolynomial π hfin h y).coeff k‖ ≤ (2 : ℝ)^r := by
    intro k y hy
    have hc := hcard y hy.2
    unfold fiberPolynomial
    rw [← hc]
    apply norm_coeff_prod_X_sub_C_le
    intro x hx
    have hxy : π x = y := (hfin y).mem_toFinset.mp hx
    exact hb x (hxy.symm ▸ hy.1)
  choose c hcd hce hcb using fun j : Fin r =>
    bounded_polynomial_removable D hD hB (fun y => (fiberPolynomial π hfin h y).coeff j)
      (hholo j) (hbound j)
  refine ⟨c, hcd, hcb, fun j y hy hDy => hce j ⟨hy,hDy⟩, fun j => ?_⟩
  let S := {y : Fin d → ℂ | MvPolynomial.eval y D ≠ 0}
  have hSd : Dense S := dense_polynomial_nonzero D hD
  have : (𝓝[S] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hSd a)
  have hcT : Filter.Tendsto (c j) (𝓝[S] a) (𝓝 (c j a)) :=
    ((hcd j a ha).differentiableAt (hB.mem_nhds ha)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hrT : ∀ᶠ y in 𝓝[S] a, (hfin y).toFinset.card = r := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hcard y hy
  have hbT : ∀ ε > 0, ∀ᶠ y in 𝓝[S] a,
      ∀ x ∈ (hfin y).toFinset, dist (h x) b < ε := by
    intro ε hε
    have ht := proper_eventually_fiber_values_close hπ hB ha h hh b hcoalesce ε hε
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds ht] with y hy x hx
    exact hy x ((hfin y).mem_toFinset.mp hx)
  have hT := tendsto_coeff_prod_of_values_coalesce (𝓝[S] a)
    (fun y => (hfin y).toFinset) (fun _ x => h x) hrT b hbT j.val
  have he : (fun y => (∏ x ∈ (hfin y).toFinset,
      (Polynomial.X - C (h x))).coeff j.val) =ᶠ[𝓝[S] a] c j := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB.mem_nhds ha)] with y hyS hyB
    exact (hce j ⟨hyB,hyS⟩).symm
  exact tendsto_nhds_unique hcT (hT.congr' he)

theorem monic_eval_as_fin {r : ℕ} (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : p.natDegree = r) (v : ℂ) :
    p.eval v = v ^ r + ∑ j : Fin r, p.coeff j * v ^ (j : ℕ) := by
  have he := congrArg (fun q : Polynomial ℂ => q.eval v) hp.as_sum
  rw [hdeg] at he
  rw [Fin.sum_univ_eq_sum_range (fun j => p.coeff j * v^j)]
  simpa only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C] using he

theorem coalescing_coeff_identity {r : ℕ} (a : Fin r → ℂ) (v b : ℂ)
    (hroot : v ^ r + ∑ j : Fin r, a j * v ^ (j : ℕ) = 0) :
    (v-b)^r = ∑ j : Fin r, (((X - C b)^r).coeff j - a j) * v^(j : ℕ) := by
  have he := monic_eval_as_fin (r := r) ((X - C b)^r) ((monic_X_sub_C b).pow r)
    (by simp) v
  simp only [eval_pow, eval_sub, eval_X, eval_C] at he
  simp only [sub_mul, Finset.sum_sub_distrib]
  linear_combination he + hroot

theorem finite_fiber_root_identity_extend {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (π : X → Y) (hπ : Continuous π) (hπo : IsOpenMap π)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) {S B : Set Y}
    (hS : Dense S) (hB : IsOpen B) (r : ℕ)
    (hcard : ∀ y ∈ S, (hfin y).toFinset.card = r)
    (h : X → ℂ) (hh : ContinuousOn h (π ⁻¹' B))
    (c : Fin r → Y → ℂ) (hc : ∀ j, ContinuousOn (c j) B)
    (hce : ∀ j y, y ∈ B → y ∈ S → c j y = (fiberPolynomial π hfin h y).coeff j) :
    ∀ x, π x ∈ B → (h x)^r + ∑ j : Fin r, c j (π x) * h x ^ (j : ℕ) = 0 := by
  classical
  let f : X → ℂ := fun x => (h x)^r + ∑ j : Fin r, c j (π x) * h x ^ (j : ℕ)
  have hf : ContinuousOn f (π ⁻¹' B) := by
    apply (hh.pow r).add
    apply continuousOn_finsetSum
    intro j _
    exact ((hc j).comp hπ.continuousOn (fun _ hx => hx)).mul (hh.pow j.val)
  have he : EqOn f (fun _ => 0) ((π ⁻¹' B) ∩ (π ⁻¹' S)) := by
    intro x hx
    have hd : (fiberPolynomial π hfin h (π x)).natDegree = r :=
      (fiberPolynomial_natDegree π hfin h (π x)).trans (hcard (π x) hx.2)
    have hp := monic_eval_as_fin (fiberPolynomial π hfin h (π x))
      (fiberPolynomial_monic π hfin h (π x)) hd (h x)
    rw [fiberPolynomial_eval_eq_zero] at hp
    change (h x)^r + ∑ j : Fin r, c j (π x) * h x ^ (j : ℕ) = 0
    rw [hp]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hce j (π x) hx.1 hx.2]
  have hd : Dense (π ⁻¹' S) := hS.preimage hπo
  have hcl : π ⁻¹' B ⊆ closure ((π ⁻¹' B) ∩ (π ⁻¹' S)) :=
    fun x hx => (hB.preimage hπ).inter_closure ⟨hx,hd x⟩
  exact he.of_subset_closure hf continuousOn_const inter_subset_left hcl

theorem analytic_coefficient_difference_bound_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : E → ℂ} {q : E} {R B : ℝ} (hR : 0 < R)
    (ha : DifferentiableOn ℂ a (Metric.ball q R))
    (hB : ∀ z ∈ Metric.ball q R, ‖a z‖ ≤ B)
    {z : E} (hz : z ∈ Metric.ball q R) :
    ‖a q - a z‖ ≤ (2 * B / R) * dist z q := by
  have hq : q ∈ Metric.ball q R := Metric.mem_ball_self hR
  have hmap : MapsTo a (Metric.ball q R) (Metric.closedBall (a q) (2 * B)) := by
    intro w hw
    change dist (a w) (a q) ≤ 2 * B
    exact (dist_le_norm_add_norm _ _).trans (by linarith [hB w hw,hB q hq])
  simpa [dist_eq_norm_sub, norm_sub_rev] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball ha hmap hz

theorem coalescing_root_bound_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} {q : E} {R B : ℝ} (hR : 0 < R)
    (a : Fin r → E → ℂ)
    (ha : ∀ j, DifferentiableOn ℂ (a j) (Metric.ball q R))
    (hab : ∀ j z, z ∈ Metric.ball q R → ‖a j z‖ ≤ B)
    {z : E} (hz : z ∈ Metric.ball q R) {v w : ℂ}
    (hv : ‖v‖ ≤ 1)
    (hroot : (v - w) ^ r = ∑ j : Fin r, (a j q - a j z) * v ^ (j : ℕ)) :
    ‖v - w‖ ^ r ≤ (r : ℝ) * (2 * B / R) * dist z q := by
  calc
    ‖v - w‖ ^ r = ‖(v - w) ^ r‖ := (norm_pow _ _).symm
    _ = ‖∑ j : Fin r, (a j q - a j z) * v ^ (j : ℕ)‖ := congrArg norm hroot
    _ ≤ ∑ j : Fin r, ‖(a j q - a j z) * v ^ (j : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin r, (2 * B / R) * dist z q := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_pow]
      calc
        ‖a j q - a j z‖ * ‖v‖ ^ (j : ℕ) ≤ ‖a j q - a j z‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv) (norm_nonneg _)
        _ ≤ (2 * B / R) * dist z q := by
          simpa using analytic_coefficient_difference_bound_center hR (ha j) (hab j) hz
    _ = (r : ℝ) * (2 * B / R) * dist z q := by simp [mul_assoc]

theorem equicontinuousAt_of_local_coalescing_polynomials
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : X} {Ω : Set X} (hΩ : Ω ∈ 𝓝 p)
    {π : X → E} (hπ : ContinuousAt π p)
    {r : ℕ} {R B : ℝ} (hR : 0 < R)
    (h : ι → X → ℂ) (a : ι → Fin r → E → ℂ)
    (ha : ∀ i j, DifferentiableOn ℂ (a i j) (Metric.ball (π p) R))
    (hab : ∀ i j z, z ∈ Metric.ball (π p) R → ‖a i j z‖ ≤ B)
    (hh : ∀ i x, x ∈ Ω → ‖h i x‖ ≤ 1)
    (hroot : ∀ i x, x ∈ Ω → (h i x - h i p) ^ r =
      ∑ j : Fin r, (a i j (π p) - a i j (π x)) * h i x ^ (j : ℕ)) :
    EquicontinuousAt h p := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have ht : Filter.Tendsto (fun x => (r : ℝ) * (2 * B / R) * dist (π x) (π p))
      (𝓝 p) (𝓝 0) := by
    simpa using ((hπ.dist (continuousAt_const : ContinuousAt (fun _ => π p) p)).const_mul ((r : ℝ) * (2 * B / R)))
  have he := (tendsto_order.mp ht).2 (ε ^ r) (pow_pos hε r)
  have hball : ∀ᶠ x in 𝓝 p, π x ∈ Metric.ball (π p) R :=
    hπ.preimage_mem_nhds (Metric.ball_mem_nhds (π p) hR)
  filter_upwards [he, hball, hΩ] with x hx hxπ hxΩ i
  have hpow := (coalescing_root_bound_center hR (a i) (ha i) (hab i) hxπ
    (hh i x hxΩ) (hroot i x hxΩ)).trans_lt hx
  have hn := lt_of_pow_lt_pow_left₀ r hε.le hpow
  simpa [dist_eq_norm_sub, norm_sub_rev] using hn

theorem fiber_card_of_ambient_sheets {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → (Fin d → ℂ))
    (hfin : ∀ y, ((fun x : V => π x.val) ⁻¹' {y}).Finite)
    (a : Fin d → ℂ) (I : Finset ℂ) (g : I → (Fin n → ℂ))
    (hi : Function.Injective g)
    (hg : ∀ z, (z ∈ V ∧ π z = a) ↔ ∃ i, g i = z) :
    (hfin a).toFinset.card = I.card := by
  have hgV : ∀ i, g i ∈ V := fun i => ((hg (g i)).mpr ⟨i,rfl⟩).1
  let s : I → V := fun i => ⟨g i, hgV i⟩
  have hsi : Function.Injective s := fun i j hij => hi (congrArg Subtype.val hij)
  have hse : ∀ x : V, π x.val = a ↔ ∃ i, s i = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (hg x.val).mp ⟨x.property,hx⟩
      exact ⟨i,Subtype.ext hi⟩
    · rintro ⟨i,rfl⟩
      exact ((hg (g i)).mpr ⟨i,rfl⟩).2
  simpa using fiber_card_of_sheets (fun x : V => π x.val) hfin a s hsi hse

end Release061

end OAI
