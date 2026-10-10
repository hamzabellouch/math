import OAI.Analysis.KadisonKastler.BoundaryIntertwiner
import OAI.Analysis.KadisonKastler.ConcreteTraceComplete
import OAI.Analysis.KadisonKastler.TraceLimits
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! # Pointwise diagonal comparison in a finite algebra

The least-norm argument is carried out in a supplied faithful tracial
Hilbert realization. Bounded completeness of the concrete finite algebra
keeps Hilbert limits in the operator algebra. No measurable selection or
existence of a boundary space is asserted here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The least-norm vector of a convex set is unique. -/
theorem eq_of_convex_least_norm {K : Set E} (hK : Convex ℝ K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    (hxm : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hym : ∀ z ∈ K, ‖y‖ ≤ ‖z‖) : x = y := by
  have hn : ‖y‖ = ‖x‖ := le_antisymm (hym x hx) (hxm y hy)
  have hm : (1 / 2 : ℝ) • (x + y) ∈ K := by
    simpa only [smul_add] using hK hx hy (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hp := hxm _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hp
  have hs := mul_self_le_mul_self (norm_nonneg x) hp
  have hpar := parallelogram_law_with_norm_mul ℂ x y
  rw [hn] at hpar
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Every nonempty closed convex subset of a Hilbert space has a unique
least-norm vector. -/
theorem exists_unique_least_norm [CompleteSpace E] {K : Set E}
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    ∃! x : E, x ∈ K ∧ ∀ y ∈ K, ‖x‖ ≤ ‖y‖ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  obtain ⟨x, hx, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconvex (0 : E)
  have hxm : ∀ y ∈ K, ‖x‖ ≤ ‖y‖ := by
    intro y hy
    have hi : (⨅ w : K, ‖(0 : E) - w‖) ≤ ‖(0 : E) - y‖ :=
      ciInf_le ⟨(0 : ℝ), Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨y, hy⟩ : K)
    simpa only [zero_sub, norm_neg] using hmin.le.trans hi
  exact ⟨x, ⟨hx, hxm⟩, fun y hy => eq_of_convex_least_norm hconvex hy.1 hx hy.2 hxm⟩

end Hilbert

section Concrete

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E)
variable (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)

include hJ in
/-- Faithfulness makes a tracial Hilbert realization injective. -/
theorem traceHilbert_injective : Function.Injective J := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (traceTwoNorm_eq_zero_iff τ _).mp
  rw [← hJ, map_sub, hxy, sub_self, norm_zero]

include hJ in
/-- Operator closed balls have closed images in a faithful tracial Hilbert
realization, by concrete bounded two-norm completeness. -/
theorem FiniteVectorTrace.isClosed_traceHilbert_ball (hτ : FiniteVectorTrace τ)
    (a : Algebra M) {r : ℝ} (hr : 0 ≤ r) :
    IsClosed (J '' Metric.closedBall a r) := by
  apply isClosed_of_closure_subset
  intro y hy
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hy
  choose x hxmem hx using hv
  have hxn (n : ℕ) : ‖x n - a‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hxmem n
  have hxb (n : ℕ) : ‖x n‖ ≤ r + ‖a‖ := by
    calc
      ‖x n‖ = ‖(x n - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ r + ‖a‖ := add_le_add (hxn n) le_rfl
  have hxc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hvlim.cauchySeq ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [← hJ, map_sub, hx, dist_eq_norm] using hN m hm n hn
  obtain ⟨b, hb, hstrong, htwo⟩ := hτ.bounded_complete x
    (add_nonneg hr (norm_nonneg a)) hxb hxc
  have hJb : Tendsto v atTop (𝓝 (J b)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [← hx, ← map_sub, hJ] using htwo
  have hyb : J b = y := tendsto_nhds_unique hJb hvlim
  have hbball : b ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ hr
    intro ξ
    have hs := (hstrong ξ).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (a : H →L[ℂ] H) ξ) atTop (𝓝 ((a : H →L[ℂ] H) ξ)))
    exact le_of_tendsto hs.norm (Eventually.of_forall fun n =>
      (x n - a).val.le_of_opNorm_le (hxn n) ξ)
  exact ⟨b, hbball, hyb⟩

/-- Closed convex hull in the supplied trace Hilbert space. -/
def diagonalTraceHull (s : Set (Algebra M)) : Set E :=
  closure (J '' convexHull ℝ s)

/-- The definition agrees with the ordinary Hilbert closed convex hull. -/
theorem diagonalTraceHull_eq (s : Set (Algebra M)) :
    diagonalTraceHull J s = closure (convexHull ℝ (J '' s)) := by
  unfold diagonalTraceHull
  congr 1
  exact (J.restrictScalars ℝ).image_convexHull s

/-- The trace hull is convex. -/
theorem diagonalTraceHull_convex (s : Set (Algebra M)) :
    Convex ℝ (diagonalTraceHull J s) := by
  rw [diagonalTraceHull_eq]
  exact (convex_convexHull ℝ _).closure

include hJ in
/-- Bounds on every generator hold throughout the trace Hilbert hull, as
actual operator-norm bounds on an element of the algebra. -/
theorem traceHull_mem_ball (hτ : FiniteVectorTrace τ) {s : Set (Algebra M)}
    (a : Algebra M) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x - a‖ ≤ r) {z : E} (hz : z ∈ diagonalTraceHull J s) :
    ∃ b : Algebra M, J b = z ∧ ‖b - a‖ ≤ r := by
  have hc : convexHull ℝ s ⊆ Metric.closedBall a r := by
    apply convexHull_min _ (convex_closedBall a r)
    intro x hx
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs x hx
  have hz' : z ∈ J '' Metric.closedBall a r :=
    (closure_minimal (Set.image_mono hc) (hτ.isClosed_traceHilbert_ball J hJ a hr)) hz
  obtain ⟨b, hb, heq⟩ := hz'
  exact ⟨b, heq, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hb⟩

include hJ in
/-- A nonempty family of contractions near one has an actual unique
least-two-norm operator in its trace Hilbert closed convex hull. -/
theorem exists_unique_diagonal_least [CompleteSpace E]
    (hτ : FiniteVectorTrace τ) {s : Set (Algebra M)} (hsne : s.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsr : ∀ x ∈ s, ‖x - 1‖ ≤ r) :
    ∃! b : Algebra M, J b ∈ diagonalTraceHull J s ∧ ‖b‖ ≤ 1 ∧ ‖b - 1‖ ≤ r ∧
      ∀ z ∈ diagonalTraceHull J s, ‖J b‖ ≤ ‖z‖ := by
  obtain ⟨z, hz, hzu⟩ := exists_unique_least_norm
    (show (diagonalTraceHull J s).Nonempty from by
      obtain ⟨x, hx⟩ := hsne
      exact ⟨J x, subset_closure ⟨x, subset_convexHull ℝ s hx, rfl⟩⟩)
    isClosed_closure (diagonalTraceHull_convex J s)
  obtain ⟨b, hbz, hbr⟩ := traceHull_mem_ball J hJ hτ 1 hr hsr hz.1
  obtain ⟨c, hcz, hc1⟩ := traceHull_mem_ball J hJ hτ 0 (r := 1) (by norm_num)
    (fun x hx => by simpa only [sub_zero] using hs1 x hx) hz.1
  have hbc : b = c := traceHilbert_injective J hJ (hbz.trans hcz.symm)
  have hb1 : ‖b‖ ≤ 1 := by simpa only [hbc, sub_zero] using hc1
  refine ⟨b, ⟨hbz ▸ hz.1, hb1, hbr, hbz ▸ hz.2⟩, ?_⟩
  intro c hc
  apply traceHilbert_injective J hJ
  exact (hzu (J c) ⟨hc.1, hc.2.2.2⟩).trans hbz.symm


include hJ in
/-- Trace-isometric linear maps carry trace convex hulls into the hull of
any containing image of the generators. -/
theorem traceHull_map (F : Algebra M →ₗ[ℂ] Algebra M)
    (hF : ∀ x, traceTwoNorm τ (F x) = traceTwoNorm τ x)
    {s t : Set (Algebra M)} (himage : F '' s ⊆ t)
    {b : Algebra M} (hb : J b ∈ diagonalTraceHull J s) :
    J (F b) ∈ diagonalTraceHull J t := by
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hb
  choose x hxmem hx using hv
  apply isClosed_closure.mem_of_tendsto
    (show Tendsto (fun n => J (F (x n))) atTop (𝓝 (J (F b))) from ?_)
    (Eventually.of_forall fun n => subset_closure ?_)
  · rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := (hvlim.sub_const (J b)).norm
    simpa only [sub_self, norm_zero, ← hx, ← map_sub, hJ, hF] using hn
  · refine ⟨F (x n), ?_, rfl⟩
    apply convexHull_mono himage
    have hm : F (x n) ∈ F '' convexHull ℝ s := ⟨x n, hxmem n, rfl⟩
    have heq : F '' convexHull ℝ s = convexHull ℝ (F '' s) :=
      (F.restrictScalars ℝ).image_convexHull s
    rwa [heq] at hm

include hJ in
/-- Least vectors transform exactly under left and right unitary actions,
provided these actions identify the two generating sets. -/
theorem diagonal_least_covariance (u v : unitary (Algebra M))
    {s t : Set (Algebra M)}
    (hforward : ∀ x ∈ s, (u : Algebra M) * x * star (v : Algebra M) ∈ t)
    (hbackward : ∀ y ∈ t, star (u : Algebra M) * y * (v : Algebra M) ∈ s)
    {b c : Algebra M}
    (hb : J b ∈ diagonalTraceHull J s)
    (hc : J c ∈ diagonalTraceHull J t)
    (hbm : ∀ z ∈ diagonalTraceHull J s, ‖J b‖ ≤ ‖z‖)
    (hcm : ∀ z ∈ diagonalTraceHull J t, ‖J c‖ ≤ ‖z‖) :
    c = (u : Algebra M) * b * star (v : Algebra M) := by
  let F := LinearMap.mulLeftRight ℂ ((u : Algebra M), star (v : Algebra M))
  let R := LinearMap.mulLeftRight ℂ (star (u : Algebra M), (v : Algebra M))
  have hF (x : Algebra M) : traceTwoNorm τ (F x) = traceTwoNorm τ x := by
    change traceTwoNorm τ (((u : Algebra M) * x) * (star v : unitary (Algebra M))) = _
    simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  have hR (x : Algebra M) : traceTwoNorm τ (R x) = traceTwoNorm τ x := by
    change traceTwoNorm τ (((star u : unitary (Algebra M)) : Algebra M) * x *
      (v : Algebra M)) = _
    simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  have hFb := traceHull_map J hJ F hF (by rintro _ ⟨x, hx, rfl⟩; exact hforward x hx) hb
  have hRc := traceHull_map J hJ R hR (by rintro _ ⟨x, hx, rfl⟩; exact hbackward x hx) hc
  have hle : ‖J (F b)‖ ≤ ‖J c‖ := by
    simpa only [hJ, hF, hR] using hbm _ hRc
  apply traceHilbert_injective J hJ
  exact eq_of_convex_least_norm (diagonalTraceHull_convex J t) hc hFb hcm
    (fun z hz => hle.trans (hcm z hz))


/-- The pointwise diagonal generating family from an exact cocycle. -/
def diagonalGenerators {G D : Type*} (W : G → D → unitary (Algebra M))
    (x y : D) : Set (Algebra M) :=
  Set.range (fun t => (W t x : Algebra M) * star (W t y : Algebra M))

include hJ in
/-- The least-norm diagonal field is an actual contraction and satisfies
exact covariance under the cocycle. This is a pointwise result. -/
theorem exists_diagonal_least_field_full [CompleteSpace E]
    (hτ : FiniteVectorTrace τ) {G D : Type*} [Group G]
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ c : D → D → Algebra M,
      (∀ x y, J (c x y) ∈ diagonalTraceHull J (diagonalGenerators W x y) ∧
        ‖c x y‖ ≤ 1 ∧ ‖c x y - 1‖ ≤ r ∧
        ∀ z ∈ diagonalTraceHull J (diagonalGenerators W x y), ‖J (c x y)‖ ≤ ‖z‖) ∧
      (∀ g x y, c x y = (W g x : Algebra M) * c (shift g x) (shift g y) *
        star (W g y : Algebra M)) := by
  have hs (x y : D) : ∃ b : Algebra M,
      J b ∈ diagonalTraceHull J (diagonalGenerators W x y) ∧ ‖b‖ ≤ 1 ∧
      ‖b - 1‖ ≤ r ∧ ∀ z ∈ diagonalTraceHull J (diagonalGenerators W x y), ‖J b‖ ≤ ‖z‖ := by
    apply (exists_unique_diagonal_least J hJ hτ (s := diagonalGenerators W x y)
      (Set.range_nonempty _) hr ?_ ?_).exists
    · rintro _ ⟨t, rfl⟩
      simpa only [Submonoid.coe_mul, Unitary.coe_star] using
        norm_unitary_le_one (W t x * star (W t y))
    · rintro _ ⟨t, rfl⟩
      exact hnear t x y
  choose c hc using hs
  refine ⟨c, hc, ?_⟩
  intro g x y
  have hgen (t : G) :
      (W g x : Algebra M) *
        ((W t (shift g x) : Algebra M) * star (W t (shift g y) : Algebra M)) *
        star (W g y : Algebra M) =
      (W (g * t) x : Algebra M) * star (W (g * t) y : Algebra M) := by
    rw [hW g t x, hW g t y, star_mul]
    noncomm_ring
  apply diagonal_least_covariance J hJ (W g x) (W g y)
    (s := diagonalGenerators W (shift g x) (shift g y))
    (t := diagonalGenerators W x y) ?_ ?_
    (hc (shift g x) (shift g y)).1 (hc x y).1
    (hc (shift g x) (shift g y)).2.2.2 (hc x y).2.2.2
  · rintro _ ⟨t, rfl⟩
    exact ⟨g * t, (hgen t).symm⟩
  · rintro _ ⟨t, rfl⟩
    refine ⟨g⁻¹ * t, ?_⟩
    have heq := hgen (g⁻¹ * t)
    rw [mul_inv_cancel_left] at heq
    dsimp only
    rw [← heq]
    symm
    calc
      _ = (star (W g x : Algebra M) * (W g x : Algebra M)) *
          ((W (g⁻¹ * t) (shift g x) : Algebra M) *
            star (W (g⁻¹ * t) (shift g y) : Algebra M)) *
          (star (W g y : Algebra M) * (W g y : Algebra M)) := by noncomm_ring
      _ = _ := by
        rw [Unitary.star_mul_self_of_mem (W g x).property,
          Unitary.star_mul_self_of_mem (W g y).property, one_mul, mul_one]


include hJ in
/-- The pointwise diagonal least field, with only its operator bounds
and covariance exposed. -/
theorem exists_diagonal_least_field [CompleteSpace E]
    (hτ : FiniteVectorTrace τ) {G D : Type*} [Group G]
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ c : D → D → Algebra M,
      (∀ x y, ‖c x y‖ ≤ 1 ∧ ‖c x y - 1‖ ≤ r) ∧
      (∀ g x y, c x y = (W g x : Algebra M) * c (shift g x) (shift g y) *
        star (W g y : Algebra M)) := by
  obtain ⟨c, hc, hcov⟩ := exists_diagonal_least_field_full J hJ hτ shift W hW hr hnear
  exact ⟨c, fun x y => ⟨(hc x y).2.1, (hc x y).2.2.1⟩, hcov⟩

end Concrete


section Polar

variable {B : Type*} [CStarAlgebra B]
local instance boundaryDiagonalOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryDiagonalStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Polar normalization respects left and right multiplication by
unitaries, for invertible elements. -/
theorem polar_unitary_sandwich {b c : B} (hbunit : IsUnit b)
    (u v a d : unitary B) (ha : (a : B) * CFC.abs b = b)
    (hd : (d : B) * CFC.abs c = c)
    (hbc : b = (u : B) * c * star (v : B)) :
    (a : B) = (u : B) * (d : B) * star (v : B) := by
  have habs : CFC.abs b = (v : B) * CFC.abs c * star (v : B) := by
    rw [hbc, mul_assoc, abs_unitary_mul]
    simpa only [Unitary.coe_star, star_star] using abs_mul_unitary c (star v)
  have hi : IsUnit (CFC.abs b) := by
    obtain ⟨t, rfl⟩ := hbunit
    exact isUnit_abs t
  apply hi.mul_right_cancel
  rw [ha, habs]
  calc
    b = (u : B) * ((d : B) * CFC.abs c) * star (v : B) := by rw [hd, hbc]
    _ = ((u : B) * (d : B) * star (v : B)) *
        ((v : B) * CFC.abs c * star (v : B)) := by
      symm
      calc
        _ = (u : B) * (d : B) * (star (v : B) * (v : B)) * CFC.abs c * star (v : B) := by
          noncomm_ring
        _ = _ := by
          rw [Unitary.star_mul_self_of_mem v.property, mul_one]
          noncomm_ring

/-- Pointwise polar normalization of a covariant near-identity field. -/
theorem exists_diagonal_polar_field {D G : Type*} (shift : G → D → D)
    (u : G → D → unitary B) (c : D → D → B)
    {r : ℝ} (hr : r < 1) (hnear : ∀ x y, ‖c x y - 1‖ ≤ r)
    (hcov : ∀ g x y, c x y = (u g x : B) * c (shift g x) (shift g y) *
      star (u g y : B)) :
    ∃ a : D → D → unitary B,
      (∀ x y, ‖(a x y : B) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, (a x y : B) = (u g x : B) * (a (shift g x) (shift g y) : B) *
        star (u g y : B)) := by
  have hp (x y : D) := exists_polar_unitary_near_one (c x y)
    ((hnear x y).trans_lt hr)
  choose a ha han using hp
  refine ⟨a, fun x y => (han x y).trans (mul_le_mul_of_nonneg_left (hnear x y) (by norm_num)), ?_⟩
  intro g x y
  apply polar_unitary_sandwich ?_ (u g x) (u g y) (a x y)
    (a (shift g x) (shift g y)) (ha x y) (ha (shift g x) (shift g y)) (hcov g x y)
  nontriviality B
  exact (Units.ofNearby 1 (c x y) (by simpa using (hnear x y).trans_lt hr)).isUnit

end Polar


/-- Pointwise diagonal comparison, including the actual least-norm
construction and its unitary polar normalization. -/
theorem exists_pointwise_diagonal_comparison
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) {G D : Type*} [Group G]
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ a : D → D → unitary (Algebra M),
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  obtain ⟨c, hc, hcov⟩ := exists_diagonal_least_field J hJ hτ shift W hW hr0 hnear
  exact exists_diagonal_polar_field shift W c hr (fun x y => (hc x y).2) hcov

end

end KadisonKastler

end OAI
