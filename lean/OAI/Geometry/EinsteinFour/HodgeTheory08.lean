import OAI.Geometry.EinsteinFour.CurvatureTensors02
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMeasure
import OAI.Geometry.EinsteinFour.ScalarRegularity06
import OAI.Geometry.EinsteinFour.ScalarRegularity07
import OAI.Geometry.EinsteinFour.WeylEstimates03
import OAI.Geometry.EinsteinFour.WeylEstimates07
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

namespace OAI


section

/-! Uniform O(t) control of the cutoff error on all normal coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatScaledCommutator_bounded (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k,
      |fourHeatScaledCommutator a b B χ u t x k| ≤ C := by
  let S := fun z : ℝ × FourSpace => ∑ k : Fin 6,
    |fourHeatScaledCommutator a b B χ u z.1 z.2 k|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    (fourHeatScaledCommutator_continuous a b B χ u ha hb hB hχ hu k).abs)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hχc).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ tsupport χ
  · have hle : |fourHeatScaledCommutator a b B χ u t x k| ≤ S (t, x) :=
      Finset.single_le_sum (fun q _ => abs_nonneg
        (fourHeatScaledCommutator a b B χ u t x q)) (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx⟩)).trans (le_max_left _ _))
  · have hz := fourHeatScaledCommutator_zero_of_locally_const a b B χ u t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem fourHeatScaledCommutator_gaussian_bound (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q))
    (r : ℝ) (hr : 0 < r) (hinner : ∀ x ∈ ball 0 r, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k,
      |(fourHeatGaussian t x / t) * fourHeatScaledCommutator a b B χ u t x k| ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := fourHeatScaledCommutator_bounded a b B χ u ha hb hB hχ hχc hu
  refine ⟨C * (384 / (Real.pi ^ 2 * r ^ 8)), by positivity, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ ball 0 r
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    rw [fourHeatScaledCommutator_zero_of_locally_const a b B χ u t x 1 he k,
      mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hrx : r ≤ ‖x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩ x k)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * r ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time r t hr ht.1 x hrx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual density-weighted covariant flux and its first derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatCovariantDerivative_differentiable
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hA : ∀ l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    DifferentiableAt ℝ (fun y => fourHeatCovariantDerivative A u i y k) x := by
  apply DifferentiableAt.add
  · exact (((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  · exact DifferentiableAt.fun_sum fun l _ =>
      (hA l).mul ((hu l).differentiableAt (by norm_num))

theorem fourHeatCovariantDerivative_sum_four
    (A : Fin 4 → FourSpace → HeatMat6) (w : Fin 4 → FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (j : Fin 4) (k : Fin 6)
    (hw : ∀ i, DifferentiableAt ℝ (fun y => w i y k) x) :
    fourHeatCovariantDerivative A (fun y l => ∑ i, w i y l) j x k =
      ∑ i, fourHeatCovariantDerivative A (w i) j x k := by
  have hd : partialDeriv (fun y => ∑ i, w i y k) j x =
      ∑ i, partialDeriv (fun y => w i y k) j x := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => w i y k) (fun i _ => hw i),
      _root_.sum_apply]
  change partialDeriv (fun y => ∑ i, w i y k) j x +
    (∑ l, A j x k l * ∑ i, w i x l) = _
  rw [hd]
  simp only [fourHeatCovariantDerivative, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun l i => A j x k l * w i x l)]

def fourHeatCovariantFlux (A : Fin 4 → FourSpace → HeatMat6)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (i : Fin 4) (x : FourSpace) (k : Fin 6) : ℝ :=
  ∑ j, (ρ x * a x i j) * fourHeatCovariantDerivative A u j x k

theorem fourHeatCovariantFlux_derivative
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i j : Fin 4) (k : Fin 6)
    (hA : ∀ l q, DifferentiableAt ℝ (fun y => A l y k q) x)
    (ha : ∀ l, DifferentiableAt ℝ (fun y => a y i l) x)
    (hρ : DifferentiableAt ℝ ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    fourHeatCovariantDerivative A (fourHeatCovariantFlux A a ρ u i) j x k =
      ∑ l, (partialDeriv (fun y => ρ y * a y i l) j x *
        fourHeatCovariantDerivative A u l x k +
        (ρ x * a x i l) * fourHeatCovariantDerivative A
          (fourHeatCovariantDerivative A u l) j x k) := by
  unfold fourHeatCovariantFlux
  rw [fourHeatCovariantDerivative_sum_four A _ x j k (fun l =>
    (hρ.mul (ha l)).mul (fourHeatCovariantDerivative_differentiable A u x l k (hA l) hu))]
  apply Finset.sum_congr rfl
  intro l _
  exact fourHeatCovariantDerivative_scalar A (fourHeatCovariantDerivative A u l)
    (fun y => ρ y * a y i l) x j k (hρ.mul (ha l))
    (fourHeatCovariantDerivative_differentiable A u x l k (hA l) hu)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality of the covariant coefficient operator, including where the
amplitude vanishes outside the normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatCovariantDerivative_germ (A : Fin 4 → FourSpace → HeatMat6)
    {u v : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (i : Fin 4) (k : Fin 6) :
    fourHeatCovariantDerivative A u i x k = fourHeatCovariantDerivative A v i x k := by
  simp only [fourHeatCovariantDerivative, fourHeat_partial_germ (h k),
    fun l => (h l).self_of_nhds]

theorem fourHeatCovariantOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6)
    {u v : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (k : Fin 6) :
    fourHeatCovariantOperator a b A V u x k = fourHeatCovariantOperator a b A V v x k := by
  have hD (i : Fin 4) (l : Fin 6) :
      (fun y => fourHeatCovariantDerivative A u i y l) =ᶠ[𝓝 x]
        fun y => fourHeatCovariantDerivative A v i y l := by
    have hn := eventually_all.mpr fun q => (h q).eventuallyEq_nhds
    filter_upwards [hn] with y hy
    exact fourHeatCovariantDerivative_germ A hy i l
  simp only [fourHeatCovariantOperator, fourHeatCovariantDerivative_germ A (hD _),
    fourHeatCovariantDerivative_germ A h, fun l => (h l).self_of_nhds]

theorem fourHeatCovariantOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6)
    {u : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 6) :
    fourHeatCovariantOperator a b A V u x k = 0 := by
  rw [fourHeatCovariantOperator_germ a b A V h k]
  have hD (i : Fin 4) : fourHeatCovariantDerivative A (fun _ _ => 0) i = fun _ _ => 0 := by
    funext y l
    simp only [fourHeatCovariantDerivative, partialDeriv, fderiv_const_apply,
      _root_.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [fourHeatCovariantOperator, hD, mul_zero, Finset.sum_const_zero,
    neg_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual finite-regularity, skew connection.
The second section and connection need regularity only near the compact
support of the first section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeat_mul_contDiff_of_tsupport (n : ℕ) (u f : FourSpace → ℝ)
    (hu : ContDiff ℝ n u) (hf : ∀ x ∈ tsupport u, ContDiffAt ℝ n f x) :
    ContDiff ℝ n (fun x => u x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport u
  · exact hu.contDiffAt.mul (hf x hx)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

theorem fourHeatCovariantDerivative_pairing_integrable
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x) :
    Integrable (fun x => ∑ k, u x k * fourHeatCovariantDerivative A v i x k) := by
  apply integrable_finsetSum
  intro k _
  have hcv (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => fourHeatCovariantDerivative A v i y k) x := by
    have hxU := hs k hx
    apply ContinuousAt.add
    · exact (((hv x hxU k).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt
    · exact tendsto_finsetSum _ fun l _ =>
        (hA x hxU k l).mul (hv x hxU l).continuousAt
  have hp := fourHeat_local_product_integrable _ _ (hu k) (hc k) hcv
  simpa only [mul_comm] using hp

theorem fourHeatCovariantDerivative_pairing_global
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) (x : FourSpace) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatCovariantDerivative A v i x k := by
  by_cases hx : x ∈ U
  · exact fourHeatCovariantDerivative_pairing A u v x i (hskew x hx)
      (fun k => (hu k).differentiable one_ne_zero x)
      (fun k => (hv x hx k).differentiableAt one_ne_zero)
  · have hz : ∀ᶠ y in 𝓝 x, ∀ k : Fin 6, u y k = 0 := by
      apply eventually_all.mpr
      intro k
      have hk : x ∉ tsupport (fun y => u y k) := fun hk => hx (hs k hk)
      filter_upwards [(isClosed_tsupport (fun y => u y k)).isOpen_compl.mem_nhds hk]
        with y hy
      exact image_eq_zero_of_notMem_tsupport (f := fun y => u y k) hy
    have hzF : (fun y => ∑ k : Fin 6, u y k * v y k) =ᶠ[𝓝 x] (fun _ => 0) :=
      hz.mono fun y hy => by simp [hy]
    have hFD : partialDeriv (fun y => ∑ k : Fin 6, u y k * v y k) i x = 0 := by
      unfold partialDeriv
      rw [hzF.fderiv_eq, fderiv_const_apply]
      rfl
    have hDu (k : Fin 6) : partialDeriv (fun y => u y k) i x = 0 := by
      have hek : (fun y => u y k) =ᶠ[𝓝 x] (fun _ => 0) := hz.mono fun y hy => hy k
      unfold partialDeriv
      rw [hek.fderiv_eq, fderiv_const_apply]
      rfl
    simp only [hFD, fourHeatCovariantDerivative, hz.self_of_nhds,
      hDu, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

theorem fourHeat_partial_integral_zero (F : FourSpace → ℝ)
    (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F) (i : Fin 4) :
    (∫ x, partialDeriv F i x) = 0 := by
  have hz := fourHeat_local_integration_by_parts (fun _ => 1) F hF hcF
    (fun _ _ => contDiffAt_const) i
  simpa only [one_mul, partialDeriv, fderiv_const_apply, _root_.zero_apply,
    zero_mul, integral_zero, neg_zero] using hz

theorem fourHeat_green_of_pairing (F L R : FourSpace → ℝ) (i : Fin 4)
    (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F) (hR : Integrable R)
    (hpoint : ∀ x, partialDeriv F i x = L x + R x) :
    (∫ x, L x) = -(∫ x, R x) := by
  have hDc : Continuous (partialDeriv F i) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hD : Integrable (partialDeriv F i) :=
    hDc.integrable_of_hasCompactSupport
      (hcF.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_fderiv_apply_subset ℝ (coordinateVector i)))
  have heq : L = fun x => partialDeriv F i x - R x := by
    funext x
    linarith only [hpoint x]
  rw [heq, integral_sub hD hR, fourHeat_partial_integral_zero F hF hcF i, zero_sub]

theorem fourHeat_pairing_contDiff (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x) :
    ContDiff ℝ 1 (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 6) : ContDiff ℝ 1 (fun x => u x k * v x k) :=
    fourHeat_mul_contDiff_of_tsupport 1 (fun x => u x k) (fun x => v x k)
      (hu k) (fun x hx => hv x (hs k hx) k)
  exact ContDiff.sum fun k _ => hp k

theorem fourHeat_pairing_compact (u v : FourSpace → Fin 6 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) :
    HasCompactSupport (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 6) : HasCompactSupport (fun x => u x k * v x k) :=
    (hc k).mul_right
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun k x => u x k * v x k) (fun k _ => hp k)
  simpa only [Finset.sum_fn] using h

theorem fourHeatCovariantDerivative_green
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ k, fourHeatCovariantDerivative A u i x k * v x k) =
      -(∫ x, ∑ k, u x k * fourHeatCovariantDerivative A v i x k) := by
  exact fourHeat_green_of_pairing (fun x => ∑ k, u x k * v x k)
    (fun x => ∑ k, fourHeatCovariantDerivative A u i x k * v x k)
    (fun x => ∑ k, u x k * fourHeatCovariantDerivative A v i x k) i
    (fourHeat_pairing_contDiff u v U hu hs hv) (fourHeat_pairing_compact u v hc)
    (fourHeatCovariantDerivative_pairing_integrable A u v U i
      (fun k => (hu k).continuous) hc hs hv hA)
    (fourHeatCovariantDerivative_pairing_global A u v U i hu hs hv hskew)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetry of the two finite contractions in the connection energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem fourHeat_metric_pairing_symm (a : Mat4)
    (ha : ∀ i j, a i j = a j i) (p q : Fin 4 → ℝ) :
    (∑ i, ∑ j, a i j * p i * q j) = ∑ i, ∑ j, a i j * q i * p j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i]
  ring

theorem fourHeat_potential_pairing_symm (V : HeatMat6)
    (hV : ∀ k l, V k l = V l k) (u v : Fin 6 → ℝ) :
    (∑ k, u k * ∑ l, V k l * v l) = ∑ k, v k * ∑ l, V k l * u l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hV l k]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality of the actual four-component covector heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped _root_.Topology
noncomputable section

theorem fourHeatOneOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4)
    {u v : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ q, (fun y => u y q) =ᶠ[𝓝 x] fun y => v y q) (k : Fin 4) :
    fourHeatOneOperator a b B C u x k = fourHeatOneOperator a b B C v x k := by
  simp only [fourHeatOneOperator, fourHeatLocalOperator_germ a b 0 (h k),
    fourHeatOneFirst, fourHeatOneZero, fourHeat_partial_germ (h _),
    fun q => (h q).self_of_nhds]

theorem fourHeatOneOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) {u : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ q, (fun y => u y q) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 4) :
    fourHeatOneOperator a b B C u x k = 0 := by
  rw [fourHeatOneOperator_germ a b B C h k]
  have hp (i : Fin 4) : partialDeriv (fun _ : FourSpace => (0 : ℝ)) i = fun _ => 0 := by
    funext y
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatOneOperator, fourHeatOneFirst, fourHeatOneZero,
    fourHeatLocalOperator, hp]
  simp only [mul_zero, Finset.sum_const_zero, neg_zero, add_zero]

theorem fourHeatOneCovariantDerivative_germ (A : Fin 4 → FourSpace → Mat4)
    {u v : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (i : Fin 4) (k : Fin 4) :
    fourHeatOneCovariantDerivative A u i x k = fourHeatOneCovariantDerivative A v i x k := by
  simp only [fourHeatOneCovariantDerivative, fourHeat_partial_germ (h k),
    fun l => (h l).self_of_nhds]

theorem fourHeatOneCovariantOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4)
    {u v : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (k : Fin 4) :
    fourHeatOneCovariantOperator a b A V u x k = fourHeatOneCovariantOperator a b A V v x k := by
  have hD (i : Fin 4) (l : Fin 4) :
      (fun y => fourHeatOneCovariantDerivative A u i y l) =ᶠ[𝓝 x]
        fun y => fourHeatOneCovariantDerivative A v i y l := by
    have hn := eventually_all.mpr fun q => (h q).eventuallyEq_nhds
    filter_upwards [hn] with y hy
    exact fourHeatOneCovariantDerivative_germ A hy i l
  simp only [fourHeatOneCovariantOperator, fourHeatOneCovariantDerivative_germ A (hD _),
    fourHeatOneCovariantDerivative_germ A h, fun l => (h l).self_of_nhds]

theorem fourHeatOneCovariantOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4)
    {u : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 4) :
    fourHeatOneCovariantOperator a b A V u x k = 0 := by
  rw [fourHeatOneCovariantOperator_germ a b A V h k]
  have hD (i : Fin 4) : fourHeatOneCovariantDerivative A (fun _ _ => 0) i = fun _ _ => 0 := by
    funext y l
    simp only [fourHeatOneCovariantDerivative, partialDeriv, fderiv_const_apply,
      _root_.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [fourHeatOneCovariantOperator, hD, mul_zero, Finset.sum_const_zero,
    neg_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dilation and domination of a bounded amplitude with vanishing first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Asymptotics Set
open scoped _root_.Topology

noncomputable section

theorem fourHeat_norm_sqrt_smul_sq (t : ℝ) (ht : 0 ≤ t) (x : FourSpace) :
    ‖Real.sqrt t • x‖ ^ 2 = t * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht]

theorem fourHeat_vanishing_scaled_limit (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (z : FourSpace) :
    Tendsto (fun t : ℝ => f (Real.sqrt t • z) / t) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 z z)) := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hr : (fun x => f x - (1 / 2 : ℝ) * B x x)
      =o[𝓝 0] (fun x : FourSpace => ‖x‖ ^ 2) := by
    simpa [hf0, hD0, B] using fourHeat_second_order_remainder_at f hf
  have hs : Tendsto (fun t : ℝ => Real.sqrt t • z) (𝓝[>] 0)
      (𝓝 (0 : FourSpace)) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => z) (𝓝 (0 : ℝ)) (𝓝 z))).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  by_cases hz : z = 0
  · subst z
    simp [hf0]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hh := ((hr.comp_tendsto hs).tendsto_div_nhds_zero).mul_const (‖z‖ ^ 2)
  simp only [zero_mul] at hh
  have hh' : Tendsto (fun t : ℝ => f (Real.sqrt t • z) / t - (1 / 2 : ℝ) * B z z)
      (𝓝[>] 0) (𝓝 0) := by
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    dsimp only [Function.comp_apply]
    rw [fourHeat_norm_sqrt_smul_sq t ht.le]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    have hsq := Real.sq_sqrt ht.le
    field_simp [ht.ne', hnz]
    rw [hsq]
    ring
  have h := hh'.add_const ((1 / 2 : ℝ) * B z z)
  simpa only [sub_add_cancel, zero_add] using h

theorem fourHeat_vanishing_quadratic_bound (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖f x‖ ≤ K * ‖x‖ ^ 2 := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hr : (fun x => f x - (1 / 2 : ℝ) * B x x)
      =o[𝓝 0] (fun x : FourSpace => ‖x‖ ^ 2) := by
    simpa [hf0, hD0, B] using fourHeat_second_order_remainder_at f hf
  obtain ⟨δ, hδ, he⟩ := Metric.eventually_nhds_iff.mp (hr.bound zero_lt_one)
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  refine ⟨1 + ‖B‖ + C / δ ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : ‖x‖ < δ
  · have he' := he (by simpa [dist_zero_right] using hx)
    simp only [one_mul, norm_pow, norm_norm] at he'
    have hb := B.le_opNorm₂ x x
    have hhalf : ‖(1 / 2 : ℝ) * B x x‖ ≤ ‖B‖ * ‖x‖ ^ 2 := by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc
        (1 / 2 : ℝ) * ‖B x x‖ ≤ ‖B x x‖ := by nlinarith [norm_nonneg (B x x)]
        _ ≤ ‖B‖ * ‖x‖ ^ 2 := by nlinarith [hb]
    calc
      ‖f x‖ ≤ ‖f x - (1 / 2 : ℝ) * B x x‖ + ‖(1 / 2 : ℝ) * B x x‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ ‖x‖ ^ 2 + ‖B‖ * ‖x‖ ^ 2 := add_le_add he' hhalf
      _ ≤ (1 + ‖B‖ + C / δ ^ 2) * ‖x‖ ^ 2 := by
        have hdiv : 0 ≤ C / δ ^ 2 := by positivity
        nlinarith [mul_nonneg hdiv (sq_nonneg ‖x‖)]
  · have hxδ : δ ≤ ‖x‖ := le_of_not_gt hx
    have hratio : C ≤ (C / δ ^ 2) * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
      exact mul_le_mul_of_nonneg_left (show δ ^ 2 ≤ ‖x‖ ^ 2 by nlinarith) hC0
    calc
      ‖f x‖ ≤ C := hC x
      _ ≤ (C / δ ^ 2) * ‖x‖ ^ 2 := hratio
      _ ≤ (1 + ‖B‖ + C / δ ^ 2) * ‖x‖ ^ 2 := by
        nlinarith [mul_nonneg (norm_nonneg B) (sq_nonneg ‖x‖)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact coordinate changes for continuous alternating two-tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatCompactTensorLift (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) (z : FourSpace) : CovariantCoordinates 2 := by
  classical
  exact if z ∈ C.target then T (C.symm z) else 0

theorem heatCompactTensorLift_support (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) :
    support (heatCompactTensorLift C T) ⊆ C '' tsupport T := by
  classical
  intro z hz
  by_cases h : z ∈ C.target
  · refine ⟨C.symm z, subset_closure ?_, C.right_inv h⟩
    simpa only [heatCompactTensorLift, ite_eq_left h, mem_support] using hz
  · exact False.elim (hz (by simp only [heatCompactTensorLift, ite_eq_right h]))

theorem heatCompactTensorLift_tsupport (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) (hc : HasCompactSupport T)
    (hs : tsupport T ⊆ C.source) :
    tsupport (heatCompactTensorLift C T) ⊆ C '' tsupport T :=
  closure_minimal (heatCompactTensorLift_support C T)
    (hc.image_of_continuousOn (C.continuousOn.mono hs)).isClosed

theorem heatCompactTensorLift_continuous (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatCompactTensorLift C T) := by
  classical
  have hK := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ C.target
  · have h := (hT.continuousAt (C.open_source.mem_nhds (C.map_target hz))).comp
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hz))
    apply h.congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hz] with w hw
    exact ite_eq_left hw
  · have hzK : z ∉ C '' tsupport T := by
      rintro ⟨x, hx, rfl⟩
      exact hz (C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 2))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    exact not_ne_iff.mp (fun hn => hw (heatCompactTensorLift_support C T hn))

theorem heatCompactTensorLift_skew (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2)
    (hT : ∀ z i j, T z ![j,i] = -T z ![i,j]) :
    ∀ z i j, heatCompactTensorLift C T z ![j,i] = -heatCompactTensorLift C T z ![i,j] := by
  classical
  intro z i j
  by_cases hz : z ∈ C.target
  · simp only [heatCompactTensorLift, ite_eq_left hz]
    exact hT _ _ _
  · simp only [heatCompactTensorLift, ite_eq_right hz, Pi.zero_apply, neg_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The jointly constructed amplitudes restrict to the radial
transport amplitudes for every fixed initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyWeightedAverage_slice (m : ℕ) (U f : HeatRadialFrameSpace → ℝ)
    (q : CoordinateFrameSpace) (x : FourSpace) :
    heatFamilyWeightedAverage m U f (x, q) =
      fourHeatWeightedRadialAverage m (fun y => U (y, q)) (fun y => f (y, q)) x := rfl

theorem HeatFamilySmoothCoefficients.amplitude_slice (E : HeatFamilySmoothCoefficients)
    (m : ℕ) : m ≤ 3 → ∀ q : CoordinateFrameSpace,
      (fun x => E.amplitude m (x, q)) =
        fourHeatBundleCoefficient (fun x => E.a (x, q)) (fun x => E.b (x, q))
          (fun x => E.B (x, q)) (fun x => E.C (x, q)) (fun x => E.U (x, q)) m := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm q
    have hrec := ih (by omega) q
    funext x k l
    have hu (a : Fin 6) : ContDiff ℝ 2 (fun z => E.amplitude m z a l) :=
      (E.amplitude_regular m (by omega) a l).of_le (by norm_num)
    have ho : (fun y => -heatFamilyBundleOperator E.a E.b E.B E.C
        (fun z a => E.amplitude m z a l) (y, q) k) =
        (fun y => -fourHeatBundleOperator (E.a (y, q)) (E.b (y, q)) (E.B (y, q)) (E.C (y, q))
          (fun z a => fourHeatBundleCoefficient (fun x => E.a (x, q))
            (fun x => E.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.U (x, q)) m z a l) y k) := by
      funext y
      rw [heatFamilyBundleOperator_slice E.a E.b E.B E.C
        (fun z a => E.amplitude m z a l) hu (y, q) k]
      have he : (fun z a => E.amplitude m (z, q) a l) =
          (fun z a => fourHeatBundleCoefficient (fun x => E.a (x, q))
            (fun x => E.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.U (x, q)) m z a l) := by
        funext z a
        exact congrArg (fun A : FourSpace → HeatMat6 => A z a l) hrec
      rw [he]
    change heatFamilyWeightedAverage m E.U (fun y => -heatFamilyBundleOperator E.a E.b E.B E.C
      (fun z a => E.amplitude m z a l) y k) (x, q) = _
    rw [heatFamilyWeightedAverage_slice, ho]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform compact bounds for the actual transport family and the
coefficient left by the third transport equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyScalar_compact_jet_bound (f : HeatRadialFrameSpace → ℝ)
    (hf : ContDiff ℝ 4 f) (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ n : ℕ, n ≤ 4 → ∀ z ∈ K, ‖iteratedFDeriv ℝ n f z‖ ≤ C := by
  have hb (n : Fin 5) : ∃ C ≥ (0 : ℝ), ∀ z ∈ K, ‖iteratedFDeriv ℝ n.val f z‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ n.val f) :=
      hf.continuous_iteratedFDeriv (by exact_mod_cast (show n.val ≤ 4 by omega))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩
  choose C hC hb using hb
  refine ⟨∑ n : Fin 5, C n, Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro n hn z hz
  let i : Fin 5 := ⟨n, by omega⟩
  exact (hb i z hz).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

theorem HeatFamilySmoothCoefficients.amplitude_compact_bound (E : HeatFamilySmoothCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ∀ k l : Fin 6, ‖iteratedFDeriv ℝ n (fun y => E.amplitude m y k l) z‖ ≤ C := by
  have hb (i : Fin 4 × Fin 6 × Fin 6) : ∃ C ≥ (0 : ℝ), ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ n (fun y => E.amplitude i.1.val y i.2.1 i.2.2) z‖ ≤ C :=
    heatFamilyScalar_compact_jet_bound _ (E.amplitude_regular i.1.val (by omega) i.2.1 i.2.2) K hK
  choose C hC hb using hb
  refine ⟨∑ i : Fin 4 × Fin 6 × Fin 6, C i,
    Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro m hm n hn z hz k l
  let i : Fin 4 × Fin 6 × Fin 6 := (⟨m, by omega⟩, k, l)
  exact (hb i n hn z hz).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

def HeatFamilySmoothCoefficients.lastCoefficient (E : HeatFamilySmoothCoefficients)
    (z : HeatRadialFrameSpace) (k l : Fin 6) : ℝ :=
  heatFamilyBundleOperator E.a E.b E.B E.C (fun y q => E.amplitude 3 y q l) z k

theorem HeatFamilySmoothCoefficients.lastCoefficient_regular (E : HeatFamilySmoothCoefficients)
    (k l : Fin 6) : ContDiff ℝ 2 (fun z => E.lastCoefficient z k l) :=
  heatFamilyBundleOperator_contDiff 2 E.a E.b E.B E.C _
    (fun i j => (E.a_regular i j).of_le (by norm_num))
    (fun i => (E.b_regular i).of_le (by norm_num))
    (fun i k l => (E.B_regular i k l).of_le (by norm_num))
    (fun k l => (E.C_regular k l).of_le (by norm_num))
    (fun q => E.amplitude_regular 3 (by omega) q l) k

theorem HeatFamilySmoothCoefficients.lastCoefficient_compact_bound (E : HeatFamilySmoothCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ K, ∀ k l : Fin 6, |E.lastCoefficient z k l| ≤ C := by
  have hb (i : Fin 6 × Fin 6) : ∃ C ≥ (0 : ℝ), ∀ z ∈ K, |E.lastCoefficient z i.1 i.2| ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (E.lastCoefficient_regular i.1 i.2).continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro z hz
    have h : |E.lastCoefficient z i.1 i.2| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC z hz
    exact h.trans (le_max_left _ _)
  choose C hC hb using hb
  refine ⟨∑ i : Fin 6 × Fin 6, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro z hz k l
  exact (hb (k, l) z hz).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ (k, l)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Slicing the family operator gives exactly the corresponding one-form
operator, including its second spatial derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyOneOperator_slice
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → Mat4) (C : HeatRadialFrameSpace → Mat4)
    (u : HeatRadialFrameSpace → Fin 4 → ℝ)
    (hu : ∀ l, ContDiff ℝ 2 (fun z => u z l))
    (z : HeatRadialFrameSpace) (k : Fin 4) :
    heatFamilyOneOperator a b B C u z k =
      fourHeatOneOperator (a z) (b z) (B z) (C z) (fun x l => u (x, z.2) l) z.1 k := by
  have hp (i : Fin 4) (l : Fin 4) :
      ContDiff ℝ 1 (heatFamilyScalarPartial (fun z => u z l) i) :=
    heatFamilyScalarPartial_contDiff 1 _ (hu l) i
  have he (i : Fin 4) (l : Fin 4) :
      (fun x => heatFamilyScalarPartial (fun z => u z l) i (x, z.2)) =
        partialDeriv (fun x => u (x, z.2) l) i := by
    funext x
    exact heatFamilyScalarPartial_slice _ (x, z.2)
      ((hu l).differentiable (by norm_num) _) i
  have hfirst (i : Fin 4) (l : Fin 4) :
      heatFamilyScalarPartial (fun y => u y l) i z =
        partialDeriv (fun x => u (x, z.2) l) i z.1 :=
    heatFamilyScalarPartial_slice _ z ((hu l).differentiable (by norm_num) z) i
  have hsecond (i j : Fin 4) :
      heatFamilyScalarPartial (heatFamilyScalarPartial (fun y => u y k) i) j z =
        partialDeriv (partialDeriv (fun x => u (x, z.2) k) i) j z.1 := by
    rw [heatFamilyScalarPartial_slice _ z ((hp i k).differentiable one_ne_zero z) j]
    rw [he i k]
  unfold heatFamilyOneOperator fourHeatOneOperator fourHeatLocalOperator
    fourHeatOneFirst fourHeatOneZero
  simp only [hfirst, hsecond, zero_mul, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coefficient operator of the bundle parametrix is the connection
Laplacian expression with the actual normal-frame curvature potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalConnectionOperator_eq {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => heatTwoFormConnection g c D.point i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 6) :
    fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k =
    fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalBundleFirst D x) (heatNormalBundleZero D x) u x k := by
  apply fourHeatCovariantOperator_eq _ _ _ _ u x _ hA hu k
  intro i j
  exact congrFun (congrFun (heatNormalInverse_symm g o e x) i) j |>.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and exact cutoff residual of the actual normal
bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalBundleParametrix_time_differentiable {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (k l : Fin 6) : DifferentiableAt ℝ (fun s => heatNormalBundleParametrix E s x k l) t := by
  exact ((fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t x)).differentiableAt

theorem heatNormalBundleParametrix_space_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (t : ℝ) (k l : Fin 6) :
    ContDiff ℝ 2 (fun x => heatNormalBundleParametrix E t x k l) := by
  exact ((fourHeatGaussian_smooth t).of_le (by norm_num)).mul
    (fourHeatPolynomial_contDiff (fun m y => E.amplitude m y k l)
      (fun m => (E.amplitude_regular m (by omega) k l).of_le (by norm_num)) t)

def heatNormalCutoffParametrix {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (t : ℝ)
    (x : FourSpace) : HeatMat6 := fun k l => χ x * heatNormalBundleParametrix E t x k l

theorem heatNormalCutoffParametrix_residual_identity {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (hχ : ContDiffAt ℝ 2 χ x) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (ha : ∀ i j, a i j = a j i) (k l : Fin 6) :
    deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
      fourHeatBundleOperator a b B C
        (fun y q => heatNormalCutoffParametrix E χ t y q l) x k =
    χ x * (deriv (fun s => heatNormalBundleParametrix E s x k l) t +
      fourHeatBundleOperator a b B C
        (fun y q => heatNormalBundleParametrix E t y q l) x k) +
      fourHeatLocalOperator a b 0 χ x * heatNormalBundleParametrix E t x k l -
      2 * (∑ i, ∑ j, a i j * partialDeriv χ i x *
        partialDeriv (fun y => heatNormalBundleParametrix E t y k l) j x) +
      ∑ i, ∑ q, B i k q * partialDeriv χ i x * heatNormalBundleParametrix E t x q l := by
  have hd := (heatNormalBundleParametrix_time_differentiable E t ht x k l).hasDerivAt.const_mul
    (χ x)
  change HasDerivAt (fun s => heatNormalCutoffParametrix E χ s x k l) _ t at hd
  rw [hd.deriv]
  unfold heatNormalCutoffParametrix
  rw [fourHeatBundleOperator_cutoff a b B C χ _ x ha hχ
    (fun q => (heatNormalBundleParametrix_space_regular E t q l).contDiffAt) k]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing lower-order signed traces for the actual normal-frame
connection and first heat amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heat_hodgeMatrix_symmetric : twoFormHodgeMatrixᵀ = twoFormHodgeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoFormHodgeMatrix]

theorem heat_signed_skew_trace (A : HeatMat6) (hA : Aᵀ = -A) :
    (twoFormHodgeMatrix * A).trace = 0 := by
  have h : (twoFormHodgeMatrix * A).trace = -(twoFormHodgeMatrix * A).trace := by
    calc
      _ = (twoFormHodgeMatrix * A)ᵀ.trace := (Matrix.trace_transpose _).symm
      _ = _ := by
        rw [Matrix.transpose_mul, hA, heat_hodgeMatrix_symmetric, Matrix.neg_mul,
          Matrix.trace_neg, Matrix.trace_mul_comm]
  linarith

theorem heatTwoFormConnectionMatrix_signed_trace (B : Mat4) :
    (twoFormHodgeMatrix * heatTwoFormConnectionMatrix B).trace = 0 :=
  heat_signed_skew_trace _ (heatTwoFormConnectionMatrix_skew B)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heat_actual_potential_signed_trace (e : FrameBundle g) :
    (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace = 0 := by
  let R := twoFormMetricCurvatureTensor g e
  have hf (i j k l : Fin 4) : R ![j,i,k,l] = -R ![i,j,k,l] :=
    twoFormMetricCurvatureTensor_skew g e i j k l
  have hp (i j k l : Fin 4) : R ![k,l,i,j] = R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l
  have hb (i j k l : Fin 4) : R ![i,j,k,l] + R ![j,k,i,l] + R ![k,i,j,l] = 0 := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_firstBianchi e.frame i j k l
  change (twoFormHodgeMatrix * twoFormPotentialMatrix R).trace = 0
  rw [twoFormPotentialMatrix, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    twoFormHodgeMatrix_trace, twoFormCurvatureMatrix_signed_trace R hf hp hb]
  ring

variable [T3Space M] [CompactSpace M]
  {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.first_amplitude_signed_trace
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    (twoFormHodgeMatrix * E.amplitude 1 0).trace = 0 := by
  rw [E.first_amplitude_intrinsic_center he, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, twoFormHodgeMatrix_trace,
    heat_actual_potential_signed_trace]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A quantitative second-order bound from a bounded Hessian on a ball.
This will be applied uniformly to the signed first heat coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff _root_.Topology

noncomputable section

theorem fourHeat_quadratic_bound_of_hessian (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 2 f) (f0 : f 0 = 0) (D0 : fderiv ℝ f 0 = 0)
    (R C : ℝ) (hC : 0 ≤ C)
    (hess : ∀ y ∈ closedBall (0 : FourSpace) R, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C)
    (x : FourSpace) (hx : x ∈ closedBall 0 R) : ‖f x‖ ≤ C * ‖x‖ ^ 2 := by
  let S := closedBall (0 : FourSpace) ‖x‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hsR : S ⊆ closedBall (0 : FourSpace) R := by
    apply closedBall_subset_closedBall
    simpa only [mem_closedBall_zero_iff] using hx
  have h0S : (0 : FourSpace) ∈ S := mem_closedBall_self (norm_nonneg x)
  have hxS : x ∈ S := by simp [S]
  have hd : ∀ y ∈ S, ‖fderiv ℝ f y‖ ≤ C * ‖x‖ := by
    intro y hy
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z)
      (fun z hz => hess z (hsR hz)) hS h0S hy
    rw [D0, sub_zero, sub_zero] at hh
    have hy' : ‖y‖ ≤ ‖x‖ := by simpa only [S, mem_closedBall_zero_iff] using hy
    exact hh.trans (mul_le_mul_of_nonneg_left hy' hC)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hf.differentiable two_ne_zero y) hd hS h0S hxS
  simpa only [f0, sub_zero, pow_two, mul_assoc] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Second derivatives of the signed quadratic connection term at a
radial center, where the connection itself vanishes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_partial_finite_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (x : FourSpace)
    (hF : ∀ k, DifferentiableAt ℝ (F k) x) (i : Fin 4) :
    partialDeriv (fun y => ∑ k, F k y) i x = ∑ k, partialDeriv (F k) i x := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun k _ => hF k), _root_.sum_apply]

theorem heat_partial_second_finite_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (x : FourSpace)
    (hF : ∀ k, ContDiffAt ℝ 2 (F k) x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => ∑ k, F k y) i) j x =
      ∑ k, partialDeriv (partialDeriv (F k) i) j x := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ k, DifferentiableAt ℝ (F k) y := by
    apply eventually_all.mpr
    intro k
    filter_upwards [(hF k).eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have he : partialDeriv (fun y => ∑ k, F k y) i =ᶠ[𝓝 x]
      (fun y => ∑ k, partialDeriv (F k) i y) := by
    filter_upwards [hn] with y hy
    exact heat_partial_finite_sum F y hy i
  rw [fourHeat_partial_germ he j]
  apply heat_partial_finite_sum
  intro k
  exact (((hF k).fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero

def heatSixPartial (A : FourSpace → HeatMat6) (i : Fin 4) (x : FourSpace) : HeatMat6 :=
  fun k l => partialDeriv (fun y => A y k l) i x

theorem heat_trace_product_second_zero (H : HeatMat6) (A B : FourSpace → HeatMat6)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun x => (H * A x * B x).trace) i) j 0 =
      (H * (heatSixPartial A i 0 * heatSixPartial B j 0 +
        heatSixPartial A j 0 * heatSixPartial B i 0)).trace := by
  have heq : (fun x => (H * A x * B x).trace) =
      (fun x => ∑ k, ∑ l, ∑ q, H k l * (A x l q * B x q k)) := by
    funext x
    calc
      (H * A x * B x).trace = (H * (A x * B x)).trace :=
        congrArg Matrix.trace (Matrix.mul_assoc H (A x) (B x))
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  have hreg (k l q : Fin 6) : ContDiffAt ℝ 2
      (fun x => H k l * (A x l q * B x q k)) 0 :=
    contDiffAt_const.mul ((hA l q).mul (hB q k))
  rw [heq, heat_partial_second_finite_sum _ 0
    (fun k => ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun q _ => hreg k l q))) i j]
  simp_rw [heat_partial_second_finite_sum _ 0
    (fun l => ContDiffAt.sum (fun q _ => hreg _ l q)) i j]
  simp_rw [heat_partial_second_finite_sum _ 0 (fun q => hreg _ _ q) i j]
  simp_rw [fourHeat_second_const_mul]
  have hp (k l q : Fin 6) :
      partialDeriv (partialDeriv (fun x => A x l q * B x q k) i) j 0 =
        partialDeriv (fun x => A x l q) i 0 * partialDeriv (fun x => B x q k) j 0 +
        partialDeriv (fun x => A x l q) j 0 * partialDeriv (fun x => B x q k) i 0 := by
    rw [scalar_partial_second_product_at _ _ 0 (hA l q) (hB q k) i j]
    simp only [hA0, hB0, Matrix.zero_apply, mul_zero, zero_mul, zero_add, add_zero]
  simp_rw [hp]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, heatSixPartial,
    Matrix.add_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem HeatNormalFrameData.connection_square_second
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩)
    (a i : Fin 4) :
    partialDeriv (partialDeriv (fun x =>
      (twoFormHodgeMatrix * heatTwoFormConnection g c D.point a x *
        heatTwoFormConnection g c D.point a x).trace) i) i 0 =
      (1 / 2 : ℝ) * (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i a *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i a).trace := by
  rw [heat_trace_product_second_zero twoFormHodgeMatrix _ _
    (fun k l => (D.twoForm_connection_regular a k l).of_le (by norm_num))
    (fun k l => (D.twoForm_connection_regular a k l).of_le (by norm_num))
    (D.twoForm_connection_zero a) (D.twoForm_connection_zero a) i i]
  have hm : heatSixPartial (heatTwoFormConnection g c D.point a) i 0 =
      (1 / 2 : ℝ) • twoFormConnectionCurvatureMatrix
        (twoFormMetricCurvatureTensor g ⟨c, f⟩) i a := by
    ext k l
    exact D.twoForm_connection_half_curvature i a k l
  rw [hm]
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-component connection is exactly the tensor connection on
alternating two-tensors, including its scalar derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_twoForm_covariant_tensor (C : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → TwoFormFour) (x : FourSpace)
    (ha : DifferentiableAt ℝ a x) (i : Fin 4) (hC : (C i x)ᵀ = -C i x) :
    tensorCovariantDirection C (fun y => twoFormTensor (a y)) i x =
      twoFormTensor (WithLp.toLp 2 (fun k => fourHeatCovariantDerivative
        (fun j y => heatTwoFormConnectionMatrix (C j y)) (fun y k => a y k) i x k)) := by
  have he : WithLp.toLp 2 (fun k => fourHeatCovariantDerivative
      (fun j y => heatTwoFormConnectionMatrix (C j y)) (fun y k => a y k) i x k) =
      fderiv ℝ a x (coordinateVector i) + twoFormSkewAction (twoFormExtract (C i x)) (a x) := by
    ext k
    change partialDeriv (fun y => a y k) i x +
      (heatTwoFormConnectionMatrix (C i x) *ᵥ WithLp.ofLp (a x)) k = _
    rw [heat_twoForm_partial_component a x ha i k, heatTwoFormConnectionMatrix_action]
    rfl
  rw [he]
  change tensorPartial (fun y => twoFormTensor (a y)) i x -
    tensorSlotAction (C i x) (twoFormTensor (a x)) = _
  rw [tensorPartial_twoForm ha, ← twoFormMatrix_extract _ hC,
    tensorSlotAction_twoForm, sub_neg_eq_add]
  exact (twoFormTensorLinear.map_add _ _).symm

theorem heat_fourCovariant_congr (A : Fin 4 → FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (h : u =ᶠ[𝓝 x] v) (i : Fin 4) (k : Fin 6) :
    fourHeatCovariantDerivative A u i x k = fourHeatCovariantDerivative A v i x k := by
  have he : (fun y => u y k) =ᶠ[𝓝 x] (fun y => v y k) :=
    h.mono fun y hy => congrFun hy k
  have hd : partialDeriv (fun y => u y k) i x = partialDeriv (fun y => v y k) i x :=
    congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq
  simp only [fourHeatCovariantDerivative, hd, h.self_of_nhds]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative of an actual smooth one-form is closed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem tensorSlotAction_one (A : Mat4) (T : CovariantCoordinates 1) (k : Fin 4) :
    tensorSlotAction A T ![k] = ∑ p, A p k * T ![p] := by
  have hup (p : Fin 4) : Function.update ![k] (0 : Fin 1) p = ![p] := by
    ext i
    fin_cases i
    simp
  simp only [tensorSlotAction, Fin.sum_univ_one, covariantSlotAction,
    Matrix.cons_val_zero, hup]

private theorem exterior_second_zero (X : CovariantCoordinates 3)
    (A : CovariantCoordinates 1) (R : Angular.CurvatureArray)
    (hX : ∀ i j k, X ![i,j,k] - X ![j,i,k] = -(∑ p, R i j k p * A ![p]))
    (hR : AlgebraicCurvature.FirstBianchi R) (i j k : Fin 4) :
    (X ![i,j,k] - X ![i,k,j]) - (X ![j,i,k] - X ![j,k,i]) +
      (X ![k,i,j] - X ![k,j,i]) = 0 := by
  have hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0 := hR
  have hc : (∑ p, R i j k p * A ![p]) + (∑ p, R j k i p * A ![p]) +
      (∑ p, R k i j p * A ![p]) = 0 := by
    calc
      _ = ∑ p, (R i j k p + R j k i p + R k i j p) * A ![p] := by
        simp only [add_mul, Finset.sum_add_distrib]
      _ = 0 := by simp only [hB, zero_mul, Finset.sum_const_zero]
  linarith only [hX i j k, hX j k i, hX k i j, hc]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormExterior_closed (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    smoothTwoFormExterior (smoothOneFormExterior (o := o) u) = 0 := by
  funext e i j k
  change twoFormExteriorComponent (fun p q r =>
    twoFormFramedCovariantDerivative o (smoothOneFormExterior (o := o) u).val e ![p,q,r]) i j k = 0
  unfold twoFormExteriorComponent
  have hD (p q r : Fin 4) := smoothOneFormExterior_covariant (o := o) hRic u e p q r
  simp only [hD]
  let X := covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e
  let A := covariantFieldFramed g u.val e
  let R := frameCurvature g e.base e.frame
  apply exterior_second_zero X A R ?_ (frame_algebraic_firstBianchi e.frame)
  intro p q r
  have h := u.property.framed_commutator (g := g) e p q ![r]
  change X ![p,q,r] - X ![q,p,r] = -tensorSlotAction (curvatureEndomorphism R p q) A ![r] at h
  rw [tensorSlotAction_one] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar diagonal is the squared norm of the half-time evaluation
column. Its integral is the actual infinite spectral trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatDiagonal (t : ℝ≥0) (ht : 0 < t) (x : M) : ℝ :=
  ‖scalarHeatColumn g o d (t / 2) (half_pos ht) x‖ ^ 2

theorem scalarHeatColumn_norm_square (t : ℝ≥0) (ht : 0 < t) (x : M) :
    ‖scalarHeatColumn g o d t ht x‖ ^ 2 =
      ∑' i : ScalarBaseEigenIndex g o d,
        (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x) ^ 2 := by
  let v := scalarHeatColumn g o d t ht x
  have h := (scalarBaseEigenbasis g o d).repr.inner_map_map v v
  rw [lp.inner_eq_tsum] at h
  rw [← real_inner_self_eq_norm_sq, ← h]
  apply tsum_congr
  intro i
  rw [HilbertBasis.repr_apply_apply, real_inner_self_eq_norm_sq]
  have hbi : scalarBaseEigenbasis g o d i = scalarBaseEigenvector g o d i := by
    simp only [scalarBaseEigenbasis, HilbertBasis.coe_mk]
  rw [hbi]
  have he : inner ℝ (scalarBaseEigenvector g o d i) v =
      scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x :=
    (real_inner_comm _ _).trans (scalarHeatColumn_pairing g o d t ht x _)
  rw [he, Real.norm_eq_abs, sq_abs]

theorem scalarHeatDiagonal_series (t : ℝ≥0) (ht : 0 < t) (x : M) :
    scalarHeatDiagonal g o d t ht x =
      ∑' i : ScalarBaseEigenIndex g o d,
        (scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) x) ^ 2 :=
  scalarHeatColumn_norm_square g o d (t / 2) (half_pos ht) x

theorem scalarHeatDiagonal_integral (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, scalarHeatDiagonal g o d t ht x ∂normalizedVolume g) =
      ∑' i : ScalarBaseEigenIndex g o d, scalarBaseHeatWeight g o d t i := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let F := fun (i : ScalarBaseEigenIndex g o d) (x : M) =>
    (scalarHeatToContinuous g o d (t / 2) (half_pos ht) (scalarBaseEigenvector g o d i) x) ^ 2
  have hi (i : ScalarBaseEigenIndex g o d) : Integrable (F i) (normalizedVolume g) :=
    ((scalarHeatToContinuous g o d (t / 2) (half_pos ht) _).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖F i x‖ ∂normalizedVolume g) := by
    have h := scalarHeat_weight_square_summable g o d (t / 2) (half_pos ht)
    apply h.congr
    intro i
    simp only [F, Real.norm_eq_abs, abs_sq]
    exact (scalarHeat_eigen_integral g o d (t / 2) (half_pos ht) i).symm
  simp_rw [scalarHeatDiagonal_series]
  change (∫ x, ∑' i, F i x ∂normalizedVolume g) = _
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro i
  rw [scalarHeat_eigen_integral]
  simp only [scalarBaseHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseEigenbasis_apply (i : ScalarBaseEigenIndex g o d) :
    scalarBaseEigenbasis g o d i = scalarBaseEigenvector g o d i := by
  simp only [scalarBaseEigenbasis, HilbertBasis.coe_mk]

def scalarBaseHeatLiftSource (t : ℝ≥0) (ht : 0 < t) :
    Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  scalarBaseHeatPowerSource g o d t ht 1

theorem scalarBaseHeatLiftSource_resolvent (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarBaseResolvent g o d (scalarBaseHeatLiftSource g o d t ht f) = scalarBaseHeat g o d t f := by
  simpa only [pow_one, scalarBaseHeatLiftSource] using scalarBaseHeatPowerSource_resolvent g o d t ht 1 f

omit [SecondCountableTopology M] in
theorem scalarBaseHeatWeight_half_sq (t : ℝ≥0) (i : ScalarBaseEigenIndex g o d) :
    scalarBaseHeatWeight g o d (t / 2) i ^ 2 = scalarBaseHeatWeight g o d t i := by
  simp only [scalarBaseHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

theorem scalarBaseHeatLiftWeight_bound (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) :
    |(i.1.val : ℝ)⁻¹ * scalarBaseHeatWeight g o d t i| ≤ Real.exp t / t := by
  simpa only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] using
    scalarBaseHeatPowerWeight_bound g o d t ht 1 i

theorem scalarBaseHeat_series (t : ℝ≥0) (f : Lp ℝ 2 (normalizedVolume g)) :
    HasSum (fun i : ScalarBaseEigenIndex g o d =>
      (scalarBaseHeatWeight g o d t i * inner ℝ (scalarBaseEigenvector g o d i) f) •
        scalarBaseEigenvector g o d i) (scalarBaseHeat g o d t f) := by
  have hs := ((scalarBaseEigenbasis g o d).hasSum_repr f).mapL (scalarBaseHeat g o d t)
  have he : (fun i : ScalarBaseEigenIndex g o d =>
      scalarBaseHeat g o d t ((scalarBaseEigenbasis g o d).repr f i • scalarBaseEigenbasis g o d i)) =
      (fun i => (scalarBaseHeatWeight g o d t i * inner ℝ (scalarBaseEigenvector g o d i) f) •
        scalarBaseEigenvector g o d i) := by
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply, scalarBaseEigenbasis_apply, scalarBaseHeat_eigenvector,
      smul_smul, mul_comm]
  rwa [he] at hs

theorem scalarBaseHeatLiftSource_eigen (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) :
    scalarBaseHeatLiftSource g o d t ht (scalarBaseEigenvector g o d i) =
      ((i.1.val : ℝ)⁻¹ * scalarBaseHeatWeight g o d t i) • scalarBaseEigenvector g o d i := by
  apply scalarBaseResolvent_injective g o d
  rw [scalarBaseHeatLiftSource_resolvent, scalarBaseHeat_eigenvector, map_smul]
  have he := Module.End.mem_eigenspace_iff.mp (scalarBaseEigenvector_hasEigenvector g o d i).1
  change scalarBaseResolvent g o d (scalarBaseEigenvector g o d i) =
    (i.1.val : ℝ) • scalarBaseEigenvector g o d i at he
  rw [he, smul_smul]
  congr 1
  have hn : (i.1.val : ℝ) ≠ 0 := (scalarBaseResolvent_eigenvalue g o d i.1.property).1.ne'
  field_simp

def scalarBaseHeatDerivative (t : ℝ≥0) (ht : 0 < t) :
    Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  scalarBaseHeat g o d t - scalarBaseHeatLiftSource g o d t ht

theorem scalarBaseHeatDerivative_eigen (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) :
    scalarBaseHeatDerivative g o d t ht (scalarBaseEigenvector g o d i) =
      (-scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d t i) • scalarBaseEigenvector g o d i := by
  change scalarBaseHeat g o d t _ - scalarBaseHeatLiftSource g o d t ht _ = _
  rw [scalarBaseHeat_eigenvector, scalarBaseHeatLiftSource_eigen, ← sub_smul]
  congr 1
  unfold scalarBaseHeatRate
  ring

theorem scalarBaseHeatDerivative_series (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (normalizedVolume g)) :
    HasSum (fun i : ScalarBaseEigenIndex g o d =>
      (-scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d t i *
        inner ℝ (scalarBaseEigenvector g o d i) f) • scalarBaseEigenvector g o d i)
      (scalarBaseHeatDerivative g o d t ht f) := by
  have hs := ((scalarBaseEigenbasis g o d).hasSum_repr f).mapL (scalarBaseHeatDerivative g o d t ht)
  have he : (fun i : ScalarBaseEigenIndex g o d => scalarBaseHeatDerivative g o d t ht
      ((scalarBaseEigenbasis g o d).repr f i • scalarBaseEigenbasis g o d i)) =
      (fun i => (-scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d t i *
        inner ℝ (scalarBaseEigenvector g o d i) f) • scalarBaseEigenvector g o d i) := by
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply, scalarBaseEigenbasis_apply,
      scalarBaseHeatDerivative_eigen, smul_smul]
    congr 1
    ring
  rwa [he] at hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant scalar heat mode has multiplicity exactly one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

include o in
theorem smoothScalarBaseL2_one_ne_zero : smoothScalarBaseL2 g (smoothScalarConst 1) ≠ 0 := by
  intro h
  have hp := congrArg (scalarBasePullback g o) h
  rw [scalarBasePullback_smooth, map_zero] at hp
  have hf := smoothScalarValueL2_injective g o
    (hp.trans (map_zero (smoothScalarValueL2 g (canonicalFrameMeasure g o))).symm)
  have hv := congrArg (fun f : SmoothScalar (M := M) => f.val (Classical.arbitrary M)) hf
  change (1 : ℝ) = 0 at hv
  exact one_ne_zero hv

variable [PreconnectedSpace M]

theorem scalarBase_fixed_space_eq_span (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap 1 =
      Submodule.span ℝ {smoothScalarBaseL2 g (smoothScalarConst 1)} := by
  apply le_antisymm
  · intro f hf
    have hfix : scalarBaseResolvent g o d f = f := by
      have he : scalarBaseResolvent g o d f = (1 : ℝ) • f :=
        Module.End.mem_eigenspace_iff.mp hf
      exact he.trans (one_smul ℝ f)
    obtain ⟨c, hc⟩ := scalarBaseResolvent_fixed_constant g o d hRic f hfix
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton _))
  · apply Submodule.span_le.mpr
    intro f hf
    rw [mem_singleton_iff] at hf
    subst f
    apply Module.End.mem_eigenspace_iff.mpr
    change scalarBaseResolvent g o d (smoothScalarBaseL2 g (smoothScalarConst 1)) =
      (1 : ℝ) • smoothScalarBaseL2 g (smoothScalarConst 1)
    rw [one_smul]
    exact scalarBaseResolvent_fixed_one g o d

theorem scalarBase_fixed_finrank (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Module.finrank ℝ (Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap 1) = 1 := by
  rw [scalarBase_fixed_space_eq_span hRic d]
  exact finrank_span_singleton (smoothScalarBaseL2_one_ne_zero (o := o))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing scalar has intrinsic H1 forcing. This is the
pre-positivity bootstrap from its proved L8 values and L4 weak gradients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance minimumH1Source_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalar_minimum_H1_source (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ∃ S : scalarH1 d, ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarWeightedH1ToH1 d w))
        (scalarH1Gradient d i v)) = -(inner ℝ (scalarH1Value d S) (scalarH1Value d v)) := by
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  have hbu : scalarBasePullback g o b = scalarH1Value d u := scalarH1BaseValue_spec g o d u
  have hu8 : MemLp (scalarH1Value d u : FrameBundle g → ℝ) 8 (canonicalFrameMeasure g o) := by
    rw [← hbu]
    exact (memLp_congr_ae (Lp.coeFn_compMeasurePreserving b (canonicalFrameMeasure_base g o)).symm).mp
      ((scalar_minimum_memLp_eight g o d hp hp4 w hw hm hmin).comp_measurePreserving
        (canonicalFrameMeasure_base g o))
  obtain ⟨N, hN, _⟩ := scalarH1_subcritical_compose d u hp hp4 hu8
    (scalar_subcritical_minimum_gradient_memLp_four g o d hp hp4 w hw hm hmin)
  obtain ⟨F, hF, hweak⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  have hNF : scalarH1Value d N = scalarBasePullback g o F := by
    apply Lp.ext
    have hbase := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hF
    have hT := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae
      (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w)
    have hval : (scalarBasePullback g o b : FrameBundle g → ℝ) =ᵐ[canonicalFrameMeasure g o]
        (fun e => b e.base) := Lp.coeFn_compMeasurePreserving b (canonicalFrameMeasure_base g o)
    rw [hbu] at hval
    filter_upwards [hN, hbase, hT, hval,
      Lp.coeFn_compMeasurePreserving F (canonicalFrameMeasure_base g o)]
      with e hn hf ht hu hfp
    change scalarH1Value d N e = Lp.compMeasurePreserving FrameBundle.base
      (canonicalFrameMeasure_base g o) F e
    rw [hfp]
    simp only [Function.comp_apply]
    rw [hf, ht]
    change scalarH1Value d N e = |b e.base| ^ (p - 2) * b e.base
    rw [← hu]
    exact hn
  refine ⟨(2 : ℝ) • u - (2 * ‖w‖ ^ 2) • N, ?_⟩
  intro v
  simpa only [map_sub, map_smul, hNF] using hweak v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The smooth Hodge Laplacian agrees pointwise with the covariant
component expression for dδ + δd. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_framed (hRic : RicciThree g)
    (u : smoothTwoForms o) (e : FrameBundle g) :
    twoFormFramedValue o (smoothHodgeLaplacian hRic u).val e =
      (6 : ℝ) • twoFormFramedValue o u.val e -
        (2 : ℝ) • twoFormFramedValue o (smoothTwoFormCurvature u).val e -
          twoFormFramedRoughTrace o u.val e := by
  let L : smoothTwoForms o →ₗ[ℝ] CovariantCoordinates 2 :=
    { toFun w := twoFormTensorLinear
        (twoFormFrameActionLinear ((o.frame e.base).changeMatrix e.frame) (w.val e.base))
      map_add' w v := by simp only [Submodule.coe_add, Pi.add_apply, map_add]
      map_smul' r w := by simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply] }
  have hL (w : smoothTwoForms o) : L w = twoFormFramedValue o w.val e :=
    (twoFormFramedValue_eq o w.val e).symm
  calc
    _ = L (smoothHodgeLaplacian hRic u) := (hL _).symm
    _ = (6 : ℝ) • L u - (2 : ℝ) • L (smoothTwoFormCurvature u) -
        L (smoothTwoFormRoughTrace hRic u) := by
      rw [smoothHodgeLaplacian, map_sub, map_sub, map_smul, map_smul]
    _ = _ := by
      rw [hL, hL, hL]
      exact congrArg (fun T : CovariantCoordinates 2 =>
        (6 : ℝ) • twoFormFramedValue o u.val e -
          (2 : ℝ) • twoFormFramedValue o (smoothTwoFormCurvature u).val e - T)
        (u.property.framedValue_roughTrace hRic e)

theorem smoothHodgeLaplacian_component (hRic : RicciThree g)
    (u : smoothTwoForms o) (e : FrameBundle g) (j k : Fin 4) :
    twoFormFramedValue o (smoothHodgeLaplacian hRic u).val e ![j,k] =
      twoFormSecondDeRham (twoFormFramedSecondDerivative o u.val e) j k := by
  let R := frameCurvature g e.base e.frame
  let a := twoFormFrameValue o u.val e
  have hR : twoFormMetricCurvatureTensor g e =
      fun v => R (v 0) (v 1) (v 2) (v 3) := by
    funext v
    have hv : ![v 0,v 1,v 2,v 3] = v := by ext i; fin_cases i <;> rfl
    rw [← hv]
    exact frameTensor_curvatureCoordinates e.frame _ _ _ _
  have hT (i j k l : Fin 4) :
      twoFormFramedSecondDerivative o u.val e ![i,j,k,l] -
        twoFormFramedSecondDerivative o u.val e ![j,i,k,l] =
          -tensorSlotAction (curvatureEndomorphism R i j) (twoFormTensor a) ![k,l] := by
    have h := u.property.framed_commutator e i j ![k,l]
    rw [twoFormFramedValue_eq] at h
    exact h
  rw [twoFormSecondDeRham_eq _ R a hT (frame_algebraic_firstSkew e.frame)
    (frame_algebraic_lastSkew e.frame) (frame_algebraic_firstBianchi e.frame)
      (frame_algebraic_ricciThree e.frame hRic)]
  rw [smoothHodgeLaplacian_framed]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hc : twoFormFrameValue o (smoothTwoFormCurvature u).val e =
      twoFormCurvatureAction (fun v => R (v 0) (v 1) (v 2) (v 3)) a := by
    have h := twoFormCurvatureField_frame (o := o) u.val e
    rw [hR] at h
    exact h
  rw [twoFormFramedValue_eq, twoFormFramedValue_eq, hc]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential of a smooth two-form is an actual smooth one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormCodifferentialField (u : smoothTwoForms o) : smoothCovariantFields M 1 :=
  smoothCovariantMetricTrace (g := g)
    (smoothCovariantDerivative g (smoothTwoFormCovariantField u))

theorem smoothTwoFormCovariantField_derivative_framed (u : smoothTwoForms o)
    (e : FrameBundle g) :
    covariantFieldFramed g (covariantFieldDerivative g (smoothTwoFormCovariantField u).val) e =
      twoFormFramedCovariantDerivative o u.val e := by
  rw [covariantFieldFramed_eq]
  rfl

theorem smoothTwoFormCodifferentialField_framed (u : smoothTwoForms o) (e : FrameBundle g) :
    covariantFieldFramed g (smoothTwoFormCodifferentialField u).val e =
      twoFormCodiffTensor (twoFormFramedCovariantDerivative o u.val e) := by
  have h := covariantMetricTraceField_framed
    (covariantFieldDerivative g (smoothTwoFormCovariantField u).val) e
  exact h.trans (congrArg twoFormCodiffTensor (smoothTwoFormCovariantField_derivative_framed u e))

theorem smoothTwoFormCodifferentialField_component (u : smoothTwoForms o)
    (e : FrameBundle g) (k : Fin 4) :
    covariantFieldFramed g (smoothTwoFormCodifferentialField u).val e ![k] =
      smoothTwoFormCodifferential u e k := by
  rw [smoothTwoFormCodifferentialField_framed]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior/codifferential energy is a continuous nonnegative scalar
on the base. Its vanishing detects actual smooth harmonic forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormDeRhamDensity (o : FrameOrientation g) (u : M → TwoFormFour) (x : M) : ℝ :=
  twoFormDeRhamQuadratic (fun i j k =>
    twoFormFramedCovariantDerivative o u ⟨x,o.frame x⟩ ![i,j,k])

theorem twoFormDeRhamDensity_eq_frame (u : M → TwoFormFour) (e : FrameBundle g) :
    twoFormDeRhamDensity o u e.base = twoFormDeRhamQuadratic
      (fun i j k => twoFormFramedCovariantDerivative o u e ![i,j,k]) := by
  let P := (o.frame e.base).changeMatrix e.frame
  have hP : P * Pᵀ = 1 := mul_eq_one_comm.mp ((o.frame e.base).changeMatrix_orthogonal e.frame)
  have hd : twoFormFramedCovariantDerivative o u e =
      frameTensor P (twoFormFramedCovariantDerivative o u ⟨e.base,o.frame e.base⟩) := by
    unfold twoFormFramedCovariantDerivative
    rw [← frameTensor_mul, (o.frame e.base).mul_changeMatrix e.frame]
  rw [hd, twoFormDeRhamQuadratic_frame P hP]
  rfl

theorem TwoFormSmooth.continuous_framedDeRhamDensity {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (fun e : FrameBundle g =>
      twoFormDeRhamQuadratic (fun i j k => twoFormFramedCovariantDerivative o u e ![i,j,k])) := by
  have hD (i j k : Fin 4) : Continuous (fun e => twoFormFramedCovariantDerivative o u e ![i,j,k]) :=
    (continuous_apply _).comp hu.continuous_framedCovariantDerivative
  apply Continuous.add
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro k _
    exact (((hD i j k).sub (hD j i k)).add (hD k i j)).pow 2
  · apply continuous_finsetSum
    intro k _
    exact ((continuous_finsetSum _ (fun i _ => hD i i k)).neg).pow 2

theorem TwoFormSmooth.continuous_deRhamDensity {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (twoFormDeRhamDensity o u) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (hu.continuous_framedDeRhamDensity.continuousAt.comp
    (continuousAt_localGramSection g c 1 (by simp))).congr_of_eventuallyEq
  filter_upwards [] with x
  have he := twoFormDeRhamDensity_eq_frame (o := o) u (localGramSection g c 1 (by simp) x)
  rw [localGramSection_base] at he
  exact he

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem smoothTwoFormDeRhamEnergy_eq_base (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = ∫ x, twoFormDeRhamDensity o u.val x ∂normalizedVolume g := by
  have hi := u.property.continuous_deRhamDensity.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  apply integral_congr_ae
  filter_upwards [] with e
  exact (twoFormDeRhamDensity_eq_frame u.val e).symm

theorem smoothTwoFormDeRhamEnergy_eq_zero_iff (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = 0 ↔ u ∈ smoothHarmonicTwoForms := by
  constructor
  · intro h
    let _ := normalizedVolume_isOpenPosMeasure g
    have hn (x : M) : 0 ≤ twoFormDeRhamDensity o u.val x := twoFormDeRhamQuadratic_nonneg _
    have hc := u.property.continuous_deRhamDensity
    have hi := hc.integrable_of_hasCompactSupport
      (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
    rw [smoothTwoFormDeRhamEnergy_eq_base] at h
    have ha := (integral_eq_zero_iff_of_nonneg hn hi).mp h
    have hz : twoFormDeRhamDensity o u.val = 0 := Measure.eq_of_ae_eq ha hc continuous_const
    apply (mem_smoothHarmonicTwoForms u).mpr
    have hf (e : FrameBundle g) := congrFun hz e.base
    simp only [twoFormDeRhamDensity_eq_frame, Pi.zero_apply] at hf
    constructor
    · intro e i j k
      exact ((twoFormDeRhamQuadratic_eq_zero _).mp (hf e)).1 i j k
    · intro e k
      exact ((twoFormDeRhamQuadratic_eq_zero _).mp (hf e)).2 k
  · exact smoothHarmonicTwoForm_energy_zero u

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual product rules for the scalar differential and two-form
codifferential. These identify the first-order terms of the Hodge operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFramedValue_product (ρ : SmoothScalar (M := M)) (u : smoothTwoForms o)
    (e : FrameBundle g) (a : Fin 2 → Fin 4) :
    twoFormFramedValue o (smoothTwoFormProduct ρ u).val e a =
      ρ.val e.base * twoFormFramedValue o u.val e a := by
  rw [twoFormFramedValue_eq, twoFormFramedValue_eq]
  change twoFormTensor (twoFormFrameValue o (fun x => ρ.val x • u.val x) e) a = _
  rw [twoFormFrameValue_mul]
  exact congrFun (twoFormTensorLinear.map_smul (ρ.val e.base) (twoFormFrameValue o u.val e)) a

variable [T2Space M] [CompactSpace M]

theorem scalarGradient_smoothScalarProduct (ρ f : SmoothScalar (M := M))
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarProduct ρ f).val e i =
      scalarGradient g ρ.val e i * f.val e.base +
        ρ.val e.base * scalarGradient g f.val e i := by
  let γ := fun t => parallelFrameFlowMap g i t e
  have hγ := (parallelFrameFlowMap_curve_continuous g i e).continuousAt (x := 0)
  have hp := parallelFrameFlowMap_primitive g i e 0
  have h := actual_scalarValue_parallel_derivative g (smoothScalarProduct ρ f).property γ 0 i hγ hp
  have hρ := actual_scalarValue_parallel_derivative g ρ.property γ 0 i hγ hp
  have hf := actual_scalarValue_parallel_derivative g f.property γ 0 i hγ hp
  have he := h.unique (hρ.mul hf)
  simpa only [γ, parallelFrameFlowMap_zero] using he

theorem twoFormFramedCovariantDerivative_product (ρ : SmoothScalar (M := M))
    (u : smoothTwoForms o) (e : FrameBundle g) (i j k : Fin 4) :
    twoFormFramedCovariantDerivative o (smoothTwoFormProduct ρ u).val e ![i,j,k] =
      scalarGradient g ρ.val e i * twoFormFramedValue o u.val e ![j,k] +
        ρ.val e.base * twoFormFramedCovariantDerivative o u.val e ![i,j,k] := by
  let γ := fun t => parallelFrameFlowMap g i t e
  have hγ := (parallelFrameFlowMap_curve_continuous g i e).continuousAt (x := 0)
  have hp := parallelFrameFlowMap_primitive g i e 0
  have h := (smoothTwoFormProduct ρ u).property.framedValue_parallel_derivative γ 0 i hγ hp ![j,k]
  have hρ := actual_scalarValue_parallel_derivative g ρ.property γ 0 i hγ hp
  have hu := u.property.framedValue_parallel_derivative γ 0 i hγ hp ![j,k]
  have hprod := hρ.mul hu
  have heq : (fun t => ρ.val (γ t).base * twoFormFramedValue o u.val (γ t) ![j,k]) =
      fun t => twoFormFramedValue o (smoothTwoFormProduct ρ u).val (γ t) ![j,k] := by
    funext t
    exact (twoFormFramedValue_product ρ u (γ t) ![j,k]).symm
  change HasDerivAt (fun t => ρ.val (γ t).base * twoFormFramedValue o u.val (γ t) ![j,k]) _ 0 at hprod
  rw [heq] at hprod
  have he := h.unique hprod
  have hc : Fin.cons i ![j,k] = ![i,j,k] := by
    ext p
    fin_cases p <;> rfl
  simpa only [γ, parallelFrameFlowMap_zero, hc] using he

def scalarDifferentialFiber (g : SmoothMetric M) (ρ : SmoothScalar (M := M))
    (e : FrameBundle g) : FourSpace := WithLp.toLp 2 (fun i => scalarGradient g ρ.val e i)

theorem twoFormCodifferential_product (ρ : SmoothScalar (M := M))
    (u : smoothTwoForms o) (e : FrameBundle g) (k : Fin 4) :
    smoothTwoFormCodifferential (smoothTwoFormProduct ρ u) e k =
      ρ.val e.base * smoothTwoFormCodifferential u e k +
        twoFormCodifferentialSymbol (scalarDifferentialFiber g ρ e) (twoFormFrameValue o u.val e) k := by
  change -(∑ i, twoFormFramedCovariantDerivative o (smoothTwoFormProduct ρ u).val e ![i,i,k]) =
    ρ.val e.base * (-(∑ i, twoFormFramedCovariantDerivative o u.val e ![i,i,k])) + _
  simp_rw [twoFormFramedCovariantDerivative_product]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, neg_add, mul_neg,
    twoFormCodifferentialSymbol_matrix]
  have hsk (i : Fin 4) : twoFormFramedValue o u.val e ![i,k] =
      -(twoFormMatrix (twoFormFrameValue o u.val e) k i) := by
    rw [twoFormFramedValue_eq]
    exact congrArg (fun A : Mat4 => A k i) (twoFormMatrix_skew (twoFormFrameValue o u.val e))
  simp_rw [hsk]
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg,
    Matrix.mulVec, dotProduct, scalarDifferentialFiber]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact resolvent of one plus the two-form Hodge
Laplacian, constructed from the proved nonnegative weak Hodge form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormShiftedHodgeCompact : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  twoFormHodgeCompact - twoFormRoughSolution.comp twoFormH1ToL2

theorem twoFormShiftedHodgeCompact_compact : IsCompactOperator (twoFormShiftedHodgeCompact (o := o)) :=
  twoFormHodgeCompact_compact.sub (twoFormH1ToL2_compact.clm_comp twoFormRoughSolution)

def twoFormShiftedHodge : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  ContinuousLinearMap.id ℝ (TwoFormH1 o) - twoFormShiftedHodgeCompact

theorem twoFormShiftedHodge_inner (u v : TwoFormH1 o) :
    inner ℝ (twoFormShiftedHodge u) v =
      twoFormHodgeForm u v + inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v) := by
  change inner ℝ (u - (twoFormHodgeCompact u - twoFormRoughSolution (twoFormH1ToL2 u))) v = _
  rw [inner_sub_left, inner_sub_left, twoFormRoughSolution_weak]
  have he := twoFormHodgeOperator_inner u v
  change inner ℝ (u - twoFormHodgeCompact u) v = _ at he
  rw [inner_sub_left] at he
  linarith only [he]

theorem twoFormShiftedHodge_eq_zero (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : twoFormShiftedHodge u = 0) : u = 0 := by
  have h := congrArg (fun v : TwoFormH1 o => inner ℝ v u) hu
  rw [twoFormShiftedHodge_inner, inner_zero_left] at h
  have hQ := twoFormHodgeForm_nonneg hRic u
  have hn := real_inner_self_nonneg (x := twoFormH1ToL2 u)
  have hz : inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 u) = 0 := by linarith only [h, hQ, hn]
  exact twoFormH1_eq_zero_of_value_eq_zero hRic u (inner_self_eq_zero.mp hz)

theorem twoFormShiftedHodge_injective (hRic : RicciThree g) :
    Function.Injective (twoFormShiftedHodge (o := o)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply twoFormShiftedHodge_eq_zero hRic
  rw [map_sub, huv, sub_self]

theorem twoFormShiftedHodge_surjective (hRic : RicciThree g) :
    Function.Surjective (twoFormShiftedHodge (o := o)) := by
  rcases (twoFormShiftedHodgeCompact_compact (o := o)).hasEigenvalue_or_mem_resolventSet
      (one_ne_zero : (1 : ℝ) ≠ 0) with hv | hr
  · obtain ⟨u, hu⟩ := hv.exists_hasEigenvector
    have he := Module.End.mem_eigenspace_iff.mp hu.1
    change twoFormShiftedHodgeCompact u = (1 : ℝ) • u at he
    rw [one_smul] at he
    have hz : twoFormShiftedHodge u = 0 := by
      change u - twoFormShiftedHodgeCompact u = 0
      rw [he, sub_self]
    exact (hu.2 (twoFormShiftedHodge_eq_zero hRic u hz)).elim
  · have hi := spectrum.mem_resolventSet_iff.mp hr
    simp only [map_one] at hi
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hi).2

def twoFormShiftedHodgeEquiv (hRic : RicciThree g) : TwoFormH1 o ≃L[ℝ] TwoFormH1 o :=
  ContinuousLinearEquiv.ofBijective twoFormShiftedHodge
    (LinearMap.ker_eq_bot.mpr (twoFormShiftedHodge_injective hRic))
    (LinearMap.range_eq_top.mpr (twoFormShiftedHodge_surjective hRic))

def twoFormShiftedSolution (hRic : RicciThree g) : TwoFormL2 o →L[ℝ] TwoFormH1 o :=
  (twoFormShiftedHodgeEquiv hRic).symm.toContinuousLinearMap.comp twoFormRoughSolution

theorem twoFormShiftedSolution_equation (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedHodge (twoFormShiftedSolution hRic f) = twoFormRoughSolution f :=
  (twoFormShiftedHodgeEquiv hRic).apply_symm_apply _

theorem twoFormShiftedSolution_weak (hRic : RicciThree g) (f : TwoFormL2 o) (v : TwoFormH1 o) :
    twoFormHodgeForm (twoFormShiftedSolution hRic f) v +
      inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) (twoFormH1ToL2 v) =
        inner ℝ f (twoFormH1ToL2 v) := by
  rw [← twoFormShiftedHodge_inner, twoFormShiftedSolution_equation, twoFormRoughSolution_weak]

def twoFormShiftedResolvent (hRic : RicciThree g) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormH1ToL2.comp (twoFormShiftedSolution hRic)

theorem twoFormShiftedResolvent_compact (hRic : RicciThree g) :
    IsCompactOperator (twoFormShiftedResolvent (o := o) hRic) :=
  twoFormH1ToL2_compact.comp_clm (twoFormShiftedSolution hRic)

theorem twoFormShiftedResolvent_selfAdjoint (hRic : RicciThree g) (f h : TwoFormL2 o) :
    inner ℝ (twoFormShiftedResolvent hRic f) h =
      inner ℝ f (twoFormShiftedResolvent hRic h) := by
  have hf := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic h)
  have hh := twoFormShiftedSolution_weak hRic h (twoFormShiftedSolution hRic f)
  change inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) h = _
  calc
    _ = inner ℝ h (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) := real_inner_comm _ _
    _ = twoFormHodgeForm (twoFormShiftedSolution hRic h) (twoFormShiftedSolution hRic f) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic h))
          (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) := hh.symm
    _ = twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic h) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f))
          (twoFormH1ToL2 (twoFormShiftedSolution hRic h)) := by
      rw [twoFormHodgeForm_comm, real_inner_comm]
    _ = _ := hf

theorem twoFormShiftedResolvent_nonneg (hRic : RicciThree g) (f : TwoFormL2 o) :
    0 ≤ inner ℝ (twoFormShiftedResolvent hRic f) f := by
  have h := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  change 0 ≤ inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) f
  calc
    0 ≤ twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic f) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f))
          (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) :=
      add_nonneg (twoFormHodgeForm_nonneg hRic _) (real_inner_self_nonneg (x := _))
    _ = inner ℝ f (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) := h
    _ = _ := real_inner_comm _ _

theorem twoFormShiftedResolvent_injective (hRic : RicciThree g) :
    Function.Injective (twoFormShiftedResolvent (o := o) hRic) := by
  intro f h he
  have hu := twoFormH1ToL2_injective hRic he
  have hv := congrArg (twoFormShiftedHodge (o := o)) hu
  exact twoFormRoughSolution_injective ((twoFormShiftedSolution_equation hRic f).symm.trans
    (hv.trans (twoFormShiftedSolution_equation hRic h)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weak Hodge Poisson solvability for actual L2 two-form sources
orthogonal to the harmonic kernel, with the normalized solution unique. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_weakHodgePoisson (hRic : RicciThree g) (f : TwoFormL2 o)
    (hf : ∀ v ∈ twoFormWeitzenbockKernel (o := o), inner ℝ f (twoFormH1ToL2 v) = 0) :
    ∃ u : TwoFormH1 o,
      (∀ v ∈ twoFormWeitzenbockKernel (o := o), inner ℝ u v = 0) ∧
      ∀ v : TwoFormH1 o, twoFormHodgeForm u v = inner ℝ f (twoFormH1ToL2 v) := by
  obtain ⟨u, hu⟩ := twoFormRegularizedHodge_surjective (o := o) hRic (twoFormRoughSolution f)
  have he (v : TwoFormH1 o) : twoFormHodgeForm u v +
      inner ℝ (twoFormHarmonicProjection u) v = inner ℝ f (twoFormH1ToL2 v) := by
    have h := congrArg (fun w : TwoFormH1 o => inner ℝ w v) hu
    change inner ℝ (twoFormHodgeOperator u + twoFormHarmonicProjection u) v =
      inner ℝ (twoFormRoughSolution f) v at h
    rw [inner_add_left, twoFormHodgeOperator_inner, twoFormRoughSolution_weak] at h
    exact h
  have hp : twoFormHarmonicProjection u ∈ twoFormWeitzenbockKernel (o := o) :=
    Submodule.starProjection_apply_mem _ u
  have hz : twoFormHodgeForm u (twoFormHarmonicProjection u) = 0 := by
    rw [twoFormHodgeForm_comm]
    exact twoFormHodgeForm_zero_left hRic _
      ((mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mp hp) u
  have hP : twoFormHarmonicProjection u = 0 := by
    have h := he (twoFormHarmonicProjection u)
    rw [hz, hf _ hp, zero_add] at h
    exact inner_self_eq_zero.mp h
  refine ⟨u, ?_, fun v => ?_⟩
  · intro v hv
    have h := Submodule.starProjection_inner_eq_zero
      (K := twoFormWeitzenbockKernel (o := o)) u v hv
    change inner ℝ (u - twoFormHarmonicProjection u) v = 0 at h
    simpa only [hP, sub_zero] using h
  · simpa only [hP, inner_zero_left, add_zero] using he v

theorem weakHodgePoisson_unique (hRic : RicciThree g) (f : TwoFormL2 o)
    (u w : TwoFormH1 o)
    (hu : ∀ v, twoFormHodgeForm u v = inner ℝ f (twoFormH1ToL2 v))
    (hw : ∀ v, twoFormHodgeForm w v = inner ℝ f (twoFormH1ToL2 v))
    (huorth : ∀ v ∈ twoFormWeitzenbockKernel (o := o), inner ℝ u v = 0)
    (hworth : ∀ v ∈ twoFormWeitzenbockKernel (o := o), inner ℝ w v = 0) : u = w := by
  have hd (v : TwoFormH1 o) : twoFormHodgeForm (u - w) v = 0 := by
    have hs : twoFormHodgeForm (u - w) v = twoFormHodgeForm u v - twoFormHodgeForm w v := by
      unfold twoFormHodgeForm
      simp only [map_sub, inner_sub_left]
      ring
    rw [hs, hu v, hw v, sub_self]
  have hk : u - w ∈ twoFormWeitzenbockKernel (o := o) :=
    (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mpr (hd (u - w))
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left, huorth _ hk, hworth _ hk, sub_self]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The density-weighted connection Laplacian is the covariant
divergence of the actual metric flux. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatCovariantOperator_divergence
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (k : Fin 6)
    (hA : ∀ i l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hρ0 : ρ x ≠ 0)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x)
    (hsym : ∀ i j, a x i j = a x j i) :
    ρ x * fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A V u x k =
      -(∑ i, fourHeatCovariantDerivative A (fourHeatCovariantFlux A a ρ u i) i x k) +
        ρ x * ∑ l, V k l * u x l := by
  let Q := ∑ i : Fin 4, ∑ j : Fin 4, a x i j *
    fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k
  let B := ∑ i : Fin 4, fourHeatDensityDrift a ρ x i *
    fourHeatCovariantDerivative A u i x k
  have hb (i : Fin 4) :
      (∑ j, partialDeriv (fun y => ρ y * a y j i) j x) =
        -(ρ x * fourHeatDensityDrift a ρ x i) := by
    have h := fourHeatDensityDrift_weighted a ρ x i hρ hρ0 (fun j => ha j i)
    linarith only [h]
  have hfirst : (∑ i : Fin 4, ∑ j : Fin 4,
      partialDeriv (fun y => ρ y * a y i j) i x * fourHeatCovariantDerivative A u j x k) =
      -(ρ x * B) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hb]
    simp only [B, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond : (∑ i : Fin 4, ∑ j : Fin 4,
      (ρ x * a x i j) *
        fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u j) i x k) =
      ρ x * Q := by
    rw [Finset.sum_comm]
    simp only [Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hflux (i : Fin 4) := fourHeatCovariantFlux_derivative A a ρ u x i i k
    hA (ha i) hρ hu
  have hdiv : (∑ i, fourHeatCovariantDerivative A (fourHeatCovariantFlux A a ρ u i) i x k) =
      ρ x * Q - ρ x * B := by
    simp_rw [hflux, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  rw [hdiv]
  change ρ x * (-Q + B + ∑ l, V k l * u x l) = _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for a covariant divergence, with a compact test
section and coefficients regular only on its support. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeat_covariant_divergence_green
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (W : Fin 4 → FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hW : ∀ x ∈ U, ∀ i k, ContDiffAt ℝ 1 (fun y => W i y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 6,
      u x k * fourHeatCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 6, fourHeatCovariantDerivative A u i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      u x k * fourHeatCovariantDerivative A (W i) i x k) :=
    fourHeatCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => hA x hx i k l)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatCovariantDerivative_green A u (W i) U i hu hc hs
    (fun x hx k => hW x hx i k) (fun x hx k l => hA x hx i k l)
    (fun x hx => hskew x hx i)
  linarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local regularity and compact support of the flux needed for the
second integration by parts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantDerivative_contDiffAt
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hA : ∀ l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatCovariantDerivative A u i y k) x := by
  apply ContDiffAt.add
  · exact ((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  · exact ContDiffAt.sum fun l _ => (hA l).mul ((hu l).of_le (by norm_num))

theorem fourHeatCovariantFlux_contDiffAt
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hA : ∀ j l, ContDiffAt ℝ 1 (fun y => A j y k l) x)
    (ha : ∀ j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ContDiffAt ℝ 1 ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatCovariantFlux A a ρ u i y k) x := by
  apply ContDiffAt.sum
  intro j _
  exact (hρ.mul (ha j)).mul (fourHeatCovariantDerivative_contDiffAt A u x j k (hA j) hu)

theorem fourHeatCovariantDerivative_support
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (i : Fin 4) (k : Fin 6) :
    tsupport (fun x => fourHeatCovariantDerivative A u i x k) ⊆
      ⋃ l : Fin 6, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hu (l : Fin 6) : x ∉ tsupport (fun y => u y l) :=
    fun h => hn (mem_iUnion.mpr ⟨l, h⟩)
  have hp : partialDeriv (fun y => u y k) i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hu k
      (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h))
  have hz (l : Fin 6) : u x l = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => u y l) (hu l)
  apply hx
  simp only [fourHeatCovariantDerivative, hp, hz, mul_zero, Finset.sum_const_zero, zero_add]

theorem fourHeatCovariantFlux_support
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ) (i : Fin 4) (k : Fin 6) :
    tsupport (fun x => fourHeatCovariantFlux A a ρ u i x k) ⊆
      ⋃ l : Fin 6, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hz (j : Fin 4) : fourHeatCovariantDerivative A u j x k = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A u j y k)
      (fun h => hn (fourHeatCovariantDerivative_support A u j k h))
  apply hx
  simp only [fourHeatCovariantFlux, hz, mul_zero, Finset.sum_const_zero]

theorem fourHeatCovariantFlux_compact
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) (i : Fin 4) (k : Fin 6) :
    HasCompactSupport (fun x => fourHeatCovariantFlux A a ρ u i x k) :=
  (isCompact_iUnion hc).of_isClosed_subset (isClosed_tsupport _)
    (fourHeatCovariantFlux_support A a ρ u i k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-order Gaussian limit, with the actual Euclidean normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeat_bilinear_coordinates (B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ)
    (x : FourSpace) :
    B x x = ∑ i, ∑ j, B (coordinateVector i) (coordinateVector j) * x i * x j := by
  have hx : (∑ i, x i • coordinateVector i) = x := sum_coordinateVector (WithLp.ofLp x)
  calc
    B x x = B (∑ i, x i • coordinateVector i) (∑ j, x j • coordinateVector j) := by
      rw [hx]
    _ = _ := by
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem fourHeatGaussian_bilinear_integral
    (B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) :
    (∫ x : FourSpace, fourHeatGaussian 1 x * ((1 / 2 : ℝ) * B x x)) =
      ∑ i, B (coordinateVector i) (coordinateVector i) := by
  have h := fourHeatGaussian_hessian_integral 1 zero_lt_one
    (fun i j => B (coordinateVector i) (coordinateVector j))
  have he : (fun x : FourSpace => fourHeatGaussian 1 x * ((1 / 2 : ℝ) * B x x)) =
      fun x => (1 / 2 : ℝ) * ((∑ i, ∑ j,
        B (coordinateVector i) (coordinateVector j) * x i * x j) * fourHeatGaussian 1 x) := by
    funext x
    rw [fourHeat_bilinear_coordinates]
    ring
  rw [he, integral_const_mul, h]
  simp only [Matrix.trace, Matrix.diag]
  ring

theorem fourHeatGaussian_second_order_limit (f : FourSpace → ℝ)
    (hc : Continuous f) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun t : ℝ => (∫ x : FourSpace, fourHeatGaussian t x * f x) / t)
      (𝓝[>] 0) (𝓝 (∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i))) := by
  obtain ⟨K, _, hK⟩ := fourHeat_vanishing_quadratic_bound f hf hf0 hD0 C hC
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ z : FourSpace,
      ‖fourHeatGaussian 1 z * (f (Real.sqrt t • z) / t)‖ ≤
        K * (‖z‖ ^ 2 * fourHeatGaussian 1 z) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Eventually.of_forall fun z => by
      rw [norm_mul, norm_div, Real.norm_of_nonneg (fourHeatGaussian_pos 1 zero_lt_one z).le,
        Real.norm_of_nonneg ht.le]
      have hscale : ‖f (Real.sqrt t • z)‖ / t ≤ K * ‖z‖ ^ 2 := by
        apply (div_le_iff₀ ht).mpr
        calc
          ‖f (Real.sqrt t • z)‖ ≤ K * ‖Real.sqrt t • z‖ ^ 2 := hK _
          _ = K * ‖z‖ ^ 2 * t := by rw [fourHeat_norm_sqrt_smul_sq t ht.le]; ring
      calc
        _ ≤ fourHeatGaussian 1 z * (K * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hscale (fourHeatGaussian_pos 1 zero_lt_one z).le
        _ = _ := by ring
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun z : FourSpace => fourHeatGaussian 1 z * (f (Real.sqrt t • z) / t)) volume := by
    apply Continuous.aestronglyMeasurable
    exact (fourHeatGaussian_continuous 1).mul
      ((hc.comp
        ((continuous_const : Continuous (fun _ : FourSpace => Real.sqrt t)).smul continuous_id)).div_const t)
  have hpoint (z : FourSpace) :=
    (fourHeat_vanishing_scaled_limit f hf hf0 hD0 z).const_mul (fourHeatGaussian 1 z)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure FourSpace)) (l := 𝓝[>] (0 : ℝ))
    (F := fun t z => fourHeatGaussian 1 z * (f (Real.sqrt t • z) / t))
    (f := fun z => fourHeatGaussian 1 z * ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 z z))
    (fun z => K * (‖z‖ ^ 2 * fourHeatGaussian 1 z)) (Eventually.of_forall hmeas) hbound
    ((fourHeatGaussian_moment_integrable 1 1 zero_lt_one).const_mul K)
    (Eventually.of_forall hpoint)
  rw [fourHeatGaussian_bilinear_integral] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hd := fourHeatGaussian_integral_dilate t ht (fun x => f (-x) / t) 0
  simp only [zero_sub, neg_neg] at hd
  simpa only [← mul_div_assoc, integral_div] using hd.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Four-component cutoff commutator for the actual one-form heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology
noncomputable section

def fourHeatOneScaledCommutator (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (χ : FourSpace → ℝ)
    (u : Fin 4 → FourSpace → Fin 4 → ℝ) (t : ℝ) (x : FourSpace) (k : Fin 4) : ℝ :=
  t * fourHeatLocalOperator (a x) (b x) 0 χ x * fourHeatOnePolynomial u t x k -
  2 * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
    (t * partialDeriv (fun y => fourHeatOnePolynomial u t y k) j x -
      x j / 2 * fourHeatOnePolynomial u t x k)) +
  t * (∑ i, ∑ q, B x i k q * partialDeriv χ i x * fourHeatOnePolynomial u t x q)

theorem fourHeatOneScaledCommutator_identity (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun y => u m y q)) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (k : Fin 4) :
    fourHeatLocalOperator (a x) (b x) 0 χ x *
        (fourHeatGaussian t x * fourHeatOnePolynomial u t x k) -
      2 * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
        partialDeriv (fun y => fourHeatGaussian t y * fourHeatOnePolynomial u t y k) j x) +
      (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
        (fourHeatGaussian t x * fourHeatOnePolynomial u t x q)) =
      (fourHeatGaussian t x / t) * fourHeatOneScaledCommutator a b B χ u t x k := by
  have hP (q : Fin 4) : DifferentiableAt ℝ (fun y => fourHeatOnePolynomial u t y q) x :=
    ((fourHeatPolynomial_contDiff (fun m y => u m y q) (fun m => hu m q) t).differentiable
      (by norm_num)).differentiableAt
  simp_rw [fourHeatGaussian_amplitude_partial_at t ht.ne' _ x (hP k)]
  unfold fourHeatOneScaledCommutator
  have hg : (∑ i, ∑ j, a x i j * partialDeriv χ i x *
      (fourHeatGaussian t x * (partialDeriv (fun y => fourHeatOnePolynomial u t y k) j x -
        x j / (2 * t) * fourHeatOnePolynomial u t x k))) =
      (fourHeatGaussian t x / t) * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
        (t * partialDeriv (fun y => fourHeatOnePolynomial u t y k) j x -
          x j / 2 * fourHeatOnePolynomial u t x k)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hB : (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
      (fourHeatGaussian t x * fourHeatOnePolynomial u t x q)) =
      fourHeatGaussian t x * (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
        fourHeatOnePolynomial u t x q) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hg, hB]
  field_simp

theorem fourHeatOneScaledCommutator_continuous (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) (k : Fin 4) :
    Continuous (fun z : ℝ × FourSpace => fourHeatOneScaledCommutator a b B χ u z.1 z.2 k) := by
  have hL : Continuous (fun x => fourHeatLocalOperator (a x) (b x) 0 χ x) :=
    (fourHeatLocalOperator_contDiff 0 a b (fun _ => 0) χ
      (fun i j => contDiff_zero.mpr (ha i j)) (fun i => contDiff_zero.mpr (hb i))
      contDiff_const hχ).continuous
  have hP (q : Fin 4) : Continuous (fun z : ℝ × FourSpace =>
      fourHeatOnePolynomial u z.1 z.2 q) :=
    fourHeatPolynomial_joint_continuous _ (fun m => (hu m q).continuous)
  have hD (q : Fin 4) (j : Fin 4) : Continuous (fun z : ℝ × FourSpace =>
      partialDeriv (fun y => fourHeatOnePolynomial u z.1 y q) j z.2) :=
    fourHeatPolynomial_partial_joint_continuous _
      (fun m => (hu m q).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × FourSpace => partialDeriv χ i z.2) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp continuous_snd
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × FourSpace => a z.2 i j) :=
    (ha i j).comp continuous_snd
  have hBB (i : Fin 4) (q : Fin 4) : Continuous (fun z : ℝ × FourSpace => B z.2 i k q) :=
    (hB i k q).comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × FourSpace => z.2 j) :=
    (EuclideanSpace.proj j).continuous.comp continuous_snd
  exact ((continuous_fst.mul (hL.comp continuous_snd)).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hBB i q).mul (hχi i)).mul (hP q)))))

theorem fourHeatOneScaledCommutator_zero_of_locally_const (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (t : ℝ) (x : FourSpace) (c : ℝ) (hc : χ =ᶠ[𝓝 x] fun _ => c) (k : Fin 4) :
    fourHeatOneScaledCommutator a b B χ u t x k = 0 := by
  have hp (i : Fin 4) : partialDeriv χ i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hc.eventuallyEq_nhds] with y hy
    rw [fourHeat_partial_germ hy]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  have hpp (i j : Fin 4) : partialDeriv (partialDeriv χ i) j x = 0 := by
    rw [fourHeat_partial_germ (hp i)]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatOneScaledCommutator, fourHeatLocalOperator, hpp,
    fun i => (hp i).self_of_nhds, mul_zero, zero_mul, Finset.sum_const_zero,
    neg_zero, add_zero, sub_zero]

theorem fourHeatOneScaledCommutator_bounded (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k,
      |fourHeatOneScaledCommutator a b B χ u t x k| ≤ C := by
  let S := fun z : ℝ × FourSpace => ∑ k : Fin 4,
    |fourHeatOneScaledCommutator a b B χ u z.1 z.2 k|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    (fourHeatOneScaledCommutator_continuous a b B χ u ha hb hB hχ hu k).abs)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hχc).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ tsupport χ
  · have hle : |fourHeatOneScaledCommutator a b B χ u t x k| ≤ S (t, x) :=
      Finset.single_le_sum (fun q _ => abs_nonneg
        (fourHeatOneScaledCommutator a b B χ u t x q)) (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx⟩)).trans (le_max_left _ _))
  · have hz := fourHeatOneScaledCommutator_zero_of_locally_const a b B χ u t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem fourHeatOneScaledCommutator_gaussian_bound (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q))
    (r : ℝ) (hr : 0 < r) (hinner : ∀ x ∈ ball 0 r, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k,
      |(fourHeatGaussian t x / t) * fourHeatOneScaledCommutator a b B χ u t x k| ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := fourHeatOneScaledCommutator_bounded a b B χ u ha hb hB hχ hχc hu
  refine ⟨C * (384 / (Real.pi ^ 2 * r ^ 8)), by positivity, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ ball 0 r
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    rw [fourHeatOneScaledCommutator_zero_of_locally_const a b B χ u t x 1 he k,
      mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hrx : r ≤ ‖x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩ x k)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * r ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time r t hr ht.1 x hrx) hC
      _ = _ := by ring
end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOne_skew_pairing (A : Mat4) (hA : Aᵀ = -A)
    (p q : Fin 4 → ℝ) :
    (∑ k, (∑ l, A k l * p l) * q k) =
      -(∑ k, p k * ∑ l, A k l * q l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (k l : Fin 4) : A l k = -A k l := congrFun (congrFun hA k) l
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hs k l]
  ring

theorem fourHeatOneCovariantDerivative_pairing
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (hA : (A i x)ᵀ = -A i x)
    (hu : ∀ k, DifferentiableAt ℝ (fun y => u y k) x)
    (hv : ∀ k, DifferentiableAt ℝ (fun y => v y k) x) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k := by
  rw [fourHeat_partial_sum_oneForm (fun k y => u y k * v y k) x
    (fun k => (hu k).mul (hv k)) i]
  change (∑ k, partialDeriv (fun y => u y k * v y k) i x) =
    (∑ k, (partialDeriv (fun y => u y k) i x + ∑ l, A i x k l * u x l) * v x k) +
      ∑ k, u x k * (partialDeriv (fun y => v y k) i x + ∑ l, A i x k l * v x l)
  have hd (k : Fin 4) := scalar_partial_product (fun y => u y k) (fun y => v y k)
    x (hu k) (hv k) i
  simp_rw [hd]
  simp only [Finset.sum_add_distrib, add_mul, mul_add]
  have hs := fourHeatOne_skew_pairing (A i x) hA (u x) (v x)
  linarith only [hs]

theorem fourHeatOneCovariantDerivative_pairing_integrable
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x) :
    Integrable (fun x => ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k) := by
  apply integrable_finsetSum
  intro k _
  have hcv (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => fourHeatOneCovariantDerivative A v i y k) x := by
    have hxU := hs k hx
    apply ContinuousAt.add
    · exact (((hv x hxU k).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt
    · exact tendsto_finsetSum _ fun l _ =>
        (hA x hxU k l).mul (hv x hxU l).continuousAt
  have hp := fourHeat_local_product_integrable _ _ (hu k) (hc k) hcv
  simpa only [mul_comm] using hp

theorem fourHeatOneCovariantDerivative_pairing_global
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) (x : FourSpace) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k := by
  by_cases hx : x ∈ U
  · exact fourHeatOneCovariantDerivative_pairing A u v x i (hskew x hx)
      (fun k => (hu k).differentiable one_ne_zero x)
      (fun k => (hv x hx k).differentiableAt one_ne_zero)
  · have hz : ∀ᶠ y in 𝓝 x, ∀ k : Fin 4, u y k = 0 := by
      apply eventually_all.mpr
      intro k
      have hk : x ∉ tsupport (fun y => u y k) := fun hk => hx (hs k hk)
      filter_upwards [(isClosed_tsupport (fun y => u y k)).isOpen_compl.mem_nhds hk]
        with y hy
      exact image_eq_zero_of_notMem_tsupport (f := fun y => u y k) hy
    have hzF : (fun y => ∑ k : Fin 4, u y k * v y k) =ᶠ[𝓝 x] (fun _ => 0) :=
      hz.mono fun y hy => by simp [hy]
    have hFD : partialDeriv (fun y => ∑ k : Fin 4, u y k * v y k) i x = 0 := by
      unfold partialDeriv
      rw [hzF.fderiv_eq, fderiv_const_apply]
      rfl
    have hDu (k : Fin 4) : partialDeriv (fun y => u y k) i x = 0 := by
      have hek : (fun y => u y k) =ᶠ[𝓝 x] (fun _ => 0) := hz.mono fun y hy => hy k
      unfold partialDeriv
      rw [hek.fderiv_eq, fderiv_const_apply]
      rfl
    simp only [hFD, fourHeatOneCovariantDerivative, hz.self_of_nhds,
      hDu, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

theorem fourHeatOne_pairing_contDiff (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x) :
    ContDiff ℝ 1 (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 4) : ContDiff ℝ 1 (fun x => u x k * v x k) :=
    fourHeat_mul_contDiff_of_tsupport 1 (fun x => u x k) (fun x => v x k)
      (hu k) (fun x hx => hv x (hs k hx) k)
  exact ContDiff.sum fun k _ => hp k

theorem fourHeatOne_pairing_compact (u v : FourSpace → Fin 4 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) :
    HasCompactSupport (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 4) : HasCompactSupport (fun x => u x k * v x k) :=
    (hc k).mul_right
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun k x => u x k * v x k) (fun k _ => hp k)
  simpa only [Finset.sum_fn] using h

theorem fourHeatOneCovariantDerivative_green
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) =
      -(∫ x, ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k) := by
  exact fourHeat_green_of_pairing (fun x => ∑ k, u x k * v x k)
    (fun x => ∑ k, fourHeatOneCovariantDerivative A u i x k * v x k)
    (fun x => ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k) i
    (fourHeatOne_pairing_contDiff u v U hu hs hv) (fourHeatOne_pairing_compact u v hc)
    (fourHeatOneCovariantDerivative_pairing_integrable A u v U i
      (fun k => (hu k).continuous) hc hs hv hA)
    (fourHeatOneCovariantDerivative_pairing_global A u v U i hu hs hv hskew)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform quadratic control of a joint family whose spatial first jet
vanishes at the normal center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

local instance heatFamilyHessianDualNormedGroup : NormedAddCommGroup (FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance heatFamilyHessianDualNormedSpace : NormedSpace ℝ (FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance heatFamilyHessianBilinearNormedGroup :
    NormedAddCommGroup (FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance heatFamilyHessianBilinearNormedSpace :
    NormedSpace ℝ (FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def heatFamilySpatialFDeriv (F : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) : FourSpace →L[ℝ] ℝ :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ FourSpace CoordinateFrameSpace)

theorem heatFamilySpatialFDeriv_slice (F : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) (hF : DifferentiableAt ℝ F z) :
    fderiv ℝ (fun x : FourSpace => F (x, z.2)) z.1 = heatFamilySpatialFDeriv F z := by
  have harg : HasFDerivAt (fun x : FourSpace => (x, z.2))
      (ContinuousLinearMap.inl ℝ FourSpace CoordinateFrameSpace) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  exact (hF.hasFDerivAt.comp z.1 harg).fderiv

theorem heatFamily_quadratic_bound (F : HeatRadialFrameSpace → ℝ)
    (hF : ContDiff ℝ 2 F) (R : ℝ) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K,
      F (0, q) = 0 → fderiv ℝ (fun x : FourSpace => F (x, q)) 0 = 0 →
      ∀ x ∈ closedBall (0 : FourSpace) R, ‖F (x, q)‖ ≤ C * ‖x‖ ^ 2 := by
  let L : FourSpace →L[ℝ] HeatRadialFrameSpace := ContinuousLinearMap.inl ℝ _ _
  let G := heatFamilySpatialFDeriv F
  have hG : ContDiff ℝ 1 G := (hF.fderiv_right (m := 1) (by norm_num)).clm_comp contDiff_const
  let H := fun z : HeatRadialFrameSpace => (fderiv ℝ G z).comp L
  have hH : Continuous H := (hG.continuous_fderiv one_ne_zero).clm_comp_const L
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : FourSpace) R).prod hK).bddAbove_image
    hH.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq hf0 hd0 x hx
  have hslice : ContDiff ℝ 2 (fun x : FourSpace => F (x, q)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  apply fourHeat_quadratic_bound_of_hessian _ hslice hf0 hd0 R (max C 0) (le_max_right _ _) _ x hx
  intro y hy
  have he : (fun x : FourSpace => fderiv ℝ (fun u : FourSpace => F (u, q)) x) =
      fun x => G (x, q) := by
    funext x
    exact heatFamilySpatialFDeriv_slice F (x, q) (hF.differentiable two_ne_zero _)
  have harg : HasFDerivAt (fun x : FourSpace => (x, q)) L y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const q y)
  have hGd : HasFDerivAt G (fderiv ℝ G (y, q)) (y, q) :=
    (hG.differentiable one_ne_zero (y, q)).hasFDerivAt
  have hd : fderiv ℝ (fun x : FourSpace => G (x, q)) y = H (y, q) :=
    (HasFDerivAt.comp (f := fun x : FourSpace => (x, q)) (g := G) y hGd harg).fderiv
  change ‖fderiv ℝ (fun z : FourSpace => fderiv ℝ (fun u : FourSpace => F (u, q)) z) y‖ ≤ _
  rw [he, hd]
  exact (hC (mem_image_of_mem _ (show (y, q) ∈ closedBall (0 : FourSpace) R ×ˢ K from ⟨hy, hq⟩))).trans (le_max_left _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single extended coefficient family provides the normal
bundle extension on every geometric slice where the germs agree. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def HeatFamilySmoothCoefficients.normalExtension (E : HeatFamilySmoothCoefficients)
    {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (ha : E.a =ᶠ[𝓝 (0, frameCoordinateState g c e)] (fun z => (heatFamilyMetric g c P z)⁻¹))
    (hb : E.b =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyDrift g c P)
    (hB : E.B =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyFirst g c P)
    (hC : E.C =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyZero g c P)
    (hU : E.U =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyLeading g c P) :
    HeatNormalBundleExtension D := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun x : FourSpace => (x, q)) (𝓝 0) (𝓝 (0, q)) :=
    continuousAt_id.prodMk continuousAt_const
  have hG := heatFamilyNormal_germs D he P hP hpoint
  exact {
    base := {
      a := fun x => E.a (x, q)
      b := fun x => E.b (x, q)
      U := fun x => E.U (x, q)
      a_regular := fun i j => (E.a_regular i j).comp (contDiff_id.prodMk contDiff_const)
      b_regular := fun i => (E.b_regular i).comp (contDiff_id.prodMk contDiff_const)
      U_regular := E.U_regular.comp (contDiff_id.prodMk contDiff_const)
      U_pos := fun x => E.U_pos (x, q)
      a_near := Filter.EventuallyEq.trans (hi.eventually ha) hG.1
      b_near := Filter.EventuallyEq.trans (hi.eventually hb) hG.2.1
      U_near := Filter.EventuallyEq.trans (hi.eventually hU) hG.2.2.2.2 }
    B := fun x => E.B (x, q)
    C := fun x => E.C (x, q)
    B_regular := fun i k l => (E.B_regular i k l).comp (contDiff_id.prodMk contDiff_const)
    C_regular := fun k l => (E.C_regular k l).comp (contDiff_id.prodMk contDiff_const)
    B_near := Filter.EventuallyEq.trans (hi.eventually hB) hG.2.2.1
    C_near := Filter.EventuallyEq.trans (hi.eventually hC) hG.2.2.2.1 }

theorem HeatFamilySmoothCoefficients.normalExtension_amplitude (E : HeatFamilySmoothCoefficients)
    {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (ha : E.a =ᶠ[𝓝 (0, frameCoordinateState g c e)] (fun z => (heatFamilyMetric g c P z)⁻¹))
    (hb : E.b =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyDrift g c P)
    (hB : E.B =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyFirst g c P)
    (hC : E.C =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyZero g c P)
    (hU : E.U =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyLeading g c P)
    (m : ℕ) (hm : m ≤ 3) :
    (fun x => E.amplitude m (x, frameCoordinateState g c e)) =
      (E.normalExtension D he P hP hpoint ha hb hB hC hU).amplitude m :=
  E.amplitude_slice m hm (frameCoordinateState g c e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint C4 one-form amplitudes with the center and frame retained. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

structure HeatFamilyOneCoefficients where
  base : HeatFamilySmoothCoefficients
  B : HeatRadialFrameSpace → Fin 4 → Mat4
  C : HeatRadialFrameSpace → Mat4
  B_regular : ∀ i k l, ContDiff ℝ 10 (fun z => B z i k l)
  C_regular : ∀ k l, ContDiff ℝ 10 (fun z => C z k l)

def heatFamilyOneCoefficientSequence (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (B : HeatRadialFrameSpace → Fin 4 → Mat4)
    (C : HeatRadialFrameSpace → Mat4) (U : HeatRadialFrameSpace → ℝ) :
    ℕ → HeatRadialFrameSpace → Mat4
  | 0 => fun z k l => U z * (if k = l then 1 else 0)
  | m + 1 => fun z k l => heatFamilyWeightedAverage m U
      (fun y => -heatFamilyOneOperator a b B C
        (fun w q => heatFamilyOneCoefficientSequence a b B C U m w q l) y k) z

theorem heatFamilyOneCoefficientSequence_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → Mat4) (C : HeatRadialFrameSpace → Mat4)
    (U : HeatRadialFrameSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun z => a z i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun z => b z i)) →
    (∀ i k l, ContDiff ℝ (n + 2 * m : ℕ) (fun z => B z i k l)) →
    (∀ k l, ContDiff ℝ (n + 2 * m : ℕ) (fun z => C z k l)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ z, U z ≠ 0) →
    ∀ k l, ContDiff ℝ n (fun z => heatFamilyOneCoefficientSequence a b B C U m z k l) := by
  induction m with
  | zero =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    simpa only [heatFamilyOneCoefficientSequence, mul_zero, add_zero] using hU.mul
      (contDiff_const (c := if k = l then (1 : ℝ) else 0))
  | succ m ih =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b B C U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (fun i k l => he ▸ hB i k l)
      (fun k l => he ▸ hC k l) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    apply heatFamilyWeightedAverage_contDiff n m U _ (hU.of_le hle) _ hU0
    exact (heatFamilyOneOperator_contDiff n a b B C _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle)
      (fun i k l => (hB i k l).of_le hle) (fun k l => (hC k l).of_le hle)
      (fun q => hreg q l) k).neg

def HeatFamilyOneCoefficients.amplitude (E : HeatFamilyOneCoefficients) :
    ℕ → HeatRadialFrameSpace → Mat4 :=
  heatFamilyOneCoefficientSequence E.base.a E.base.b E.B E.C E.base.U

theorem HeatFamilyOneCoefficients.amplitude_regular (E : HeatFamilyOneCoefficients)
    (m : ℕ) (hm : m ≤ 3) (k l : Fin 4) :
    ContDiff ℝ 4 (fun z => E.amplitude m z k l) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact heatFamilyOneCoefficientSequence_contDiff m 4 E.base.a E.base.b E.B E.C E.base.U
    (fun i j => (E.base.a_regular i j).of_le hle) (fun i => (E.base.b_regular i).of_le hle)
    (fun i k l => (E.B_regular i k l).of_le hle) (fun k l => (E.C_regular k l).of_le hle)
    (E.base.U_regular.of_le hle) (fun z => (E.base.U_pos z).ne') k l


end
end PositiveEinsteinFour.Geometry
end


section

/-! The polynomial and its first spatial derivatives are jointly
continuous in time, normal vector and initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyPolynomial_continuous (u : Fin 4 → HeatRadialFrameSpace → ℝ)
    (hu : ∀ m, Continuous (u m)) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatPolynomial (fun m x => u m (x, z.2.2)) z.1 z.2.1) := by
  have h0 := (hu 0).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have h1 := (hu 1).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have h2 := (hu 2).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have h3 := (hu 3).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  exact ((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
    ((continuous_fst.pow 3).mul h3)

theorem heatFamilyPolynomial_partial_continuous (u : Fin 4 → HeatRadialFrameSpace → ℝ)
    (hu : ∀ m, ContDiff ℝ 1 (u m)) (i : Fin 4) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fourHeatPolynomial (fun m x => u m (x, z.2.2)) z.1) i z.2.1) := by
  have hs (q : CoordinateFrameSpace) (m : Fin 4) :
      ContDiff ℝ 1 (fun x : FourSpace => u m (x, q)) :=
    (hu m).comp (contDiff_id.prodMk contDiff_const)
  have he (z : ℝ × HeatRadialFrameSpace) :
      partialDeriv (fourHeatPolynomial (fun m x => u m (x, z.2.2)) z.1) i z.2.1 =
      fourHeatPolynomial (fun m x => heatFamilyScalarPartial (u m) i (x, z.2.2)) z.1 z.2.1 := by
    rw [fourHeatPolynomial_partial _ (hs z.2.2)]
    unfold fourHeatPolynomial
    simp only [← heatFamilyScalarPartial_slice _ (z.2.1, z.2.2)
      ((hu _).differentiable one_ne_zero _) i]
  simp_rw [he]
  exact heatFamilyPolynomial_continuous _ (fun m =>
    (heatFamilyScalarPartial_contDiff 0 _ (hu m) i).continuous)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar transport amplitudes with joint center and frame dependence. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

def heatFamilyScalarOperator (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (u : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  heatFamilyOneOperator a b (fun _ => 0) (fun _ => 0) (fun y _ => u y) z 0

theorem heatFamilyScalarOperator_contDiff (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (u : HeatRadialFrameSpace → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun z => a z i j))
    (hb : ∀ i, ContDiff ℝ n (fun z => b z i)) (hu : ContDiff ℝ (n + 2 : ℕ) u) :
    ContDiff ℝ n (heatFamilyScalarOperator a b u) :=
  heatFamilyOneOperator_contDiff n a b _ _ _ ha hb
    (fun _ _ _ => contDiff_const) (fun _ _ => contDiff_const) (fun _ => hu) 0

theorem heatFamilyScalarOperator_slice (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (u : HeatRadialFrameSpace → ℝ)
    (hu : ContDiff ℝ 2 u) (z : HeatRadialFrameSpace) :
    heatFamilyScalarOperator a b u z =
      fourHeatLocalOperator (a z) (b z) 0 (fun x => u (x, z.2)) z.1 := by
  unfold heatFamilyScalarOperator
  rw [heatFamilyOneOperator_slice a b _ _ _ (fun _ => hu) z 0]
  simp only [fourHeatOneOperator, fourHeatOneFirst, fourHeatOneZero, Pi.zero_apply,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

def heatFamilyScalarSequence (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (U : HeatRadialFrameSpace → ℝ) :
    ℕ → HeatRadialFrameSpace → ℝ
  | 0 => U
  | m + 1 => heatFamilyWeightedAverage m U
      (fun z => -heatFamilyScalarOperator a b (heatFamilyScalarSequence a b U m) z)

theorem heatFamilyScalarSequence_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (U : HeatRadialFrameSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun z => a z i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun z => b z i)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ z, U z ≠ 0) →
    ContDiff ℝ n (heatFamilyScalarSequence a b U m) := by
  induction m with
  | zero =>
    intro n a b U ha hb hU hU0
    simpa only [heatFamilyScalarSequence, mul_zero, add_zero] using hU
  | succ m ih =>
    intro n a b U ha hb hU hU0
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    exact heatFamilyWeightedAverage_contDiff n m U _ (hU.of_le hle)
      ((heatFamilyScalarOperator_contDiff n a b _ (fun i j => (ha i j).of_le hle)
        (fun i => (hb i).of_le hle) hreg).neg) hU0

def HeatFamilySmoothCoefficients.scalarAmplitude (E : HeatFamilySmoothCoefficients) :
    ℕ → HeatRadialFrameSpace → ℝ := heatFamilyScalarSequence E.a E.b E.U

theorem HeatFamilySmoothCoefficients.scalarAmplitude_regular (E : HeatFamilySmoothCoefficients)
    (m : ℕ) (hm : m ≤ 3) : ContDiff ℝ 4 (E.scalarAmplitude m) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact heatFamilyScalarSequence_contDiff m 4 E.a E.b E.U
    (fun i j => (E.a_regular i j).of_le hle) (fun i => (E.b_regular i).of_le hle)
    (E.U_regular.of_le hle) (fun z => (E.U_pos z).ne')

theorem HeatFamilySmoothCoefficients.scalarAmplitude_slice (E : HeatFamilySmoothCoefficients)
    (m : ℕ) : m ≤ 3 → ∀ q : CoordinateFrameSpace,
      (fun x => E.scalarAmplitude m (x, q)) =
        fourHeatCoefficient (fun x => E.a (x, q)) (fun x => E.b (x, q))
          (fun _ => 0) (fun x => E.U (x, q)) m := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm q
    have hrec := ih (by omega) q
    have hu : ContDiff ℝ 2 (E.scalarAmplitude m) :=
      (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)
    funext x
    change heatFamilyWeightedAverage m E.U
      (fun y => -heatFamilyScalarOperator E.a E.b (E.scalarAmplitude m) y) (x, q) = _
    rw [heatFamilyWeightedAverage_slice]
    have ho : (fun y => -heatFamilyScalarOperator E.a E.b (E.scalarAmplitude m) (y, q)) =
        (fun y => -fourHeatLocalOperator (E.a (y, q)) (E.b (y, q)) 0
          (fourHeatCoefficient (fun z => E.a (z, q)) (fun z => E.b (z, q))
            (fun _ => 0) (fun z => E.U (z, q)) m) y) := by
      funext y
      rw [heatFamilyScalarOperator_slice E.a E.b _ hu, hrec]
    rw [ho]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express compact normal-coordinate tensors in one actual smooth
manifold chart, without changing their frame-bundle values. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {c : M}

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem heatNormalChartMap_source (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source) :
    (C.trans (chartAt FourSpace c)).source = C.source := by
  ext x
  change (x ∈ C.source ∧ C x ∈ (chartAt FourSpace c).source) ↔ x ∈ C.source
  exact ⟨And.left, fun hx => ⟨hx, hCt (C.map_source hx)⟩⟩

omit [T3Space M] in
theorem heatNormalChartTensor_realization (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 2) (f : FrameBundle g) :
    heatNormalFrameTensorLift g c C T f =
    heatNormalFrameTensorLift g c (chartAt FourSpace c).symm
      (heatCompactTensorLift (C.trans (chartAt FourSpace c)) T) f := by
  classical
  let B := C.trans (chartAt FourSpace c)
  by_cases hf : f.base ∈ C.target
  · have hfc := hCt hf
    have hz : chartAt FourSpace c f.base ∈ B.target := by
      change chartAt FourSpace c f.base ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target
      exact ⟨(chartAt FourSpace c).map_source hfc, by rwa [(chartAt FourSpace c).left_inv hfc]⟩
    rw [heatNormalFrameTensorLift, ite_eq_left hf, heatNormalFrameTensorLift,
      ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (heatCompactTensorLift B T (chartAt FourSpace c f.base))
    rw [heatCompactTensorLift, ite_eq_left hz]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (T (C.symm ((chartAt FourSpace c).symm (chartAt FourSpace c f.base))))
    rw [(chartAt FourSpace c).left_inv hfc]
  · rw [heatNormalFrameTensorLift, ite_eq_right hf]
    by_cases hfc : f.base ∈ (chartAt FourSpace c).source
    · have hz : chartAt FourSpace c f.base ∉ B.target := by
        intro h
        apply hf
        have h' : (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target := h.2
        rwa [(chartAt FourSpace c).left_inv hfc] at h'
      rw [heatNormalFrameTensorLift,
        ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
      change (0 : CovariantCoordinates 2) =
        frameTensor _ (heatCompactTensorLift B T (chartAt FourSpace c f.base))
      rw [heatCompactTensorLift, ite_eq_right hz]
      funext a
      simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · rw [heatNormalFrameTensorLift,
        ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hfc)]

local instance heatNormalChartTensorCompact [CompactSpace M] : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalTensor_L2_realization [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] [Nonempty M] {o : FrameOrientation g}
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 2) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source)
    (ha : ∀ z i j, T z ![j,i] = -T z ![i,j]) :
    let F : C(FrameBundle g, TwoTensorEuclidean) :=
      ⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c C T f),
        (PiLp.continuous_toLp 2 _).comp
          (heatNormalFrameTensorLift_continuous g c C T hCt hT hc hs)⟩
    twoFormTensorL2 (twoFormFromContinuousTensor (o := o) F) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F := by
  let B := C.trans (chartAt FourSpace c)
  have hBs : tsupport T ⊆ B.source := by rwa [heatNormalChartMap_source C hCt]
  have hBT : ContinuousOn T B.source := hT.mono (by rw [heatNormalChartMap_source C hCt])
  let H := heatCompactTensorLift B T
  have hH : Continuous H := heatCompactTensorLift_continuous B T hBT hc hBs
  have hK : IsCompact (B '' tsupport T) := hc.image_of_continuousOn (B.continuousOn.mono hBs)
  have hKt : B '' tsupport T ⊆ (chartAt FourSpace c).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (B.map_source (hBs hx)).1
  have hHs := heatCompactTensorLift_tsupport B T hc hBs
  have heq : heatChartTensor g c H hH.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) =
      (⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c C T f),
        (PiLp.continuous_toLp 2 _).comp
          (heatNormalFrameTensorLift_continuous g c C T hCt hT hc hs)⟩ :
        C(FrameBundle g, TwoTensorEuclidean)) := by
    ext f a
    exact congrFun (heatNormalChartTensor_realization C hCt T f).symm a
  simpa only [heq] using heatChartTensor_L2_realization (o := o) c H hH
    (heatCompactTensorLift_skew B T ha) hK hKt hHs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Both terms of the cutoff heat residual vanish outside the spatial
support of the actual cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_residual_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace)
    (hx : x ∉ tsupport χ) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (k l : Fin 6) :
    deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
      fourHeatBundleOperator a b B C
        (fun y q => heatNormalCutoffParametrix E χ t y q l) x k = 0 := by
  have hχ : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  have htime : (fun s => heatNormalCutoffParametrix E χ s x k l) = fun _ => (0 : ℝ) := by
    funext s
    simp only [heatNormalCutoffParametrix, hχ.self_of_nhds, zero_mul]
  have hspace (q : Fin 6) :
      (fun y => heatNormalCutoffParametrix E χ t y q l) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hχ] with y hy
    simp only [heatNormalCutoffParametrix, hy, zero_mul]
  rw [htime, deriv_const, fourHeatBundleOperator_zero_of_locally_zero a b B C hspace k,
    zero_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed matrix parametrix has the identity as its actual
initial distribution. Compact support supplies all amplitude bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_initial {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (f : FourSpace → ℝ)
    (hf : Continuous f) (k l : Fin 6) :
    Tendsto (fun t => ∫ x : FourSpace, heatNormalCutoffParametrix E χ t x k l * f x)
      (𝓝[Ioi 0] 0) (𝓝 ((if k = l then 1 else 0) * f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => χ x * E.amplitude m x k l * f x
  have hu (m : Fin 4) : Continuous (u m) :=
    (hχ.mul (E.amplitude_regular m (by omega) k l).continuous).mul hf
  have huc (m : Fin 4) : HasCompactSupport (u m) := (hχc.mul_right).mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image
      continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hzero : u 0 0 = (if k = l then 1 else 0) * f 0 := by
    change χ 0 * E.amplitude 0 0 k l * f 0 = _
    rw [hχ0, E.amplitude_zero, hU]
    simp only [one_smul, Matrix.one_apply, one_mul]
  rw [hzero] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [heatNormalCutoffParametrix, heatNormalBundleParametrix,
        fourHeatBundlePolynomial, fourHeatPolynomial, u]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual one-form components and the Levi-Civita derivative in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatOneForm_covariant_skew (A : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates 1) (x : FourSpace) (i k : Fin 4)
    (hA : (A i x)ᵀ = -A i x) :
    tensorCovariantDirection A T i x ![k] =
      partialDeriv (fun y => T y ![k]) i x + ∑ l, A i x k l * T x ![l] := by
  have hs (l : Fin 4) : A i x l k = -A i x k l :=
    congrArg (fun B : Mat4 => B k l) hA
  change partialDeriv (fun y => T y ![k]) i x - tensorSlotAction (A i x) (T x) ![k] = _
  rw [tensorSlotAction_one]
  simp_rw [hs, neg_mul, Finset.sum_neg_distrib]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def heatNormalOneFormValue (c : M) (P : FourSpace → CoordinateFrameSpace)
    (u : smoothCovariantFields M 1) (x : FourSpace) (k : Fin 4) : ℝ :=
  frameTensor (P x).2 (covariantFieldCoordinates u.val c (P x).1) ![k]

omit [IsManifold I4 ∞ M] in
theorem heatNormalOneFormValue_regular (n : ℕ) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : smoothCovariantFields M 1)
    (x : FourSpace) (hP : ContDiffAt ℝ n P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target) (k : Fin 4) :
    ContDiffAt ℝ n (fun y => heatNormalOneFormValue c P u y k) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hT (a : Fin 1 → Fin 4) : ContDiffAt ℝ n
      (fun y => covariantFieldCoordinates u.val c (P y).1 a) x :=
    ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => covariantFieldCoordinates u.val c z a) x
      ((u.property c (P x).1 hx a).of_le (by simp)) hP.fst
  unfold heatNormalOneFormValue frameTensor
  exact ContDiffAt.sum (fun a _ => (contDiffAt_prod (fun i _ => hE (a i) (![k] i))).mul (hT a))

theorem heatNormalOneForm_covariant (c : M) (P : FourSpace → CoordinateFrameSpace)
    (u : smoothCovariantFields M 1) (x : FourSpace) (hP : ContDiffAt ℝ 1 P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i k : Fin 4) :
    frameTensor (P x).2 (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      tensorCovariantDirection (connectionMatrix g c) (covariantFieldCoordinates u.val c)
        r (P x).1) ![k] =
      partialDeriv (fun y => heatNormalOneFormValue c P u y k) i x +
        ∑ l, heatNormalFrameConnection g c P i x k l * heatNormalOneFormValue c P u x l := by
  have h := congrArg (fun T : CovariantCoordinates 1 => T ![k])
    (heatNormal_covariant_pullback g c P (covariantFieldCoordinates u.val c) x
      (hP.differentiableAt one_ne_zero)
      (fun a => (u.property c (P x).1 hx a).differentiableAt (by simp)) hG.self_of_nhds i)
  rw [heatOneForm_covariant_skew _ _ x i k
    (heatNormalFrameConnection_skew g c P x (hP.differentiableAt one_ne_zero) hx hG i)] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-order image of a compact C4 normal amplitude is an actual
compact C2 amplitude, so it can be realized in the same global L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneOperatorAmplitude (E : HeatNormalOneExtension D)
    (a : FourSpace → FourSpace) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y l => a y l) x k)

theorem heatNormalOneOperatorAmplitude_regular (E : HeatNormalOneExtension D)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) :
    ContDiff ℝ 2 (heatNormalOneOperatorAmplitude E a) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  apply fourHeatOneOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · exact fun i j => (E.base.a_regular i j).of_le (by norm_num)
  · exact fun i => (E.base.b_regular i).of_le (by norm_num)
  · exact fun i k l => (E.B_regular i k l).of_le (by norm_num)
  · exact fun k l => (E.C_regular k l).of_le (by norm_num)
  · intro l
    exact (contDiff_piLp (p := 2)).mp ha l

theorem heatNormalOneOperatorAmplitude_support (E : HeatNormalOneExtension D)
    (a : FourSpace → FourSpace) :
    tsupport (heatNormalOneOperatorAmplitude E a) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra hn
  have hz : a =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hk (k : Fin 4) : (fun y => a y k) =ᶠ[𝓝 x] (fun _ => 0) :=
    hz.mono fun y hy => by change a y k = 0; rw [hy]; rfl
  apply hx
  apply WithLp.ofLp_injective 2
  funext k
  exact fourHeatOneOperator_zero_of_locally_zero (E.base.a x) (E.base.b x) (E.B x)
    (E.C x) hk k


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual second transport coefficient at the center, with its
quadratic Weitzenböck contribution to the signed trace isolated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

def heatMatrixScalarOperator (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → HeatMat6) (x : FourSpace) : HeatMat6 :=
  fun k l => fourHeatLocalOperator a b 0 (fun y => A y k l) x

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.second_amplitude_center (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    (2 : ℝ) • E.amplitude 2 0 =
      -heatMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0 -
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) * E.amplitude 1 0 := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hB : E.B 0 = fun _ => 0 := by
    funext i
    exact congrFun E.B_near.self_of_nhds i |>.trans (D.bundleFirst_zero i)
  have hC : E.C 0 = twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) :=
    E.C_near.self_of_nhds.trans (D.bundleZero_intrinsic_center he)
  ext k l
  have hrec := fourHeatBundleCoefficient_center 1 E.base.a E.base.b E.B E.C E.base.U
    (by rw [hU]; exact one_ne_zero) k l
  have hrec' : (2 : ℝ) * E.amplitude 2 0 k l =
      -fourHeatBundleOperator (E.base.a 0) (E.base.b 0) (E.B 0) (E.C 0)
        (fun y q => E.amplitude 1 y q l) 0 k := by
    simpa only [HeatNormalBundleExtension.amplitude, Nat.cast_one, one_add_one_eq_two] using hrec
  rw [hB, hC] at hrec'
  simp only [fourHeatBundleOperator, fourHeatBundleFirst, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, fourHeatBundleZero] at hrec'
  change 2 * E.amplitude 2 0 k l =
    -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 (fun y => E.amplitude 1 y k l) 0 -
      ∑ q, twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) k q * E.amplitude 1 0 q l
  linarith only [hrec']

theorem HeatNormalBundleExtension.second_amplitude_signed_trace
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    2 * (twoFormHodgeMatrix * E.amplitude 2 0).trace =
      -(twoFormHodgeMatrix * heatMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0).trace +
      (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace := by
  have h := congrArg (fun A : HeatMat6 => (twoFormHodgeMatrix * A).trace)
    (E.second_amplitude_center he)
  rw [E.first_amplitude_intrinsic_center he] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sub, Matrix.mul_neg,
    Matrix.trace_sub, Matrix.trace_neg, Matrix.mul_one] at h
  rw [heat_actual_potential_signed_trace, mul_zero] at h
  simpa only [zero_sub, sub_neg_eq_add, Matrix.mul_assoc] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second normal tensor derivatives agree with the six scalar
covariant derivatives used in the bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heatNormal_tensor_first {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace)
    (x : FourSpace) (hP : ContDiffAt ℝ 1 P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) i x =
      twoFormTensor (heatNormalTwoFormNabla o c P u i x) := by
  rw [heatNormal_covariant_pullback g c P (twoFormCoordinates o u c) x
    (hP.differentiableAt one_ne_zero)
    (fun a => (hu.coordinates_contDiffAt c (P x).1 hx a).differentiableAt (by simp))
    hG.self_of_nhds i]
  exact heatNormalTwoFormNabla_tensor hu c P x hP hx hG i

theorem heatNormal_tensor_second {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i j : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) i) j x =
      twoFormTensor (WithLp.toLp 2 (fun k => fourHeatCovariantDerivative
        (heatTwoFormConnection g c P)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c P)
          (fun y k => heatNormalTwoFormValue o c P u y k) i) j x k)) := by
  have hP1 := hP.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hp : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 P y := hP1.eventually (by norm_num)
  have ht : ∀ᶠ y in 𝓝 x, (P y).1 ∈ (chartAt FourSpace c).target :=
    hP.continuousAt.fst.preimage_mem_nhds ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hfirst : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) i =ᶠ[𝓝 x]
      (fun y => twoFormTensor (heatNormalTwoFormNabla o c P u i y)) := by
    filter_upwards [hp, ht, hG.eventually_nhds] with y hpy hty hgy
    exact heatNormal_tensor_first hu c P y hpy hty hgy i
  rw [heat_covariant_congr (heatNormalFrameConnection g c P) _ _ x hfirst j]
  have hdet : (P x).2.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hG.self_of_nhds
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
    norm_num at h
  have hn := (heatNormalTwoFormNabla_contDiffAt 1 hu c P x hP hx hdet i).differentiableAt
    one_ne_zero
  rw [heat_twoForm_covariant_tensor (heatNormalFrameConnection g c P)
    (heatNormalTwoFormNabla o c P u i) x hn j
    (heatNormalFrameConnection_skew g c P x (hP.differentiableAt (by norm_num)) hx hG j)]
  have he : (fun y k => heatNormalTwoFormNabla o c P u i y k) =ᶠ[𝓝 x]
      fourHeatCovariantDerivative (heatTwoFormConnection g c P)
        (fun y k => heatNormalTwoFormValue o c P u y k) i := by
    filter_upwards [hp, ht] with y hpy hty
    funext k
    exact heatNormalTwoFormNabla_component hu c P y hpy hty i k
  apply congrArg twoFormTensor
  apply congrArg (WithLp.toLp 2)
  funext k
  exact heat_fourCovariant_congr (heatTwoFormConnection g c P) _ _ x he j k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite signed Gram expansion of the four transport amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

def heatSignedGram (A B : HeatMat6) : ℝ :=
  (twoFormHodgeMatrix * (Aᵀ * B)).trace

theorem heatSignedGram_add_left (A B C : HeatMat6) :
    heatSignedGram (A + B) C = heatSignedGram A C + heatSignedGram B C := by
  simp [heatSignedGram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]

theorem heatSignedGram_add_right (A B C : HeatMat6) :
    heatSignedGram A (B + C) = heatSignedGram A B + heatSignedGram A C := by
  simp [heatSignedGram, Matrix.mul_add, Matrix.trace_add]

theorem heatSignedGram_smul_left (a : ℝ) (A B : HeatMat6) :
    heatSignedGram (a • A) B = a * heatSignedGram A B := by
  simp [heatSignedGram, Matrix.transpose_smul,
    Matrix.trace_smul]

theorem heatSignedGram_smul_right (a : ℝ) (A B : HeatMat6) :
    heatSignedGram A (a • B) = a * heatSignedGram A B := by
  simp [heatSignedGram, Matrix.trace_smul]

theorem heatSignedGram_comm (A B : HeatMat6) : heatSignedGram A B = heatSignedGram B A := by
  unfold heatSignedGram
  calc
    _ = ((twoFormHodgeMatrix * (Aᵀ * B))ᵀ).trace := (Matrix.trace_transpose _).symm
    _ = ((Bᵀ * A) * twoFormHodgeMatrix).trace := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        heat_hodgeMatrix_symmetric]
    _ = _ := Matrix.trace_mul_comm _ _

theorem heatSignedGram_one_left (A : HeatMat6) :
    heatSignedGram 1 A = (twoFormHodgeMatrix * A).trace := by
  simp [heatSignedGram]

theorem heatSignedGram_one_one : heatSignedGram 1 1 = 0 := by
  simpa [heatSignedGram] using twoFormHodgeMatrix_trace

theorem heatSignedGram_polynomial (U t : ℝ) (A B C : HeatMat6) :
    heatSignedGram (U • 1 + t • A + t ^ 2 • B + t ^ 3 • C)
      (U • 1 + t • A + t ^ 2 • B + t ^ 3 • C) =
    2 * t * (U * (twoFormHodgeMatrix * A).trace) + t ^ 2 *
      (2 * U * (twoFormHodgeMatrix * B).trace + heatSignedGram A A +
        t * (2 * U * (twoFormHodgeMatrix * C).trace + 2 * heatSignedGram A B) +
        t ^ 2 * (2 * heatSignedGram A C + heatSignedGram B B) +
        t ^ 3 * (2 * heatSignedGram B C) + t ^ 4 * heatSignedGram C C) := by
  simp only [heatSignedGram_add_left, heatSignedGram_add_right,
    heatSignedGram_smul_left, heatSignedGram_smul_right]
  rw [heatSignedGram_comm A 1, heatSignedGram_comm B 1, heatSignedGram_comm C 1,
    heatSignedGram_comm B A, heatSignedGram_comm C A, heatSignedGram_comm C B]
  simp only [heatSignedGram_one_left, Matrix.mul_one,
    twoFormHodgeMatrix_trace]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation and radial integration commute with the fixed
Hodge-signed trace on the six-dimensional two-form fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise Interval

noncomputable section

private instance heatSignedTraceENorm : ENormedAddMonoid HeatMat6 :=
  @NormedAddGroup.toENormedAddMonoid HeatMat6
    (inferInstanceAs (NormedAddGroup HeatMat6))

def heatSignedTraceLinear : HeatMat6 →ₗ[ℝ] ℝ where
  toFun A := (twoFormHodgeMatrix * A).trace
  map_add' A B := by rw [Matrix.mul_add, Matrix.trace_add]
  map_smul' r A := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]

theorem heatSixPartial_eq_fderiv (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x) (i : Fin 4) :
    heatSixPartial A i x = fderiv ℝ A x (coordinateVector i) := by
  have hd : DifferentiableAt ℝ A x :=
    differentiableAt_pi.mpr (fun k => differentiableAt_pi.mpr (hA k))
  ext k l
  let L₁ : HeatMat6 →L[ℝ] (Fin 6 → ℝ) := ContinuousLinearMap.proj k
  let L₂ : (Fin 6 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj l
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector i))
    ((L₂.comp L₁).hasFDerivAt.comp x hd.hasFDerivAt).fderiv

theorem heatSignedTrace_partial (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x) (i : Fin 4) :
    partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i x =
      (twoFormHodgeMatrix * heatSixPartial A i x).trace := by
  have hd : DifferentiableAt ℝ A x :=
    differentiableAt_pi.mpr (fun k => differentiableAt_pi.mpr (hA k))
  let L := heatSignedTraceLinear.toContinuousLinearMap
  rw [heatSixPartial_eq_fderiv A x hA i]
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector i))
    (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

theorem heatSignedTrace_second (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun y => A y k l) x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i) j x =
      (twoFormHodgeMatrix * heatSixPartial (heatSixPartial A i) j x).trace := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ k l, DifferentiableAt ℝ (fun z => A z k l) y :=
    eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      ((hA k l).eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))))
  have he : partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i =ᶠ[𝓝 x]
      (fun y => (twoFormHodgeMatrix * heatSixPartial A i y).trace) :=
    hn.mono (fun y hy => heatSignedTrace_partial A y hy i)
  rw [fourHeat_partial_germ he j]
  apply heatSignedTrace_partial
  intro k l
  exact (((hA k l).fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero

theorem heatSignedTrace_weightedRadial (m : ℕ) (U : FourSpace → ℝ)
    (F : FourSpace → HeatMat6) (hU : Continuous U) (hF : Continuous F)
    (hU0 : ∀ x, U x ≠ 0) (x : FourSpace) :
    (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
      fourHeatWeightedRadialAverage m U (fun y => F y k l) x)).trace =
      fourHeatWeightedRadialAverage m U (fun y => (twoFormHodgeMatrix * F y).trace) x := by
  let G : ℝ → HeatMat6 := fun s => (s ^ m / U (s • x)) • F (s • x)
  have hs : Continuous (fun s : ℝ => s • x) := continuous_id.smul continuous_const
  have hG : Continuous G :=
    ((continuous_id.pow m).div (hU.comp hs) (fun s => hU0 (s • x))).smul (hF.comp hs)
  have hi : IntervalIntegrable G volume 0 1 := hG.intervalIntegrable 0 1
  have heq : (fun k l => fourHeatWeightedRadialAverage m U (fun y => F y k l) x) =
      U x • ∫ s : ℝ in 0..1, G s := by
    ext k l
    let L₁ : HeatMat6 →L[ℝ] (Fin 6 → ℝ) := ContinuousLinearMap.proj k
    let L₂ : (Fin 6 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj l
    have h := (L₂.comp L₁).intervalIntegral_comp_comm hi
    change (∫ s : ℝ in 0..1, G s k l) = (∫ s : ℝ in 0..1, G s) k l at h
    simp only [fourHeatWeightedRadialAverage, fourHeatRadialAverage, Matrix.smul_apply,
      smul_eq_mul]
    rw [← h]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change s ^ m * (F (s • x) k l / U (s • x)) = s ^ m / U (s • x) * F (s • x) k l
    ring
  rw [heq]
  let L := heatSignedTraceLinear.toContinuousLinearMap
  have h := L.intervalIntegral_comp_comm hi
  change (∫ s : ℝ in 0..1, (twoFormHodgeMatrix * G s).trace) =
    (twoFormHodgeMatrix * ∫ s : ℝ in 0..1, G s).trace at h
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← h]
  change U x * (∫ s : ℝ in 0..1, (twoFormHodgeMatrix * G s).trace) =
    U x * (∫ s : ℝ in 0..1, s ^ m * ((twoFormHodgeMatrix * F (s • x)).trace / U (s • x)))
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [G, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual adjoint relation between d on one-forms and δ on two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem smoothOneFormExterior_adjoint (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) v =
      ∫ e, ∑ j, covariantFieldFramed g u.val e ![j] *
        smoothTwoFormCodifferential v e j ∂canonicalFrameMeasure g o := by
  let μ := canonicalFrameMeasure g o
  let A := fun i j e => covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
    twoFormFramedValue o v.val e ![i,j]
  let B := fun i j e => covariantFieldFramed g u.val e ![j] *
    twoFormFramedCovariantDerivative o v.val e ![i,i,j]
  have hA (i j : Fin 4) : Integrable (A i j) μ :=
    (((continuous_apply _).comp u.property.derivative.continuous_framed).mul
      ((continuous_apply _).comp v.property.continuous_framedValue)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hB (i j : Fin 4) : Integrable (B i j) μ :=
    (((continuous_apply _).comp u.property.continuous_framed).mul
      ((continuous_apply _).comp v.property.continuous_framedCovariantDerivative)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have ha : (∫ e, ∑ i, ∑ j, A i j e ∂μ) = -(∫ e, ∑ j, ∑ i, B i j e ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hA i j)),
      integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hB i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hA _ j),
      integral_finsetSum _ (fun i _ => hB i _)]
    have hg (i j : Fin 4) : (∫ e, A i j e ∂μ) = -(∫ e, B i j e ∂μ) :=
      smoothOneForm_direction_green hRic u v i j
    simp_rw [hg, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have he : smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) v =
      ∫ e, ∑ i, ∑ j, A i j e ∂μ := by
    rw [smoothTwoFormL2Inner_eq_frame]
    apply integral_congr_ae
    filter_upwards [] with e
    exact smoothOneFormExterior_frame_pairing u v e
  rw [he, ha, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with e
  change -(∑ j, ∑ i, B i j e) = ∑ j, covariantFieldFramed g u.val e ![j] *
    -(∑ i, twoFormFramedCovariantDerivative o v.val e ![i,i,j])
  simp only [B, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]

theorem smoothHarmonic_orthogonal_exact (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (v : smoothTwoForms o)
    (hv : v ∈ smoothHarmonicTwoForms) :
    smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) v = 0 := by
  have hc := ((mem_smoothHarmonicTwoForms v).mp hv).2
  rw [smoothOneFormExterior_adjoint hRic]
  simp only [hc, mul_zero, Finset.sum_const_zero, integral_zero]

theorem smoothHarmonic_exact_eq_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hu : smoothOneFormExterior (o := o) u ∈ smoothHarmonicTwoForms) :
    smoothOneFormExterior (o := o) u = 0 :=
  smoothTwoFormL2Inner_definite _ (smoothHarmonic_orthogonal_exact hRic u _ hu)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the first covariant derivatives of actual
smooth one-forms, and their Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormGreenCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem oneForm_derivative_green (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) (i j k l : Fin 4) :
    (∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
      covariantFieldFramed g (covariantFieldDerivative g v.val) e ![k,l]
        ∂canonicalFrameMeasure g o) =
      -(∫ e, covariantFieldFramed g u.val e ![j] *
        covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g v.val))
          e ![i,k,l] ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![j],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g v.val) e ![k,l],
    (continuous_apply _).comp v.property.derivative.continuous_framed⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g v.val))
      e ![i,k,l],
    (continuous_apply _).comp v.property.derivative.derivative.continuous_framed⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![j]
  · intro t e
    exact v.property.derivative.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![k,l]

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneForm_ricci_commutator (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (e : FrameBundle g) (j : Fin 4) :
    (∑ i, (covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![i,j,i] -
      covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![j,i,i])) =
      3 * covariantFieldFramed g u.val e ![j] := by
  have hidx (a b c : Fin 4) : Fin.cons a (Fin.cons b ![c]) = ![a,b,c] := by
    ext k
    fin_cases k <;> rfl
  have hc (i : Fin 4) : covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![i,j,i] -
      covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![j,i,i] =
      -(∑ p, frameCurvature g e.base e.frame i j i p *
        covariantFieldFramed g u.val e ![p]) := by
    simpa only [tensorSlotAction_one, curvatureEndomorphism, hidx] using
      u.property.framed_commutator (g := g) e i j ![i]
  simp_rw [hc]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  have hr (a b : Fin 4) : (∑ i, frameCurvature g e.base e.frame i a b i) =
      if a = b then 3 else 0 := frame_algebraic_ricciThree e.frame hRic a b
  calc
    -(∑ p, ∑ i, frameCurvature g e.base e.frame i j i p * covariantFieldFramed g u.val e ![p]) =
        ∑ p, (∑ i, frameCurvature g e.base e.frame i j p i) *
          covariantFieldFramed g u.val e ![p] := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [frameCurvature_last_skew e.frame i j i p]
      ring
    _ = 3 * covariantFieldFramed g u.val e ![j] := by
      simp only [hr j, ite_mul, zero_mul]
      simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeat_rate_weight_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : ScalarBaseEigenIndex g o d =>
      scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d t i) := by
  have ht2 := half_pos ht
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (scalarBaseHeatRate_nonneg g o d i)
    (Real.exp_pos _).le) _
    ((scalarHeat_weight_summable g o d (t / 2) ht2).mul_left
      (Real.exp (t / 2 : ℝ≥0) / (t / 2 : ℝ≥0)))
  intro i
  have hw : 0 ≤ scalarBaseHeatWeight g o d (t / 2) i := (Real.exp_pos _).le
  have hm : 0 ≤ i.1.val⁻¹ := (inv_pos.mpr (scalarBaseResolvent_eigenvalue g o d i.1.property).1).le
  have hb := scalarBaseHeatLiftWeight_bound g o d (t / 2) ht2 i
  rw [abs_of_nonneg (mul_nonneg hm hw)] at hb
  calc
    _ = scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d (t / 2) i ^ 2 :=
      congrArg (scalarBaseHeatRate g o d i * ·) (scalarBaseHeatWeight_half_sq g o d t i).symm
    _ = (scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d (t / 2) i) *
        scalarBaseHeatWeight g o d (t / 2) i := by ring
    _ ≤ (i.1.val⁻¹ * scalarBaseHeatWeight g o d (t / 2) i) *
        scalarBaseHeatWeight g o d (t / 2) i := by
      apply mul_le_mul_of_nonneg_right _ hw
      apply mul_le_mul_of_nonneg_right _ hw
      unfold scalarBaseHeatRate
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hw

def scalarBaseHeatRealTerm (f : Lp ℝ 2 (normalizedVolume g))
    (i : ScalarBaseEigenIndex g o d) (s : ℝ) : Lp ℝ 2 (normalizedVolume g) :=
  (Real.exp (-s * scalarBaseHeatRate g o d i) * inner ℝ (scalarBaseEigenvector g o d i) f) •
    scalarBaseEigenvector g o d i

def scalarBaseHeatRealDerivativeTerm (f : Lp ℝ 2 (normalizedVolume g))
    (i : ScalarBaseEigenIndex g o d) (s : ℝ) : Lp ℝ 2 (normalizedVolume g) :=
  (-scalarBaseHeatRate g o d i * Real.exp (-s * scalarBaseHeatRate g o d i) *
    inner ℝ (scalarBaseEigenvector g o d i) f) • scalarBaseEigenvector g o d i

theorem scalarBaseHeatRealDerivativeTerm_bound (ε : ℝ≥0)
    (f : Lp ℝ 2 (normalizedVolume g)) (i : ScalarBaseEigenIndex g o d) (s : ℝ) (hs : ε ≤ s) :
    ‖scalarBaseHeatRealDerivativeTerm g o d f i s‖ ≤
      (scalarBaseHeatRate g o d i * scalarBaseHeatWeight g o d ε i) * ‖f‖ := by
  have hr := scalarBaseHeatRate_nonneg g o d i
  have hc : ‖inner ℝ (scalarBaseEigenvector g o d i) f‖ ≤ ‖f‖ := by
    simpa only [(scalarBaseEigenvector_orthonormal g o d).1 i, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (scalarBaseEigenvector g o d i) f
  have hw : Real.exp (-s * scalarBaseHeatRate g o d i) ≤ scalarBaseHeatWeight g o d ε i := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simp only [scalarBaseHeatRealDerivativeTerm, norm_smul, norm_mul,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg hr, abs_of_pos (Real.exp_pos _),
    (scalarBaseEigenvector_orthonormal g o d).1 i, mul_one]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hw hr) hc (abs_nonneg _)
    (mul_nonneg hr (Real.exp_pos _).le)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar heat output in H1, with its exact smooth realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatH1Lift (t : ℝ≥0) (ht : 0 < t) : Lp ℝ 2 (normalizedVolume g) →L[ℝ] scalarH1 d :=
  (scalarBaseShiftedSolution g o d).comp (scalarBaseHeatLiftSource g o d t ht)

theorem scalarHeatH1Lift_value (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarH1BaseValue g o d (scalarHeatH1Lift d t ht f) = scalarBaseHeat g o d t f :=
  scalarBaseHeatLiftSource_resolvent g o d t ht f

theorem scalarHeatH1Lift_smooth (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (normalizedVolume g))
    (u : SmoothScalar (M := M)) (hu : scalarBaseHeat g o d t f = smoothScalarBaseL2 g u) :
    scalarHeatH1Lift d t ht f = smoothScalarToH1 d u := by
  apply scalarH1BaseValue_injective g o d
  rw [scalarHeatH1Lift_value, scalarH1BaseValue_smooth, hu]

theorem scalarHeatH1Lift_eigen (t : ℝ≥0) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    scalarHeatH1Lift d t ht (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i • smoothScalarToH1 d (scalarBaseEigenfunction g o d i) := by
  apply scalarH1BaseValue_injective g o d
  rw [scalarHeatH1Lift_value, map_smul, scalarH1BaseValue_smooth,
    ← scalarBaseEigenfunction_L2, scalarBaseHeat_eigenvector]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat kernel is obtained from actual evaluation columns.
Its integral action, symmetry and diagonal follow from the semigroup law. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance scalarKernel_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem scalarHeatToContinuous_add (t s : ℝ≥0) (ht : 0 < t) (hs : 0 < s)
    (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarHeatToContinuous g o d (t + s) (add_pos ht hs) f =
      scalarHeatToContinuous g o d t ht (scalarBaseHeat g o d s f) := by
  let := normalizedVolume_isOpenPosMeasure g
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)
  rw [scalarHeatToContinuous_L2, scalarHeatToContinuous_L2, scalarBaseHeat_add]

theorem scalarHeatColumn_add (t s : ℝ≥0) (ht : 0 < t) (hs : 0 < s) (x : M) :
    scalarHeatColumn g o d (t + s) (add_pos ht hs) x =
      scalarBaseHeat g o d s (scalarHeatColumn g o d t ht x) := by
  apply ext_inner_right ℝ
  intro f
  rw [scalarHeatColumn_pairing, scalarBaseHeat_selfAdjoint, scalarHeatColumn_pairing]
  exact congrArg (fun F : C(M, ℝ) => F x) (scalarHeatToContinuous_add g o d t s ht hs f)

def scalarHeatKernel (t : ℝ≥0) (ht : 0 < t) (x y : M) : ℝ :=
  scalarHeatToContinuous g o d (t / 2) (half_pos ht)
    (scalarHeatColumn g o d (t / 2) (half_pos ht) x) y

theorem scalarHeatKernel_pairing (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    scalarHeatKernel g o d t ht x y = inner ℝ
      (scalarHeatColumn g o d (t / 2) (half_pos ht) y)
      (scalarHeatColumn g o d (t / 2) (half_pos ht) x) :=
  (scalarHeatColumn_pairing g o d (t / 2) (half_pos ht) y _).symm

theorem scalarHeatKernel_symm (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    scalarHeatKernel g o d t ht x y = scalarHeatKernel g o d t ht y x := by
  rw [scalarHeatKernel_pairing, scalarHeatKernel_pairing]
  exact real_inner_comm _ _

theorem scalarHeatKernel_diagonal (t : ℝ≥0) (ht : 0 < t) (x : M) :
    scalarHeatKernel g o d t ht x x = scalarHeatDiagonal g o d t ht x := by
  rw [scalarHeatKernel_pairing, real_inner_self_eq_norm_sq]
  rfl

theorem scalarHeatKernel_L2 (t : ℝ≥0) (ht : 0 < t) (x : M) :
    ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      (scalarHeatToContinuous g o d (t / 2) (half_pos ht)
        (scalarHeatColumn g o d (t / 2) (half_pos ht) x)) =
      scalarHeatColumn g o d t ht x := by
  rw [scalarHeatToContinuous_L2]
  simpa only [add_halves] using
    (scalarHeatColumn_add g o d (t / 2) (t / 2) (half_pos ht) (half_pos ht) x).symm

theorem scalarHeatKernel_action (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (normalizedVolume g)) (x : M) :
    (∫ y, scalarHeatKernel g o d t ht x y * f y ∂normalizedVolume g) =
      scalarHeatToContinuous g o d t ht f x := by
  rw [← scalarHeatColumn_pairing g o d t ht x f]
  rw [← scalarHeatKernel_L2 g o d t ht x, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    (scalarHeatToContinuous g o d (t / 2) (half_pos ht)
      (scalarHeatColumn g o d (t / 2) (half_pos ht) x))] with y hy
  rw [hy]
  simp only [RCLike.inner_apply', conj_trivial, scalarHeatKernel]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity and strict positivity of the actual subcritical minimizer.
Its H1 forcing is constructed, then local H3 and Fourier inversion give the
continuous representative needed by the proved strong minimum principle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance minimumContinuity_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalar_subcritical_minimum_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ∃ f : M → ℝ, Continuous f ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] f := by
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  obtain ⟨S, hS⟩ := scalar_minimum_H1_source g o d hp hp4 w hw hm hmin
  have hlocal (x : M) : ∃ U : Set M, ∃ F : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContinuousOn F U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] F := by
    let z₀ : ChartTarget x := ⟨chartAt FourSpace x x,
      (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)⟩
    obtain ⟨r, hr, ht, z, he, hreg⟩ := scalar_local_weighted_H3 g o d S u hS x z₀
    obtain ⟨G, hG, hzG⟩ := scalar_local_H3_continuous_real_representative z hreg
    have he' : (fun y => chartVolumeDensity g x (scalarRescaledPoint g x z₀ r y) *
        b ((chartAt FourSpace x).symm (scalarRescaledPoint g x z₀ r y))) =ᵐ[
          volume.restrict (ball (0 : FourSpace) (1 / 4))] G := by
      have he₁ : (fun y => chartVolumeDensity g x (scalarRescaledPoint g x z₀ r y) *
          b ((chartAt FourSpace x).symm (scalarRescaledPoint g x z₀ r y))) =ᵐ[
            volume.restrict (ball (0 : FourSpace) (1 / 4))] z :=
        ae_restrict_of_ae_restrict_of_subset
          (ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) he
      exact he₁.trans hzG
    obtain ⟨U, hU, hxU, _, H, hH, heH⟩ := scalar_chart_continuous_unweight g x z₀ r hr
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) b ht G hG he'
    let W := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' U
    refine ⟨W, fun y => H (chartAt FourSpace x y),
      (chartAt FourSpace x).isOpen_inter_preimage hU, ⟨mem_chart_source FourSpace x, hxU⟩,
      ?_, scalar_chart_representative_ae g x U hU b H heH⟩
    intro y hy
    exact ((hH.continuousAt (hU.mem_nhds hy.2)).comp
      ((chartAt FourSpace x).continuousAt hy.1)).continuousWithinAt
  obtain ⟨f, hf, hfb⟩ := scalar_continuous_representative_of_local g b hlocal
  exact ⟨f, hf, (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p)
    (by exact_mod_cast hp4.le) w).trans hfb.symm⟩

variable [PreconnectedSpace M]

theorem scalar_subcritical_minimum_positive_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hn : ∀ᵐ x ∂normalizedVolume g,
      0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) :
    ∃ f : M → ℝ, Continuous f ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] f ∧ ∀ x, 0 < f x := by
  obtain ⟨f, hf, hrep⟩ := scalar_subcritical_minimum_continuous g o d hp hp4 w hw hm hmin
  exact ⟨f, hf, hrep,
    scalar_subcritical_minimum_positive_of_continuous g o d hp hp4 w hw hm hmin hn f hf hrep⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth harmonic two-forms are preserved by Hodge star,
with finite positive and negative summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormDeRhamEnergy_hodge (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy (smoothTwoFormHodge o u) = smoothTwoFormDeRhamEnergy u := by
  rw [smoothTwoForm_Weitzenbock hRic, smoothTwoForm_Weitzenbock hRic,
    smoothTwoFormCovariantEnergy_hodge, smoothTwoFormL2Inner_hodge_self]
  congr 2
  unfold smoothTwoFormL2Inner
  apply integral_congr_ae
  filter_upwards [] with x
  change inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩)
    (twoFormHodge (u.val x))) (twoFormHodge (u.val x)) =
      inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩)
        (u.val x)) (u.val x)
  rw [twoFormMetricCurvatureAction_hodge hRic]
  exact twoFormHodge.inner_map_map _ _

theorem smoothHarmonicTwoForms_hodge (hRic : RicciThree g) (u : smoothTwoForms o)
    (hu : u ∈ smoothHarmonicTwoForms) : smoothTwoFormHodge o u ∈ smoothHarmonicTwoForms := by
  apply (smoothTwoFormDeRhamEnergy_eq_zero_iff _).mp
  rw [smoothTwoFormDeRhamEnergy_hodge hRic]
  exact smoothHarmonicTwoForm_energy_zero u hu

def smoothHarmonicHodge (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] smoothHarmonicTwoForms (o := o) where
  toFun u := ⟨smoothTwoFormHodge o u.val, smoothHarmonicTwoForms_hodge hRic u.val u.property⟩
  map_add' u v := Subtype.ext (map_add (smoothTwoFormHodge o) u.val v.val)
  map_smul' r u := Subtype.ext (map_smul (smoothTwoFormHodge o) r u.val)

theorem smoothHarmonicHodge_involutive (hRic : RicciThree g) :
    Function.Involutive (smoothHarmonicHodge (o := o) hRic) := by
  intro u
  apply Subtype.ext
  exact smoothTwoFormHodge_involutive o u.val

local instance : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def smoothHarmonicPositive (hRic : RicciThree g) :
    Submodule ℝ (smoothHarmonicTwoForms (o := o)) :=
  Module.End.eigenspace (R := ℝ) (M := smoothHarmonicTwoForms (o := o)) (smoothHarmonicHodge (o := o) hRic) (1 : ℝ)

def smoothHarmonicNegative (hRic : RicciThree g) :
    Submodule ℝ (smoothHarmonicTwoForms (o := o)) :=
  Module.End.eigenspace (R := ℝ) (M := smoothHarmonicTwoForms (o := o)) (smoothHarmonicHodge (o := o) hRic) (-1 : ℝ)

instance smoothHarmonicPositive_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicPositive (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  infer_instance

instance smoothHarmonicNegative_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicNegative (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  infer_instance

def smoothHarmonicPlus (hRic : RicciThree g) (u : smoothHarmonicTwoForms (o := o)) :
    smoothHarmonicPositive (o := o) hRic :=
  ⟨(2 : ℝ)⁻¹ • (u + smoothHarmonicHodge (o := o) hRic u), by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [map_smul, map_add, smoothHarmonicHodge_involutive, one_smul]
    rw [add_comm]⟩

def smoothHarmonicMinus (hRic : RicciThree g) (u : smoothHarmonicTwoForms (o := o)) :
    smoothHarmonicNegative (o := o) hRic :=
  ⟨(2 : ℝ)⁻¹ • (u - smoothHarmonicHodge (o := o) hRic u), by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [map_smul, (smoothHarmonicHodge (o := o) hRic).map_sub,
      smoothHarmonicHodge_involutive, neg_one_smul]
    module⟩

theorem smoothHarmonic_decomposition (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o)) :
    (smoothHarmonicPlus hRic u).val + (smoothHarmonicMinus hRic u).val = u := by
  change (2 : ℝ)⁻¹ • (u + smoothHarmonicHodge (o := o) hRic u) +
    (2 : ℝ)⁻¹ • (u - smoothHarmonicHodge (o := o) hRic u) = u
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic codifferential density and the four-dimensional Hodge
splitting of the actual de Rham energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormCodiffTensor_squareNorm (A : CovariantCoordinates 3) :
    frameTensorSquareNorm (twoFormCodiffTensor A) =
      ∑ k, twoFormCodiffComponent (fun p q r => A ![p,q,r]) k ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro k _
  change (-∑ i, A ![i,i,k]) * (-∑ i, A ![i,i,k]) = (-∑ i, A ![i,i,k]) ^ 2
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormCodiffDensity (u : smoothTwoForms o) : M → ℝ :=
  covariantFieldNormSq g (smoothTwoFormCodifferentialField u).val

theorem twoFormCodiffDensity_eq_frame (u : smoothTwoForms o) (e : FrameBundle g) :
    twoFormCodiffDensity u e.base =
      frameTensorSquareNorm (twoFormCodiffTensor (twoFormFramedCovariantDerivative o u.val e)) :=
  (covariantFieldNormSq_eq_frame (smoothTwoFormCodifferentialField u).val e).trans
    (congrArg frameTensorSquareNorm (smoothTwoFormCodifferentialField_framed u e))

theorem twoFormCodiffDensity_continuous (u : smoothTwoForms o) :
    Continuous (twoFormCodiffDensity u) :=
  (smoothTwoFormCodifferentialField u).property.continuous_normSq

theorem twoFormDeRhamDensity_hodge (u : smoothTwoForms o) (x : M) :
    twoFormDeRhamDensity o u.val x =
      twoFormCodiffDensity u x + twoFormCodiffDensity (smoothTwoFormHodge o u) x := by
  obtain ⟨S, hS, U, hU, hxU, hUt, hp⟩ := twoForm_positive_chart o x
  let z := chartAt FourSpace x x
  let e := chartGramSection g x S hS ⟨z, hUt hxU⟩
  have hb : e.base = x := (chartAt FourSpace x).left_inv (mem_chart_source FourSpace x)
  rw [← hb, twoFormDeRhamDensity_eq_frame, twoFormCodiffDensity_eq_frame u e,
    twoFormCodiffDensity_eq_frame (smoothTwoFormHodge o u) e]
  have hplain := u.property.gramCovariantDerivative x S hS U hU hUt hp z hxU
  have hstar := (smoothTwoFormHodge o u).property.gramCovariantDerivative
    x S hS U hU hUt hp z hxU
  rw [hplain, hstar]
  have hr : twoFormLocalNablaRows (g := g) x S
      (twoFormChartValue o (smoothTwoFormHodge o u).val x S hS) z =
      fun i => twoFormHodge (twoFormLocalNablaRows (g := g) x S
        (twoFormChartValue o u.val x S hS) z i) := by
    funext i
    exact u.property.localNablaRows_hodge x S hS U hU hUt hp z hxU i
  rw [hr, twoFormCodiffTensor_squareNorm, twoFormCodiffTensor_squareNorm]
  exact twoForm_rows_deRham_hodge _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differentiated codifferential and the actual exact dδ term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormCodifferentialField_derivative (hRic : RicciThree g)
    (u : smoothTwoForms o) (e : FrameBundle g) (i k : Fin 4) :
    covariantFieldFramed g (covariantFieldDerivative g (smoothTwoFormCodifferentialField u).val)
      e ![i,k] = -(∑ j, twoFormFramedSecondDerivative o u.val e ![i,j,j,k]) := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hs := (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    u.property.framedCovariant_parallel_derivative γ 0 i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,j,k])).neg
  have heq : (fun t => -(∑ j, twoFormFramedCovariantDerivative o u.val (γ t) ![j,j,k])) =
      fun t => covariantFieldFramed g (smoothTwoFormCodifferentialField u).val (γ t) ![k] := by
    funext t
    exact (smoothTwoFormCodifferentialField_component u (γ t) k).symm
  change HasDerivAt (fun t => -(∑ j,
    twoFormFramedCovariantDerivative o u.val (γ t) ![j,j,k])) _ 0 at hs
  rw [heq] at hs
  have hd := (smoothTwoFormCodifferentialField u).property.parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![k]
  have h := hd.unique hs
  rw [hzero] at h
  exact h

def smoothTwoFormDDelta (u : smoothTwoForms o) : smoothTwoForms o :=
  smoothOneFormExterior (smoothTwoFormCodifferentialField u)

theorem smoothTwoFormDDelta_component (hRic : RicciThree g) (u : smoothTwoForms o)
    (e : FrameBundle g) (i j : Fin 4) :
    twoFormFramedValue o (smoothTwoFormDDelta u).val e ![i,j] =
      -(∑ k, twoFormFramedSecondDerivative o u.val e ![i,k,k,j]) +
        ∑ k, twoFormFramedSecondDerivative o u.val e ![j,k,k,i] := by
  have he := smoothOneFormExterior_framed (o := o) (smoothTwoFormCodifferentialField u) e i j
  rw [smoothTwoFormCodifferentialField_derivative hRic,
    smoothTwoFormCodifferentialField_derivative hRic] at he
  exact he.trans (by ring)

theorem smoothTwoFormDDelta_closed (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormExterior (smoothTwoFormDDelta u) = 0 :=
  smoothOneFormExterior_closed hRic (smoothTwoFormCodifferentialField u)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form codifferential as a linear map to smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormCodifferentialField_add (u v : smoothTwoForms o) :
    smoothTwoFormCodifferentialField (u + v) =
      smoothTwoFormCodifferentialField u + smoothTwoFormCodifferentialField v := by
  apply Subtype.ext
  apply covariantField_eq_of_framed (g := g)
  intro e
  simp only [Submodule.coe_add, covariantFieldFramed_add]
  funext a
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  rw [ha]
  simp only [Pi.add_apply, smoothTwoFormCodifferentialField_component]
  exact congrFun (congrFun (map_add (smoothTwoFormCodifferential (o := o)) u v) e) (a 0)

theorem smoothTwoFormCodifferentialField_smul (r : ℝ) (u : smoothTwoForms o) :
    smoothTwoFormCodifferentialField (r • u) = r • smoothTwoFormCodifferentialField u := by
  apply Subtype.ext
  apply covariantField_eq_of_framed (g := g)
  intro e
  simp only [Submodule.coe_smul, covariantFieldFramed_smul]
  funext a
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  rw [ha]
  simp only [Pi.smul_apply, smul_eq_mul, smoothTwoFormCodifferentialField_component]
  exact congrFun (congrFun (map_smul (smoothTwoFormCodifferential (o := o)) r u) e) (a 0)

def smoothTwoFormCodifferentialLinear :
    smoothTwoForms o →ₗ[ℝ] smoothCovariantFields M 1 where
  toFun := smoothTwoFormCodifferentialField
  map_add' := smoothTwoFormCodifferentialField_add
  map_smul' := smoothTwoFormCodifferentialField_smul

end
end PositiveEinsteinFour.Geometry
end


section

/-! Spectral bounds and the actual weak Hodge equation for eigenvectors
of the shifted resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedResolvent_norm_le (hRic : RicciThree g) (f : TwoFormL2 o) :
    ‖twoFormShiftedResolvent hRic f‖ ≤ ‖f‖ := by
  have he := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  have hQ := twoFormHodgeForm_nonneg hRic (twoFormShiftedSolution hRic f)
  rw [real_inner_self_eq_norm_sq] at he
  have hC := real_inner_le_norm f (twoFormShiftedResolvent hRic f)
  change ‖twoFormH1ToL2 (twoFormShiftedSolution hRic f)‖ ≤ ‖f‖
  change inner ℝ f (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) ≤
    ‖f‖ * ‖twoFormH1ToL2 (twoFormShiftedSolution hRic f)‖ at hC
  nlinarith only [he, hQ, hC, norm_nonneg f,
    norm_nonneg (twoFormH1ToL2 (twoFormShiftedSolution hRic f))]

theorem twoFormShiftedResolvent_pos (hRic : RicciThree g) (f : TwoFormL2 o) (hf : f ≠ 0) :
    0 < inner ℝ (twoFormShiftedResolvent hRic f) f := by
  have hn : twoFormShiftedResolvent hRic f ≠ 0 := by
    intro h
    exact hf (twoFormShiftedResolvent_injective hRic (h.trans (map_zero _).symm))
  have he := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  have hQ := twoFormHodgeForm_nonneg hRic (twoFormShiftedSolution hRic f)
  have hp : 0 < inner ℝ (twoFormShiftedResolvent hRic f) (twoFormShiftedResolvent hRic f) :=
    by simpa only [real_inner_self_eq_norm_sq, sq_pos_iff, norm_ne_zero_iff] using hn
  have hc := real_inner_comm f (twoFormShiftedResolvent hRic f)
  change twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic f) +
    inner ℝ (twoFormShiftedResolvent hRic f) (twoFormShiftedResolvent hRic f) =
      inner ℝ f (twoFormShiftedResolvent hRic f) at he
  linarith only [he, hQ, hp, hc]

theorem twoFormShiftedResolvent_eigenvalue (hRic : RicciThree g) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ) :
    0 < μ ∧ μ ≤ 1 := by
  obtain ⟨f, hf⟩ := hμ.exists_hasEigenvector
  have he := Module.End.mem_eigenspace_iff.mp hf.1
  change twoFormShiftedResolvent hRic f = μ • f at he
  have hp := twoFormShiftedResolvent_pos hRic f hf.2
  rw [he, real_inner_smul_left] at hp
  have hμpos : 0 < μ := by nlinarith only [hp, real_inner_self_nonneg (x := f)]
  have hn := twoFormShiftedResolvent_norm_le hRic f
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos] at hn
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf.2
  exact ⟨hμpos, by nlinarith only [hn, hfpos]⟩

theorem twoFormResolvent_eigenvector_weak (hRic : RicciThree g) {μ : ℝ} {f : TwoFormL2 o}
    (hf : Module.End.HasEigenvector (twoFormShiftedResolvent hRic).toLinearMap μ f) :
    ∃ u : TwoFormH1 o, twoFormH1ToL2 u = f ∧
      ∀ v : TwoFormH1 o, twoFormHodgeForm u v =
        (μ⁻¹ - 1) * inner ℝ f (twoFormH1ToL2 v) := by
  have hm : μ ≠ 0 := ne_of_gt
    (twoFormShiftedResolvent_eigenvalue hRic (Module.End.hasEigenvalue_of_hasEigenvector hf)).1
  have he := Module.End.mem_eigenspace_iff.mp hf.1
  change twoFormShiftedResolvent hRic f = μ • f at he
  let u := μ⁻¹ • twoFormShiftedSolution hRic f
  have hu : twoFormH1ToL2 u = f := by
    change twoFormH1ToL2 (μ⁻¹ • twoFormShiftedSolution hRic f) = f
    rw [map_smul]
    change μ⁻¹ • twoFormShiftedResolvent hRic f = f
    rw [he, smul_smul, inv_mul_cancel₀ hm, one_smul]
  refine ⟨u, hu, fun v => ?_⟩
  have hw := twoFormShiftedSolution_weak hRic f v
  change twoFormHodgeForm (twoFormShiftedSolution hRic f) v +
    inner ℝ (twoFormShiftedResolvent hRic f) (twoFormH1ToL2 v) = _ at hw
  rw [he, real_inner_smul_left] at hw
  change twoFormHodgeForm (μ⁻¹ • twoFormShiftedSolution hRic f) v = _
  rw [twoFormHodgeForm_smul_left]
  calc
    _ = μ⁻¹ * ((1 - μ) * inner ℝ f (twoFormH1ToL2 v)) := by
      congr 1
      linarith only [hw]
    _ = _ := by field_simp [hm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak Hodge equation has an actual L2 forcing for the rough
resolvent. This is the equation used in local regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeEquation_rough_iff (u : TwoFormH1 o) (f : TwoFormL2 o) :
    (∀ v : TwoFormH1 o, twoFormHodgeForm u v = inner ℝ f (twoFormH1ToL2 v)) ↔
      u = twoFormRoughSolution (f + twoFormWeitzenbockPotential (twoFormH1ToL2 u)) := by
  constructor
  · intro hu
    apply twoFormRoughSolution_unique
    intro v
    have he := hu v
    unfold twoFormHodgeForm at he
    rw [inner_add_left]
    linarith only [he]
  · intro hu v
    have he := twoFormRoughSolution_weak
      (f + twoFormWeitzenbockPotential (twoFormH1ToL2 u)) v
    rw [← hu, inner_add_left] at he
    unfold twoFormHodgeForm
    linarith only [he]

theorem twoFormHodgeEquation_smooth_test (hRic : RicciThree g)
    (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : ∀ v : TwoFormH1 o, twoFormHodgeForm u v = inner ℝ f (twoFormH1ToL2 v))
    (v : SmoothH1TwoForm o) :
    twoFormGreenDual hRic (smoothH1ToL2 v) (twoFormH1ToL2 u) =
      inner ℝ (f + twoFormWeitzenbockPotential (twoFormH1ToL2 u))
        (smoothTwoFormToL2 (smoothH1ToL2 v)) := by
  rw [← twoFormH1_inner_smooth hRic]
  have he := twoFormRoughSolution_weak
    (f + twoFormWeitzenbockPotential (twoFormH1ToL2 u)) (smoothTwoFormToH1 v)
  rw [← (twoFormHodgeEquation_rough_iff u f).mp hu, twoFormH1ToL2_smooth] at he
  exact he

theorem twoFormWeakHarmonic_rough (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) := by
  apply twoFormRoughSolution_unique
  exact (twoFormWeakPotentialKernel_weak _ _).mp hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact amplitudes have globally C1 covariant fluxes even though the
normal coefficients are regular only inside the chosen chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantFlux_contDiff
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (i : Fin 4) (k : Fin 6) :
    ContDiff ℝ 1 (fun x => fourHeatCovariantFlux A a ρ u i x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact fourHeatCovariantFlux_contDiffAt A a ρ u x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (fun l => (hu l).contDiffAt)
  · have hsub : tsupport (fun y => fourHeatCovariantFlux A a ρ u i y k) ⊆ U :=
      (fourHeatCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
    have hn : x ∉ tsupport (fun y => fourHeatCovariantFlux A a ρ u i y k) :=
      fun hh => hx (hsub hh)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hN := (isClosed_tsupport (fun y => fourHeatCovariantFlux A a ρ u i y k)).isOpen_compl.mem_nhds hn
    filter_upwards [hN] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantFlux A a ρ u i y k) hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOneCovariantDerivative_scalar
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (f : FourSpace → ℝ) (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ (fun y => u y k) x) :
    fourHeatOneCovariantDerivative A (fun y l => f y * u y l) i x k =
      partialDeriv f i x * u x k + f x * fourHeatOneCovariantDerivative A u i x k := by
  change partialDeriv (fun y => f y * u y k) i x +
    (∑ l, A i x k l * (f x * u x l)) = _
  rw [scalar_partial_product f (fun y => u y k) x hf hu i]
  have he : (∑ l, A i x k l * (f x * u x l)) =
      f x * ∑ l, A i x k l * u x l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  change _ = partialDeriv f i x * u x k +
    f x * (partialDeriv (fun y => u y k) i x + ∑ l, A i x k l * u x l)
  ring

theorem fourHeatOneCovariantDerivative_differentiable
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hA : ∀ l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    DifferentiableAt ℝ (fun y => fourHeatOneCovariantDerivative A u i y k) x := by
  apply DifferentiableAt.add
  · exact (((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  · exact DifferentiableAt.fun_sum fun l _ =>
      (hA l).mul ((hu l).differentiableAt (by norm_num))

theorem fourHeatOneCovariantDerivative_sum_four
    (A : Fin 4 → FourSpace → Mat4) (w : Fin 4 → FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (j : Fin 4) (k : Fin 4)
    (hw : ∀ i, DifferentiableAt ℝ (fun y => w i y k) x) :
    fourHeatOneCovariantDerivative A (fun y l => ∑ i, w i y l) j x k =
      ∑ i, fourHeatOneCovariantDerivative A (w i) j x k := by
  have hd : partialDeriv (fun y => ∑ i, w i y k) j x =
      ∑ i, partialDeriv (fun y => w i y k) j x := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => w i y k) (fun i _ => hw i),
      _root_.sum_apply]
  change partialDeriv (fun y => ∑ i, w i y k) j x +
    (∑ l, A j x k l * ∑ i, w i x l) = _
  rw [hd]
  simp only [fourHeatOneCovariantDerivative, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun l i => A j x k l * w i x l)]

def fourHeatOneCovariantFlux (A : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (i : Fin 4) (x : FourSpace) (k : Fin 4) : ℝ :=
  ∑ j, (ρ x * a x i j) * fourHeatOneCovariantDerivative A u j x k

theorem fourHeatOneCovariantFlux_derivative
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i j : Fin 4) (k : Fin 4)
    (hA : ∀ l q, DifferentiableAt ℝ (fun y => A l y k q) x)
    (ha : ∀ l, DifferentiableAt ℝ (fun y => a y i l) x)
    (hρ : DifferentiableAt ℝ ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    fourHeatOneCovariantDerivative A (fourHeatOneCovariantFlux A a ρ u i) j x k =
      ∑ l, (partialDeriv (fun y => ρ y * a y i l) j x *
        fourHeatOneCovariantDerivative A u l x k +
        (ρ x * a x i l) * fourHeatOneCovariantDerivative A
          (fourHeatOneCovariantDerivative A u l) j x k) := by
  unfold fourHeatOneCovariantFlux
  rw [fourHeatOneCovariantDerivative_sum_four A _ x j k (fun l =>
    (hρ.mul (ha l)).mul (fourHeatOneCovariantDerivative_differentiable A u x l k (hA l) hu))]
  apply Finset.sum_congr rfl
  intro l _
  exact fourHeatOneCovariantDerivative_scalar A (fourHeatOneCovariantDerivative A u l)
    (fun y => ρ y * a y i l) x j k (hρ.mul (ha l))
    (fourHeatOneCovariantDerivative_differentiable A u x l k (hA l) hu)

theorem fourHeatOneCovariantOperator_divergence
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (k : Fin 4)
    (hA : ∀ i l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hρ0 : ρ x ≠ 0)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x)
    (hsym : ∀ i j, a x i j = a x j i) :
    ρ x * fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A V u x k =
      -(∑ i, fourHeatOneCovariantDerivative A (fourHeatOneCovariantFlux A a ρ u i) i x k) +
        ρ x * ∑ l, V k l * u x l := by
  let Q := ∑ i : Fin 4, ∑ j : Fin 4, a x i j *
    fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k
  let B := ∑ i : Fin 4, fourHeatDensityDrift a ρ x i *
    fourHeatOneCovariantDerivative A u i x k
  have hb (i : Fin 4) :
      (∑ j, partialDeriv (fun y => ρ y * a y j i) j x) =
        -(ρ x * fourHeatDensityDrift a ρ x i) := by
    have h := fourHeatDensityDrift_weighted a ρ x i hρ hρ0 (fun j => ha j i)
    linarith only [h]
  have hfirst : (∑ i : Fin 4, ∑ j : Fin 4,
      partialDeriv (fun y => ρ y * a y i j) i x * fourHeatOneCovariantDerivative A u j x k) =
      -(ρ x * B) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hb]
    simp only [B, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond : (∑ i : Fin 4, ∑ j : Fin 4,
      (ρ x * a x i j) *
        fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u j) i x k) =
      ρ x * Q := by
    rw [Finset.sum_comm]
    simp only [Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hflux (i : Fin 4) := fourHeatOneCovariantFlux_derivative A a ρ u x i i k
    hA (ha i) hρ hu
  have hdiv : (∑ i, fourHeatOneCovariantDerivative A (fourHeatOneCovariantFlux A a ρ u i) i x k) =
      ρ x * Q - ρ x * B := by
    simp_rw [hflux, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  rw [hdiv]
  change ρ x * (-Q + B + ∑ l, V k l * u x l) = _
  ring

theorem fourHeatOneCovariantDerivative_contDiffAt
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hA : ∀ l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatOneCovariantDerivative A u i y k) x := by
  apply ContDiffAt.add
  · exact ((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  · exact ContDiffAt.sum fun l _ => (hA l).mul ((hu l).of_le (by norm_num))

theorem fourHeatOneCovariantFlux_contDiffAt
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hA : ∀ j l, ContDiffAt ℝ 1 (fun y => A j y k l) x)
    (ha : ∀ j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ContDiffAt ℝ 1 ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatOneCovariantFlux A a ρ u i y k) x := by
  apply ContDiffAt.sum
  intro j _
  exact (hρ.mul (ha j)).mul (fourHeatOneCovariantDerivative_contDiffAt A u x j k (hA j) hu)

theorem fourHeatOneCovariantDerivative_support
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (i : Fin 4) (k : Fin 4) :
    tsupport (fun x => fourHeatOneCovariantDerivative A u i x k) ⊆
      ⋃ l : Fin 4, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hu (l : Fin 4) : x ∉ tsupport (fun y => u y l) :=
    fun h => hn (mem_iUnion.mpr ⟨l, h⟩)
  have hp : partialDeriv (fun y => u y k) i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hu k
      (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h))
  have hz (l : Fin 4) : u x l = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => u y l) (hu l)
  apply hx
  simp only [fourHeatOneCovariantDerivative, hp, hz, mul_zero, Finset.sum_const_zero, zero_add]

theorem fourHeatOneCovariantFlux_support
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ) (i : Fin 4) (k : Fin 4) :
    tsupport (fun x => fourHeatOneCovariantFlux A a ρ u i x k) ⊆
      ⋃ l : Fin 4, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hz (j : Fin 4) : fourHeatOneCovariantDerivative A u j x k = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A u j y k)
      (fun h => hn (fourHeatOneCovariantDerivative_support A u j k h))
  apply hx
  simp only [fourHeatOneCovariantFlux, hz, mul_zero, Finset.sum_const_zero]

theorem fourHeatOneCovariantFlux_compact
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) (i : Fin 4) (k : Fin 4) :
    HasCompactSupport (fun x => fourHeatOneCovariantFlux A a ρ u i x k) :=
  (isCompact_iUnion hc).of_isClosed_subset (isClosed_tsupport _)
    (fourHeatOneCovariantFlux_support A a ρ u i k)

theorem fourHeatOne_covariant_divergence_green
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (W : Fin 4 → FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hW : ∀ x ∈ U, ∀ i k, ContDiffAt ℝ 1 (fun y => W i y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 4,
      u x k * fourHeatOneCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 4, fourHeatOneCovariantDerivative A u i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      u x k * fourHeatOneCovariantDerivative A (W i) i x k) :=
    fourHeatOneCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => hA x hx i k l)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatOneCovariantDerivative_green A u (W i) U i hu hc hs
    (fun x hx k => hW x hx i k) (fun x hx k l => hA x hx i k l)
    (fun x hx => hskew x hx i)
  linarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two surviving orders of the signed squared-Gaussian integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatGaussian_half_tendsto :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_div, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t)
        (𝓝[>] 0) (𝓝 0)).div_const (2 : ℝ)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

theorem fourHeatGaussian_square_first_order_limit (f : FourSpace → ℝ)
    (hc : Continuous f) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun t : ℝ => t * ∫ x : FourSpace, fourHeatGaussian t x ^ 2 * f x)
      (𝓝[>] 0) (𝓝 ((1 / (128 * Real.pi ^ 2)) *
        ∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i))) := by
  have h := ((fourHeatGaussian_second_order_limit f hc hf hf0 hD0 C hC).comp
    fourHeatGaussian_half_tendsto).const_mul (1 / (128 * Real.pi ^ 2))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have he := fourHeatGaussian_square_weighted f t ht
  dsimp only [Function.comp_apply]
  field_simp [ht.ne'] at he ⊢
  nlinarith [he]

theorem fourHeatGaussian_square_amplitude_integrable (f : FourSpace → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 * f x) := by
  apply ((fourHeatGaussian_square_integrable t ht).mul_const C).mono'
    (((fourHeatGaussian_continuous t).pow 2).mul hf).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖fourHeatGaussian t x ^ 2 * f x‖ ≤ fourHeatGaussian t x ^ 2 * C
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hC x) (sq_nonneg _)

theorem fourHeat_signed_gaussian_limit (f : FourSpace → ℝ)
    (hc : Continuous f) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (F : ℝ → FourSpace → ℝ)
    (hF : Continuous (fun z : ℝ × FourSpace => F z.1 z.2))
    (B T : ℝ) (hT : 0 < T) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖F t x‖ ≤ B) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (2 * t * f x + t ^ 2 * F t x)) (𝓝[>] 0)
      (𝓝 ((1 / (64 * Real.pi ^ 2)) *
        ((∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i)) + F 0 0))) := by
  have h := ((fourHeatGaussian_square_first_order_limit f hc hf hf0 hD0 C hC).const_mul 2).add
    (fourHeatGaussian_square_family_limit F hF B T hT hB)
  have hval : 2 * ((1 / (128 * Real.pi ^ 2)) *
      ∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i)) +
      (1 / (64 * Real.pi ^ 2)) * F 0 0 =
      (1 / (64 * Real.pi ^ 2)) *
        ((∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i)) + F 0 0) := by
    ring
  rw [hval] at h
  apply h.congr'
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht hlt
    exact ⟨ht, hlt.le⟩
  filter_upwards [hsmall] with t ht
  have hi := fourHeatGaussian_square_amplitude_integrable f hc C hC t ht.1
  have hFi := fourHeatGaussian_square_amplitude_integrable (F t)
    (hF.comp (continuous_const.prodMk continuous_id)) B (hB t ⟨ht.1.le, ht.2⟩) t ht.1
  have he : (fun x : FourSpace => fourHeatGaussian t x ^ 2 * (2 * t * f x + t ^ 2 * F t x)) =
      fun x => (2 * t) * (fourHeatGaussian t x ^ 2 * f x) +
        t ^ 2 * (fourHeatGaussian t x ^ 2 * F t x) := by funext x; ring
  rw [he, integral_add (hi.const_mul _) (hFi.const_mul _), integral_const_mul, integral_const_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weighted weak identity for a compact test of the connection
Laplacian. All differential data are the actual coefficient functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeat_potential_pairing_integrable
    (u v : FourSpace → Fin 6 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → HeatMat6) (U : Set FourSpace)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContinuousAt (fun y => v y k) x)
    (hρ : ∀ x ∈ U, ContinuousAt ρ x)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x) :
    Integrable (fun x => ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l)) := by
  apply integrable_finsetSum
  intro k _
  have hf (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => ρ y * ∑ l, V y k l * v y l) x :=
    (hρ x (hs k hx)).mul (tendsto_finsetSum Finset.univ fun l _ =>
      (hV x (hs k hx) k l).mul (hv x (hs k hx) l))
  have h := fourHeat_local_product_integrable _ _ (hu k) (hc k) hf
  simpa only [mul_comm] using h

theorem fourHeatCovariantOperator_weighted_green
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x)
    (hsym : ∀ x ∈ U, ∀ i j, a x i j = a x j i) :
    (∫ x, ∑ k, ρ x * u x k * fourHeatCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      (∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) +
      ∫ x, ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  let W := fourHeatCovariantFlux A a ρ v
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 6,
    u x k * fourHeatCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 6, u x k * (ρ x * ∑ l : Fin 6, V x k l * v x l)
  have hW (x : FourSpace) (hx : x ∈ U) (i : Fin 4) (k : Fin 6) :
      ContDiffAt ℝ 1 (fun y => W i y k) x :=
    fourHeatCovariantFlux_contDiffAt A a ρ v x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (hv x hx)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      u x k * fourHeatCovariantDerivative A (W i) i x k) :=
    fourHeatCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeat_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 6, ρ x * u x k *
      fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 6) := fourHeatCovariantOperator_divergence A a ρ (V x) v x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx) (hv x hx) (hsym x hx)
      have hm (k : Fin 6) : ρ x * u x k *
          fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k =
          -(∑ i : Fin 4, u x k * fourHeatCovariantDerivative A (W i) i x k) +
            u x k * (ρ x * ∑ l, V x k l * v x l) := by
        calc
          _ = u x k * (ρ x * fourHeatCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) v x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => u x k * fourHeatCovariantDerivative A (W i) i x k)]
    · have hz (k : Fin 6) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      simp only [B, P, hz, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_add]
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  have hgreen := fourHeat_covariant_divergence_green A u W U hu hc hs hW
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  change -(∫ x, B x) + (∫ x, P x) = _
  rw [hgreen, neg_neg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual first four heat amplitudes over nearby frames come from
one jointly C4 family with one compact derivative and residual bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatActualAmplitudeFamily (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ),
      (∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
        ∀ z ∈ closedBall (0, frameCoordinateState g c e) r,
        ∀ k l : Fin 6, ‖iteratedFDeriv ℝ n (fun y => E.amplitude m y k l) z‖ ≤ C) ∧
      (∀ z ∈ closedBall (0, frameCoordinateState g c e) r,
        ∀ k l : Fin 6, |E.lastCoefficient z k l| ≤ C) ∧
      ∀ e' : FrameBundle g, e'.base ∈ (chartAt FourSpace c).source →
        frameCoordinateState g c e' ∈ ball (frameCoordinateState g c e) r →
        ∃ D : HeatNormalFrameData g o c e', ∃ A : HeatNormalBundleExtension D,
          ∀ m : ℕ, m ≤ 3 →
            (fun x => E.amplitude m (x, frameCoordinateState g c e')) = A.amplitude m := by
  obtain ⟨F, t, ht, htI, R, hR, hreg, hbase⟩ := exists_heatRadialNormalFamily g o c e he
  let p := frameCoordinateState g c e
  let P := heatRadialFrameFamily F t
  obtain ⟨hP, hc, _⟩ := hreg (0, p) (mem_ball_self hR)
  obtain ⟨hz, hexp⟩ := hbase e he (mem_ball_self hR)
  have hf : (P (0, p)).2.det ≠ 0 := by
    rw [show P (0, p) = p from hz]
    have hg := congrArg Matrix.det (frameChartMatrix_normalizes g c e he)
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change p.2.det * (metricInChart g c p.1).det * p.2.det = 1 at hg
    intro hzero
    rw [hzero] at hg
    norm_num at hg
  have hm : heatFamilyMetric g c P (0, p) = 1 :=
    (heatFamilyMetric_exponential_germ g o c e he P (hP.of_le (by norm_num)) hexp).self_of_nhds
      |>.trans (heatNormalMetric_zero g o e)
  have hmp : 0 < (heatFamilyMetric g c P (0, p)).det := by
    rw [hm, Matrix.det_one]
    norm_num
  obtain ⟨E, ha, hb, hB, hC, hU⟩ := exists_heatFamilySmoothCoefficients g c P (0, p) hP hc hf hmp
  have hnear := ha.eventuallyEq_nhds.and (hb.eventuallyEq_nhds.and
    (hB.eventuallyEq_nhds.and (hC.eventuallyEq_nhds.and hU.eventuallyEq_nhds)))
  obtain ⟨S, hS, hnearS⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min S (min R F.radius) / 2
  have hr : 0 < r := half_pos (lt_min hS (lt_min hR F.radius_pos))
  have hrS : r ≤ S := (half_le_self (le_of_lt (lt_min hS (lt_min hR F.radius_pos)))).trans
    (min_le_left _ _)
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hS (lt_min hR F.radius_pos)))).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrF : r ≤ F.radius := (half_le_self (le_of_lt (lt_min hS (lt_min hR F.radius_pos)))).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁, hC₁, hA⟩ := E.amplitude_compact_bound (closedBall (0, p) r) (isCompact_closedBall _ _)
  obtain ⟨C₂, hC₂, hL⟩ := E.lastCoefficient_compact_bound (closedBall (0, p) r) (isCompact_closedBall _ _)
  refine ⟨E, r, hr, C₁ + C₂, add_nonneg hC₁ hC₂, ?_, ?_, ?_⟩
  · intro m hm n hn z hz k l
    exact (hA m hm n hn z hz k l).trans (le_add_of_nonneg_right hC₂)
  · intro z hz k l
    exact (hL z hz k l).trans (le_add_of_nonneg_left hC₁)
  · intro e' he' hclose
    let q := frameCoordinateState g c e'
    have hd : dist q p < r := hclose
    have hpair : dist ((0 : FourSpace), q) (0, p) < r := by
      change max (dist (0 : FourSpace) 0) (dist q p) < r
      simpa only [dist_self, max_eq_right dist_nonneg] using hd
    obtain ⟨haq, hbq, hBq, hCq, hUq⟩ := hnearS (hpair.trans_le hrS)
    have hqR : ((0 : FourSpace), q) ∈ ball (0, p) R := hpair.trans_le hrR
    have hPq := (hreg (0, q) hqR).1
    have hs : ContDiffAt ℝ 12 (fun x => P (x, q)) 0 :=
      ContDiffAt.comp (f := fun x : FourSpace => (x, q)) (g := P) 0 hPq
        (contDiffAt_id.prodMk contDiffAt_const)
    have hqF : ((0 : FourSpace), q) ∈ ball (0, p) F.radius := hpair.trans_le hrF
    have hexpq := (hbase e' he' (hd.trans_le hrR)).2
    obtain ⟨D, hD⟩ := heatFamilyFrameData F t ht htI e' he' hqF hs hexpq
    let A := E.normalExtension D he' P (hPq.of_le (by norm_num)) hD haq hbq hBq hCq hUq
    refine ⟨D, A, ?_⟩
    intro m hm
    exact E.normalExtension_amplitude D he' P (hPq.of_le (by norm_num)) hD
      haq hbq hBq hCq hUq m hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness bounds the cutoff commutator simultaneously for nearby
initial frames. The Gaussian restores the small-time factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyCommutator (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) (k l : Fin 6) : ℝ :=
  fourHeatScaledCommutator (fun x => E.a (x, z.2)) (fun x => E.b (x, z.2))
    (fun x => E.B (x, z.2)) χ (fun m x q => E.amplitude m (x, z.2) q l) t z.1 k

theorem heatFamilyCommutator_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (k l : Fin 6) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyCommutator E χ z.1 z.2 k l) := by
  have hP (q : Fin 6) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatBundlePolynomial (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 z.2.1 q) :=
    heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) q l).continuous)
  have hD (q : Fin 6) (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fun y => fourHeatBundlePolynomial
        (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 y q) j z.2.1) :=
    heatFamilyPolynomial_partial_continuous _
      (fun m => (E.amplitude_regular m (by omega) q l).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => partialDeriv χ i z.2.1) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp (continuous_fst.comp continuous_snd)
  have hχij (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (partialDeriv χ i) j z.2.1) :=
    ((fourHeat_partial_contDiff 0 _ (fourHeat_partial_contDiff 1 χ hχ i) j).continuous).comp
      (continuous_fst.comp continuous_snd)
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.a z.2 i j) :=
    (E.a_regular i j).continuous.comp continuous_snd
  have hb (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.b z.2 i) :=
    (E.b_regular i).continuous.comp continuous_snd
  have hB (i : Fin 4) (q : Fin 6) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.B z.2 i k q) :=
    (E.B_regular i k q).continuous.comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2.1 j) :=
    (EuclideanSpace.proj j).continuous.comp (continuous_fst.comp continuous_snd)
  have hL : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatLocalOperator (E.a z.2) (E.b z.2) 0 χ z.2.1) := by
    have hn : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
        -(∑ i : Fin 4, ∑ j : Fin 4, E.a z.2 i j *
          partialDeriv (partialDeriv χ i) j z.2.1) +
        ∑ i : Fin 4, E.b z.2 i * partialDeriv χ i z.2.1) :=
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hA i j).mul (hχij i j)))).neg.add
          (continuous_finsetSum _ (fun i _ => (hb i).mul (hχi i)))
    convert hn using 1
    ext z
    simp only [fourHeatLocalOperator, zero_mul, add_zero]
  exact ((continuous_fst.mul hL).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hB i q).mul (hχi i)).mul (hP q)))))

theorem heatFamilyCommutator_bounded (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k l,
      |heatFamilyCommutator E χ t (x, q) k l| ≤ C := by
  let S := fun z : ℝ × HeatRadialFrameSpace => ∑ k : Fin 6, ∑ l : Fin 6,
    |heatFamilyCommutator E χ z.1 z.2 k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (heatFamilyCommutator_continuous E χ hχ k l).abs))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ tsupport χ
  · have hle : |heatFamilyCommutator E χ t (x, q) k l| ≤ S (t, (x, q)) := by
      apply (Finset.single_le_sum (fun a _ => abs_nonneg
        (heatFamilyCommutator E χ t (x, q) k a)) (Finset.mem_univ l)).trans
      exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (heatFamilyCommutator E χ t (x, q) a b)))
        (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx, hq⟩)).trans (le_max_left _ _))
  · have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    change |fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem heatFamilyCommutator_gaussian_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
      |(fourHeatGaussian t x / t) * heatFamilyCommutator E χ t (x, q) k l| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := heatFamilyCommutator_bounded E χ hχ hc K hK
  refine ⟨C * (384 / (Real.pi ^ 2 * s ^ 8)), by positivity, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ ball 0 s
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 1 he k
    change |(fourHeatGaussian t x / t) * fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hsx : s ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hb q hq t ⟨ht.1.le, ht.2⟩ x k l)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * s ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time s t hs ht.1 x hsx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The joint one-form amplitudes restrict to the actual radial solver. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section

theorem HeatFamilyOneCoefficients.amplitude_slice (E : HeatFamilyOneCoefficients)
    (m : ℕ) : m ≤ 3 → ∀ q : CoordinateFrameSpace,
      (fun x => E.amplitude m (x, q)) =
        fourHeatOneCoefficient (fun x => E.base.a (x, q)) (fun x => E.base.b (x, q))
          (fun x => E.B (x, q)) (fun x => E.C (x, q)) (fun x => E.base.U (x, q)) m := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm q
    have hrec := ih (by omega) q
    funext x k l
    have hu (a : Fin 4) : ContDiff ℝ 2 (fun z => E.amplitude m z a l) :=
      (E.amplitude_regular m (by omega) a l).of_le (by norm_num)
    have ho : (fun y => -heatFamilyOneOperator E.base.a E.base.b E.B E.C
        (fun z a => E.amplitude m z a l) (y, q) k) =
        (fun y => -fourHeatOneOperator (E.base.a (y, q)) (E.base.b (y, q)) (E.B (y, q)) (E.C (y, q))
          (fun z a => fourHeatOneCoefficient (fun x => E.base.a (x, q))
            (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.base.U (x, q)) m z a l) y k) := by
      funext y
      rw [heatFamilyOneOperator_slice E.base.a E.base.b E.B E.C
        (fun z a => E.amplitude m z a l) hu (y, q) k]
      have he : (fun z a => E.amplitude m (z, q) a l) =
          (fun z a => fourHeatOneCoefficient (fun x => E.base.a (x, q))
            (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.base.U (x, q)) m z a l) := by
        funext z a
        exact congrArg (fun A : FourSpace → Mat4 => A z a l) hrec
      rw [he]
    change heatFamilyWeightedAverage m E.base.U (fun y => -heatFamilyOneOperator E.base.a E.base.b E.B E.C
      (fun z a => E.amplitude m z a l) y k) (x, q) = _
    rw [heatFamilyWeightedAverage_slice, ho]
    rfl


end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness bounds the one-form cutoff commutator over the common frame family. The Gaussian restores the small-time factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyOneCommutator (E : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) (k l : Fin 4) : ℝ :=
  fourHeatOneScaledCommutator (fun x => E.base.a (x, z.2)) (fun x => E.base.b (x, z.2))
    (fun x => E.B (x, z.2)) χ (fun m x q => E.amplitude m (x, z.2) q l) t z.1 k

theorem heatFamilyOneCommutator_continuous (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (k l : Fin 4) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyOneCommutator E χ z.1 z.2 k l) := by
  have hP (q : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatOnePolynomial (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 z.2.1 q) :=
    heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) q l).continuous)
  have hD (q : Fin 4) (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fun y => fourHeatOnePolynomial
        (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 y q) j z.2.1) :=
    heatFamilyPolynomial_partial_continuous _
      (fun m => (E.amplitude_regular m (by omega) q l).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => partialDeriv χ i z.2.1) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp (continuous_fst.comp continuous_snd)
  have hχij (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (partialDeriv χ i) j z.2.1) :=
    ((fourHeat_partial_contDiff 0 _ (fourHeat_partial_contDiff 1 χ hχ i) j).continuous).comp
      (continuous_fst.comp continuous_snd)
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.base.a z.2 i j) :=
    (E.base.a_regular i j).continuous.comp continuous_snd
  have hb (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.base.b z.2 i) :=
    (E.base.b_regular i).continuous.comp continuous_snd
  have hB (i : Fin 4) (q : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.B z.2 i k q) :=
    (E.B_regular i k q).continuous.comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2.1 j) :=
    (EuclideanSpace.proj j).continuous.comp (continuous_fst.comp continuous_snd)
  have hL : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatLocalOperator (E.base.a z.2) (E.base.b z.2) 0 χ z.2.1) := by
    have hn : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
        -(∑ i : Fin 4, ∑ j : Fin 4, E.base.a z.2 i j *
          partialDeriv (partialDeriv χ i) j z.2.1) +
        ∑ i : Fin 4, E.base.b z.2 i * partialDeriv χ i z.2.1) :=
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hA i j).mul (hχij i j)))).neg.add
          (continuous_finsetSum _ (fun i _ => (hb i).mul (hχi i)))
    convert hn using 1
    ext z
    simp only [fourHeatLocalOperator, zero_mul, add_zero]
  exact ((continuous_fst.mul hL).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hB i q).mul (hχi i)).mul (hP q)))))

theorem heatFamilyOneCommutator_bounded (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k l,
      |heatFamilyOneCommutator E χ t (x, q) k l| ≤ C := by
  let S := fun z : ℝ × HeatRadialFrameSpace => ∑ k : Fin 4, ∑ l : Fin 4,
    |heatFamilyOneCommutator E χ z.1 z.2 k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (heatFamilyOneCommutator_continuous E χ hχ k l).abs))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ tsupport χ
  · have hle : |heatFamilyOneCommutator E χ t (x, q) k l| ≤ S (t, (x, q)) := by
      apply (Finset.single_le_sum (fun a _ => abs_nonneg
        (heatFamilyOneCommutator E χ t (x, q) k a)) (Finset.mem_univ l)).trans
      exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (heatFamilyOneCommutator E χ t (x, q) a b)))
        (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx, hq⟩)).trans (le_max_left _ _))
  · have hz := fourHeatOneScaledCommutator_zero_of_locally_const
      (fun x => E.base.a (x, q)) (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    change |fourHeatOneScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem heatFamilyOneCommutator_gaussian_bound (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
      |(fourHeatGaussian t x / t) * heatFamilyOneCommutator E χ t (x, q) k l| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := heatFamilyOneCommutator_bounded E χ hχ hc K hK
  refine ⟨C * (384 / (Real.pi ^ 2 * s ^ 8)), by positivity, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ ball 0 s
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    have hz := fourHeatOneScaledCommutator_zero_of_locally_const
      (fun x => E.base.a (x, q)) (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 1 he k
    change |(fourHeatGaussian t x / t) * fourHeatOneScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hsx : s ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hb q hq t ⟨ht.1.le, ht.2⟩ x k l)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * s ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time s t hs ht.1 x hsx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform compact bounds for the one-form transport amplitudes and residual. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

theorem HeatFamilyOneCoefficients.amplitude_compact_bound (E : HeatFamilyOneCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ∀ k l : Fin 4, ‖iteratedFDeriv ℝ n (fun y => E.amplitude m y k l) z‖ ≤ C := by
  have hb (i : Fin 4 × Fin 4 × Fin 4) : ∃ C ≥ (0 : ℝ), ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ n (fun y => E.amplitude i.1.val y i.2.1 i.2.2) z‖ ≤ C :=
    heatFamilyScalar_compact_jet_bound _ (E.amplitude_regular i.1.val (by omega) i.2.1 i.2.2) K hK
  choose C hC hb using hb
  refine ⟨∑ i : Fin 4 × Fin 4 × Fin 4, C i,
    Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro m hm n hn z hz k l
  let i : Fin 4 × Fin 4 × Fin 4 := (⟨m, by omega⟩, k, l)
  exact (hb i n hn z hz).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

def HeatFamilyOneCoefficients.lastCoefficient (E : HeatFamilyOneCoefficients)
    (z : HeatRadialFrameSpace) (k l : Fin 4) : ℝ :=
  heatFamilyOneOperator E.base.a E.base.b E.B E.C (fun y q => E.amplitude 3 y q l) z k

theorem HeatFamilyOneCoefficients.lastCoefficient_regular (E : HeatFamilyOneCoefficients)
    (k l : Fin 4) : ContDiff ℝ 2 (fun z => E.lastCoefficient z k l) :=
  heatFamilyOneOperator_contDiff 2 E.base.a E.base.b E.B E.C _
    (fun i j => (E.base.a_regular i j).of_le (by norm_num))
    (fun i => (E.base.b_regular i).of_le (by norm_num))
    (fun i k l => (E.B_regular i k l).of_le (by norm_num))
    (fun k l => (E.C_regular k l).of_le (by norm_num))
    (fun q => E.amplitude_regular 3 (by omega) q l) k

theorem HeatFamilyOneCoefficients.lastCoefficient_compact_bound (E : HeatFamilyOneCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ K, ∀ k l : Fin 4, |E.lastCoefficient z k l| ≤ C := by
  have hb (i : Fin 4 × Fin 4) : ∃ C ≥ (0 : ℝ), ∀ z ∈ K, |E.lastCoefficient z i.1 i.2| ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (E.lastCoefficient_regular i.1 i.2).continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro z hz
    have h : |E.lastCoefficient z i.1 i.2| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC z hz
    exact h.trans (le_max_left _ _)
  choose C hC hb using hb
  refine ⟨∑ i : Fin 4 × Fin 4, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro z hz k l
  exact (hb (k, l) z hz).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ (k, l)))


end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite-smooth extension of the actual one-form coefficients, sharing
the scalar and two-form principal coefficients. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_heatFamilyOneCoefficients (E : HeatFamilySmoothCoefficients)
    (g : SmoothMetric M) (c : M) (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z₀ : HeatRadialFrameSpace) (hP : ContDiffAt ℝ 12 P z₀)
    (hz : (P z₀).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z₀).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z₀).det) :
    ∃ F : HeatFamilyOneCoefficients, F.base = E ∧
      F.B =ᶠ[𝓝 z₀] heatFamilyOneFirst g c P ∧
      F.C =ᶠ[𝓝 z₀] heatFamilyOneZero g c P := by
  choose B hB hBc hBe using fun i k l => heatFamily_scalar_extension 10
    (fun z => heatFamilyOneFirst g c P z i k l) z₀
    (heatFamilyOneFirst_contDiffAt 10 g c P z₀ (hP.of_le (by norm_num)) hz hframe hmetric.ne' i k l)
  choose C hC hCc hCe using fun k l => heatFamily_scalar_extension 10
    (fun z => heatFamilyOneZero g c P z k l) z₀
    (heatFamilyOneZero_contDiffAt 10 g c P z₀ hP hz hframe hmetric k l)
  refine ⟨{
    base := E
    B := fun z i k l => B i k l z
    C := fun z k l => C k l z
    B_regular := hB
    C_regular := hC }, rfl, ?_, ?_⟩
  · filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr
      (fun k => eventually_all.mpr (hBe i k)))] with z hz
    funext i k l
    exact hz i k l
  · filter_upwards [eventually_all.mpr (fun k => eventually_all.mpr (hCe k))] with z hz
    funext k l
    exact hz k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar cutoff commutator has one bound over a compact frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def heatFamilyScalarCommutator (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  fourHeatScaledCommutator (fun x => E.a (x, z.2)) (fun x => E.b (x, z.2))
    (fun _ => 0) χ (fun m x _ => E.scalarAmplitude m (x, z.2)) t z.1 0

theorem heatFamilyScalarCommutator_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyScalarCommutator E χ z.1 z.2) := by
  simp only [heatFamilyScalarCommutator, fourHeatScaledCommutator, Pi.zero_apply,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  have hP : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatPolynomial (fun m x => E.scalarAmplitude m (x, z.2.2)) z.1 z.2.1) :=
    heatFamilyPolynomial_continuous _ (fun m => (E.scalarAmplitude_regular m (by omega)).continuous)
  have hD (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fun y => fourHeatPolynomial
        (fun m x => E.scalarAmplitude m (x, z.2.2)) z.1 y) j z.2.1) :=
    heatFamilyPolynomial_partial_continuous _
      (fun m => (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => partialDeriv χ i z.2.1) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp (continuous_fst.comp continuous_snd)
  have hχij (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (partialDeriv χ i) j z.2.1) :=
    ((fourHeat_partial_contDiff 0 _ (fourHeat_partial_contDiff 1 χ hχ i) j).continuous).comp
      (continuous_fst.comp continuous_snd)
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.a z.2 i j) :=
    (E.a_regular i j).continuous.comp continuous_snd
  have hb (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.b z.2 i) :=
    (E.b_regular i).continuous.comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2.1 j) :=
    (EuclideanSpace.proj j).continuous.comp (continuous_fst.comp continuous_snd)
  have hL : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatLocalOperator (E.a z.2) (E.b z.2) 0 χ z.2.1) := by
    have hn : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
        -(∑ i : Fin 4, ∑ j : Fin 4, E.a z.2 i j *
          partialDeriv (partialDeriv χ i) j z.2.1) +
        ∑ i : Fin 4, E.b z.2 i * partialDeriv χ i z.2.1) :=
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hA i j).mul (hχij i j)))).neg.add
          (continuous_finsetSum _ (fun i _ => (hb i).mul (hχi i)))
    convert hn using 1
    ext z
    simp only [fourHeatLocalOperator, zero_mul, add_zero]
  exact ((continuous_fst.mul hL).mul hP).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD j)).sub (((hx j).div_const 2).mul hP))))))

theorem heatFamilyScalarCommutator_bounded (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      |heatFamilyScalarCommutator E χ t (x, q)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image
    (heatFamilyScalarCommutator_continuous E χ hχ).abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hC ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun _ => 0) χ
      (fun m x _ => E.scalarAmplitude m (x, q)) t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) 0
    change |fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem heatFamilyScalarCommutator_gaussian_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
      |(fourHeatGaussian t x / t) * heatFamilyScalarCommutator E χ t (x, q)| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := heatFamilyScalarCommutator_bounded E χ hχ hc K hK
  refine ⟨C * (384 / (Real.pi ^ 2 * s ^ 8)), by positivity, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ ball 0 s
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun _ => 0) χ
      (fun m x _ => E.scalarAmplitude m (x, q)) t x 1 he 0
    change |(fourHeatGaussian t x / t) * fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hsx : s ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hb q hq t ⟨ht.1.le, ht.2⟩ x)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * s ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time s t hs ht.1 x hsx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact bounds for scalar amplitudes and the remaining transport coefficient. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

theorem HeatFamilySmoothCoefficients.scalarAmplitude_compact_bound (E : HeatFamilySmoothCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ n (E.scalarAmplitude m) z‖ ≤ C := by
  have hb (m : Fin 4) : ∃ C ≥ (0 : ℝ), ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ n (E.scalarAmplitude m.val) z‖ ≤ C :=
    heatFamilyScalar_compact_jet_bound _ (E.scalarAmplitude_regular m.val (by omega)) K hK
  choose C hC hb using hb
  refine ⟨∑ m : Fin 4, C m, Finset.sum_nonneg (fun m _ => hC m), ?_⟩
  intro m hm n hn z hz
  let i : Fin 4 := ⟨m, by omega⟩
  exact (hb i n hn z hz).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

def HeatFamilySmoothCoefficients.scalarLastCoefficient (E : HeatFamilySmoothCoefficients)
    (z : HeatRadialFrameSpace) : ℝ :=
  heatFamilyScalarOperator E.a E.b (E.scalarAmplitude 3) z

theorem HeatFamilySmoothCoefficients.scalarLastCoefficient_regular (E : HeatFamilySmoothCoefficients) :
    ContDiff ℝ 2 E.scalarLastCoefficient :=
  heatFamilyScalarOperator_contDiff 2 E.a E.b _
    (fun i j => (E.a_regular i j).of_le (by norm_num))
    (fun i => (E.b_regular i).of_le (by norm_num)) (E.scalarAmplitude_regular 3 (by omega))

theorem HeatFamilySmoothCoefficients.scalarLastCoefficient_compact_bound
    (E : HeatFamilySmoothCoefficients) (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ K, |E.scalarLastCoefficient z| ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn E.scalarLastCoefficient_regular.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have h : |E.scalarLastCoefficient z| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC z hz
  exact h.trans (le_max_left _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported tests only require continuity on the normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem heat_continuous_mul_of_tsupport_subset {χ f : FourSpace → ℝ}
    {U : Set FourSpace} (hχ : Continuous χ) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hs : tsupport χ ⊆ U) :
    Continuous (fun x => χ x * f x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hχ.continuousAt.mul ((hf x hx).continuousAt (hU.mem_nhds hx))
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    have hx' : x ∉ tsupport χ := fun h => hx (hs h)
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx'] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_initial_local {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    {D : HeatNormalFrameData g o c e} (E : HeatNormalBundleExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (k l : Fin 6) :
    Tendsto (fun t => ∫ x, heatNormalCutoffParametrix E χ t x k l * f x)
      (𝓝[Ioi 0] 0) (𝓝 ((if k = l then 1 else 0) * f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => (χ x * f x) * E.amplitude m x k l
  have hu (m : Fin 4) : Continuous (u m) :=
    hχf.mul (E.amplitude_regular m (by omega) k l).continuous
  have huc (m : Fin 4) : HasCompactSupport (u m) := (hχc.mul_right).mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image
      continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hzero : u 0 0 = (if k = l then 1 else 0) * f 0 := by
    change (χ 0 * f 0) * E.amplitude 0 0 k l = _
    rw [hχ0, E.amplitude_zero, hU]
    simp only [one_smul, Matrix.one_apply, one_mul]
    ring
  rw [hzero] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [heatNormalCutoffParametrix, heatNormalBundleParametrix,
        fourHeatBundlePolynomial, fourHeatPolynomial, u]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six scalar components of the actual normal rough operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem HeatNormalFrameData.actual_rough_components_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) {u : M → TwoFormFour} (hu : TwoFormSmooth o u) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k) +
        (∑ i, heatNormalDrift g o e x i *
          fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k) =
        -twoFormFrameValue o (twoFormRoughTraceField o u) (D.frame x hx) k := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hg : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (D.point x).2ᵀ * metricInChart g c (D.point x).1 * (D.point x).2 = 1 := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.orthonormal x hx
  filter_upwards [hp, hg.eventually_nhds, D.actual_tensor_rough_near he hu]
    with x hpx hgx hr
  intro hx k
  let κ : CovariantCoordinates 2 →ₗ[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k).toLinearMap.comp
      (twoFormExtractLinear.comp twoTensorMatrixLinear)
  have hκ (a : TwoFormFour) : κ (twoFormTensor a) = a k :=
    congrArg (fun b : TwoFormFour => b k) (heat_extract_twoFormTensor a)
  have hh : -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j •
      tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) +
      (∑ i, heatNormalDrift g o e x i •
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      -twoFormFramedRoughTrace o u (D.frame x hx) := by
    funext v
    simpa only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hr hx v
  have hh' := congrArg κ hh
  simp only [map_neg, map_add, map_sum, map_smul, smul_eq_mul] at hh'
  have hf (i : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k := by
    rw [heatNormal_tensor_first hu c D.point x (hpx.of_le (by norm_num)) (D.in_chart x hx) hgx i, hκ]
    exact heatNormalTwoFormNabla_component hu c D.point x (hpx.of_le (by norm_num))
      (D.in_chart x hx) i k
  have hs (i j : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k := by
    rw [heatNormal_tensor_second hu c D.point x hpx (D.in_chart x hx) hgx i j, hκ]
  have ht := hu.framedValue_roughTrace hRic (D.frame x hx)
  rw [twoFormFramedValue_eq] at ht
  rw [← ht, hκ] at hh'
  simpa only [hf, hs] using hh'

end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second covariant derivatives in the actual four-component frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem heat_oneForm_covariant_component (A : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates 1) (x : FourSpace) (i k : Fin 4)
    (hA : (A i x)ᵀ = -A i x) :
    tensorCovariantDirection A T i x ![k] =
      fourHeatOneCovariantDerivative A (fun y l => T y ![l]) i x k :=
  heatOneForm_covariant_skew A T x i k hA

theorem heat_oneForm_covariant_second (A : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates 1) (x : FourSpace) (i j k : Fin 4)
    (hA : ∀ᶠ y in 𝓝 x, ∀ l, (A l y)ᵀ = -A l y) :
    tensorCovariantDirection A (tensorCovariantDirection A T i) j x ![k] =
      fourHeatOneCovariantDerivative A
        (fourHeatOneCovariantDerivative A (fun y l => T y ![l]) i) j x k := by
  have he (l : Fin 4) : (fun y => tensorCovariantDirection A T i y ![l]) =ᶠ[𝓝 x]
      (fun y => fourHeatOneCovariantDerivative A (fun z q => T z ![q]) i y l) := by
    filter_upwards [hA] with y hy
    exact heat_oneForm_covariant_component A T y i l (hy i)
  rw [heat_oneForm_covariant_component A (tensorCovariantDirection A T i) x j k (hA.self_of_nhds j)]
  change partialDeriv _ j x + (∑ l, A j x k l * _) = _
  have hd : partialDeriv (fun y => tensorCovariantDirection A T i y ![k]) j x =
      partialDeriv (fun y => fourHeatOneCovariantDerivative A (fun z q => T z ![q]) i y k) j x :=
    congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector j)) (he k).fderiv_eq
  rw [hd]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact congrArg (A j x k l * ·) (he l).self_of_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common chart, coefficient extension and actual operator agreement
for every frame in one neighborhood. These are constructed geometric data. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatCommonNormalMember (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (E : HeatFamilySmoothCoefficients) (r : ℝ) (e : FrameBundle g) where
  frameData : HeatNormalFrameData g o c e
  extension : HeatNormalBundleExtension frameData
  chart : OpenPartialHomeomorph FourSpace M
  radius_le : r ≤ frameData.radius
  point_regular : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 2 frameData.point x
  metric_pos : ∀ x ∈ ball (0 : FourSpace) r, 0 < (heatNormalMetric g o e x).det
  ball_source : ball 0 r ⊆ chart.source
  exponential : EqOn chart (frameExponential g o e) chart.source
  target_chart : chart.target ⊆ (chartAt FourSpace c).source
  inverse_regular : ContMDiffOn I4 I4 4 chart.symm chart.target
  a_family : extension.base.a = fun x => E.a (x, frameCoordinateState g c e)
  b_family : extension.base.b = fun x => E.b (x, frameCoordinateState g c e)
  B_family : extension.B = fun x => E.B (x, frameCoordinateState g c e)
  C_family : extension.C = fun x => E.C (x, frameCoordinateState g c e)
  U_family : extension.base.U = fun x => E.U (x, frameCoordinateState g c e)
  actual : ∀ x ∈ ball (0 : FourSpace) r,
    extension.base.a x = (heatNormalMetric g o e x)⁻¹ ∧
    extension.base.b x = heatNormalDrift g o e x ∧
    extension.B x = heatNormalBundleFirst frameData x ∧
    extension.C x = heatNormalBundleZero frameData x ∧
    extension.base.U x = heatNormalLeadingAmplitude g o e x

theorem exists_heatUniformNormalFamily (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r > (0 : ℝ),
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      (∀ e' ∈ U, frameCoordinateState g e.base e' ∈ ball (frameCoordinateState g e.base e) (r / 2) ∧
        Nonempty (HeatCommonNormalMember g o e.base E r e')) ∧
      ∃ C ≥ (0 : ℝ),
        (∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
          ∀ z ∈ closedBall (0, frameCoordinateState g e.base e) r,
          ∀ k l : Fin 6, ‖iteratedFDeriv ℝ n (fun y => E.amplitude m y k l) z‖ ≤ C) ∧
        (∀ z ∈ closedBall (0, frameCoordinateState g e.base e) r,
          ∀ k l : Fin 6, |E.lastCoefficient z k l| ≤ C) := by
  obtain ⟨F, t, _, _, hP, U₀, hU₀, he₀, R, hR, hdata⟩ := exists_heatNormalCommonChart g o e
  let p := frameCoordinateState g e.base e
  let P := heatRadialFrameFamily F t
  obtain ⟨D₀, C₀, hD₀P, hC₀, hE₀, hCt₀, _, hRD₀⟩ := hdata e he₀
  have hzero : P (0, p) = p := by simpa only [hD₀P] using D₀.initial
  have hc : (P (0, p)).1 ∈ (chartAt FourSpace e.base).target := by
    simpa only [hD₀P] using D₀.in_chart 0 (mem_ball_self D₀.radius_pos)
  have hf : (P (0, p)).2.det ≠ 0 := by
    rw [hzero]
    have hg := congrArg Matrix.det (frameChartMatrix_normalizes g e.base e (mem_chart_source FourSpace e.base))
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change p.2.det * (metricInChart g e.base p.1).det * p.2.det = 1 at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  have hm : heatFamilyMetric g e.base P (0, p) = 1 := by
    have hh := D₀.metric_slice_eq P hD₀P 0 (mem_ball_self D₀.radius_pos)
      (hP.differentiableAt (by norm_num)) (by rw [frameExponential_zero]; exact mem_chart_source FourSpace e.base)
    exact hh.trans (heatNormalMetric_zero g o e)
  have hmp : 0 < (heatFamilyMetric g e.base P (0, p)).det := by rw [hm, Matrix.det_one]; norm_num
  obtain ⟨E, ha, hb, hB, hC, hU⟩ := exists_heatFamilySmoothCoefficients g e.base P (0, p) hP hc hf hmp
  have hdetc : ContinuousAt (fun z => (heatFamilyMetric g e.base P z).det) (0, p) :=
    (heatFamilyMatrixDeterminant_contDiffAt 0 _ (0, p)
      (heatFamilyMetric_contDiffAt 0 g e.base P (0, p) (hP.of_le (by norm_num)) hc)).continuousAt
  have hdetpos : ∀ᶠ z in 𝓝 ((0 : FourSpace), p), 0 < (heatFamilyMetric g e.base P z).det :=
    hdetc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hmp)
  have hn : ∀ᶠ z in 𝓝 ((0 : FourSpace), p),
      ContDiffAt ℝ 2 P z ∧ 0 < (heatFamilyMetric g e.base P z).det ∧
      E.a =ᶠ[𝓝 z] (fun y => (heatFamilyMetric g e.base P y)⁻¹) ∧
      E.b =ᶠ[𝓝 z] heatFamilyDrift g e.base P ∧
      E.B =ᶠ[𝓝 z] heatFamilyFirst g e.base P ∧
      E.C =ᶠ[𝓝 z] heatFamilyZero g e.base P ∧
      E.U =ᶠ[𝓝 z] heatFamilyLeading g e.base P := by
    filter_upwards [(hP.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num),
      hdetpos, ha.eventuallyEq_nhds, hb.eventuallyEq_nhds, hB.eventuallyEq_nhds,
      hC.eventuallyEq_nhds, hU.eventuallyEq_nhds] with z hz hdz haz hbz hBz hCz hUz
    exact ⟨hz, hdz, haz, hbz, hBz, hCz, hUz⟩
  obtain ⟨S, hS, hball⟩ := Metric.mem_nhds_iff.mp hn
  let r := min R (S / 2)
  have hr : 0 < r := lt_min hR (half_pos hS)
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r < S := (min_le_right _ _).trans_lt (half_lt_self hS)
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p (r / 2)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e (mem_chart_source FourSpace e.base)).preimage_mem_nhds
      (ball_mem_nhds _ (half_pos hr))
  obtain ⟨U, hsub, hUopen, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hcoord)
  have hpair (q : CoordinateFrameSpace) (hq : q ∈ ball p (r / 2))
      (x : FourSpace) (hx : x ∈ ball 0 r) : (x, q) ∈ ball (0, p) S := by
    change max (dist x 0) (dist q p) < S
    exact max_lt (lt_trans hx hrS) ((show dist q p < r / 2 from hq).trans
      ((half_lt_self hr).trans hrS))
  refine ⟨E, r, hr, U, hUopen, heU, ?_, ?_⟩
  · intro e' he'
    obtain ⟨he'₀, hq⟩ := hsub he'
    obtain ⟨D, C, hDP, hCs, hCE, hCt, hCi, hRD⟩ := hdata e' he'₀
    let q := frameCoordinateState g e.base e'
    obtain ⟨hPq, _, haq, hbq, hBq, hCq, hUq⟩ := hball (hpair q hq 0 (mem_ball_self hr))
    have he'c : e'.base ∈ (chartAt FourSpace e.base).source := by
      have hh := hCt (C.map_source (hCs ▸ mem_ball_self hR))
      rwa [hCE (hCs ▸ mem_ball_self hR), frameExponential_zero] at hh
    let A := E.normalExtension D he'c P hPq hDP haq hbq hBq hCq hUq
    have hbs : ball (0 : FourSpace) r ⊆ C.source := by rw [hCs]; exact ball_subset_ball hrR
    have hsource (x : FourSpace) (hx : x ∈ ball 0 r) :
        frameExponential g o e' x ∈ (chartAt FourSpace e.base).source := by
      rw [← hCE (hbs hx)]
      exact hCt (C.map_source (hbs hx))
    have hraw := heatFamilyNormal_on_ball D P hDP r (hrR.trans hRD)
      (fun x hx => (hball (hpair q hq x hx)).1) hsource
      (fun x hx => (hball (hpair q hq x hx)).2.1)
    refine ⟨hq, ⟨{
      frameData := D, extension := A, chart := C,
      radius_le := hrR.trans hRD,
      point_regular := ?_, metric_pos := ?_,
      ball_source := hbs, exponential := hCE, target_chart := hCt, inverse_regular := hCi,
      a_family := rfl, b_family := rfl, B_family := rfl, C_family := rfl, U_family := rfl,
      actual := ?_ }⟩⟩
    · intro x hx
      rw [hDP]
      exact ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := P) x
        (hball (hpair q hq x hx)).1 (contDiffAt_id.prodMk contDiffAt_const)
    · intro x hx
      have hh := D.metric_slice_eq P hDP x (ball_subset_ball (hrR.trans hRD) hx)
        ((hball (hpair q hq x hx)).1.differentiableAt (by norm_num)) (hsource x hx)
      rw [← hh]
      exact (hball (hpair q hq x hx)).2.1
    · intro x hx
      obtain ⟨_, _, hax, hbx, hBx, hCx, hUx⟩ := hball (hpair q hq x hx)
      obtain ⟨ha', hb', hB', hC', hU'⟩ := hraw x hx
      exact ⟨hax.self_of_nhds.trans ha', hbx.self_of_nhds.trans hb',
        hBx.self_of_nhds.trans hB', hCx.self_of_nhds.trans hC', hUx.self_of_nhds.trans hU'⟩
  · obtain ⟨C₁, hC₁, hA⟩ := E.amplitude_compact_bound (closedBall (0, p) r) (isCompact_closedBall _ _)
    obtain ⟨C₂, hC₂, hL⟩ := E.lastCoefficient_compact_bound (closedBall (0, p) r) (isCompact_closedBall _ _)
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_, ?_⟩
    · intro m hm n hn z hz k l
      exact (hA m hm n hn z hz k l).trans (le_add_of_nonneg_right hC₂)
    · intro z hz k l
      exact (hL z hz k l).trans (le_add_of_nonneg_left hC₁)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rough equation for an actual closed and coclosed smooth one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneForm_closed_second_symmetric (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hu : smoothOneFormExterior (o := o) u = 0)
    (e : FrameBundle g) (i j k : Fin 4) :
    covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,j,k] =
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,k,j] := by
  have h := smoothOneFormExterior_covariant (o := o) hRic u e i j k
  rw [hu] at h
  have hz : twoFormFramedCovariantDerivative o (0 : M → TwoFormFour) e = 0 := by
    simpa only [zero_smul] using
      twoFormFramedCovariantDerivative_smul (o := o) (0 : ℝ) (0 : M → TwoFormFour) e
  change twoFormFramedCovariantDerivative o (0 : M → TwoFormFour) e ![i,j,k] = _ at h
  rw [hz, Pi.zero_apply] at h
  exact sub_eq_zero.mp h.symm

include o in
theorem oneForm_trace_second_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hu : ∀ e, (∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]) = 0)
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
      e ![j,i,i]) = 0 := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow j).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic j e
  have hDu : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
  have hidx (i : Fin 4) : Fin.cons j ![i,i] = ![j,i,i] := by
    ext k
    fin_cases k <;> rfl
  have hd : HasDerivAt
      (fun t => ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![i,i])
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (γ 0) ![j,i,i]) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [hidx] using hDu.parallel_derivative (g := g) γ 0 j
      (d.curve_continuous j e).continuousAt (d.parallelCurve j 0 e) ![i,i]
  have he : (fun t => ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![i,i]) =
      fun _ => (0 : ℝ) := funext (fun t => hu (γ t))
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simpa only [hzero] using hz

theorem oneForm_harmonic_rough (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hclosed : smoothOneFormExterior (o := o) u = 0)
    (hcoclosed : ∀ e, (∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) e ![i,i]) = 0)
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
      e ![i,i,j]) = 3 * covariantFieldFramed g u.val e ![j] := by
  have hc := oneForm_ricci_commutator hRic u e j
  rw [Finset.sum_sub_distrib, oneForm_trace_second_zero (o := o) hRic u hcoclosed e j,
    sub_zero] at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro i _
  exact oneForm_closed_second_symmetric hRic u hclosed e i i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth one-form divergence has mean zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormDivergenceCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem oneForm_derivative_integral_zero (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (i : Fin 4) :
    (∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]
      ∂canonicalFrameMeasure g o) = 0 := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![i],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  apply Averages.integral_flow_derivative_zero (canonicalFrameMeasure g o)
    (d.flow i).map (d.flow i).continuous (d.flow i).preserves F DF
  intro t e
  exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![i]

theorem oneFormDivergence_mean_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    (∫ e, oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) = 0 := by
  have hi (i : Fin 4) : Integrable (fun e =>
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i])
      (canonicalFrameMeasure g o) := by
    have hDu : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
    have hc : Continuous (fun e =>
        covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]) :=
      (continuous_apply _).comp (hDu.continuous_framed (g := g))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [oneFormDivergence_eq_frame]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [oneForm_derivative_integral_zero hRic u, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual scalar heat kernel. The spectral
series converges uniformly, using the bounded positive-time evaluation map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeatContinuous_eigen_split (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) :
    scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d (t / 2) i •
        scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) := by
  have h := scalarHeatToContinuous_add g o d (t / 2) (t / 2)
    (half_pos ht) (half_pos ht) (scalarBaseEigenvector g o d i)
  simpa only [add_halves, scalarBaseHeat_eigenvector, map_smul] using h

theorem scalarHeatContinuous_eigen_bound (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) (x : M) :
    |scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x| ≤
      scalarBaseHeatWeight g o d (t / 2) i *
        ‖scalarHeatToContinuous g o d (t / 2) (half_pos ht)‖ := by
  rw [scalarHeatContinuous_eigen_split]
  change |scalarBaseHeatWeight g o d (t / 2) i * _| ≤ _
  have hp : 0 < scalarBaseHeatWeight g o d (t / 2) i := Real.exp_pos _
  rw [abs_mul, abs_of_pos hp]
  have h := scalarHeatToContinuous_bound g o d (t / 2) (half_pos ht)
    (scalarBaseEigenvector g o d i) x
  rw [(scalarBaseEigenvector_orthonormal g o d).1 i] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h hp.le

theorem scalarHeatKernel_hasSum (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    HasSum (fun i : ScalarBaseEigenIndex g o d =>
      scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) y *
        scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) x)
      (scalarHeatKernel g o d t ht x y) := by
  have h := (scalarBaseEigenbasis g o d).hasSum_inner_mul_inner
    (scalarHeatColumn g o d (t / 2) (half_pos ht) y)
    (scalarHeatColumn g o d (t / 2) (half_pos ht) x)
  rw [← scalarHeatKernel_pairing g o d t ht x y] at h
  convert h using 1
  funext i
  rw [scalarBaseEigenbasis_apply, scalarHeatColumn_pairing]
  rw [← scalarHeatColumn_pairing g o d (t / 2) (half_pos ht) x]
  exact congrArg (_ * ·) (real_inner_comm _ _)

theorem scalarHeatKernel_continuous (t : ℝ≥0) (ht : 0 < t) :
    Continuous (fun p : M × M => scalarHeatKernel g o d t ht p.1 p.2) := by
  let C := ‖scalarHeatToContinuous g o d (t / 2 / 2) (half_pos (half_pos ht))‖
  have hs : Summable (fun i : ScalarBaseEigenIndex g o d =>
      scalarBaseHeatWeight g o d (t / 2) i * C ^ 2) :=
    (scalarHeat_weight_summable g o d (t / 2) (half_pos ht)).mul_right _
  have hb (i : ScalarBaseEigenIndex g o d) (p : M × M) :
      ‖scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) p.2 *
        scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) p.1‖ ≤
        scalarBaseHeatWeight g o d (t / 2) i * C ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul]
    have hx := scalarHeatContinuous_eigen_bound g o d (t / 2) (half_pos ht) i p.1
    have hy := scalarHeatContinuous_eigen_bound g o d (t / 2) (half_pos ht) i p.2
    have hp : 0 ≤ scalarBaseHeatWeight g o d (t / 2 / 2) i := (Real.exp_pos _).le
    refine (mul_le_mul hy hx (abs_nonneg _) (mul_nonneg hp
      (norm_nonneg (scalarHeatToContinuous g o d (t / 2 / 2)
        (half_pos (half_pos ht)))))).trans_eq ?_
    dsimp only [C]
    rw [mul_mul_mul_comm, ← pow_two, scalarBaseHeatWeight_half_sq]
    rw [pow_two]
  have hc := continuous_tsum
    (fun i : ScalarBaseEigenIndex g o d =>
      ((scalarHeatToContinuous g o d (t / 2) (half_pos ht)
        (scalarBaseEigenvector g o d i)).continuous.comp continuous_snd).mul
      ((scalarHeatToContinuous g o d (t / 2) (half_pos ht)
        (scalarBaseEigenvector g o d i)).continuous.comp continuous_fst)) hs hb
  exact hc.congr (fun p => (scalarHeatKernel_hasSum g o d t ht p.1 p.2).tsum_eq)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-time versions of the actual scalar heat evaluation column and
diagonal, with their exact squared-column identity at doubled time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatRealColumn (t : ℝ) (x : M) : Lp ℝ 2 (normalizedVolume g) :=
  if ht : 0 < t then scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht) x else 0

def scalarHeatRealDiagonal (t : ℝ) (x : M) : ℝ :=
  if ht : 0 < t then scalarHeatDiagonal g o d t.toNNReal (Real.toNNReal_pos.mpr ht) x else 0

theorem scalarHeatRealColumn_pos (t : ℝ) (ht : 0 < t) (x : M) :
    scalarHeatRealColumn g o d t x =
      scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht) x := dite_eq_left ht

theorem scalarHeatRealDiagonal_columns (t : ℝ) (ht : 0 < t) (x : M) :
    scalarHeatRealDiagonal g o d (t + t) x = ‖scalarHeatRealColumn g o d t x‖ ^ 2 := by
  have he : (t + t).toNNReal / 2 = t.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_ofNat, Real.coe_toNNReal _ ht.le,
      Real.coe_toNNReal _ (add_nonneg ht.le ht.le)]
    ring
  rw [scalarHeatRealDiagonal, dite_eq_left (add_pos ht ht), scalarHeatRealColumn_pos g o d t ht]
  unfold scalarHeatDiagonal
  simp only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeatRealTerm_derivative (f : Lp ℝ 2 (normalizedVolume g))
    (i : ScalarBaseEigenIndex g o d) (s : ℝ) :
    HasDerivAt (scalarBaseHeatRealTerm g o d f i) (scalarBaseHeatRealDerivativeTerm g o d f i s) s := by
  have hx : HasDerivAt (fun x : ℝ => -x * scalarBaseHeatRate g o d i)
      (-scalarBaseHeatRate g o d i) s := by
    simpa only [neg_mul, one_mul, Pi.neg_apply, id_eq] using
      (hasDerivAt_id s).neg.mul_const (scalarBaseHeatRate g o d i)
  have hd := ((hx.exp).mul_const (inner ℝ (scalarBaseEigenvector g o d i) f)).smul_const
    (scalarBaseEigenvector g o d i)
  convert hd using 1
  · rfl
  · change (-scalarBaseHeatRate g o d i * Real.exp (-s * scalarBaseHeatRate g o d i) *
      inner ℝ (scalarBaseEigenvector g o d i) f) • scalarBaseEigenvector g o d i =
      (Real.exp (-s * scalarBaseHeatRate g o d i) * -scalarBaseHeatRate g o d i *
        inner ℝ (scalarBaseEigenvector g o d i) f) • scalarBaseEigenvector g o d i
    congr 1
    ring

theorem scalarBaseHeatRealTerm_hasSum (f : Lp ℝ 2 (normalizedVolume g))
    (s : ℝ) (hs : 0 ≤ s) :
    HasSum (fun i => scalarBaseHeatRealTerm g o d f i s) (scalarBaseHeat g o d s.toNNReal f) := by
  simpa only [scalarBaseHeatRealTerm, scalarBaseHeatWeight, Real.coe_toNNReal s hs] using
    scalarBaseHeat_series g o d s.toNNReal f

theorem scalarBaseHeat_hasDerivAt (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (normalizedVolume g)) :
    HasDerivAt (fun s : ℝ => scalarBaseHeat g o d s.toNNReal f)
      (scalarBaseHeatDerivative g o d t ht f) (t : ℝ) := by
  let ε : ℝ≥0 := t / 2
  have hε : (ε : ℝ) < (t : ℝ) := half_lt_self ht
  have hε0 : 0 < ε := half_pos ht
  have hs : Summable (fun i => scalarBaseHeatRealTerm g o d f i (t : ℝ)) := by
    exact (scalarBaseHeatRealTerm_hasSum g o d f t t.coe_nonneg).summable
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((scalarBaseHeat_rate_weight_summable g o d ε hε0).mul_right ‖f‖)
    isOpen_Ioi isPreconnected_Ioi
    (fun i s _ => scalarBaseHeatRealTerm_derivative g o d f i s)
    (fun i s hs => scalarBaseHeatRealDerivativeTerm_bound g o d ε f i s hs.le)
    hε hs hε
  have hD : (∑' i, scalarBaseHeatRealDerivativeTerm g o d f i (t : ℝ)) =
      scalarBaseHeatDerivative g o d t ht f := by
    exact (scalarBaseHeatDerivative_series g o d t ht f).tsum_eq
  rw [hD] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < t from ht)] with s hs
  exact (scalarBaseHeatRealTerm_hasSum g o d f s hs.le).tsum_eq.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual nonnegative normalized subcritical minimum has a strictly
positive C1 representative; continuity and all source regularity are proved. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local instance minimumC1Regularity_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalar_subcritical_minimum_positive_C1 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hn : ∀ᵐ x ∂normalizedVolume g,
      0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) :
    ∃ v : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) 1 v ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] v ∧ ∀ x, 0 < v x := by
  obtain ⟨v, hv, hrep, hpos⟩ :=
    scalar_subcritical_minimum_positive_continuous g o d hp hp4 w hw hm hmin hn
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  have hb : (b : M → ℝ) =ᵐ[normalizedVolume g] v :=
    (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w).symm.trans hrep
  obtain ⟨F, hF, hweak⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  let S := (2 : ℝ) • b - (2 * ‖w‖ ^ 2) • F
  have hsource : (S : M → ℝ) =ᵐ[normalizedVolume g]
      fun x => (2 : ℝ) * v x + (-(2 * ‖w‖ ^ 2)) * (v x) ^ (p - 1) := by
    filter_upwards [Lp.coeFn_sub ((2 : ℝ) • b) ((2 * ‖w‖ ^ 2) • F),
      Lp.coeFn_smul (2 : ℝ) b, Lp.coeFn_smul (2 * ‖w‖ ^ 2) F, hb, hF, hrep]
      with x hs h1 h2 hb hf hr
    change ((2 : ℝ) • b - (2 * ‖w‖ ^ 2) • F) x = _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, hf, hr, abs_of_pos (hpos x)]
    have hpow : (v x) ^ (p - 2) * v x = (v x) ^ (p - 1) := by
      calc
        _ = (v x) ^ ((p - 2) + 1) := by rw [Real.rpow_add (hpos x), Real.rpow_one]
        _ = _ := by congr 1; ring
    rw [hpow]
    ring
  have hS (a : scalarH1 d) :
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i a)) =
        -(inner ℝ (scalarBasePullback g o S) (scalarH1Value d a)) := by
    have he : scalarBasePullback g o S = (2 : ℝ) • scalarH1Value d u -
        (2 * ‖w‖ ^ 2) • scalarBasePullback g o F := by
      simp only [S, b, map_sub, map_smul, scalarH1BaseValue_spec]
    rw [he]
    exact hweak a
  exact ⟨v, scalar_positive_Euler_C1 g o d S u v hv hpos hb
    2 (-(2 * ‖w‖ ^ 2)) (p - 1) hsource hS, hrep, hpos⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual nonnegative normalized subcritical minimum has a strictly
positive smooth representative; continuity and all source regularity are proved. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local instance minimumSmoothness_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalar_subcritical_minimum_positive_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hn : ∀ᵐ x ∂normalizedVolume g,
      0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) :
    ∃ v : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ v ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] v ∧ ∀ x, 0 < v x := by
  obtain ⟨v, hv, hrep, hpos⟩ :=
    scalar_subcritical_minimum_positive_continuous g o d hp hp4 w hw hm hmin hn
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  have hb : (b : M → ℝ) =ᵐ[normalizedVolume g] v :=
    (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w).symm.trans hrep
  obtain ⟨F, hF, hweak⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  let S := (2 : ℝ) • b - (2 * ‖w‖ ^ 2) • F
  have hsource : (S : M → ℝ) =ᵐ[normalizedVolume g]
      fun x => (2 : ℝ) * v x + (-(2 * ‖w‖ ^ 2)) * (v x) ^ (p - 1) := by
    filter_upwards [Lp.coeFn_sub ((2 : ℝ) • b) ((2 * ‖w‖ ^ 2) • F),
      Lp.coeFn_smul (2 : ℝ) b, Lp.coeFn_smul (2 * ‖w‖ ^ 2) F, hb, hF, hrep]
      with x hs h1 h2 hb hf hr
    change ((2 : ℝ) • b - (2 * ‖w‖ ^ 2) • F) x = _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, hf, hr, abs_of_pos (hpos x)]
    have hpow : (v x) ^ (p - 2) * v x = (v x) ^ (p - 1) := by
      calc
        _ = (v x) ^ ((p - 2) + 1) := by rw [Real.rpow_add (hpos x), Real.rpow_one]
        _ = _ := by congr 1; ring
    rw [hpow]
    ring
  have hS (a : scalarH1 d) :
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i a)) =
        -(inner ℝ (scalarBasePullback g o S) (scalarH1Value d a)) := by
    have he : scalarBasePullback g o S = (2 : ℝ) • scalarH1Value d u -
        (2 * ‖w‖ ^ 2) • scalarBasePullback g o F := by
      simp only [S, b, map_sub, map_smul, scalarH1BaseValue_spec]
    rw [he]
    exact hweak a
  exact ⟨v, scalar_positive_Euler_smooth g o d S u v hv hpos hb
    2 (-(2 * ‖w‖ ^ 2)) (p - 1) hsource hS, hrep, hpos⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential bilinear form and the global Hodge energy splitting. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothTwoFormCodifferential_continuous (u : smoothTwoForms o) (k : Fin 4) :
    Continuous (fun e => smoothTwoFormCodifferential u e k) := by
  have h := (continuous_apply ![k]).comp
    ((smoothTwoFormCodifferentialField u).property.continuous_framed (g := g))
  exact h.congr (fun e => smoothTwoFormCodifferentialField_component u e k)

theorem twoFormCodiffProduct_integrable (u v : smoothTwoForms o) :
    Integrable (fun e => ∑ k, smoothTwoFormCodifferential u e k *
      smoothTwoFormCodifferential v e k) (canonicalFrameMeasure g o) :=
  integrable_finsetSum _ (fun k _ =>
    ((smoothTwoFormCodifferential_continuous u k).mul
      (smoothTwoFormCodifferential_continuous v k)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

def twoFormCodiffPairing (u v : smoothTwoForms o) : ℝ :=
  ∫ e, ∑ k, smoothTwoFormCodifferential u e k *
    smoothTwoFormCodifferential v e k ∂canonicalFrameMeasure g o

theorem twoFormCodiffPairing_comm (u v : smoothTwoForms o) :
    twoFormCodiffPairing u v = twoFormCodiffPairing v u := by
  unfold twoFormCodiffPairing
  apply integral_congr_ae
  filter_upwards [] with e
  simp only [mul_comm]

theorem twoFormCodiffPairing_add_left (u v w : smoothTwoForms o) :
    twoFormCodiffPairing (u + v) w = twoFormCodiffPairing u w + twoFormCodiffPairing v w := by
  unfold twoFormCodiffPairing
  simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  exact integral_add (twoFormCodiffProduct_integrable u w) (twoFormCodiffProduct_integrable v w)

theorem twoFormCodiffPairing_smul_left (r : ℝ) (u v : smoothTwoForms o) :
    twoFormCodiffPairing (r • u) v = r * twoFormCodiffPairing u v := by
  unfold twoFormCodiffPairing
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact integral_const_mul _ _

theorem twoFormCodiffPairing_self (u : smoothTwoForms o) :
    twoFormCodiffPairing u u = ∫ x, twoFormCodiffDensity u x ∂normalizedVolume g := by
  have hi := (twoFormCodiffDensity_continuous u).integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  unfold twoFormCodiffPairing
  apply integral_congr_ae
  filter_upwards [] with e
  rw [twoFormCodiffDensity_eq_frame u e, twoFormCodiffTensor_squareNorm]
  apply Finset.sum_congr rfl
  intro k _
  change smoothTwoFormCodifferential u e k * smoothTwoFormCodifferential u e k =
    smoothTwoFormCodifferential u e k ^ 2
  ring

theorem smoothTwoFormDeRhamEnergy_codiff (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = twoFormCodiffPairing u u +
      twoFormCodiffPairing (smoothTwoFormHodge o u) (smoothTwoFormHodge o u) := by
  rw [smoothTwoFormDeRhamEnergy_eq_base]
  simp_rw [twoFormDeRhamDensity_hodge]
  rw [integral_add
    ((twoFormCodiffDensity_continuous u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((twoFormCodiffDensity_continuous (smoothTwoFormHodge o u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), ← twoFormCodiffPairing_self, ← twoFormCodiffPairing_self]

theorem smoothTwoFormDDelta_pairing (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormDDelta u) v = twoFormCodiffPairing u v := by
  apply Eq.trans (smoothOneFormExterior_adjoint hRic (smoothTwoFormCodifferentialField u) v)
  apply integral_congr_ae
  filter_upwards [] with e
  apply Finset.sum_congr rfl
  intro k _
  rw [smoothTwoFormCodifferentialField_component]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local weak rough equation: the H1 pairing against a
compact chart test equals the Euclidean L2 mass and covariant pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)

include hon

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
private theorem mass_pairing (A : FourSpace → TwoFormFour) (z : FourSpace) :
    inner ℝ (χ z • A z) (twoFormMassTest (g := g) c a z) =
      chartVolumeDensity g c z * inner ℝ (A z) (a z) := by
  by_cases hz : z ∈ tsupport a
  · rw [hon z hz, one_smul]
    exact real_inner_smul_right _ _ _
  · have hzero := image_eq_zero_of_notMem_tsupport hz
    simp only [twoFormMassTest, hzero, smul_zero, inner_zero_right, mul_zero]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
private theorem energy_pairing (A : FourSpace → TwoFormFour) (i : Fin 4) (z : FourSpace) :
    inner ℝ (χ z • A z) (twoFormEnergyTest (g := g) c S a i z) =
      chartVolumeDensity g c z * ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j *
        inner ℝ (A z) (twoFormLocalNabla (g := g) c S a j z) := by
  by_cases hz : z ∈ tsupport a
  · rw [hon z hz, one_smul]
    simp only [twoFormEnergyTest, real_inner_smul_right, inner_sum]
  · have hzero (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z hz j
    simp only [twoFormEnergyTest, hzero, smul_zero, Finset.sum_const_zero,
      inner_zero_right, mul_zero]

theorem twoFormGramVectorL2_mass (u : SmoothH1TwoForm o) :
    inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 u))
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        inner ℝ (twoFormChartValue o (u : smoothTwoForms o).val c S hS z) (a z) := by
  rw [L2.inner_def]
  have he : (fun z => inner ℝ
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 u) z)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt) z)) =ᵐ[volume]
      fun z => inner ℝ (χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z)
        (twoFormMassTest (g := g) c a z) := by
    filter_upwards [twoFormGramVectorL2_coe c S hS hK hKt χ hχ hc hs u,
      twoFormMassTestL2_coe (g := g) c a ha
        (hK.of_isClosed_subset (isClosed_tsupport a) has) (has.trans hKt)] with z hv hb
    rw [hv, hb]
  rw [integral_congr_ae he]
  have hm : (fun z => inner ℝ (χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z)
      (twoFormMassTest (g := g) c a z)) =
      fun z => chartVolumeDensity g c z *
        inner ℝ (twoFormChartValue o (u : smoothTwoForms o).val c S hS z) (a z) :=
    funext (mass_pairing c χ a hon _)
  rw [hm]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hez := image_eq_zero_of_notMem_tsupport (fun h => hz (hKt (has h)))
  rw [hez, inner_zero_right, mul_zero]

variable (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp

theorem twoFormGramNablaL2_energy (u : SmoothH1TwoForm o) :
    (∑ i : Fin 4, inner ℝ
      (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i (smoothTwoFormToH1 u))
      (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt) i)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (∑ i : Fin 4, ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j *
          inner ℝ (twoFormLocalNabla (g := g) c S
            (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z)
            (twoFormLocalNabla (g := g) c S a j z)) := by
  let N := fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i (smoothTwoFormToH1 u)
  let B := fun i => twoFormEnergyTestL2 (g := g) c S hS a ha
    (hK.of_isClosed_subset (isClosed_tsupport a) has) (has.trans hKt) i
  have hi (i : Fin 4) : Integrable (fun z => inner ℝ (N i z) (B i z)) :=
    L2.integrable_inner (N i) (B i)
  have he : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i : Fin 4,
      inner ℝ (N i z) (B i z) = chartVolumeDensity g c z * ∑ j : Fin 4,
        (metricInChart g c z)⁻¹ i j * inner ℝ
          (twoFormLocalNabla (g := g) c S (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z)
          (twoFormLocalNabla (g := g) c S a j z) := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [twoFormGramNablaL2_coe c S hS hK hKt χ hχ hc hs u U hU hUt hKU hp i,
      twoFormEnergyTestL2_coe (g := g) c S hS a ha
        (hK.of_isClosed_subset (isClosed_tsupport a) has) (has.trans hKt) i] with z hn hb
    rw [hn, hb]
    exact energy_pairing c S χ a hon _ i z
  change (∑ i : Fin 4, inner ℝ (N i) (B i)) = _
  simp only [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ = ∫ z, chartVolumeDensity g c z *
        (∑ i : Fin 4, ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j * inner ℝ
          (twoFormLocalNabla (g := g) c S (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z)
          (twoFormLocalNabla (g := g) c S a j z)) := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      simp_rw [hz]
      exact (Finset.mul_sum ..).symm
    _ = _ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z
        (fun h => hz (hKt (has h))) j
      simp only [hzero, inner_zero_right, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form L2 space is the Hilbert sum of the finite
eigenspaces of its compact shifted Hodge resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedResolvent_symmetric (hRic : RicciThree g) :
    (twoFormShiftedResolvent (o := o) hRic).IsSymmetric :=
  twoFormShiftedResolvent_selfAdjoint hRic

abbrev TwoFormSpectralValue (hRic : RicciThree g) :=
  Module.End.Eigenvalues (twoFormShiftedResolvent (o := o) hRic).toLinearMap

abbrev TwoFormSpectralSpace (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :=
  Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ.val

theorem twoFormSpectralValue_bounds (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : 0 < μ.val ∧ μ.val ≤ 1 :=
  twoFormShiftedResolvent_eigenvalue hRic μ.property

instance twoFormSpectralSpaceFinite (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    FiniteDimensional ℝ (TwoFormSpectralSpace hRic μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (twoFormShiftedResolvent_compact hRic) μ.val
    (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1)

theorem twoFormSpectral_orthogonal_bot (hRic : RicciThree g) :
    (⨆ μ : TwoFormSpectralValue (o := o) hRic, TwoFormSpectralSpace hRic μ)ᗮ = ⊥ := by
  change (⨆ μ : {μ // Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ ≠ ⊥},
    Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ.val)ᗮ = ⊥
  rw [iSup_ne_bot_subtype]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (twoFormShiftedResolvent_compact hRic) (twoFormShiftedResolvent_symmetric hRic)

theorem twoFormSpectral_total (hRic : RicciThree g) :
    (⨆ μ : TwoFormSpectralValue (o := o) hRic,
      TwoFormSpectralSpace hRic μ).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, twoFormSpectral_orthogonal_bot hRic]

theorem twoFormSpectral_isHilbertSum (hRic : RicciThree g) :
    IsHilbertSum ℝ (fun μ : TwoFormSpectralValue (o := o) hRic => TwoFormSpectralSpace hRic μ)
      (fun μ => (TwoFormSpectralSpace hRic μ).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal (fun μ : TwoFormSpectralValue (o := o) hRic =>
    TwoFormSpectralSpace hRic μ)
    (twoFormShiftedResolvent_symmetric hRic).orthogonalFamily_eigenspaces'
  rw [twoFormSpectral_total hRic]

def twoFormSpectralEquiv (hRic : RicciThree g) :
    TwoFormL2 o ≃ₗᵢ[ℝ] lp (fun μ : TwoFormSpectralValue (o := o) hRic =>
      TwoFormSpectralSpace hRic μ) 2 :=
  (twoFormSpectral_isHilbertSum hRic).linearIsometryEquiv

theorem twoFormSpectral_sum (hRic : RicciThree g) (f : TwoFormL2 o) :
    HasSum (fun μ : TwoFormSpectralValue (o := o) hRic =>
      ((twoFormSpectralEquiv hRic f) μ : TwoFormL2 o)) f := by
  have h := (twoFormSpectral_isHilbertSum hRic).hasSum_linearIsometryEquiv_symm
    (twoFormSpectralEquiv hRic f)
  change HasSum (fun μ : TwoFormSpectralValue (o := o) hRic =>
    ((twoFormSpectralEquiv hRic f) μ : TwoFormL2 o))
    ((twoFormSpectralEquiv hRic).symm (twoFormSpectralEquiv hRic f)) at h
  rwa [LinearIsometryEquiv.symm_apply_apply] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The flux form of the connection energy has the expected pointwise
symmetry for the actual symmetric principal and potential matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def fourHeatEnergyDensity (A : Fin 4 → FourSpace → HeatMat6)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (x : FourSpace) : ℝ :=
  (∑ i : Fin 4, ∑ k : Fin 6,
    fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) +
    ∑ k : Fin 6, u x k * (ρ x * ∑ l : Fin 6, V x k l * v x l)

theorem fourHeat_flux_pairing (A : Fin 4 → FourSpace → HeatMat6)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ)
    (u v : FourSpace → Fin 6 → ℝ) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 6,
      fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) =
      ρ x * ∑ k : Fin 6, ∑ i : Fin 4, ∑ j : Fin 4,
        a x i j * fourHeatCovariantDerivative A u i x k * fourHeatCovariantDerivative A v j x k := by
  unfold fourHeatCovariantFlux
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fourHeatEnergyDensity_symm_at (A : Fin 4 → FourSpace → HeatMat6)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (ha : ∀ i j, a x i j = a x j i) (hV : ∀ k l, V x k l = V x l k) :
    fourHeatEnergyDensity A a ρ V u v x = fourHeatEnergyDensity A a ρ V v u x := by
  have hm : (∑ k : Fin 6, ∑ i : Fin 4, ∑ j : Fin 4,
      a x i j * fourHeatCovariantDerivative A u i x k * fourHeatCovariantDerivative A v j x k) =
      ∑ k : Fin 6, ∑ i : Fin 4, ∑ j : Fin 4,
        a x i j * fourHeatCovariantDerivative A v i x k * fourHeatCovariantDerivative A u j x k := by
    apply Finset.sum_congr rfl
    intro k _
    exact fourHeat_metric_pairing_symm (a x) ha
      (fun i => fourHeatCovariantDerivative A u i x k)
      (fun i => fourHeatCovariantDerivative A v i x k)
  have hp (u v : Fin 6 → ℝ) : (∑ k, u k * (ρ x * ∑ l, V x k l * v l)) =
      ρ x * ∑ k, u k * ∑ l, V x k l * v l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold fourHeatEnergyDensity
  rw [fourHeat_flux_pairing, fourHeat_flux_pairing, hm, hp, hp,
    fourHeat_potential_pairing_symm (V x) hV]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOne_potential_pairing_integrable
    (u v : FourSpace → Fin 4 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → Mat4) (U : Set FourSpace)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContinuousAt (fun y => v y k) x)
    (hρ : ∀ x ∈ U, ContinuousAt ρ x)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x) :
    Integrable (fun x => ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l)) := by
  apply integrable_finsetSum
  intro k _
  have hf (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => ρ y * ∑ l, V y k l * v y l) x :=
    (hρ x (hs k hx)).mul (tendsto_finsetSum Finset.univ fun l _ =>
      (hV x (hs k hx) k l).mul (hv x (hs k hx) l))
  have h := fourHeat_local_product_integrable _ _ (hu k) (hc k) hf
  simpa only [mul_comm] using h

theorem fourHeatOneCovariantOperator_weighted_green
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x)
    (hsym : ∀ x ∈ U, ∀ i j, a x i j = a x j i) :
    (∫ x, ∑ k, ρ x * u x k * fourHeatOneCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      (∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) +
      ∫ x, ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  let W := fourHeatOneCovariantFlux A a ρ v
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 4,
    u x k * fourHeatOneCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 4, u x k * (ρ x * ∑ l : Fin 4, V x k l * v x l)
  have hW (x : FourSpace) (hx : x ∈ U) (i : Fin 4) (k : Fin 4) :
      ContDiffAt ℝ 1 (fun y => W i y k) x :=
    fourHeatOneCovariantFlux_contDiffAt A a ρ v x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (hv x hx)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      u x k * fourHeatOneCovariantDerivative A (W i) i x k) :=
    fourHeatOneCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeatOne_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 4, ρ x * u x k *
      fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 4) := fourHeatOneCovariantOperator_divergence A a ρ (V x) v x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx) (hv x hx) (hsym x hx)
      have hm (k : Fin 4) : ρ x * u x k *
          fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k =
          -(∑ i : Fin 4, u x k * fourHeatOneCovariantDerivative A (W i) i x k) +
            u x k * (ρ x * ∑ l, V x k l * v x l) := by
        calc
          _ = u x k * (ρ x * fourHeatOneCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) v x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => u x k * fourHeatOneCovariantDerivative A (W i) i x k)]
    · have hz (k : Fin 4) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      simp only [B, P, hz, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_add]
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  have hgreen := fourHeatOne_covariant_divergence_green A u W U hu hc hs hW
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  change -(∫ x, B x) + (∫ x, P x) = _
  rw [hgreen, neg_neg]

theorem fourHeatOne_metric_pairing_symm (a : Mat4)
    (ha : ∀ i j, a i j = a j i) (p q : Fin 4 → ℝ) :
    (∑ i, ∑ j, a i j * p i * q j) = ∑ i, ∑ j, a i j * q i * p j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i]
  ring

theorem fourHeatOne_potential_pairing_symm (V : Mat4)
    (hV : ∀ k l, V k l = V l k) (u v : Fin 4 → ℝ) :
    (∑ k, u k * ∑ l, V k l * v l) = ∑ k, v k * ∑ l, V k l * u l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hV l k]
  ring

def fourHeatOneEnergyDensity (A : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (x : FourSpace) : ℝ :=
  (∑ i : Fin 4, ∑ k : Fin 4,
    fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) +
    ∑ k : Fin 4, u x k * (ρ x * ∑ l : Fin 4, V x k l * v x l)

theorem fourHeatOne_flux_pairing (A : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ)
    (u v : FourSpace → Fin 4 → ℝ) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) =
      ρ x * ∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        a x i j * fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantDerivative A v j x k := by
  unfold fourHeatOneCovariantFlux
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fourHeatOneEnergyDensity_symm_at (A : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (ha : ∀ i j, a x i j = a x j i) (hV : ∀ k l, V x k l = V x l k) :
    fourHeatOneEnergyDensity A a ρ V u v x = fourHeatOneEnergyDensity A a ρ V v u x := by
  have hm : (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
      a x i j * fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantDerivative A v j x k) =
      ∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        a x i j * fourHeatOneCovariantDerivative A v i x k * fourHeatOneCovariantDerivative A u j x k := by
    apply Finset.sum_congr rfl
    intro k _
    exact fourHeatOne_metric_pairing_symm (a x) ha
      (fun i => fourHeatOneCovariantDerivative A u i x k)
      (fun i => fourHeatOneCovariantDerivative A v i x k)
  have hp (u v : Fin 4 → ℝ) : (∑ k, u k * (ρ x * ∑ l, V x k l * v l)) =
      ρ x * ∑ k, u k * ∑ l, V x k l * v l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold fourHeatOneEnergyDensity
  rw [fourHeatOne_flux_pairing, fourHeatOne_flux_pairing, hm, hp, hp,
    fourHeatOne_potential_pairing_symm (V x) hV]

theorem fourHeatOne_flux_pairing_swap
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (ha : ∀ x ∈ U, ∀ i j, a x i j = a x j i) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A v i x k * fourHeatOneCovariantFlux A a ρ u i x k) =
      ∑ i : Fin 4, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k := by
  by_cases hx : x ∈ U
  · rw [fourHeatOne_flux_pairing, fourHeatOne_flux_pairing]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact fourHeatOne_metric_pairing_symm (a x) (ha x hx)
      (fun i => fourHeatOneCovariantDerivative A v i x k)
      (fun i => fourHeatOneCovariantDerivative A u i x k)
  · have hU : (⋃ k, tsupport (fun y => u y k)) ⊆ U := iUnion_subset hs
    have hD (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantDerivative A u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A u i y k)
        (fun h => hx (hU (fourHeatOneCovariantDerivative_support A u i k h)))
    have hW (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantFlux A a ρ u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantFlux A a ρ u i y k)
        (fun h => hx (hU (fourHeatOneCovariantFlux_support A a ρ u i k h)))
    simp only [hD, hW, zero_mul, mul_zero, Finset.sum_const_zero]

theorem fourHeatOneCovariantFlux_contDiff
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (i : Fin 4) (k : Fin 4) :
    ContDiff ℝ 1 (fun x => fourHeatOneCovariantFlux A a ρ u i x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact fourHeatOneCovariantFlux_contDiffAt A a ρ u x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (fun l => (hu l).contDiffAt)
  · have hsub : tsupport (fun y => fourHeatOneCovariantFlux A a ρ u i y k) ⊆ U :=
      (fourHeatOneCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
    have hn : x ∉ tsupport (fun y => fourHeatOneCovariantFlux A a ρ u i y k) :=
      fun hh => hx (hsub hh)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hN := (isClosed_tsupport (fun y => fourHeatOneCovariantFlux A a ρ u i y k)).isOpen_compl.mem_nhds hn
    filter_upwards [hN] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantFlux A a ρ u i y k) hy

theorem fourHeatOneCovariantDerivative_left_integrable
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    Integrable (fun x => ∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) := by
  let F := fun x => ∑ k : Fin 4, u x k * v x k
  have hF : ContDiff ℝ 1 F := fourHeatOne_pairing_contDiff u v U hu hs hv
  have hcF : HasCompactSupport F := fourHeatOne_pairing_compact u v hc
  have hDc : Continuous (partialDeriv F i) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hD : Integrable (partialDeriv F i) :=
    hDc.integrable_of_hasCompactSupport
        (hcF.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_fderiv_apply_subset ℝ (coordinateVector i)))
  have hR := fourHeatOneCovariantDerivative_pairing_integrable A u v U i
    (fun k => (hu k).continuous) hc hs hv hA
  apply (hD.sub hR).congr
  filter_upwards [] with x
  have hp := fourHeatOneCovariantDerivative_pairing_global A u v U i hu hs hv hskew x
  change partialDeriv F i x - _ = _
  change partialDeriv F i x = _ at hp
  linarith only [hp]

theorem fourHeatOne_energy_integral
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, fourHeatOneEnergyDensity A a ρ V u v x) =
      (∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) +
      ∫ x, ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) :=
    fourHeatOneCovariantDerivative_left_integrable A u (fourHeatOneCovariantFlux A a ρ v i)
      U i hu hc hs (fun x hx k => fourHeatOneCovariantFlux_contDiffAt A a ρ v x i k
        (fun j l => hA x hx j k l) (ha x hx i) (hρ x hx) (hv x hx))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hP := fourHeatOne_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  unfold fourHeatOneEnergyDensity
  rw [integral_add (integrable_finsetSum _ (fun i _ => hi i)) hP,
    integral_finsetSum _ (fun i _ => hi i)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed squared-Gaussian integral is bounded uniformly in time
once its first coefficient vanishes quadratically. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter

noncomputable section

theorem fourHeat_signed_gaussian_bound (f F : FourSpace → ℝ) (C B t : ℝ)
    (hC : 0 ≤ C) (_hB : 0 ≤ B) (ht : 0 < t)
    (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ 2) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖∫ x : FourSpace, fourHeatGaussian t x ^ 2 * (2 * t * f x + t ^ 2 * F x)‖ ≤
      (32 * C + B) / (64 * Real.pi ^ 2) := by
  let s := t / 2
  have hs : 0 < s := half_pos ht
  let A := 1 / (64 * Real.pi ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hid : (fun x : FourSpace => fourHeatGaussian t x ^ 2 * (2 * t * f x + t ^ 2 * F x)) =
      fun x => A * (fourHeatGaussian s x * ((2 / t) * f x + F x)) := by
    funext x
    have hh := fourHeatGaussian_square_half t ht x
    change t ^ 2 * fourHeatGaussian t x ^ 2 = A * fourHeatGaussian s x at hh
    calc
      _ = (t ^ 2 * fourHeatGaussian t x ^ 2) * ((2 / t) * f x + F x) := by
        field_simp [ht.ne']
      _ = _ := by rw [hh]; ring
  let Z := fun x : FourSpace => (2 * C / t) * (‖x‖ ^ 2 * fourHeatGaussian s x) +
    B * fourHeatGaussian s x
  have hZ : Integrable Z :=
    ((fourHeatGaussian_moment_integrable 1 s hs).const_mul (2 * C / t)).add
      ((fourHeatGaussian_integrable s hs).const_mul B)
  have hz (x : FourSpace) : ‖fourHeatGaussian s x * ((2 / t) * f x + F x)‖ ≤ Z x := by
    rw [norm_mul, Real.norm_of_nonneg (fourHeatGaussian_pos s hs x).le]
    calc
      _ ≤ fourHeatGaussian s x * (‖(2 / t) * f x‖ + ‖F x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (fourHeatGaussian_pos s hs x).le
      _ = fourHeatGaussian s x * ((2 / t) * ‖f x‖ + ‖F x‖) := by
        rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / t)]
      _ ≤ fourHeatGaussian s x * ((2 / t) * (C * ‖x‖ ^ 2) + B) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hf x) (by positivity)) (hF x))
          (fourHeatGaussian_pos s hs x).le
      _ = Z x := by dsimp [Z]; ring
  rw [hid, integral_const_mul, norm_mul, Real.norm_of_nonneg hA]
  calc
    _ ≤ A * ∫ x, Z x := mul_le_mul_of_nonneg_left
      (norm_integral_le_of_norm_le hZ (Eventually.of_forall hz)) hA
    _ = A * ((2 * C / t) * (∫ x : FourSpace, ‖x‖ ^ 2 * fourHeatGaussian s x) + B) := by
      rw [integral_add ((fourHeatGaussian_moment_integrable 1 s hs).const_mul _)
        ((fourHeatGaussian_integrable s hs).const_mul _), integral_const_mul,
        integral_const_mul, fourHeatGaussian_mass s hs]
      simp only [mul_one]
    _ ≤ A * ((2 * C / t) * (32 * s) + B) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hm := fourHeatGaussian_integral_moment_bound 1 s hs
      norm_num at hm
      nlinarith
    _ = _ := by dsimp [A, s]; field_simp [ht.ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! The jointly extended one-form coefficients give actual normal extensions
with the prescribed common scalar principal part. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatFamilyOneCoefficients.normalExtension (F : HeatFamilyOneCoefficients)
    (D : HeatNormalFrameData g o c e) (base : HeatNormalExtension 10 g o e)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (hB : F.B =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyOneFirst g c P)
    (hC : F.C =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyOneZero g c P) :
    HeatNormalOneExtension D := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun x : FourSpace => (x, q)) (𝓝 0) (𝓝 (0, q)) :=
    continuousAt_id.prodMk continuousAt_const
  have hG := heatFamilyOneNormal_germs D he P hP hpoint
  exact {
    base := base
    B := fun x => F.B (x, q)
    C := fun x => F.C (x, q)
    B_regular := fun i k l => (F.B_regular i k l).comp (contDiff_id.prodMk contDiff_const)
    C_regular := fun k l => (F.C_regular k l).comp (contDiff_id.prodMk contDiff_const)
    B_near := Filter.EventuallyEq.trans (hi.eventually hB) hG.1
    C_near := Filter.EventuallyEq.trans (hi.eventually hC) hG.2 }

theorem HeatFamilyOneCoefficients.normalExtension_amplitude (F : HeatFamilyOneCoefficients)
    (D : HeatNormalFrameData g o c e) (base : HeatNormalExtension 10 g o e)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (hB : F.B =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyOneFirst g c P)
    (hC : F.C =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyOneZero g c P)
    (ha : base.a = fun x => F.base.a (x, frameCoordinateState g c e))
    (hb : base.b = fun x => F.base.b (x, frameCoordinateState g c e))
    (hU : base.U = fun x => F.base.U (x, frameCoordinateState g c e)) (m : ℕ) (hm : m ≤ 3) :
    (fun x => F.amplitude m (x, frameCoordinateState g c e)) =
      (F.normalExtension D base he P hP hpoint hB hC).amplitude m := by
  rw [F.amplitude_slice m hm]
  change _ = fourHeatOneCoefficient base.a base.b _ _ base.U m
  rw [ha, hb, hU]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential operator in the actual bundle parametrix agrees
with the global smooth Hodge Laplacian in the constructed normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem heat_smoothHodge_frameValue {g : SmoothMetric M} {o : FrameOrientation g}
    (hRic : RicciThree g) (u : smoothTwoForms o) (e : FrameBundle g) :
    twoFormFrameValue o (smoothHodgeLaplacian hRic u).val e =
      (6 : ℝ) • twoFormFrameValue o u.val e -
        (2 : ℝ) • twoFormFrameValue o (twoFormCurvatureField o u.val) e -
          twoFormFrameValue o (twoFormRoughTraceField o u.val) e := by
  let L := twoFormExtractLinear.comp twoTensorMatrixLinear
  have hl (a : TwoFormFour) : L (twoFormTensor a) = a := heat_extract_twoFormTensor a
  have h := smoothHodgeLaplacian_framed hRic u e
  rw [← u.property.framedValue_roughTrace hRic e] at h
  simp only [twoFormFramedValue_eq] at h
  have he := congrArg L h
  simpa only [map_sub, map_smul, hl, smoothTwoFormCurvature] using he

theorem HeatNormalFrameData.actual_bundle_operator_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) (u : smoothTwoForms o) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ _hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
      fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
        (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
      heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  filter_upwards [hp, D.actual_rough_components_near he hRic u.property] with x hpx hr
  intro hx k
  have hd : (D.point x).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hA (i : Fin 4) (j l : Fin 6) : DifferentiableAt ℝ
      (fun y => heatTwoFormConnection g c D.point i y j l) x :=
    (heatTwoFormConnection_contDiffAt 1 c D.point x hpx (D.in_chart x hx) hd i j l).differentiableAt
      one_ne_zero
  have hv (l : Fin 6) : ContDiffAt ℝ 2
      (fun y => heatNormalTwoFormValue o c D.point u.val y l) x := by
    let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) l
    simpa only [Function.comp_def] using! π.contDiff.contDiffAt.comp x
      (heatNormalTwoFormValue_contDiffAt 2 u.property c D.point x hpx (D.in_chart x hx))
  rw [← heatNormalConnectionOperator_eq D _ x hA hv k]
  change (-(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i) j x k) +
    (∑ i, heatNormalDrift g o e x i * fourHeatCovariantDerivative
      (heatTwoFormConnection g c D.point)
      (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i x k)) + _ = _
  rw [hr hx k, D.value_as_actual _ x hx, heat_smoothHodge_frameValue hRic u (D.frame x hx)]
  have hV := congrArg (fun a : TwoFormFour => a k) (D.potential_action_as_actual u.val x hx)
  change (∑ l, heatNormalPotential g c D.point x k l *
      heatNormalTwoFormValue o c D.point u.val x l) =
    6 * twoFormFrameValue o u.val (D.frame x hx) k -
      2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k at hV
  rw [hV]
  change -twoFormFrameValue o (twoFormRoughTraceField o u.val) (D.frame x hx) k +
      (6 * twoFormFrameValue o u.val (D.frame x hx) k -
        2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k) = _
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar normal parametrix has the actual delta initial pairing
and may be differentiated under each compactly supported test integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {e : FrameBundle g}

def HeatNormalExtension.scalarCutoff (E : HeatNormalExtension 10 g o e)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  χ x * E.scalarParametrix t x

theorem HeatNormalExtension.scalarCutoff_regular (E : HeatNormalExtension 10 g o e)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) :
    ContDiff ℝ 4 (E.scalarCutoff χ t) := hχ.mul (E.scalarParametrix_regular t)

theorem HeatNormalExtension.scalarCutoff_support (E : HeatNormalExtension 10 g o e)
    (χ : FourSpace → ℝ) (t : ℝ) : tsupport (E.scalarCutoff χ t) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem HeatNormalExtension.scalarCutoff_initial (E : HeatNormalExtension 10 g o e)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1) :
    Tendsto (fun t => ∫ x, E.scalarCutoff χ t x * f x) (𝓝[Ioi 0] 0) (𝓝 (f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => (χ x * f x) * E.scalarAmplitude m x
  have hu (m : Fin 4) : Continuous (u m) :=
    hχf.mul (E.scalarAmplitude_regular m (by omega)).continuous
  have huc (m : Fin 4) : HasCompactSupport (u m) := hc.mul_right.mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hz : u 0 0 = f 0 := by
    change (χ 0 * f 0) * E.scalarAmplitude 0 0 = f 0
    rw [hχ0, E.scalarAmplitude_zero, one_mul, mul_one]
  rw [hz] at h
  apply h.congr'
  exact Eventually.of_forall fun t => integral_congr_ae (Eventually.of_forall fun x => by
    dsimp only [HeatNormalExtension.scalarCutoff, HeatNormalExtension.scalarParametrix,
      fourHeatPolynomial, u]
    ring)

theorem HeatNormalExtension.scalarCutoff_pairing_deriv (E : HeatNormalExtension 10 g o e)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, E.scalarCutoff χ s x * f x)
      (∫ x, deriv (fun s => E.scalarCutoff χ s x) t * f x) t := by
  let u : Fin 4 → FourSpace → ℝ := fun m => E.scalarAmplitude m
  have h := fourHeat_compact_polynomial_pairing_deriv (fun x => χ x * f x) hχf hc.mul_right
    u (fun m => (E.scalarAmplitude_regular m (by omega)).continuous) t ht
  have hfun : (fun s => ∫ x, (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x)) =
      fun s => ∫ x, E.scalarCutoff χ s x * f x := by
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x) =
        (χ x * (fourHeatGaussian s x * fourHeatPolynomial u s x)) * f x
      ring
  have hval : (∫ x, (χ x * f x) * fourHeatGaussianPolynomialTime u t x) =
      ∫ x, deriv (fun s => E.scalarCutoff χ s x) t * f x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hd := (fourHeatGaussianPolynomial_hasDerivAt u t ht x).const_mul (χ x)
      change HasDerivAt (fun s => E.scalarCutoff χ s x)
        (χ x * fourHeatGaussianPolynomialTime u t x) t at hd
      change χ x * f x * fourHeatGaussianPolynomialTime u t x =
        deriv (fun s => E.scalarCutoff χ s x) t * f x
      rw [hd.deriv]
      ring
  rwa [hfun, hval] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual transport identities hold on the entire common normal ball,
not only on a separately chosen germ for each initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.transport (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i, ∑ j : Fin 4, N.extension.base.a x i j * x j = x i) ∧
    (∀ j, ∑ i : Fin 4, N.extension.base.a x i j * x i = x j) ∧
    fourHeatEikonalDefect (N.extension.base.a x) x = 0 ∧
    fourHeatRadialTransport (N.extension.base.a x) (N.extension.base.b x)
      N.extension.base.U x = 0 ∧
    (∀ k l, (∑ i : Fin 4, x i * N.extension.B x i k l) = 0) := by
  let A := N.extension
  let J := frameExponentialJacobian g o e
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : FourSpace) r := isOpen_ball.mem_nhds hx
  have ha : A.base.a =ᶠ[𝓝 x] (fun y => (heatNormalMetric g o e y)⁻¹) := by
    filter_upwards [hnear] with y hy
    exact (N.actual y hy).1
  have hnorm : ∀ᶠ y in 𝓝 x, A.base.U y ^ 2 * J y = 1 := by
    filter_upwards [hnear] with y hy
    rw [(N.actual y hy).2.2.2.2]
    exact heatNormalLeadingAmplitude_normalization g o e y
      (Real.sqrt_pos.mpr (N.metric_pos y hy))
  have hJg : J =ᶠ[𝓝 x] (fun y => (A.base.U y ^ 2)⁻¹) := by
    filter_upwards [hnorm] with y hy
    exact eq_inv_of_mul_eq_one_right hy
  have hJ : DifferentiableAt ℝ J x :=
    (((A.base.U_regular.differentiable (by norm_num) x).pow 2).inv
      (pow_ne_zero 2 (A.base.U_pos x).ne')).congr_of_eventuallyEq hJg
  have hrad : ∀ᶠ y in 𝓝 x, ∀ i, ∑ j : Fin 4, A.base.a y i j * y j = y i := by
    filter_upwards [hnear] with y hy i
    rw [(N.actual y hy).1]
    exact congrFun (heatNormalMetric_inverse_radial g o hRic e he y (N.metric_pos y hy).ne') i
  have hcol (j : Fin 4) : ∑ i : Fin 4, A.base.a x i j * x i = x j := by
    have hs (i : Fin 4) : A.base.a x i j = A.base.a x j i := by
      rw [ha.self_of_nhds]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    simp_rw [hs]
    exact hrad.self_of_nhds j
  refine ⟨hrad.self_of_nhds, hcol, ?_, ?_, ?_⟩
  · rw [ha.self_of_nhds]
    exact heatNormalMetric_eikonal g o hRic e he x (N.metric_pos x hx).ne'
  · have hb : A.base.b x = fourHeatDensityDrift A.base.a J x := by
      rw [(N.actual x hx).2.1]
      exact (fourHeatDensityDrift_germ ha Filter.EventuallyEq.rfl).symm
    rw [hb]
    exact fourHeatDensity_leading_transport A.base.a J A.base.U x
      (fun i j => (A.base.a_regular i j).differentiable (by norm_num) x) hJ
      (A.base.U_regular.differentiable (by norm_num) x) hrad hcol hnorm
  · intro k l
    rw [(N.actual x hx).2.2.1]
    have hh := N.frameData.bundleFirst_radial hRic he x
      (ball_subset_ball N.radius_le hx) (N.metric_pos x hx).ne'
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      using congrArg (fun B : HeatMat6 => B k l) hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive Ricci curvature kills the actual closed and coclosed
smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormBochnerCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem oneForm_valueSquare_integrable (u : smoothCovariantFields M 1) (j : Fin 4) :
    Integrable (fun e => covariantFieldFramed g u.val e ![j] ^ 2)
      (canonicalFrameMeasure g o) := by
  have hc : Continuous (fun e => covariantFieldFramed g u.val e ![j] ^ 2) :=
    ((continuous_apply _).comp (u.property.continuous_framed (g := g))).pow 2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem oneForm_secondPair_integrable (u : smoothCovariantFields M 1) (i j : Fin 4) :
    Integrable (fun e => covariantFieldFramed g u.val e ![j] *
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,i,j]) (canonicalFrameMeasure g o) := by
  have hDu : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
  have hDDu : CovariantFieldSmooth (covariantFieldDerivative g
      (covariantFieldDerivative g u.val)) := hDu.derivative
  have hc : Continuous (fun e => covariantFieldFramed g u.val e ![j] *
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,i,j]) :=
    ((continuous_apply _).comp (u.property.continuous_framed (g := g))).mul
      ((continuous_apply _).comp (hDDu.continuous_framed (g := g)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem oneForm_harmonic_component_integral (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hclosed : smoothOneFormExterior (o := o) u = 0)
    (hcoclosed : ∀ e, (∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) e ![i,i]) = 0) (j : Fin 4) :
    (∫ e, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o) = 0 := by
  have he : (∑ i, ∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val)
      e ![i,j] ^ 2 ∂canonicalFrameMeasure g o) =
      -3 * ∫ e, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o := by
    calc
      _ = ∑ i, -(∫ e, covariantFieldFramed g u.val e ![j] *
          covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
            e ![i,i,j] ∂canonicalFrameMeasure g o) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [pow_two] using oneForm_derivative_green (o := o) hRic u u i j i j
      _ = -(∫ e, ∑ i, covariantFieldFramed g u.val e ![j] *
          covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
            e ![i,i,j] ∂canonicalFrameMeasure g o) := by
        rw [integral_finsetSum _ (fun i _ => oneForm_secondPair_integrable (o := o) u i j)]
        rw [Finset.sum_neg_distrib]
      _ = -(∫ e, 3 * covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with e
        rw [← Finset.mul_sum, oneForm_harmonic_rough hRic u hclosed hcoclosed e j]
        ring
      _ = _ := by rw [integral_const_mul]; ring
  have hgrad : 0 ≤ ∑ i, ∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val)
      e ![i,j] ^ 2 ∂canonicalFrameMeasure g o :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun e => sq_nonneg _))
  have hv : 0 ≤ ∫ e, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o :=
    integral_nonneg (fun e => sq_nonneg _)
  linarith only [he, hgrad, hv]

theorem oneForm_harmonic_eq_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hclosed : smoothOneFormExterior (o := o) u = 0)
    (hcoclosed : ∀ e, (∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) e ![i,i]) = 0) : u = 0 := by
  apply oneForm_eq_zero_of_norm_integral
  rw [oneForm_norm_integral (o := o) u,
    integral_finsetSum _ (fun j _ => oneForm_valueSquare_integrable (o := o) u j)]
  simp only [oneForm_harmonic_component_integral hRic u hclosed hcoclosed,
    Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The spectral scalar heat evolution satisfies the actual geometric
Laplacian equation in L2. The heat output has a smooth representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

local instance scalarHeatEquation_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalar_smooth_laplacian_of_weak (u : scalarH1 d) (H : Lp ℝ 2 (normalizedVolume g))
    (F : SmoothScalar (M := M)) (hF : scalarH1BaseValue g o d u = smoothScalarBaseL2 g F)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        inner ℝ H (scalarH1BaseValue g o d v)) :
    smoothScalarBaseL2 g (smoothScalarLaplacian g F) = -H := by
  have hu : u = smoothScalarToH1 d F := by
    apply scalarH1_eq_smooth_of_value d u F
    rw [← scalarH1BaseValue_spec g o d u, hF, scalarBasePullback_smooth]
  have hp (φ : SmoothScalar (M := M)) :
      inner ℝ (smoothScalarBaseL2 g (smoothScalarLaplacian g F)) (smoothScalarBaseL2 g φ) =
        inner ℝ (-H) (smoothScalarBaseL2 g φ) := by
    have he := hw (smoothScalarToH1 d φ)
    rw [hu, scalarH1BaseValue_smooth] at he
    change smoothScalarDirichlet d F φ = inner ℝ H (smoothScalarBaseL2 g φ) at he
    have hgreen := smoothScalarDirichlet_laplacian_pairing d φ F
    rw [smoothScalarDirichlet_symm d φ F] at hgreen
    have hi := (scalarBasePullback g o).inner_map_map
      (smoothScalarBaseL2 g (smoothScalarLaplacian g F)) (smoothScalarBaseL2 g φ)
    rw [scalarBasePullback_smooth, scalarBasePullback_smooth, smoothScalarLaplacian_valueL2] at hi
    have hc := real_inner_comm (smoothScalarValueL2 g (canonicalFrameMeasure g o) φ)
      (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) F)
    rw [inner_neg_left]
    linarith only [he, hgreen, hi, hc]
  have hall := (smoothScalarBaseL2_dense g).equalizer
    (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (funext hp)
  exact ext_inner_right ℝ (congrFun hall)

theorem scalarHeat_laplacian (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (normalizedVolume g)) :
    ∃ F : SmoothScalar (M := M), scalarBaseHeat g o d t f = smoothScalarBaseL2 g F ∧
      smoothScalarBaseL2 g (smoothScalarLaplacian g F) = scalarBaseHeatDerivative g o d t ht f := by
  obtain ⟨F, hF⟩ := scalarBaseHeat_smooth_representative g o d t ht f
  let u := scalarBaseShiftedSolution g o d (scalarBaseHeatLiftSource g o d t ht f)
  have hu : scalarH1BaseValue g o d u = scalarBaseHeat g o d t f :=
    scalarBaseHeatLiftSource_resolvent g o d t ht f
  have hw (v : scalarH1 d) :
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        inner ℝ (scalarBaseHeatLiftSource g o d t ht f - scalarBaseHeat g o d t f)
          (scalarH1BaseValue g o d v) := by
    have he := scalarBaseShiftedSolution_weak g o d (scalarBaseHeatLiftSource g o d t ht f) v
    rw [scalarH1_inner_base, hu] at he
    rw [inner_sub_left]
    linarith only [he]
  refine ⟨F, hF, ?_⟩
  have he := scalar_smooth_laplacian_of_weak g o d u _ F (hu.trans hF) hw
  rw [he]
  change -(scalarBaseHeatLiftSource g o d t ht f - scalarBaseHeat g o d t f) =
    scalarBaseHeat g o d t f - scalarBaseHeatLiftSource g o d t ht f
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar differential and minus divergence are adjoint. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance scalarOneFormCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalar_oneForm_direction_green (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) (i : Fin 4) :
    (∫ e, scalarGradient g f.val e i * covariantFieldFramed g u.val e ![i]
      ∂canonicalFrameMeasure g o) =
    -(∫ e, f.val e.base *
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]
        ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => f.val e.base,
    f.property.continuous.comp (continuous_frameBase g)⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e => scalarGradient g f.val e i,
    actual_scalarGradient_continuous g f.property i⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![i],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact actual_scalarValue_parallel_derivative g f.property _ t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e)
  · intro t e
    exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![i]

theorem scalar_oneForm_adjoint (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) :
    (∫ e, ∑ i, scalarGradient g f.val e i * covariantFieldFramed g u.val e ![i]
      ∂canonicalFrameMeasure g o) =
    -(∫ e, f.val e.base * oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) := by
  have hL (i : Fin 4) : Integrable (fun e =>
      scalarGradient g f.val e i * covariantFieldFramed g u.val e ![i])
      (canonicalFrameMeasure g o) :=
    ((actual_scalarGradient_continuous g f.property i).mul
      ((continuous_apply _).comp u.property.continuous_framed)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hR (i : Fin 4) : Integrable (fun e => f.val e.base *
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i])
      (canonicalFrameMeasure g o) :=
    ((f.property.continuous.comp (continuous_frameBase g)).mul
      ((continuous_apply _).comp u.property.derivative.continuous_framed)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hL i)]
  simp_rw [scalar_oneForm_direction_green hRic f u]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hR i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with e
  rw [oneFormDivergence_eq_frame, Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp scalar Sobolev inequality and the two Weyl gaps follow from
actual variational minima, their proved positive smooth regularity, Euler
rigidity and the critical exponent limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local instance sharpScalar_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem actual_scalar_subcritical_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ) (hp : 2 < p) (hp4 : p < 4) (b : SmoothScalar (M := M)) :
    (∫ x, |b.val x| ^ p ∂normalizedVolume g) ^ (2 / p) ≤
      (∫ x, b.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet d b b / 2 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)⟩
  obtain ⟨w, hw, hm, hm1, hn, hmin⟩ :=
    scalar_subcritical_nonnegative_minimum g o d hp hp4
  obtain ⟨v, hv, hrep, hpos⟩ :=
    scalar_subcritical_minimum_positive_smooth g o d hp hp4 w hw hm1 hmin hn
  exact scalar_subcritical_bound_of_positive_representative g o hRic d hp hp4
    w hw hm hmin ⟨v, hv⟩ hpos hrep b

theorem actual_sharpScalarSobolev (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    SharpScalarSobolev o d :=
  sharpScalarSobolev_of_subcritical_moments g o d
    (fun p hp hp4 b => actual_scalar_subcritical_bound g o hRic d p hp hp4 b)

theorem actual_gurskyLeBrunGap (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : GurskyLeBrunGapInput g o :=
  gurskyLeBrunGap_of_sharpScalarSobolev o hRic
    (actual_sharpScalarSobolev g o hRic (canonicalParallelMetricData g o hRic))
    (actual_sharpScalarSobolev g o.reversed hRic
      (canonicalParallelMetricData g o.reversed hRic))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic weak rough equation in actual local orthonormal-frame
coefficients. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

def twoFormLocalTestH1 : SmoothH1TwoForm o := twoFormGramTest o c S a ha hK hKt has

def twoFormLocalPairing (u : TwoFormH1 o) : ℝ :=
  (normalizedChartFactor g).toReal *
    (inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) +
    ∑ i : Fin 4, inner ℝ (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u)
      (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt) i))

theorem twoFormLocalPairing_continuous :
    Continuous (twoFormLocalPairing (o := o) c S hS hK hKt χ hχ hc hs a ha has) :=
  continuous_const.mul
    (((twoFormGramVectorL2 c S hK hKt χ hχ hc hs).continuous.inner continuous_const).add
      (continuous_finsetSum _ (fun i _ =>
        (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i).continuous.inner continuous_const)))

include hon hU hKU hp

theorem twoFormLocalPairing_smooth (u : SmoothH1TwoForm o) :
    inner ℝ (smoothTwoFormToH1 u)
      (smoothTwoFormToH1 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has)) =
      twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has (smoothTwoFormToH1 u) := by
  rw [smoothTwoFormToH1.inner_map_map]
  change smoothTwoFormL2Inner (u : smoothTwoForms o) (twoFormGramTest o c S a ha hK hKt has) +
    smoothTwoFormCovariantEnergy (u : smoothTwoForms o) (twoFormGramTest o c S a ha hK hKt has) = _
  rw [smoothTwoFormL2Inner_gramTest (u : smoothTwoForms o) c S hS a ha hK hKt has,
    smoothTwoFormCovariantEnergy_gramTest (u : smoothTwoForms o) c S hS a ha hK hKt has U hU hUt hKU hp]
  unfold twoFormLocalPairing
  rw [twoFormGramVectorL2_mass c S hS hK hKt χ hχ hc hs a ha has hon u,
    twoFormGramNablaL2_energy c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp u]
  ring

theorem twoFormH1_localPairing (u : TwoFormH1 o) :
    inner ℝ u (smoothTwoFormToH1 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has)) =
      twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (continuous_id.inner continuous_const)
      (twoFormLocalPairing_continuous c S hS hK hKt χ hχ hc hs a ha has)) ?_
  intro v
  change inner ℝ (smoothTwoFormToH1 v)
    (smoothTwoFormToH1 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has)) =
      twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has (smoothTwoFormToH1 v)
  exact twoFormLocalPairing_smooth c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp v

theorem twoFormRough_localEquation (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) :
    twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has u =
      inner ℝ f (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) := by
  rw [← twoFormH1_localPairing c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp,
    hu, twoFormRoughSolution_weak, twoFormH1ToL2_smooth]

theorem twoFormHarmonic_localEquation (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has u =
      inner ℝ (twoFormWeitzenbockPotential (twoFormH1ToL2 u))
        (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) :=
  twoFormRough_localEquation c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp u _
    (twoFormWeakHarmonic_rough u hu)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral multipliers on the actual two-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormSpectralMultiplier (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (twoFormSpectralEquiv hRic).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2
      (fun μ => a μ • ContinuousLinearMap.id ℝ (TwoFormSpectralSpace hRic μ))
      hC (fun μ => by
        calc
          ‖a μ • ContinuousLinearMap.id ℝ (TwoFormSpectralSpace hRic μ)‖ ≤ |a μ| := by
            apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
            intro v
            change ‖a μ • v‖ ≤ |a μ| * ‖v‖
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ C := ha μ)).comp
      (twoFormSpectralEquiv hRic).toContinuousLinearEquiv.toContinuousLinearMap)

theorem twoFormSpectralMultiplier_coordinate (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : TwoFormL2 o) (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic a C hC ha f)) μ =
      a μ • (twoFormSpectralEquiv hRic f) μ := by
  change ((twoFormSpectralEquiv hRic)
    ((twoFormSpectralEquiv hRic).symm _)) μ = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem twoFormSpectralMultiplier_norm (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : TwoFormL2 o) :
    ‖twoFormSpectralMultiplier hRic a C hC ha f‖ ≤ C * ‖f‖ := by
  rw [← (twoFormSpectralEquiv hRic).norm_map (twoFormSpectralMultiplier hRic a C hC ha f),
    ← (twoFormSpectralEquiv hRic).norm_map f]
  calc
    _ ≤ ‖C • twoFormSpectralEquiv hRic f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro μ
      rw [twoFormSpectralMultiplier_coordinate, norm_smul, Real.norm_eq_abs]
      change |a μ| * ‖(twoFormSpectralEquiv hRic f) μ‖ ≤
        ‖C • (twoFormSpectralEquiv hRic f) μ‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha μ) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

theorem twoFormSpectralMultiplier_inner (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : TwoFormL2 o) :
    inner ℝ (twoFormSpectralMultiplier hRic a C hC ha f) h =
      ∑' μ, a μ * inner ℝ ((twoFormSpectralEquiv hRic f) μ)
        ((twoFormSpectralEquiv hRic h) μ) := by
  rw [← (twoFormSpectralEquiv hRic).inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  rw [twoFormSpectralMultiplier_coordinate, real_inner_smul_left]

theorem twoFormSpectralMultiplier_selfAdjoint (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : TwoFormL2 o) :
    inner ℝ (twoFormSpectralMultiplier hRic a C hC ha f) h =
      inner ℝ f (twoFormSpectralMultiplier hRic a C hC ha h) := by
  calc
    _ = ∑' μ, a μ * inner ℝ ((twoFormSpectralEquiv hRic f) μ)
        ((twoFormSpectralEquiv hRic h) μ) := twoFormSpectralMultiplier_inner hRic a C hC ha f h
    _ = ∑' μ, a μ * inner ℝ ((twoFormSpectralEquiv hRic h) μ)
        ((twoFormSpectralEquiv hRic f) μ) := by
      apply tsum_congr
      intro μ
      rw [real_inner_comm]
    _ = inner ℝ (twoFormSpectralMultiplier hRic a C hC ha h) f :=
      (twoFormSpectralMultiplier_inner hRic a C hC ha h f).symm
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Classification from oriented Hodge and model hypotheses, together with
polar volume, smooth Poisson solvability, both Weyl gaps, the orientation cover
and the obstruction to a free metric involution of CP2. -/

namespace PositiveEinsteinFour

open EinsteinFour _root_.OAI.PositiveEinsteinFour.Geometry
open scoped Manifold ContDiff

noncomputable section

universe u

structure ClassicalOrientedData {M : Type u} [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold I4 ∞ M] [T3Space M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    (g : SmoothMetric M) (o : FrameOrientation g) where
  hodge : GurskyLeBrunHodgeInput g o
  model : DerdzinskiHitchinInput g o

def ClassicalOrientedInputs (X : ClosedOrientedMetricFour.{u}) : Prop :=
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  ∀ (g : SmoothMetric X.manifold) (o : FrameOrientation g),
    RicciThree g → IsEinstein g → HasPositiveSectionalCurvature g →
      Nonempty (ClassicalOrientedData g o)

theorem ClassicalOrientedInputs.toRemaining {X : ClosedOrientedMetricFour.{u}}
    (h : ClassicalOrientedInputs X) : RemainingOrientedInputs X := by
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  intro g o hRic hEinstein hpositive
  obtain ⟨p⟩ := h g o hRic hEinstein hpositive
  exact ⟨actual_petersen_poisson g o hRic,
    actualJacobiPolarInput_proved g o hRic, actual_gurskyLeBrunGap g o hRic, p.hodge, p.model⟩

variable (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure ClassicalClassificationInputs (_M : Type u) : Prop where
  oriented : ∀ X : ClosedOrientedMetricFour.{u}, ClassicalOrientedInputs X

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]

theorem classificationOn_of_classical_inputs (h : ClassicalClassificationInputs M) :
    ClassificationOn M := by
  intro g hEinstein hpositive
  exact classified_of_actual_oriented_models g
    (fun X => ((h.oriented X).toRemaining.toPublished).models) hEinstein hpositive

end
end PositiveEinsteinFour
end


section

/-! The codifferential squares to zero in degrees two and one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance codifferentialBaseProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem smoothScalar_eq_zero_of_square_integral (f : SmoothScalar (M := M))
    (hf : (∫ e, f.val e.base ^ 2 ∂canonicalFrameMeasure g o) = 0) : f = 0 := by
  let _ := normalizedVolume_isOpenPosMeasure g
  have hc : Continuous (fun x => f.val x ^ 2) := f.property.continuous.pow 2
  have hi := hc.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  have hb : (∫ x, f.val x ^ 2 ∂normalizedVolume g) = 0 :=
    (canonicalFrameMeasure_integral_base g o _ hi).symm.trans hf
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f.val x)) hi).mp hb
  have he : (fun x => f.val x ^ 2) = 0 := Measure.eq_of_ae_eq ha hc continuous_const
  apply Subtype.ext
  funext x
  exact sq_eq_zero_iff.mp (congrFun he x)

theorem smoothTwoFormCodifferential_gradient_orthogonal (hRic : RicciThree g)
    (u : smoothTwoForms o) (f : SmoothScalar (M := M)) :
    (∫ e, ∑ i, scalarGradient g f.val e i *
      covariantFieldFramed g (smoothTwoFormCodifferentialField u).val e ![i]
      ∂canonicalFrameMeasure g o) = 0 := by
  have ha := smoothOneFormExterior_adjoint hRic (smoothScalarDifferential g f) u
  rw [smoothScalarDifferential_closed] at ha
  simp only [smoothScalarDifferential_framed,
    ← smoothTwoFormCodifferentialField_component] at ha
  exact ha.symm.trans (show smoothTwoFormL2Inner (0 : smoothTwoForms o) u = 0 by
    simp [smoothTwoFormL2Inner])

theorem smoothTwoFormCodifferential_divergence (hRic : RicciThree g)
    (u : smoothTwoForms o) :
    smoothOneFormDivergence g (smoothTwoFormCodifferentialField u) = 0 := by
  let f := smoothOneFormDivergence g (smoothTwoFormCodifferentialField u)
  apply smoothScalar_eq_zero_of_square_integral (o := o)
  have hA := scalar_oneForm_adjoint (o := o) hRic f (smoothTwoFormCodifferentialField u)
  have hG := smoothTwoFormCodifferential_gradient_orthogonal hRic u f
  rw [hG] at hA
  have hzero := neg_eq_zero.mp hA.symm
  change (∫ e, f.val e.base * f.val e.base ∂canonicalFrameMeasure g o) = 0 at hzero
  simpa only [pow_two] using hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetry of the compact connection flux paired with a local section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators

noncomputable section

theorem fourHeat_flux_pairing_swap
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (ha : ∀ x ∈ U, ∀ i j, a x i j = a x j i) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 6,
      fourHeatCovariantDerivative A v i x k * fourHeatCovariantFlux A a ρ u i x k) =
      ∑ i : Fin 4, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k := by
  by_cases hx : x ∈ U
  · rw [fourHeat_flux_pairing, fourHeat_flux_pairing]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact fourHeat_metric_pairing_symm (a x) (ha x hx)
      (fun i => fourHeatCovariantDerivative A v i x k)
      (fun i => fourHeatCovariantDerivative A u i x k)
  · have hU : (⋃ k, tsupport (fun y => u y k)) ⊆ U := iUnion_subset hs
    have hD (i : Fin 4) (k : Fin 6) : fourHeatCovariantDerivative A u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A u i y k)
        (fun h => hx (hU (fourHeatCovariantDerivative_support A u i k h)))
    have hW (i : Fin 4) (k : Fin 6) : fourHeatCovariantFlux A a ρ u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantFlux A a ρ u i y k)
        (fun h => hx (hU (fourHeatCovariantFlux_support A a ρ u i k h)))
    simp only [hD, hW, zero_mul, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability in the finite-regularity connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantDerivative_left_integrable
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    Integrable (fun x => ∑ k, fourHeatCovariantDerivative A u i x k * v x k) := by
  let F := fun x => ∑ k : Fin 6, u x k * v x k
  have hF : ContDiff ℝ 1 F := fourHeat_pairing_contDiff u v U hu hs hv
  have hcF : HasCompactSupport F := fourHeat_pairing_compact u v hc
  have hDc : Continuous (partialDeriv F i) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hD : Integrable (partialDeriv F i) :=
    hDc.integrable_of_hasCompactSupport
        (hcF.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_fderiv_apply_subset ℝ (coordinateVector i)))
  have hR := fourHeatCovariantDerivative_pairing_integrable A u v U i
    (fun k => (hu k).continuous) hc hs hv hA
  apply (hD.sub hR).congr
  filter_upwards [] with x
  have hp := fourHeatCovariantDerivative_pairing_global A u v U i hu hs hv hskew x
  change partialDeriv F i x - _ = _
  change partialDeriv F i x = _ at hp
  linarith only [hp]

theorem fourHeat_energy_integral
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, fourHeatEnergyDensity A a ρ V u v x) =
      (∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) +
      ∫ x, ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) :=
    fourHeatCovariantDerivative_left_integrable A u (fourHeatCovariantFlux A a ρ v i)
      U i hu hc hs (fun x hx k => fourHeatCovariantFlux_contDiffAt A a ρ v x i k
        (fun j l => hA x hx j k l) (ha x hx i) (hρ x hx) (hv x hx))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hP := fourHeat_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  unfold fourHeatEnergyDensity
  rw [integral_add (integrable_finsetSum _ (fun i _ => hi i)) hP,
    integral_finsetSum _ (fun i _ => hi i)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOne_compact_flux_green
    (A : Fin 4 → FourSpace → Mat4)
    (W : Fin 4 → FourSpace → Fin 4 → ℝ) (v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace)
    (hW : ∀ i k, ContDiff ℝ 1 (fun x => W i x k))
    (hcW : ∀ i k, HasCompactSupport (fun x => W i x k))
    (hsW : ∀ i k, tsupport (fun x => W i x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 4,
      v x k * fourHeatOneCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A v i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      v x k * fourHeatOneCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatOneCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) hv (fun x hx k l => hA x hx i k l)
      (fun x hx => hskew x hx i)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatOneCovariantDerivative_green A (W i) v U i (hW i) (hcW i) (hsW i)
    hv (fun x hx k l => hA x hx i k l) (fun x hx => hskew x hx i)
  simpa only [mul_comm] using h

theorem fourHeatOne_potential_pairing_swap
    (u v : FourSpace → Fin 4 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → Mat4) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hV : ∀ x ∈ U, ∀ k l, V x k l = V x l k) (x : FourSpace) :
    (∑ k, v x k * (ρ x * ∑ l, V x k l * u x l)) =
      ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  by_cases hx : x ∈ U
  · have hp (p q : Fin 4 → ℝ) : (∑ k, p k * (ρ x * ∑ l, V x k l * q l)) =
        ρ x * ∑ k, p k * ∑ l, V x k l * q l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hp, hp, fourHeatOne_potential_pairing_symm (V x) (hV x hx)]
  · have hz (k : Fin 4) : u x k = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => u y k) (fun h => hx (hs k h))
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_mul]

theorem fourHeatOneCovariantOperator_compact_adjoint
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x)
    (hsym : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hVsym : ∀ x ∈ U, ∀ k l, V x k l = V x l k) :
    (∫ x, ∑ k, ρ x * u x k * fourHeatOneCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      ∫ x, ∑ k, ρ x * v x k * fourHeatOneCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) u x k := by
  let W := fourHeatOneCovariantFlux A a ρ u
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 4,
    v x k * fourHeatOneCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 4, u x k * (ρ x * ∑ l : Fin 4, V x k l * v x l)
  have hW (i : Fin 4) (k : Fin 4) : ContDiff ℝ 1 (fun x => W i x k) :=
    fourHeatOneCovariantFlux_contDiff A a ρ u U hu hs hA ha hρ i k
  have hcW (i : Fin 4) (k : Fin 4) : HasCompactSupport (fun x => W i x k) :=
    fourHeatOneCovariantFlux_compact A a ρ u hc i k
  have hsW (i : Fin 4) (k : Fin 4) : tsupport (fun x => W i x k) ⊆ U :=
    (fourHeatOneCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      v x k * fourHeatOneCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatOneCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeatOne_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 4, ρ x * v x k *
      fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 4) := fourHeatOneCovariantOperator_divergence A a ρ (V x) u x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx)
        (fun l => (hu l).contDiffAt) (hsym x hx)
      have hm (k : Fin 4) : ρ x * v x k *
          fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k =
          -(∑ i : Fin 4, v x k * fourHeatOneCovariantDerivative A (W i) i x k) +
            v x k * (ρ x * ∑ l, V x k l * u x l) := by
        calc
          _ = v x k * (ρ x * fourHeatOneCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) u x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => v x k * fourHeatOneCovariantDerivative A (W i) i x k),
        fourHeatOne_potential_pairing_swap u v ρ V U hs hVsym x]
    · have hz (k : Fin 4) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      have hD (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantDerivative A u i x k = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A u i y k)
          (fun h => hx ((iUnion_subset hs) (fourHeatOneCovariantDerivative_support A u i k h)))
      have hDD (i j : Fin 4) (k : Fin 4) :
          fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y =>
          fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j y k)
        intro h
        obtain ⟨l, hl⟩ := mem_iUnion.mp (fourHeatOneCovariantDerivative_support A
          (fourHeatOneCovariantDerivative A u i) j k h)
        exact hx ((iUnion_subset hs) (fourHeatOneCovariantDerivative_support A u i l hl))
      have hDW (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantDerivative A (W i) i x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A (W i) i y k)
        intro h
        exact hx ((iUnion_subset (hsW i)) (fourHeatOneCovariantDerivative_support A (W i) i k h))
      simp only [B, P, fourHeatOneCovariantOperator, hz, hD, hDD, hDW,
        zero_mul, mul_zero, Finset.sum_const_zero, neg_zero, add_zero]
  have hgreen := fourHeatOne_compact_flux_green A W v U hW hcW hsW
    (fun x hx k => (hv x hx k).of_le (by norm_num))
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A v i x k * W i x k) := by
    simpa only [mul_comm] using fourHeatOneCovariantDerivative_pairing_integrable A (W i) v U i
      (fun k => (hW i k).continuous) (hcW i) (hsW i)
      (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hj (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) :=
    fourHeatOneCovariantDerivative_left_integrable A u (fourHeatOneCovariantFlux A a ρ v i) U i
      (fun k => (hu k).of_le (by norm_num)) hc hs
      (fun x hx k => fourHeatOneCovariantFlux_contDiffAt A a ρ v x i k
        (fun j l => hA x hx j k l) (ha x hx i) (hρ x hx) (hv x hx))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hflux : (∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A v i x k * W i x k) =
      ∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k := by
    rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_finsetSum _ (fun i _ => hj i)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact fourHeatOne_flux_pairing_swap A a ρ u v U hs hsym x
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  change _ = -(∫ x, B x) + (∫ x, P x)
  rw [hgreen, neg_neg, hflux]
  exact fourHeatOneCovariantOperator_weighted_green A a ρ V u v U
    (fun k => (hu k).of_le (by norm_num)) hc hs hv hA ha hρ hρ0 hV hskew hsym

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-coordinate Hodge operator at every regular point
of a nondegenerate normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.rough_pullback_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
      ∀ (T : FourSpace → CovariantCoordinates 2),
      (∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z) →
      ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (T (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (T (D.point y).1)) i x v) =
        -frameTensor (D.point x).2
          (twoFormSecondTrace (metricInChart g c (D.point x).1)⁻¹
            (covariantDerivative g c (covariantDerivative g c T) (D.point x).1)) v := by
  have hgx : ∀ᶠ y in 𝓝 x,
      (D.point y).2ᵀ * metricInChart g c (D.point y).1 * (D.point y).2 = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.orthonormal y hy
  have ha := D.inverseMetric_transport x hx hs hd.ne'
  have hb := D.drift_transport_at x hx hP hs hd
  intro T hT v
  exact heatNormal_rough_pullback g c D.point T x hP hT (D.in_chart x hx) hgx
    (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) ha hb v

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.actual_tensor_rough_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
    ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x v) =
        -twoFormFramedRoughTrace o u (D.frame x hx) v := by
  have h := D.rough_pullback_at x hx hP hs hd
  intro u hu v
  rw [D.roughTrace_as_actual hu x hx]
  exact h (twoFormCoordinates o u c) (fun z hz => hu.coordinates_contDiffAt c z hz) v

theorem HeatNormalFrameData.actual_rough_components_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (hRic : RicciThree g)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hpx : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
    ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ k : Fin 6,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k) +
        (∑ i, heatNormalDrift g o e x i *
          fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k) =
        -twoFormFrameValue o (twoFormRoughTraceField o u) (D.frame x hx) k := by
  have hgx : ∀ᶠ y in 𝓝 x,
      (D.point y).2ᵀ * metricInChart g c (D.point y).1 * (D.point y).2 = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.orthonormal y hy
  have hr := D.actual_tensor_rough_at x hx hpx hs hd
  intro u hu k
  let κ : CovariantCoordinates 2 →ₗ[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k).toLinearMap.comp
      (twoFormExtractLinear.comp twoTensorMatrixLinear)
  have hκ (a : TwoFormFour) : κ (twoFormTensor a) = a k :=
    congrArg (fun b : TwoFormFour => b k) (heat_extract_twoFormTensor a)
  have hh : -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j •
      tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) +
      (∑ i, heatNormalDrift g o e x i •
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      -twoFormFramedRoughTrace o u (D.frame x hx) := by
    funext v
    simpa only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hr u hu v
  have hh' := congrArg κ hh
  simp only [map_neg, map_add, map_sum, map_smul, smul_eq_mul] at hh'
  have hf (i : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k := by
    rw [heatNormal_tensor_first hu c D.point x (hpx.of_le (by norm_num)) (D.in_chart x hx) hgx i, hκ]
    exact heatNormalTwoFormNabla_component hu c D.point x (hpx.of_le (by norm_num))
      (D.in_chart x hx) i k
  have hs (i j : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k := by
    rw [heatNormal_tensor_second hu c D.point x hpx (D.in_chart x hx) hgx i j, hκ]
  have ht := hu.framedValue_roughTrace hRic (D.frame x hx)
  rw [twoFormFramedValue_eq] at ht
  rw [← ht, hκ] at hh'
  simpa only [hf, hs] using hh'

theorem HeatNormalFrameData.actual_bundle_operator_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (hRic : RicciThree g)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hpx : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hdet : 0 < (heatNormalMetric g o e x).det) :
    ∀ (u : smoothTwoForms o), ∀ k : Fin 6,
      fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
        (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
      heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
  have hr := D.actual_rough_components_at hRic x hx hpx hs hdet
  intro u k
  have hd : (D.point x).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hA (i : Fin 4) (j l : Fin 6) : DifferentiableAt ℝ
      (fun y => heatTwoFormConnection g c D.point i y j l) x :=
    (heatTwoFormConnection_contDiffAt 1 c D.point x hpx (D.in_chart x hx) hd i j l).differentiableAt
      one_ne_zero
  have hv (l : Fin 6) : ContDiffAt ℝ 2
      (fun y => heatNormalTwoFormValue o c D.point u.val y l) x := by
    let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) l
    simpa only [Function.comp_def] using! π.contDiff.contDiffAt.comp x
      (heatNormalTwoFormValue_contDiffAt 2 u.property c D.point x hpx (D.in_chart x hx))
  rw [← heatNormalConnectionOperator_eq D _ x hA hv k]
  change (-(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i) j x k) +
    (∑ i, heatNormalDrift g o e x i * fourHeatCovariantDerivative
      (heatTwoFormConnection g c D.point)
      (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i x k)) + _ = _
  rw [hr u.val u.property k, D.value_as_actual _ x hx, heat_smoothHodge_frameValue hRic u (D.frame x hx)]
  have hV := congrArg (fun a : TwoFormFour => a k) (D.potential_action_as_actual u.val x hx)
  change (∑ l, heatNormalPotential g c D.point x k l *
      heatNormalTwoFormValue o c D.point u.val x l) =
    6 * twoFormFrameValue o u.val (D.frame x hx) k -
      2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k at hV
  rw [hV]
  change -twoFormFrameValue o (twoFormRoughTraceField o u.val) (D.frame x hx) k +
      (6 * twoFormFrameValue o u.val (D.frame x hx) k -
        2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k) = _
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-coordinate Hodge operator agrees with the actual operator
on one geometric neighborhood for every smooth test section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.rough_pullback_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    : ∀ᶠ x in 𝓝 (0 : FourSpace),
      ∀ (T : FourSpace → CovariantCoordinates 2),
      (∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z) →
      ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (T (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (T (D.point y).1)) i x v) =
        -frameTensor (D.point x).2
          (twoFormSecondTrace (metricInChart g c (D.point x).1)⁻¹
            (covariantDerivative g c (covariantDerivative g c T) (D.point x).1)) v := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hg : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (D.point x).2ᵀ * metricInChart g c (D.point x).1 * (D.point x).2 = 1 := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.orthonormal x hx
  filter_upwards [hp, hg.eventually_nhds, D.inverseMetric_transport_near he,
    D.drift_transport_near he, ball_mem_nhds (0 : FourSpace) D.radius_pos]
      with x hpx hgx ha hb hx
  intro T hT v
  exact heatNormal_rough_pullback g c D.point T x hpx hT (D.in_chart x hx) hgx
    (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) ha hb v

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.actual_tensor_rough_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ hx : x ∈ ball 0 D.radius, ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x v) =
        -twoFormFramedRoughTrace o u (D.frame x hx) v := by
  filter_upwards [D.rough_pullback_uniform_near he] with x h
  intro u hu hx v
  rw [D.roughTrace_as_actual hu x hx]
  exact h (twoFormCoordinates o u c) (fun z hz => hu.coordinates_contDiffAt c z hz) v

theorem HeatNormalFrameData.actual_rough_components_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k) +
        (∑ i, heatNormalDrift g o e x i *
          fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k) =
        -twoFormFrameValue o (twoFormRoughTraceField o u) (D.frame x hx) k := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hg : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (D.point x).2ᵀ * metricInChart g c (D.point x).1 * (D.point x).2 = 1 := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.orthonormal x hx
  filter_upwards [hp, hg.eventually_nhds, D.actual_tensor_rough_uniform_near he]
    with x hpx hgx hr
  intro u hu hx k
  let κ : CovariantCoordinates 2 →ₗ[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k).toLinearMap.comp
      (twoFormExtractLinear.comp twoTensorMatrixLinear)
  have hκ (a : TwoFormFour) : κ (twoFormTensor a) = a k :=
    congrArg (fun b : TwoFormFour => b k) (heat_extract_twoFormTensor a)
  have hh : -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j •
      tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) +
      (∑ i, heatNormalDrift g o e x i •
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      -twoFormFramedRoughTrace o u (D.frame x hx) := by
    funext v
    simpa only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hr u hu hx v
  have hh' := congrArg κ hh
  simp only [map_neg, map_add, map_sum, map_smul, smul_eq_mul] at hh'
  have hf (i : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k := by
    rw [heatNormal_tensor_first hu c D.point x (hpx.of_le (by norm_num)) (D.in_chart x hx) hgx i, hκ]
    exact heatNormalTwoFormNabla_component hu c D.point x (hpx.of_le (by norm_num))
      (D.in_chart x hx) i k
  have hs (i j : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k := by
    rw [heatNormal_tensor_second hu c D.point x hpx (D.in_chart x hx) hgx i j, hκ]
  have ht := hu.framedValue_roughTrace hRic (D.frame x hx)
  rw [twoFormFramedValue_eq] at ht
  rw [← ht, hκ] at hh'
  simpa only [hf, hs] using hh'

theorem HeatNormalFrameData.actual_bundle_operator_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ (u : smoothTwoForms o), ∀ _hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
      fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
        (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
      heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  filter_upwards [hp, D.actual_rough_components_uniform_near he hRic] with x hpx hr
  intro u hx k
  have hd : (D.point x).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hA (i : Fin 4) (j l : Fin 6) : DifferentiableAt ℝ
      (fun y => heatTwoFormConnection g c D.point i y j l) x :=
    (heatTwoFormConnection_contDiffAt 1 c D.point x hpx (D.in_chart x hx) hd i j l).differentiableAt
      one_ne_zero
  have hv (l : Fin 6) : ContDiffAt ℝ 2
      (fun y => heatNormalTwoFormValue o c D.point u.val y l) x := by
    let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) l
    simpa only [Function.comp_def] using! π.contDiff.contDiffAt.comp x
      (heatNormalTwoFormValue_contDiffAt 2 u.property c D.point x hpx (D.in_chart x hx))
  rw [← heatNormalConnectionOperator_eq D _ x hA hv k]
  change (-(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i) j x k) +
    (∑ i, heatNormalDrift g o e x i * fourHeatCovariantDerivative
      (heatTwoFormConnection g c D.point)
      (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i x k)) + _ = _
  rw [hr u.val u.property hx k, D.value_as_actual _ x hx, heat_smoothHodge_frameValue hRic u (D.frame x hx)]
  have hV := congrArg (fun a : TwoFormFour => a k) (D.potential_action_as_actual u.val x hx)
  change (∑ l, heatNormalPotential g c D.point x k l *
      heatNormalTwoFormValue o c D.point u.val x l) =
    6 * twoFormFrameValue o u.val (D.frame x hx) k -
      2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k at hV
  rw [hV]
  change -twoFormFrameValue o (twoFormRoughTraceField o u.val) (D.frame x hx) k +
      (6 * twoFormFrameValue o u.val (D.frame x hx) k -
        2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k) = _
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! One common actual normal family for all three Euler heat degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatCommonEulerMember (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (F : HeatFamilyOneCoefficients) (r : ℝ) (e : FrameBundle g) where
  normal : HeatCommonNormalMember g o c F.base r e
  one : HeatNormalOneExtension normal.frameData
  one_base : one.base = normal.extension.base
  point_regular_four : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 4 normal.frameData.point x
  one_B_family : one.B = fun x => F.B (x, frameCoordinateState g c e)
  one_C_family : one.C = fun x => F.C (x, frameCoordinateState g c e)
  one_actual : ∀ x ∈ ball (0 : FourSpace) r,
    one.B x = heatNormalOneFirst normal.frameData x ∧
    one.C x = heatNormalOneZero normal.frameData x

theorem exists_heatUniformEulerFamily (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ F : HeatFamilyOneCoefficients, ∃ r > (0 : ℝ),
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∀ e' ∈ U, frameCoordinateState g e.base e' ∈ ball (frameCoordinateState g e.base e) (r / 2) ∧
        Nonempty (HeatCommonEulerMember g o e.base F r e') := by
  obtain ⟨F, t, _, _, hP, U₀, hU₀, he₀, R, hR, hdata⟩ := exists_heatNormalCommonChart g o e
  let p := frameCoordinateState g e.base e
  let P := heatRadialFrameFamily F t
  obtain ⟨D₀, C₀, hD₀P, hC₀, hE₀, hCt₀, _, hRD₀⟩ := hdata e he₀
  have hzero : P (0, p) = p := by simpa only [hD₀P] using D₀.initial
  have hc : (P (0, p)).1 ∈ (chartAt FourSpace e.base).target := by
    simpa only [hD₀P] using D₀.in_chart 0 (mem_ball_self D₀.radius_pos)
  have hf : (P (0, p)).2.det ≠ 0 := by
    rw [hzero]
    have hg := congrArg Matrix.det (frameChartMatrix_normalizes g e.base e (mem_chart_source FourSpace e.base))
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change p.2.det * (metricInChart g e.base p.1).det * p.2.det = 1 at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  have hm : heatFamilyMetric g e.base P (0, p) = 1 := by
    have hh := D₀.metric_slice_eq P hD₀P 0 (mem_ball_self D₀.radius_pos)
      (hP.differentiableAt (by norm_num)) (by rw [frameExponential_zero]; exact mem_chart_source FourSpace e.base)
    exact hh.trans (heatNormalMetric_zero g o e)
  have hmp : 0 < (heatFamilyMetric g e.base P (0, p)).det := by rw [hm, Matrix.det_one]; norm_num
  obtain ⟨E, ha, hb, hB, hC, hU⟩ := exists_heatFamilySmoothCoefficients g e.base P (0, p) hP hc hf hmp
  obtain ⟨F₀, _hFE, hFB, hFC⟩ := exists_heatFamilyOneCoefficients E g e.base P (0, p) hP hc hf hmp
  let F : HeatFamilyOneCoefficients := { F₀ with base := E }
  have hdetc : ContinuousAt (fun z => (heatFamilyMetric g e.base P z).det) (0, p) :=
    (heatFamilyMatrixDeterminant_contDiffAt 0 _ (0, p)
      (heatFamilyMetric_contDiffAt 0 g e.base P (0, p) (hP.of_le (by norm_num)) hc)).continuousAt
  have hdetpos : ∀ᶠ z in 𝓝 ((0 : FourSpace), p), 0 < (heatFamilyMetric g e.base P z).det :=
    hdetc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hmp)
  have hn : ∀ᶠ z in 𝓝 ((0 : FourSpace), p),
      ContDiffAt ℝ 4 P z ∧ 0 < (heatFamilyMetric g e.base P z).det ∧
      E.a =ᶠ[𝓝 z] (fun y => (heatFamilyMetric g e.base P y)⁻¹) ∧
      E.b =ᶠ[𝓝 z] heatFamilyDrift g e.base P ∧
      E.B =ᶠ[𝓝 z] heatFamilyFirst g e.base P ∧
      E.C =ᶠ[𝓝 z] heatFamilyZero g e.base P ∧
      E.U =ᶠ[𝓝 z] heatFamilyLeading g e.base P ∧
      F.B =ᶠ[𝓝 z] heatFamilyOneFirst g e.base P ∧
      F.C =ᶠ[𝓝 z] heatFamilyOneZero g e.base P := by
    filter_upwards [(hP.of_le (show (4 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num),
      hdetpos, ha.eventuallyEq_nhds, hb.eventuallyEq_nhds, hB.eventuallyEq_nhds,
      hC.eventuallyEq_nhds, hU.eventuallyEq_nhds, hFB.eventuallyEq_nhds,
      hFC.eventuallyEq_nhds] with z hz hdz haz hbz hBz hCz hUz hB1z hC1z
    exact ⟨hz, hdz, haz, hbz, hBz, hCz, hUz, hB1z, hC1z⟩
  obtain ⟨S, hS, hball⟩ := Metric.mem_nhds_iff.mp hn
  let r := min R (S / 2)
  have hr : 0 < r := lt_min hR (half_pos hS)
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r < S := (min_le_right _ _).trans_lt (half_lt_self hS)
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p (r / 2)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e (mem_chart_source FourSpace e.base)).preimage_mem_nhds
      (ball_mem_nhds _ (half_pos hr))
  obtain ⟨U, hsub, hUopen, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hcoord)
  have hpair (q : CoordinateFrameSpace) (hq : q ∈ ball p (r / 2))
      (x : FourSpace) (hx : x ∈ ball 0 r) : (x, q) ∈ ball (0, p) S := by
    change max (dist x 0) (dist q p) < S
    exact max_lt (lt_trans hx hrS) ((show dist q p < r / 2 from hq).trans
      ((half_lt_self hr).trans hrS))
  refine ⟨F, r, hr, U, hUopen, heU, ?_⟩
  intro e' he'
  obtain ⟨he'₀, hq⟩ := hsub he'
  obtain ⟨D, C, hDP, hCs, hCE, hCt, hCi, hRD⟩ := hdata e' he'₀
  let q := frameCoordinateState g e.base e'
  obtain ⟨hPq, _, haq, hbq, hBq, hCq, hUq, hB1q, hC1q⟩ := hball (hpair q hq 0 (mem_ball_self hr))
  have he'c : e'.base ∈ (chartAt FourSpace e.base).source := by
    have hh := hCt (C.map_source (hCs ▸ mem_ball_self hR))
    rwa [hCE (hCs ▸ mem_ball_self hR), frameExponential_zero] at hh
  let A := E.normalExtension D he'c P (hPq.of_le (by norm_num)) hDP haq hbq hBq hCq hUq
  have hbs : ball (0 : FourSpace) r ⊆ C.source := by rw [hCs]; exact ball_subset_ball hrR
  have hsource (x : FourSpace) (hx : x ∈ ball 0 r) :
      frameExponential g o e' x ∈ (chartAt FourSpace e.base).source := by
    rw [← hCE (hbs hx)]
    exact hCt (C.map_source (hbs hx))
  have hraw := heatFamilyNormal_on_ball D P hDP r (hrR.trans hRD)
    (fun x hx => (hball (hpair q hq x hx)).1.of_le (by norm_num)) hsource
    (fun x hx => (hball (hpair q hq x hx)).2.1)
  let N : HeatCommonNormalMember g o e.base E r e' := {
    frameData := D, extension := A, chart := C,
    radius_le := hrR.trans hRD,
    point_regular := fun x hx => by
      rw [hDP]
      exact ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := P) x
        ((hball (hpair q hq x hx)).1.of_le (by norm_num)) (contDiffAt_id.prodMk contDiffAt_const)
    metric_pos := fun x hx => by
      have hh := D.metric_slice_eq P hDP x (ball_subset_ball (hrR.trans hRD) hx)
        ((hball (hpair q hq x hx)).1.differentiableAt (by norm_num)) (hsource x hx)
      rw [← hh]
      exact (hball (hpair q hq x hx)).2.1
    ball_source := hbs, exponential := hCE, target_chart := hCt, inverse_regular := hCi,
    a_family := rfl, b_family := rfl, B_family := rfl, C_family := rfl, U_family := rfl,
    actual := fun x hx => by
      obtain ⟨_, _, hax, hbx, hBx, hCx, hUx, _, _⟩ := hball (hpair q hq x hx)
      obtain ⟨ha', hb', hB', hC', hU'⟩ := hraw x hx
      exact ⟨hax.self_of_nhds.trans ha', hbx.self_of_nhds.trans hb',
        hBx.self_of_nhds.trans hB', hCx.self_of_nhds.trans hC', hUx.self_of_nhds.trans hU'⟩ }
  let A₁ := F.normalExtension D A.base he'c P (hPq.of_le (by norm_num)) hDP hB1q hC1q
  have hraw₁ := heatFamilyOneNormal_on_ball D P hDP r (hrR.trans hRD)
    (fun x hx => (hball (hpair q hq x hx)).1.of_le (by norm_num)) hsource
    (fun x hx => (hball (hpair q hq x hx)).2.1)
  refine ⟨hq, ⟨{
    normal := N, one := A₁, one_base := rfl,
    one_B_family := rfl, one_C_family := rfl,
    point_regular_four := ?_, one_actual := ?_ }⟩⟩
  · intro x hx
    rw [hDP]
    exact ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := P) x
      (hball (hpair q hq x hx)).1 (contDiffAt_id.prodMk contDiffAt_const)
  · intro x hx
    obtain ⟨_, _, _, _, _, _, _, hB1x, hC1x⟩ := hball (hpair q hq x hx)
    exact ⟨hB1x.self_of_nhds.trans (hraw₁ x hx).1, hC1x.self_of_nhds.trans (hraw₁ x hx).2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The residual of every member of the common family is the same jointly
continuous last transport coefficient, times its explicit Gaussian factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.amplitude_family (N : HeatCommonNormalMember g o c E r e)
    (m : ℕ) (hm : m ≤ 3) :
    N.extension.amplitude m = fun x => E.amplitude m (x, frameCoordinateState g c e) := by
  unfold HeatNormalBundleExtension.amplitude
  rw [N.a_family, N.b_family, N.B_family, N.C_family, N.U_family]
  exact (E.amplitude_slice m hm _).symm

theorem HeatCommonNormalMember.amplitude_transport (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (m : ℕ) (hm : m ≤ 2) (k l : Fin 6) :
    fourHeatRadialTransport (N.extension.base.a x) (N.extension.base.b x)
      (fun y => N.extension.amplitude (m + 1) y k l) x +
      (m + 1 : ℝ) * N.extension.amplitude (m + 1) x k l =
    -fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
      (N.extension.B x) (N.extension.C x) (fun y q => N.extension.amplitude m y q l) x k := by
  obtain ⟨hrow, hcol, _, hU, _⟩ := N.transport hRic he x hx
  exact fourHeatBundleCoefficient_transport m _ _ _ _ _ x
    (N.extension.base.U_regular.of_le (by norm_num)) (fun y => (N.extension.base.U_pos y).ne')
    (fun i j => (N.extension.base.a_regular i j).of_le (by norm_num))
    (fun i => (N.extension.base.b_regular i).of_le (by norm_num))
    (fun i k l => (N.extension.B_regular i k l).of_le (by norm_num))
    (fun k l => (N.extension.C_regular k l).of_le (by norm_num))
    (fun k l => (N.extension.amplitude_regular m (by omega) k l).of_le (by norm_num))
    hrow hcol hU k l

theorem HeatCommonNormalMember.parametrix_residual (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (t : ℝ) (ht : 0 < t) (k l : Fin 6) :
    deriv (fun s => heatNormalBundleParametrix N.extension s x k l) t +
      fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
        (N.extension.B x) (N.extension.C x)
        (fun y q => heatNormalBundleParametrix N.extension t y q l) x k =
    fourHeatGaussian t x * t ^ 3 * E.lastCoefficient (x, frameCoordinateState g c e) k l := by
  obtain ⟨_, _, hEik, hU, hrad⟩ := N.transport hRic he x hx
  have hreg (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => N.extension.amplitude m y q l) :=
    (N.extension.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have hzero (q : Fin 6) : fourHeatRadialTransport (N.extension.base.a x) (N.extension.base.b x)
      (fun y => N.extension.amplitude 0 y q l) x = 0 := by
    by_cases hql : q = l
    · subst q
      simpa [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient] using hU
    · have hz : (fun y => N.extension.amplitude 0 y q l) = fun _ => (0 : ℝ) := by
        funext y
        simp [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient, hql]
      rw [hz]
      simpa only [zero_mul] using
        fourHeatRadialTransport_const_mul (N.extension.base.a x) (N.extension.base.b x) 0 N.extension.base.U x
  have hh := fourHeatBundlePolynomial_gaussian_residual (N.extension.base.a x) (N.extension.base.b x)
    (N.extension.B x) (N.extension.C x) (fun m y q => N.extension.amplitude m y q l) hreg t ht x hrad hEik hzero
    (by intro q; simpa using N.amplitude_transport hRic he x hx 0 (by omega) q l)
    (by intro q; convert N.amplitude_transport hRic he x hx 1 (by omega) q l using 1 <;> norm_num)
    (by intro q; convert N.amplitude_transport hRic he x hx 2 (by omega) q l using 1 <;> norm_num) k
  refine hh.trans ?_
  congr 1
  change fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
    (N.extension.B x) (N.extension.C x) (fun y q => N.extension.amplitude 3 y q l) x k = _
  rw [show N.extension.amplitude 3 = fun y => E.amplitude 3 (y, frameCoordinateState g c e)
    from N.amplitude_family 3 (by omega)]
  rw [N.a_family, N.b_family, N.B_family, N.C_family]
  exact (heatFamilyBundleOperator_slice E.a E.b E.B E.C _
    (fun q => (E.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) _ k).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-one de Rham vanishing: every actual smooth closed one-form is
the differential of a smooth scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothScalar_primitive (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hu : smoothOneFormExterior (o := o) u = 0) :
    ∃ f : SmoothScalar (M := M), u = smoothScalarDifferential g f := by
  obtain ⟨f, hf, hlap⟩ := actual_petersen_poisson g o hRic
    (oneFormDivergence g u) (oneFormDivergence_smooth u)
  let F : SmoothScalar (M := M) := ⟨f,hf⟩
  let v := u - smoothScalarDifferential g F
  have hc : smoothOneFormExterior (o := o) v = 0 := by
    change smoothOneFormExteriorLinear (u - smoothScalarDifferential g F) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hu.trans (smoothScalarDifferential_closed F).symm)
  have hm := oneFormDivergence_mean_zero (o := o) hRic u
  have ht (e : FrameBundle g) :
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g v.val) e ![i,i]) = 0 := by
    rw [← oneFormDivergence_eq_frame]
    have hd := congrArg (fun a : SmoothScalar (M := M) => a.val e.base)
      (map_sub (smoothOneFormDivergence g) u (smoothScalarDifferential g F))
    change oneFormDivergence g v e.base =
      oneFormDivergence g u e.base - oneFormDivergence g (smoothScalarDifferential g F) e.base at hd
    rw [hd, oneFormDivergence_differential]
    have hl := hlap e
    rw [hm, sub_zero] at hl
    exact sub_eq_zero.mpr hl.symm
  have hv : v = 0 := oneForm_harmonic_eq_zero hRic v hc ht
  exact ⟨F, sub_eq_zero.mp hv⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The degree-one Hodge Laplacian is the actual dδ+δd operator.
Its symmetry and nonnegative energy follow from the geometric adjoints. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothOneFormHodgeLaplacian : smoothCovariantFields M 1 →ₗ[ℝ] smoothCovariantFields M 1 :=
  (smoothTwoFormCodifferentialLinear (o := o)).comp smoothOneFormExteriorLinear -
    (smoothScalarDifferentialLinear g).comp (smoothOneFormDivergence g)

theorem smoothOneFormHodgeLaplacian_apply (u : smoothCovariantFields M 1) :
    smoothOneFormHodgeLaplacian (o := o) u =
      smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) u) -
        smoothScalarDifferential g (smoothOneFormDivergence g u) := rfl

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance oneFormHodge_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem smoothScalarDifferential_pairing (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothScalarDifferential g f) u =
      -(∫ x, f.val x * oneFormDivergence g u x ∂normalizedVolume g) := by
  have hi : Integrable (fun x => f.val x * oneFormDivergence g u x) (normalizedVolume g) :=
    (f.property.continuous.mul (oneFormDivergence_smooth u).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  unfold smoothOneFormL2Pairing
  simp_rw [smoothScalarDifferential_framed]
  exact scalar_oneForm_adjoint hRic f u

theorem smoothTwoFormCodifferential_pairing (hRic : RicciThree g)
    (u : smoothTwoForms o) (v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothTwoFormCodifferentialField u) v =
      smoothTwoFormL2Inner u (smoothOneFormExterior (o := o) v) := by
  rw [smoothOneFormL2Pairing_comm, smoothTwoFormL2Inner_comm,
    smoothOneFormExterior_adjoint hRic]
  simp only [smoothOneFormL2Pairing, smoothTwoFormCodifferentialField_component]

def smoothOneFormHodgeEnergy (u v : smoothCovariantFields M 1) : ℝ :=
  smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) (smoothOneFormExterior (o := o) v) +
    ∫ x, oneFormDivergence g u x * oneFormDivergence g v x ∂normalizedVolume g

theorem smoothOneFormHodgeLaplacian_pairing (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothOneFormHodgeLaplacian (o := o) u) v =
      smoothOneFormHodgeEnergy (o := o) u v := by
  rw [smoothOneFormHodgeLaplacian_apply, smoothOneFormL2Pairing_sub,
    smoothTwoFormCodifferential_pairing hRic, smoothScalarDifferential_pairing hRic]
  change _ - -_ = _ + _
  rw [sub_neg_eq_add]
  rfl

omit [CompactSpace M] [Nonempty M] in
theorem smoothOneFormHodgeEnergy_comm (u v : smoothCovariantFields M 1) :
    smoothOneFormHodgeEnergy (o := o) u v = smoothOneFormHodgeEnergy (o := o) v u := by
  unfold smoothOneFormHodgeEnergy
  rw [smoothTwoFormL2Inner_comm]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => mul_comm _ _

theorem smoothOneFormHodgeLaplacian_selfAdjoint (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothOneFormHodgeLaplacian (o := o) u) v =
      smoothOneFormL2Pairing (o := o) u (smoothOneFormHodgeLaplacian (o := o) v) := by
  rw [smoothOneFormHodgeLaplacian_pairing hRic, smoothOneFormL2Pairing_comm,
    smoothOneFormHodgeLaplacian_pairing hRic, smoothOneFormHodgeEnergy_comm]

omit [CompactSpace M] [Nonempty M] in
theorem smoothOneFormHodgeEnergy_nonneg (u : smoothCovariantFields M 1) :
    0 ≤ smoothOneFormHodgeEnergy (o := o) u u :=
  add_nonneg (smoothTwoFormL2Inner_nonneg _) (integral_nonneg fun _ => mul_self_nonneg _)

theorem smoothOneFormHodgeLaplacian_nonneg (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    0 ≤ smoothOneFormL2Pairing (o := o) (smoothOneFormHodgeLaplacian (o := o) u) u := by
  rw [smoothOneFormHodgeLaplacian_pairing hRic]
  exact smoothOneFormHodgeEnergy_nonneg u

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 heat semigroup for the nonnegative two-form Hodge
Laplacian, defined from its proved compact resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatRate (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) : ℝ :=
  μ.val⁻¹ - 1

theorem twoFormHeatRate_nonneg (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : 0 ≤ twoFormHeatRate hRic μ :=
  sub_nonneg.mpr ((one_le_inv₀ (twoFormSpectralValue_bounds hRic μ).1).mpr
    (twoFormSpectralValue_bounds hRic μ).2)

theorem twoFormHeatRate_eq_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : twoFormHeatRate hRic μ = 0 ↔ μ.val = 1 := by
  change μ.val⁻¹ - 1 = 0 ↔ _
  rw [sub_eq_zero, inv_eq_one]

def twoFormHeatWeight (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) : ℝ :=
  Real.exp (-(t : ℝ) * twoFormHeatRate hRic μ)

theorem twoFormHeatWeight_bound (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) : |twoFormHeatWeight hRic t μ| ≤ 1 := by
  rw [twoFormHeatWeight, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (twoFormHeatRate_nonneg hRic μ)

def twoFormHeat (hRic : RicciThree g) (t : ℝ≥0) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (twoFormHeatWeight hRic t) 1 zero_le_one
    (twoFormHeatWeight_bound hRic t)

theorem twoFormHeat_coordinate (hRic : RicciThree g) (t : ℝ≥0) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormHeat hRic t f)) μ =
      twoFormHeatWeight hRic t μ • (twoFormSpectralEquiv hRic f) μ :=
  twoFormSpectralMultiplier_coordinate hRic _ _ _ _ f μ

theorem twoFormHeat_zero (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormHeat hRic 0 f = f := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormHeat_coordinate]
  simp only [twoFormHeatWeight, NNReal.coe_zero, neg_zero, zero_mul, Real.exp_zero, one_smul]

theorem twoFormHeat_add (hRic : RicciThree g) (t s : ℝ≥0) (f : TwoFormL2 o) :
    twoFormHeat hRic (t + s) f = twoFormHeat hRic t (twoFormHeat hRic s f) := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormHeat_coordinate, twoFormHeat_coordinate, twoFormHeat_coordinate, smul_smul]
  congr 1
  simp only [twoFormHeatWeight, NNReal.coe_add]
  rw [← Real.exp_add]
  congr 1
  ring

theorem twoFormHeat_contraction (hRic : RicciThree g) (t : ℝ≥0) (f : TwoFormL2 o) :
    ‖twoFormHeat hRic t f‖ ≤ ‖f‖ := by
  simpa only [twoFormHeat, one_mul] using twoFormSpectralMultiplier_norm hRic
    (twoFormHeatWeight hRic t) 1 zero_le_one (twoFormHeatWeight_bound hRic t) f

theorem twoFormHeat_selfAdjoint (hRic : RicciThree g) (t : ℝ≥0) (f h : TwoFormL2 o) :
    inner ℝ (twoFormHeat hRic t f) h = inner ℝ f (twoFormHeat hRic t h) :=
  twoFormSpectralMultiplier_selfAdjoint hRic _ _ _ _ f h

theorem twoFormHeat_nonneg (hRic : RicciThree g) (t : ℝ≥0) (f : TwoFormL2 o) :
    0 ≤ inner ℝ (twoFormHeat hRic t f) f := by
  rw [twoFormHeat, twoFormSpectralMultiplier_inner]
  exact tsum_nonneg fun μ => mul_nonneg (Real.exp_pos _).le (real_inner_self_nonneg (x := _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local weak two-form equation with actual L2 coefficients on
both sides, including the localized forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

theorem twoFormL2GramValue_H1 (u : TwoFormH1 o) :
    twoFormL2GramValue c S hK hKt χ hχ hc hs hS (twoFormH1ToL2 u) =
      twoFormGramVectorL2 c S hK hKt χ hχ hc hs u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((twoFormL2GramValue c S hK hKt χ hχ hc hs hS).continuous.comp
      twoFormH1ToL2.continuous) (twoFormGramVectorL2 c S hK hKt χ hχ hc hs).continuous) ?_
  intro v
  change twoFormL2GramValue c S hK hKt χ hχ hc hs hS (twoFormH1ToL2 (smoothTwoFormToH1 v)) =
    twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 v)
  rw [twoFormH1ToL2_smooth, twoFormL2GramValue_smooth]
  rfl

variable (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)

include hon in
theorem twoFormL2_localTest (f : TwoFormL2 o) :
    inner ℝ f (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) =
      (normalizedChartFactor g).toReal * inner ℝ
        (twoFormL2GramValue c S hK hKt χ hχ hc hs hS f)
        (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt)) := by
  refine UniformSpace.Completion.induction_on f
    (isClosed_eq (continuous_id.inner continuous_const)
      (continuous_const.mul ((twoFormL2GramValue c S hK hKt χ hχ hc hs hS).continuous.inner
        continuous_const))) ?_
  intro v
  change inner ℝ (smoothTwoFormToL2 v)
    (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) =
      (normalizedChartFactor g).toReal * inner ℝ
        (twoFormL2GramValue c S hK hKt χ hχ hc hs hS (smoothTwoFormToL2 v))
        (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt))
  rw [smoothTwoFormToL2.inner_map_map, twoFormL2GramValue_smooth]
  change smoothTwoFormL2Inner (v : smoothTwoForms o) (twoFormGramTest o c S a ha hK hKt has) =
    (normalizedChartFactor g).toReal * inner ℝ
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 (smoothL2AsH1 v))) _
  rw [smoothTwoFormL2Inner_gramTest (v : smoothTwoForms o) c S hS a ha hK hKt has,
    twoFormGramVectorL2_mass c S hS hK hKt χ hχ hc hs a ha has hon (smoothL2AsH1 v)]
  rfl

variable (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hon hU hKU hp

theorem twoFormRough_localL2Equation (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) :
    inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) +
      ∑ i : Fin 4, inner ℝ (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u)
        (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt) i) =
    inner ℝ (twoFormL2GramValue c S hK hKt χ hχ hc hs hS f)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) := by
  have he := twoFormRough_localEquation c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp u f hu
  rw [twoFormL2_localTest c S hS hK hKt χ hχ hc hs a ha has hon] at he
  exact mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne' he

theorem twoFormHarmonic_localL2Equation (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) +
      ∑ i : Fin 4, inner ℝ (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u)
        (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt) i) =
    inner ℝ (twoFormL2GramValue c S hK hKt χ hχ hc hs hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) :=
  twoFormRough_localL2Equation c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp u _
    (twoFormWeakHarmonic_rough u hu)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual shifted resolvent in its spectral
coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSpectralValue_abs_le (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : |μ.val| ≤ 1 := by
  rw [abs_of_pos (twoFormSpectralValue_bounds hRic μ).1]
  exact (twoFormSpectralValue_bounds hRic μ).2

theorem twoFormShiftedResolvent_eq_multiplier (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic f = twoFormSpectralMultiplier hRic
      (fun μ => μ.val) 1 zero_le_one (twoFormSpectralValue_abs_le hRic) f := by
  have hsum := (twoFormSpectral_sum hRic f).mapL (twoFormShiftedResolvent hRic)
  have hmult := twoFormSpectral_sum hRic (twoFormSpectralMultiplier hRic
    (fun μ => μ.val) 1 zero_le_one (twoFormSpectralValue_abs_le hRic) f)
  apply hsum.unique
  convert hmult using 1
  ext μ
  rw [twoFormSpectralMultiplier_coordinate]
  exact Module.End.mem_eigenspace_iff.mp ((twoFormSpectralEquiv hRic f) μ).property

theorem twoFormShiftedResolvent_coordinate (hRic : RicciThree g) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormShiftedResolvent hRic f)) μ =
      μ.val • (twoFormSpectralEquiv hRic f) μ := by
  rw [twoFormShiftedResolvent_eq_multiplier, twoFormSpectralMultiplier_coordinate]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence for contraction multipliers on the actual
two-form spectral decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSpectralMultiplier_sub_norm_sq (hRic : RicciThree g)
    (a b : TwoFormSpectralValue (o := o) hRic → ℝ)
    (ha : ∀ μ, |a μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1) (f : TwoFormL2 o) :
    ‖twoFormSpectralMultiplier hRic a 1 zero_le_one ha f -
      twoFormSpectralMultiplier hRic b 1 zero_le_one hb f‖ ^ 2 =
      ∑' μ, (a μ - b μ) ^ 2 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (twoFormSpectralEquiv hRic).inner_map_map,
    map_sub, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  change inner ℝ
    ((twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic a 1 zero_le_one ha f)) μ -
      (twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic b 1 zero_le_one hb f)) μ)
    ((twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic a 1 zero_le_one ha f)) μ -
      (twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic b 1 zero_le_one hb f)) μ) = _
  rw [twoFormSpectralMultiplier_coordinate, twoFormSpectralMultiplier_coordinate,
    ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem twoFormSpectralMultiplier_tendsto {α : Type*} {l : Filter α}
    (hRic : RicciThree g) (a : α → TwoFormSpectralValue (o := o) hRic → ℝ)
    (b : TwoFormSpectralValue (o := o) hRic → ℝ)
    (ha : ∀ x μ, |a x μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1)
    (hab : ∀ μ, Tendsto (fun x => a x μ) l (𝓝 (b μ))) (f : TwoFormL2 o) :
    Tendsto (fun x => twoFormSpectralMultiplier hRic (a x) 1 zero_le_one (ha x) f) l
      (𝓝 (twoFormSpectralMultiplier hRic b 1 zero_le_one hb f)) := by
  have hsum : Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      4 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2) := by
    have hs := lp.summable_inner (𝕜 := ℝ)
      (twoFormSpectralEquiv hRic f) (twoFormSpectralEquiv hRic f)
    simp only [real_inner_self_eq_norm_sq] at hs
    exact hs.mul_left 4
  have hbound (x : α) (μ : TwoFormSpectralValue (o := o) hRic) :
      ‖(a x μ - b μ) ^ 2 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2‖ ≤
        4 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2 := by
    have hdiff : |a x μ - b μ| ≤ 2 :=
      (abs_sub (a x μ) (b μ)).trans (by linarith only [ha x μ, hb μ])
    have hsq : (a x μ - b μ) ^ 2 ≤ 4 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hdiff)
        (add_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a x μ - b μ)))
      nlinarith only [hprod, sq_abs (a x μ - b μ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hpoint (μ : TwoFormSpectralValue (o := o) hRic) :
      Tendsto (fun x => (a x μ - b μ) ^ 2 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2)
        l (𝓝 (0 : ℝ)) := by
    convert (((hab μ).sub_const (b μ)).pow 2).mul_const
      (‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2) using 1
    simp
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)
  simp only [tsum_zero] at ht
  have hn : Tendsto (fun x => ‖twoFormSpectralMultiplier hRic (a x) 1 zero_le_one (ha x) f -
      twoFormSpectralMultiplier hRic b 1 zero_le_one hb f‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [twoFormSpectralMultiplier_sub_norm_sq] using ht
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · exact congrArg nhds Real.sqrt_zero.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual regularized Weyl energy and sharp scalar inequality give
the limiting Holder inequality needed for equality rigidity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance gapLimitFrameCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance gapLimitProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

omit [PreconnectedSpace M] in
theorem weylRoot_weighted_moment (hRic : RicciThree g) (ε : ℝ) (k n : ℕ) :
    (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ k *
      (canonicalParallelMetricData g o hRic).toMetricGreenData.weylRootField ε e ^ n
      ∂canonicalFrameMeasure g o) =
    ∫ x, plusNorm o x ^ k * (plusNorm o x ^ 2 + ε ^ 2) ^ ((n : ℝ) / 6)
      ∂normalizedVolume g := by
  let f : M → ℝ := fun x => plusNorm o x ^ k *
    (plusNorm o x ^ 2 + ε ^ 2) ^ ((n : ℝ) / 6)
  calc
    _ = ∫ e : FrameBundle g, f e.base ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      change normalizedBlockNorm _ ^ k * regularizedWeylRoot ε _ ^ n = _
      rw [regularizedWeylRoot_eq, ← actual_plusNorm_frame o e he,
        ← Real.rpow_mul_natCast (by positivity)]
      dsimp only [f]
      congr 2
      ring
    _ = _ := canonicalFrameMeasure_integral_base g o _ (by
      have hc : Continuous f := ((continuous_plusNorm g o).pow k).mul
        ((((continuous_plusNorm g o).pow 2).add continuous_const).rpow_const
          (fun _ => Or.inr (by positivity)))
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem actual_weyl_gap_limiting_inequality (hRic : RicciThree g) :
    Real.sqrt (∫ x, ((plusNorm o x ^ 2) ^ (1 / 3 : ℝ)) ^ 2 ∂normalizedVolume g) ≤
      ∫ x, plusNorm o x * (plusNorm o x ^ 2) ^ (1 / 3 : ℝ) ∂normalizedVolume g := by
  let p := canonicalParallelMetricData g o hRic
  let d := p.toMetricGreenData
  let v : C(M, ℝ) := ⟨plusNorm o, continuous_plusNorm g o⟩
  have hs (n : ℕ) :
      Real.sqrt (∫ x, (v x ^ 2 + weylGapEpsilon n ^ 2) ^ (2 / 3 : ℝ) ∂normalizedVolume g) ≤
        (∫ x, v x * (v x ^ 2 + weylGapEpsilon n ^ 2) ^ (1 / 3 : ℝ) ∂normalizedVolume g) +
          weylGapEpsilon n ^ (2 / 3 : ℝ) := by
    let ε := weylGapEpsilon n
    have hε := weylGapEpsilon_pos n
    have hsob := sharpScalarSobolev_regularized o p (canonicalParallelMetricData_orientation o hRic)
      (actual_sharpScalarSobolev g o hRic p) ε hε
    have henergy := d.weylRoot_energy_le ε hε
    have hi₁ : Integrable (fun e => ∑ i, d.weylRootFirstField ε hε i e ^ 2)
        (canonicalFrameMeasure g o) :=
      (continuous_finsetSum _ (fun i _ => (d.weylRootFirstField ε hε i).continuous.pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi₂ : Integrable (fun e => 2 * d.weylRootField ε e ^ 2)
        (canonicalFrameMeasure g o) :=
      ((d.weylRootField ε).continuous.pow 2).const_mul 2
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_add hi₁ hi₂, integral_const_mul, probReal_univ, mul_one] at henergy
    have hbound : Real.sqrt (∫ e, d.weylRootField ε e ^ 4 ∂canonicalFrameMeasure g o) ≤
        (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) *
          d.weylRootField ε e ^ 2 ∂canonicalFrameMeasure g o) + ε ^ (2 / 3 : ℝ) := by
      linarith
    have h4 := weylRoot_weighted_moment (o := o) hRic ε 0 4
    have h2 := weylRoot_weighted_moment (o := o) hRic ε 1 2
    norm_num only [pow_zero, one_mul, pow_one, Nat.cast_ofNat] at h4 h2
    simpa only [h4, h2, v, ContinuousMap.coe_mk, d, p, ε] using hbound
  have ht4 := integral_weyl_regularized_power_tendsto (normalizedVolume g) v 1
    (2 / 3 : ℝ) (by norm_num)
  simp only [ContinuousMap.one_apply, one_mul] at ht4
  have ht2 := integral_weyl_regularized_power_tendsto (normalizedVolume g) v v
    (1 / 3 : ℝ) (by norm_num)
  have htε := weylGapEpsilon_tendsto.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))
  have hlim := le_of_tendsto_of_tendsto (Real.continuous_sqrt.continuousAt.tendsto.comp ht4)
    (ht2.add htε) (Eventually.of_forall hs)
  simp only [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), add_zero] at hlim
  convert hlim using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Real.rpow_mul_natCast (sq_nonneg _)]
  norm_num [v]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration of a divergence whose flux, rather than its test, is compact. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeat_compact_flux_green
    (A : Fin 4 → FourSpace → HeatMat6)
    (W : Fin 4 → FourSpace → Fin 6 → ℝ) (v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace)
    (hW : ∀ i k, ContDiff ℝ 1 (fun x => W i x k))
    (hcW : ∀ i k, HasCompactSupport (fun x => W i x k))
    (hsW : ∀ i k, tsupport (fun x => W i x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 6,
      v x k * fourHeatCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A v i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      v x k * fourHeatCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) hv (fun x hx k l => hA x hx i k l)
      (fun x hx => hskew x hx i)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatCovariantDerivative_green A (W i) v U i (hW i) (hcW i) (hsW i)
    hv (fun x hx k l => hA x hx i k l) (fun x hx => hskew x hx i)
  simpa only [mul_comm] using h

theorem fourHeat_potential_pairing_swap
    (u v : FourSpace → Fin 6 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → HeatMat6) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hV : ∀ x ∈ U, ∀ k l, V x k l = V x l k) (x : FourSpace) :
    (∑ k, v x k * (ρ x * ∑ l, V x k l * u x l)) =
      ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  by_cases hx : x ∈ U
  · have hp (p q : Fin 6 → ℝ) : (∑ k, p k * (ρ x * ∑ l, V x k l * q l)) =
        ρ x * ∑ k, p k * ∑ l, V x k l * q l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hp, hp, fourHeat_potential_pairing_symm (V x) (hV x hx)]
  · have hz (k : Fin 6) : u x k = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => u y k) (fun h => hx (hs k h))
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual normal chart supports all smooth Hodge tests and the
finite-regularity frame and inverse needed by the compact parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatNormalOperatorChart {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 4 C.symm C.target ∧
      C.target ⊆ (chartAt FourSpace c).source ∧
      ContDiffOn ℝ 4 D.point C.source ∧ C.source ⊆ ball 0 D.radius ∧
      ∀ x ∈ C.source, ∀ u : smoothTwoForms o, ∀ k : Fin 6,
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
        heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
  obtain ⟨r₀, C₀, hr₀, hC₀, hE, hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ C₀.source ∧
      ∀ u : smoothTwoForms o, ∀ hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
        heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
    filter_upwards [hC₀ ▸ ball_mem_nhds (0 : FourSpace) hr₀,
      D.actual_bundle_operator_uniform_near he hRic] with x hx hop
    exact ⟨hx, hop⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let C := C₀.restrOpen (ball 0 r) isOpen_ball
  have hs : C.source = ball 0 r := inter_eq_right.mpr (fun x hx => (hball hx).1)
  refine ⟨r, C, hr, hs, (fun x hx => hE hx.1), ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (hI.contMDiffAt (C₀.open_target.mem_nhds hy.1)).contMDiffWithinAt
  · intro y hy
    exact hCt hy.1
  · intro x hx
    exact (hP.contDiffAt (C₀.open_source.mem_nhds hx.1)).contDiffWithinAt
  · intro x hx
    exact hD hx.1
  · intro x hx u k
    exact (hball (hs ▸ hx)).2 u (hD hx.1) k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual codifferential extends continuously from the two-form H1
completion into the one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothH1Codifferential : SmoothH1TwoForm o →ₗ[ℝ] SmoothL2OneForm o where
  toFun u := ⟨smoothTwoFormCodifferentialField u⟩
  map_add' u v := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothTwoFormCodifferentialLinear (o := o)).map_add u v
  map_smul' r u := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothTwoFormCodifferentialLinear (o := o)).map_smul r u

theorem smoothH1Codifferential_norm_sq (u : SmoothH1TwoForm o) :
    ‖smoothH1Codifferential u‖ ^ 2 =
      twoFormCodiffPairing (u : smoothTwoForms o) (u : smoothTwoForms o) := by
  rw [← real_inner_self_eq_norm_sq, smoothOneForm_inner_eq]
  change smoothOneFormL2Pairing (o := o)
    (smoothTwoFormCodifferentialField (u : smoothTwoForms o))
    (smoothTwoFormCodifferentialField (u : smoothTwoForms o)) = _
  exact integral_congr_ae (Filter.Eventually.of_forall fun e =>
    Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·)
      (smoothTwoFormCodifferentialField_component (u : smoothTwoForms o) e k)
      (smoothTwoFormCodifferentialField_component (u : smoothTwoForms o) e k))

theorem smoothH1Codifferential_norm_le (hRic : RicciThree g) (u : SmoothH1TwoForm o) :
    ‖smoothH1Codifferential u‖ ≤ (1 + ‖twoFormWeitzenbockPotential (o := o)‖) * ‖u‖ := by
  let v := smoothTwoFormToH1 u
  let w := twoFormH1ToL2 v
  let K := ‖twoFormWeitzenbockPotential (o := o)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hv : ‖v‖ = ‖u‖ := smoothTwoFormToH1.norm_map u
  have hw : ‖w‖ ≤ ‖u‖ := (twoFormH1ToL2_norm_le v).trans_eq hv
  have hc : 0 ≤ twoFormCodiffPairing (smoothTwoFormHodge o (u : smoothTwoForms o))
      (smoothTwoFormHodge o (u : smoothTwoForms o)) := by
    exact integral_nonneg fun e => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have he : ‖smoothH1Codifferential u‖ ^ 2 ≤ twoFormHodgeForm v v := by
    have hf := twoFormHodgeForm_smooth hRic u
    have hs := smoothTwoFormDeRhamEnergy_codiff (u : smoothTwoForms o)
    have hn := smoothH1Codifferential_norm_sq u
    change twoFormHodgeForm v v = _ at hf
    linarith only [hf, hs, hn, hc]
  have hi : -inner ℝ (twoFormWeitzenbockPotential w) w ≤ K * ‖u‖ ^ 2 := by
    calc
      -inner ℝ (twoFormWeitzenbockPotential w) w ≤
          ‖twoFormWeitzenbockPotential w‖ * ‖w‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      _ ≤ (K * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right
        (twoFormWeitzenbockPotential.le_opNorm w) (norm_nonneg _)
      _ ≤ K * ‖u‖ ^ 2 := by
        have hs := (sq_le_sq₀ (norm_nonneg w) (norm_nonneg u)).mpr hw
        nlinarith [mul_le_mul_of_nonneg_left hs hK]
  have hb : ‖smoothH1Codifferential u‖ ^ 2 ≤ (1 + K) * ‖u‖ ^ 2 := by
    change ‖smoothH1Codifferential u‖ ^ 2 ≤ inner ℝ v v -
      inner ℝ (twoFormWeitzenbockPotential w) w at he
    rw [real_inner_self_eq_norm_sq, hv] at he
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  have hk : 1 + K ≤ (1 + K) ^ 2 := by nlinarith
  calc
    ‖smoothH1Codifferential u‖ ^ 2 ≤ (1 + K) * ‖u‖ ^ 2 := hb
    _ ≤ (1 + K) ^ 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    _ = ((1 + K) * ‖u‖) ^ 2 := by ring

def smoothH1CodifferentialCLM (hRic : RicciThree g) :
    SmoothH1TwoForm o →L[ℝ] SmoothL2OneForm o :=
  smoothH1Codifferential.mkContinuous (1 + ‖twoFormWeitzenbockPotential (o := o)‖)
    (smoothH1Codifferential_norm_le hRic)

def twoFormH1Codifferential (hRic : RicciThree g) : TwoFormH1 o →L[ℝ] OneFormL2 o :=
  (smoothOneFormToL2.toContinuousLinearMap.comp (smoothH1CodifferentialCLM hRic)).fromCompletion

theorem twoFormH1Codifferential_smooth (hRic : RicciThree g) (u : SmoothH1TwoForm o) :
    twoFormH1Codifferential hRic (smoothTwoFormToH1 u) =
      smoothOneFormToL2 ⟨smoothTwoFormCodifferentialField (u : smoothTwoForms o)⟩ :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative from actual scalar H1 to actual one-form L2.
The extension is made along the dense range of smooth first jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem smoothScalarFirstJet_injective
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Function.Injective (smoothScalarFirstJet d) := by
  intro f h he
  apply smoothScalarValueL2_injective g o
  exact congrArg (fun u : ScalarJetL2 g (canonicalFrameMeasure g o) => u none) he

def scalarFirstJetRangeEquiv (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    SmoothScalar (M := M) ≃ₗ[ℝ] LinearMap.range (smoothScalarFirstJet d) :=
  LinearEquiv.ofInjective (smoothScalarFirstJet d) (smoothScalarFirstJet_injective d)

def scalarFirstJetRangeInclusion (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    LinearMap.range (smoothScalarFirstJet d) →ₗᵢ[ℝ] scalarH1 d where
  toLinearMap :=
    { toFun := fun u => ⟨u.val, Submodule.le_topologicalClosure _ u.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' _ := rfl

theorem scalarFirstJetRangeInclusion_dense
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    DenseRange (scalarFirstJetRangeInclusion d) := by
  change Dense (Set.range (scalarFirstJetRangeInclusion d))
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro u
  apply closure_mono (s := Set.range (smoothScalarFirstJet d)) ?_ u.property
  rintro v ⟨a, rfl⟩
  exact ⟨scalarFirstJetRangeInclusion d (scalarFirstJetRangeEquiv d a),
    ⟨scalarFirstJetRangeEquiv d a, rfl⟩, rfl⟩

theorem scalarFirstJetRangeInclusion_equiv
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    scalarFirstJetRangeInclusion d (scalarFirstJetRangeEquiv d f) = smoothScalarToH1 d f := rfl

theorem smoothScalarDifferential_dirichlet
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f h : SmoothScalar (M := M)) :
    smoothOneFormL2Pairing (o := o) (smoothScalarDifferential g f)
      (smoothScalarDifferential g h) = smoothScalarDirichlet d f h := by
  rw [smoothScalarDirichlet_eq_integral]
  unfold smoothOneFormL2Pairing
  simp only [smoothScalarDifferential_framed]

theorem smoothScalarDifferential_norm_le
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    ‖(⟨smoothScalarDifferential g f⟩ : SmoothL2OneForm o)‖ ≤ ‖smoothScalarToH1 d f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, smoothOneForm_inner_eq,
    smoothScalarDifferential_dirichlet d, scalarH1_norm_sq]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth]
  unfold smoothScalarDirichlet
  simp only [real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

def smoothScalarDifferentialL2 : SmoothScalar (M := M) →ₗ[ℝ] SmoothL2OneForm o where
  toFun f := ⟨smoothScalarDifferential g f⟩
  map_add' f h := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothScalarDifferentialLinear g).map_add f h
  map_smul' r f := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothScalarDifferentialLinear g).map_smul r f

def scalarFirstJetDifferential (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    LinearMap.range (smoothScalarFirstJet d) →ₗ[ℝ] SmoothL2OneForm o :=
  smoothScalarDifferentialL2.comp (scalarFirstJetRangeEquiv d).symm.toLinearMap

theorem scalarFirstJetDifferential_equiv
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    scalarFirstJetDifferential d (scalarFirstJetRangeEquiv d f) =
      (⟨smoothScalarDifferential g f⟩ : SmoothL2OneForm o) := by
  change smoothScalarDifferentialL2
    ((scalarFirstJetRangeEquiv d).symm (scalarFirstJetRangeEquiv d f)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem scalarFirstJetDifferential_norm_le
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : LinearMap.range (smoothScalarFirstJet d)) : ‖scalarFirstJetDifferential d u‖ ≤ ‖u‖ := by
  obtain ⟨f, rfl⟩ := (scalarFirstJetRangeEquiv d).surjective u
  rw [scalarFirstJetDifferential_equiv]
  exact smoothScalarDifferential_norm_le d f

def scalarFirstJetDifferentialCLM (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    LinearMap.range (smoothScalarFirstJet d) →L[ℝ] OneFormL2 o :=
  smoothOneFormToL2.toContinuousLinearMap.comp
    ((scalarFirstJetDifferential d).mkContinuous 1
      (fun u => by simpa only [one_mul] using scalarFirstJetDifferential_norm_le d u))

def scalarH1Differential (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    scalarH1 d →L[ℝ] OneFormL2 o :=
  (scalarFirstJetDifferentialCLM d).extend (scalarFirstJetRangeInclusion d).toContinuousLinearMap

theorem scalarH1Differential_range
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : LinearMap.range (smoothScalarFirstJet d)) :
    scalarH1Differential d (scalarFirstJetRangeInclusion d u) =
      scalarFirstJetDifferentialCLM d u := by
  exact ContinuousLinearMap.extend_eq (scalarFirstJetDifferentialCLM d)
    (e := (scalarFirstJetRangeInclusion d).toContinuousLinearMap)
    (scalarFirstJetRangeInclusion_dense d)
    (scalarFirstJetRangeInclusion d).isometry.isUniformInducing u

theorem scalarH1Differential_smooth
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    scalarH1Differential d (smoothScalarToH1 d f) =
      smoothOneFormToL2 (⟨smoothScalarDifferential g f⟩ : SmoothL2OneForm o) := by
  calc
    _ = scalarH1Differential d
        (scalarFirstJetRangeInclusion d (scalarFirstJetRangeEquiv d f)) :=
      congrArg (scalarH1Differential d) (scalarFirstJetRangeInclusion_equiv d f).symm
    _ = scalarFirstJetDifferentialCLM d (scalarFirstJetRangeEquiv d f) :=
      scalarH1Differential_range d _
    _ = _ := congrArg smoothOneFormToL2 (scalarFirstJetDifferential_equiv d f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual closed/exact degree-one quotient vanishes under Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev smoothClosedOneForms : Submodule ℝ (smoothCovariantFields M 1) :=
  (smoothOneFormExteriorLinear (o := o)).ker

local instance : AddCommGroup (smoothClosedOneForms (o := o)) :=
  Submodule.addCommGroup _

def smoothExactOneForms : Submodule ℝ (smoothClosedOneForms (o := o)) :=
  (LinearMap.range (smoothScalarDifferentialLinear g)).comap
    (smoothClosedOneForms (o := o)).subtype

abbrev OneFormDeRhamCohomology :=
  (smoothClosedOneForms (o := o)) ⧸ (smoothExactOneForms (o := o))

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]

theorem smoothExactOneForms_eq_top (hRic : RicciThree g) :
    smoothExactOneForms (o := o) = ⊤ := by
  apply top_unique
  intro u _
  obtain ⟨f, hf⟩ := exists_smoothScalar_primitive hRic u.val u.property
  change u.val ∈ LinearMap.range (smoothScalarDifferentialLinear g)
  exact ⟨f, hf.symm⟩

theorem oneFormDeRhamCohomology_eq_zero (hRic : RicciThree g)
    (u : OneFormDeRhamCohomology (o := o)) : u = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := smoothExactOneForms (o := o)) u
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [smoothExactOneForms_eq_top hRic]
  trivial

theorem oneFormDeRhamCohomology_subsingleton (hRic : RicciThree g) :
    Subsingleton (OneFormDeRhamCohomology (o := o)) :=
  ⟨fun u v => (oneFormDeRhamCohomology_eq_zero hRic u).trans
    (oneFormDeRhamCohomology_eq_zero hRic v).symm⟩

theorem oneFormDeRhamCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (OneFormDeRhamCohomology (o := o)) = 0 := by
  let _ := oneFormDeRhamCohomology_subsingleton (o := o) hRic
  exact Module.finrank_zero_of_subsingleton

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive Ricci curvature eliminates the kernel of the actual
degree-one Hodge Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormKernel_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem smoothOneFormHodgeLaplacian_eq_zero (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hu : smoothOneFormHodgeLaplacian (o := o) u = 0) :
    u = 0 := by
  have he := smoothOneFormHodgeLaplacian_pairing (o := o) hRic u u
  rw [hu] at he
  have hz : smoothOneFormL2Pairing (o := o) 0 u = 0 := by
    simpa only [zero_smul, zero_mul] using smoothOneFormL2Pairing_smul (o := o) 0 u u
  rw [hz] at he
  have hdiv : 0 ≤ ∫ x, oneFormDivergence g u x * oneFormDivergence g u x
      ∂normalizedVolume g := integral_nonneg fun _ => mul_self_nonneg _
  have hnonneg := smoothTwoFormL2Inner_nonneg (smoothOneFormExterior (o := o) u)
  have hdu : smoothOneFormExterior (o := o) u = 0 := by
    apply smoothTwoFormL2Inner_definite
    change 0 = _ + _ at he
    linarith
  have hbase : (∫ x, oneFormDivergence g u x ^ 2 ∂normalizedVolume g) = 0 := by
    change 0 = _ + _ at he
    simp only [pow_two]
    linarith
  let f := smoothOneFormDivergence g u
  have hi : Integrable (fun x => f.val x ^ 2) (normalizedVolume g) :=
    (f.property.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf : f = 0 := smoothScalar_eq_zero_of_square_integral (o := o) f
    ((canonicalFrameMeasure_integral_base g o _ hi).trans hbase)
  apply oneForm_harmonic_eq_zero hRic u hdu
  intro e
  rw [← oneFormDivergence_eq_frame]
  exact congrArg (fun v : SmoothScalar (M := M) => v.val e.base) hf

theorem smoothOneFormHodgeLaplacian_injective (hRic : RicciThree g) :
    Function.Injective (smoothOneFormHodgeLaplacian (o := o)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply smoothOneFormHodgeLaplacian_eq_zero hRic
  rw [map_sub, huv, sub_self]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-one Weitzenböck equation for Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

include o in
theorem oneFormDivergence_gradient (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (e : FrameBundle g) (j : Fin 4) :
    scalarGradient g (oneFormDivergence g u) e j =
      ∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![j,i,i] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow j).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic j e
  have hidx (i : Fin 4) : Fin.cons j ![i,i] = ![j,i,i] := by
    ext k
    fin_cases k <;> rfl
  have hd : HasDerivAt
      (fun t => ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![i,i])
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (γ 0) ![j,i,i]) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [hidx] using u.property.derivative.parallel_derivative (g := g) γ 0 j
      (d.curve_continuous j e).continuousAt (d.parallelCurve j 0 e) ![i,i]
  have heq : (fun t => ∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) (γ t) ![i,i]) =
      (fun t => oneFormDivergence g u (γ t).base) := by
    funext t
    exact (oneFormDivergence_eq_frame u (γ t)).symm
  rw [heq] at hd
  have hg := actual_scalarValue_parallel_derivative g (oneFormDivergence_smooth (g := g) u) γ 0 j
    (d.curve_continuous j e).continuousAt (d.parallelCurve j 0 e)
  have h := hg.unique hd
  simpa only [hzero] using h

theorem smoothOneForm_Weitzenbock (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (e : FrameBundle g) (j : Fin 4) :
    covariantFieldFramed g (smoothOneFormHodgeLaplacian (o := o) u).val e ![j] =
      -(∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,i,j]) + 3 * covariantFieldFramed g u.val e ![j] := by
  have hsub := congrFun (covariantFieldFramed_add (g := g)
    (smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) u)).val
    (-((smoothScalarDifferential g (smoothOneFormDivergence g u)).val)) e) ![j]
  have hneg := congrFun (covariantFieldFramed_smul (g := g) (-1 : ℝ)
    (smoothScalarDifferential g (smoothOneFormDivergence g u)).val e) ![j]
  have hc := oneForm_ricci_commutator hRic u e j
  rw [Finset.sum_sub_distrib] at hc
  change covariantFieldFramed g
    ((smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) u)).val +
      -(smoothScalarDifferential g (smoothOneFormDivergence g u)).val) e ![j] = _
  rw [hsub]
  simp only [Pi.add_apply]
  rw [← neg_one_smul ℝ ((smoothScalarDifferential g (smoothOneFormDivergence g u)).val),
    hneg, smoothTwoFormCodifferentialField_component]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [smoothScalarDifferential_framed]
  change -(∑ i, twoFormFramedCovariantDerivative o (smoothOneFormExterior (o := o) u).val e ![i,i,j]) +
    (-1 : ℝ) * scalarGradient g (oneFormDivergence g u) e j = _
  simp_rw [smoothOneFormExterior_covariant hRic, Finset.sum_sub_distrib]
  rw [oneFormDivergence_gradient (o := o) hRic]
  linarith only [hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong continuity of the actual two-form heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatWeight_continuous (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Continuous (fun t : ℝ≥0 => twoFormHeatWeight hRic t μ) := by
  change Continuous (fun t : ℝ≥0 => Real.exp (-(t : ℝ) * twoFormHeatRate hRic μ))
  exact Real.continuous_exp.comp (continuous_subtype_val.neg.mul_const _)

theorem twoFormHeat_continuous (hRic : RicciThree g) (f : TwoFormL2 o) :
    Continuous (fun t : ℝ≥0 => twoFormHeat hRic t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact twoFormSpectralMultiplier_tendsto hRic (twoFormHeatWeight hRic)
    (twoFormHeatWeight hRic t) (twoFormHeatWeight_bound hRic)
    (twoFormHeatWeight_bound hRic t)
    (fun μ => (twoFormHeatWeight_continuous hRic μ).continuousAt) f

theorem twoFormHeat_tendsto_zero_time (hRic : RicciThree g) (f : TwoFormL2 o) :
    Tendsto (fun t : ℝ≥0 => twoFormHeat hRic t f) (𝓝 0) (𝓝 f) := by
  have h := (twoFormHeat_continuous hRic f).continuousAt (x := 0)
  change Tendsto (fun t : ℝ≥0 => twoFormHeat hRic t f) (𝓝 0)
    (𝓝 (twoFormHeat hRic 0 f)) at h
  rwa [twoFormHeat_zero] at h

theorem twoFormHeat_joint_continuous (hRic : RicciThree g) :
    Continuous (fun tf : ℝ≥0 × TwoFormL2 o => twoFormHeat hRic tf.1 tf.2) := by
  apply continuous_iff_continuousAt.mpr
  intro tf
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have htime := Metric.continuousAt_iff.mp
    ((twoFormHeat_continuous hRic tf.2).continuousAt (x := tf.1))
    (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, htime⟩ := htime
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
  intro sf hsf
  have hst : dist sf.1 tf.1 < δ := by
    calc
      dist sf.1 tf.1 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ < δ := lt_of_lt_of_le hsf (min_le_left _ _)
  have hsu : dist sf.2 tf.2 < ε / 2 := by
    calc
      dist sf.2 tf.2 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε / 2 := lt_of_lt_of_le hsf (min_le_right _ _)
  calc
    dist (twoFormHeat hRic sf.1 sf.2) (twoFormHeat hRic tf.1 tf.2) ≤
        dist (twoFormHeat hRic sf.1 sf.2) (twoFormHeat hRic sf.1 tf.2) +
        dist (twoFormHeat hRic sf.1 tf.2) (twoFormHeat hRic tf.1 tf.2) := dist_triangle _ _ _
    _ ≤ dist sf.2 tf.2 + dist (twoFormHeat hRic sf.1 tf.2) (twoFormHeat hRic tf.1 tf.2) := by
      apply add_le_add_left
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      exact twoFormHeat_contraction hRic sf.1 (sf.2 - tf.2)
    _ < ε / 2 + ε / 2 := add_lt_add hsu (htime hst)
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time heat lies in the actual weak Hodge domain. The
resolvent lift is obtained from an explicit bounded spectral multiplier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatLiftWeight_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    |μ.val⁻¹ * twoFormHeatWeight hRic t μ| ≤ Real.exp t / t := by
  have htR : 0 < (t : ℝ) := ht
  have hm := (twoFormSpectralValue_bounds hRic μ).1
  have he : (t : ℝ) * μ.val⁻¹ ≤ Real.exp ((t : ℝ) * μ.val⁻¹) := by
    have h := Real.add_one_le_exp ((t : ℝ) * μ.val⁻¹)
    linarith only [h]
  have he' := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-((t : ℝ) * μ.val⁻¹))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at he'
  have hweight : twoFormHeatWeight hRic t μ =
      Real.exp t * Real.exp (-((t : ℝ) * μ.val⁻¹)) := by
    rw [twoFormHeatWeight, twoFormHeatRate, ← Real.exp_add]
    congr 1
    ring
  rw [hweight, abs_of_pos (mul_pos (inv_pos.mpr hm)
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)))]
  calc
    μ.val⁻¹ * (Real.exp t * Real.exp (-((t : ℝ) * μ.val⁻¹))) =
        (Real.exp t / t) * (((t : ℝ) * μ.val⁻¹) * Real.exp (-((t : ℝ) * μ.val⁻¹))) := by
      field_simp [ne_of_gt htR]
    _ ≤ (Real.exp t / t) * 1 := mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := mul_one _

def twoFormHeatLiftSource (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (fun μ => μ.val⁻¹ * twoFormHeatWeight hRic t μ)
    (Real.exp t / t) (by positivity) (twoFormHeatLiftWeight_bound hRic t ht)

theorem twoFormHeatLiftSource_resolvent (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic (twoFormHeatLiftSource hRic t ht f) = twoFormHeat hRic t f := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormShiftedResolvent_coordinate, twoFormHeat_coordinate]
  change μ.val • (twoFormSpectralEquiv hRic
    (twoFormSpectralMultiplier hRic _ _ _ _ f)) μ = _
  rw [twoFormSpectralMultiplier_coordinate, smul_smul]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1), one_mul]

def twoFormHeatLift (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    TwoFormL2 o →L[ℝ] TwoFormH1 o :=
  (twoFormShiftedSolution hRic).comp (twoFormHeatLiftSource hRic t ht)

theorem twoFormHeatLift_value (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) : twoFormH1ToL2 (twoFormHeatLift hRic t ht f) = twoFormHeat hRic t f :=
  twoFormHeatLiftSource_resolvent hRic t ht f

theorem twoFormHeatLift_weak (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) (v : TwoFormH1 o) :
    twoFormHodgeForm (twoFormHeatLift hRic t ht f) v =
      inner ℝ (twoFormHeatLiftSource hRic t ht f - twoFormHeat hRic t f) (twoFormH1ToL2 v) := by
  have h := twoFormShiftedSolution_weak hRic (twoFormHeatLiftSource hRic t ht f) v
  change twoFormHodgeForm (twoFormHeatLift hRic t ht f) v +
    inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht f)) (twoFormH1ToL2 v) = _ at h
  rw [twoFormHeatLift_value] at h
  rw [inner_sub_left]
  linarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The completed Weitzenböck potential has the actual smooth chart
coefficients. In particular its compact chart coordinates are H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormWeitzenbockPotential_smooth (w : SmoothL2TwoForm o) :
    twoFormWeitzenbockPotential (smoothTwoFormToL2 w) =
      smoothTwoFormToL2 ((2 : ℝ) • smoothL2Curvature w - (5 : ℝ) • w) := by
  change (2 : ℝ) • twoFormL2Curvature (smoothTwoFormToL2 w) -
    (5 : ℝ) • smoothTwoFormToL2 w = _
  rw [twoFormL2Curvature_smooth, map_sub, map_smul, map_smul]

theorem twoFormChartValue_potential (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (w : SmoothL2TwoForm o) (z : FourSpace) :
    twoFormChartValue o
      (((2 : ℝ) • smoothL2Curvature w - (5 : ℝ) • w : SmoothL2TwoForm o) :
        smoothTwoForms o).val c S hS z =
      twoFormChartPotential (g := g) c S z
        (twoFormChartValue o (w : smoothTwoForms o).val c S hS z) := by
  change twoFormChartValue o
    ((2 : ℝ) • twoFormCurvatureField o (w : smoothTwoForms o).val -
      (5 : ℝ) • (w : smoothTwoForms o).val) c S hS z = _
  have hcurv : twoFormChartValue o (twoFormCurvatureField o (w : smoothTwoForms o).val)
      c S hS z = twoFormCurvatureOperator
        (frameTensor (chartGramMatrix g c S z) (curvatureCoordinates g c z))
        (twoFormChartValue o (w : smoothTwoForms o).val c S hS z) := by
    by_cases hz : z ∈ (chartAt FourSpace c).target
    · simp only [twoFormChartValue, dite_eq_left hz]
      rw [twoFormCurvatureField_frame, twoFormMetricCurvatureTensor_chart]
      rfl
    · simp only [twoFormChartValue, dite_eq_right hz, map_zero]
  rw [sub_eq_add_neg, ← neg_smul]
  rw [twoFormChartValue_add, twoFormChartValue_smul, twoFormChartValue_smul]
  simp only [Pi.add_apply, Pi.smul_apply, hcurv]
  let a := twoFormChartValue o (w : smoothTwoForms o).val c S hS z
  let R := twoFormCurvatureOperator
    (frameTensor (chartGramMatrix g c S z) (curvatureCoordinates g c z))
  change (2 : ℝ) • R a + (-5 : ℝ) • a = (2 : ℝ) • R a - (5 : ℝ) • a
  rw [neg_smul, sub_eq_add_neg]

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηK : tsupport η ⊆ K) (hon : ∀ z ∈ tsupport η, χ z = 1)

include hon in
theorem twoFormPotential_chart_pair (u : TwoFormH1 o) (r : Fin 6) :
    twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) =
      twoFormCoefficientPairL2 (twoFormPotentialCoefficient (g := g) c S η r)
        (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
        (twoFormPotentialCoefficient_compact c S η hcη r)
        (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq
      ((twoFormVectorComponentL2 r).continuous.comp
        ((twoFormL2GramValue c S hK hKt η hη hcη hηK hS).continuous.comp
          (twoFormWeitzenbockPotential.continuous.comp twoFormH1ToL2.continuous)))
      ((twoFormCoefficientPairL2 _ _ _).continuous.comp
        (twoFormGramVectorL2 c S hK hKt χ hχ hc hs).continuous)) ?_
  intro w
  change twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 (smoothTwoFormToH1 w)))) =
    twoFormCoefficientPairL2 (twoFormPotentialCoefficient (g := g) c S η r)
      (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
      (twoFormPotentialCoefficient_compact c S η hcη r)
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w))
  rw [twoFormH1ToL2_smooth, twoFormWeitzenbockPotential_smooth, twoFormL2GramValue_smooth]
  apply Lp.ext
  have hl := twoFormGramVectorL2_coe c S hS hK hKt η hη hcη hηK
    (smoothL2AsH1 ((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w))
  have hr := twoFormGramVectorL2_coe c S hS hK hKt χ hχ hc hs w
  filter_upwards [twoFormVectorComponentL2_coe r
      (smoothTwoFormGramL2Linear c S hK hKt η hη hcη hηK
        ((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w)),
    hl, twoFormCoefficientPair_coe (twoFormPotentialCoefficient (g := g) c S η r)
      (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
      (twoFormPotentialCoefficient_compact c S η hcη r)
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w)), hr]
      with z hz hlz hp hrz
  rw [hz]
  change (twoFormGramVectorL2 c S hK hKt η hη hcη hηK
    (smoothTwoFormToH1 (smoothL2AsH1
      ((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w)))) z r = _
  rw [hlz]
  change η z * twoFormChartValue o
    (((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w :
      SmoothL2TwoForm o) : smoothTwoForms o).val c S hS z r = _
  have hp' : (twoFormCoefficientPairL2 (twoFormPotentialCoefficient (g := g) c S η r)
      (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
      (twoFormPotentialCoefficient_compact c S η hcη r)
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w))) z =
    inner ℝ ((twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w)) z)
      (twoFormPotentialCoefficient (g := g) c S η r z) := hp
  rw [hp', hrz, twoFormChartValue_potential]
  rw [inner_smul_left, twoFormPotentialCoefficient_pair]
  change η z * _ = χ z * (η z * _)
  by_cases he : η z = 0
  · simp only [he, zero_mul, mul_zero]
  · rw [hon z (subset_tsupport η he), one_mul]
    rfl

include hon hχ hc hs in
theorem twoFormPotential_chart_memSobolev_one (u : TwoFormH1 o) (r : Fin 6) :
    MemSobolev 1 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))) : 𝓢'(FourSpace, ℂ)) := by
  rw [twoFormPotential_chart_pair c S hS hK hKt χ hχ hc hs η hη hcη hηK hon]
  exact twoFormCoefficientPair_memSobolev_one _
    (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r)
    (twoFormPotentialCoefficient_compact c S η hcη r) _
    (fun k => twoFormGramVectorComponent_memSobolev_one c S hK hKt χ hχ hc hs u k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar component divergence equations with actual L2 flux and source,
deduced from the intrinsic weak rough equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormScalarTestL2 (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  (hψ.continuous.memLp_of_hasCompactSupport hcψ).toLp ψ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (χ ψ : FourSpace → ℝ)
  (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hχs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψs : tsupport ψ ⊆ (chartAt FourSpace c).target)
  (hon : ∀ z ∈ tsupport ψ, χ z = 1) (b : TwoFormFour)

include hon in
theorem twoFormMassPair_scalarTest (V : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    inner ℝ V (twoFormMassTestL2 (g := g) c (fun z => ψ z • b) (hψ.smul contDiff_const).contDiffOn
      hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs)) =
      inner ℝ (twoFormMassPair (g := g) c χ hχ hcχ hχs b V) (twoFormScalarTestL2 ψ hψ hcψ) := by
  rw [twoFormMassTestL2_separated c χ ψ hχ hcχ hχs hψ hcψ hψs hon b]
  exact (twoFormCoefficientPair_test _ _ _ V ψ hψ.continuous hcψ).symm

include hon in
theorem twoFormEnergyPair_scalarTest (N : Lp TwoFormFour 2 (volume : Measure FourSpace)) (i : Fin 4) :
    inner ℝ N (twoFormEnergyTestL2 (g := g) c S hS (fun z => ψ z • b)
      (hψ.smul contDiff_const).contDiffOn hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs) i) =
      (∑ j : Fin 4, inner ℝ (twoFormFluxPair (g := g) c χ hχ hcχ hχs b i j N)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) +
      inner ℝ (twoFormConnectionPair (g := g) c S hS χ hχ hcχ hχs b i N)
        (twoFormScalarTestL2 ψ hψ hcψ) := by
  rw [twoFormEnergyTestL2_separated c S hS χ ψ hχ hcχ hχs hψ hcψ hψs hon b i,
    inner_add_right, inner_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact (twoFormCoefficientPair_test _ _ _ N _ (twoFormCutoffPartial_smooth ψ hψ j).continuous
      (hcψ.fderiv_apply ℝ (coordinateVector j))).symm
  · exact (twoFormCoefficientPair_test _ _ _ N ψ hψ.continuous hcψ).symm

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
  {o : FrameOrientation g}

variable {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hχK : tsupport χ ⊆ K) (hψK : tsupport ψ ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hon hU hKU hp hψK in
theorem twoFormRough_scalarWeakEquation (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) :
    (∑ j : Fin 4, inner ℝ
      (twoFormDivergenceFlux (g := g) c χ hχ hcχ (hχK.trans hKt) b
        (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hcχ hχK i u) j)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
    inner ℝ (twoFormDivergenceSource (g := g) c S hS χ hχ hcχ (hχK.trans hKt) b
      (twoFormGramVectorL2 c S hK hKt χ hχ hcχ hχK u)
      (twoFormL2GramValue c S hK hKt χ hχ hcχ hχK hS f)
      (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hcχ hχK i u))
      (twoFormScalarTestL2 ψ hψ hcψ) := by
  let a : FourSpace → TwoFormFour := fun z => ψ z • b
  have ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target := (hψ.smul contDiff_const).contDiffOn
  have has : tsupport a ⊆ K := (tsupport_smul_subset_left _ _).trans hψK
  have hona : ∀ z ∈ tsupport a, χ z = 1 :=
    fun z hz => hon z (tsupport_smul_subset_left _ _ hz)
  have he := twoFormRough_localL2Equation c S hS hK hKt χ hχ hcχ hχK a ha has hona
    U hU hUt hKU hp u f hu
  change inner ℝ _ (twoFormMassTestL2 (g := g) c a ha _ _) +
    (∑ i : Fin 4, inner ℝ _ (twoFormEnergyTestL2 (g := g) c S hS a ha _ _ i)) =
    inner ℝ _ (twoFormMassTestL2 (g := g) c a ha _ _) at he
  rw [twoFormMassPair_scalarTest c χ ψ hχ hcχ (hχK.trans hKt) hψ hcψ (hψK.trans hKt) hon b,
    twoFormMassPair_scalarTest c χ ψ hχ hcχ (hχK.trans hKt) hψ hcψ (hψK.trans hKt) hon b] at he
  have hi (i : Fin 4) := twoFormEnergyPair_scalarTest (g := g) c S hS χ ψ hχ hcχ (hχK.trans hKt)
    hψ hcψ (hψK.trans hKt) hon b (twoFormGramNablaL2 c S hS hK hKt χ hχ hcχ hχK i u) i
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hi i)
  rw [hsum] at he
  rw [Finset.sum_add_distrib] at he
  unfold twoFormDivergenceFlux twoFormDivergenceSource
  simp only [map_sub, inner_sub_left, sum_inner]
  rw [Finset.sum_comm]
  linarith only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart coefficient of an actual smooth two-form lies
in every integer Sobolev space. This supplies smooth Hodge-Poisson data. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_smooth_gram_integer (n : ℕ) (c : M) (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ K) (v : Fin 2 → Fin 4) (w : smoothTwoForms o) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η hη hcη hsη v (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) :
        𝓢'(FourSpace, ℂ)) := by
  let A : FourSpace → ℝ := fun z => η z * frameTensor (chartGramMatrix g c S z)
    (twoFormCoordinates o w.val c z) v
  have hA : ContDiff ℝ ∞ A := by
    apply scalarCutoff_contDiff η _ hη
    intro z hz
    exact contDiffAt_pi.mp (w.property.gramTensor_contDiffAt c S z (hKt (hsη hz))) v
  have hcA : HasCompactSupport A := hcη.mul_right
  let ψ := (hcA.toSchwartzMap hA).postcompCLM Complex.ofRealCLM
  have he : scalarComplexL2 (twoFormGramValueL2 c S hK hKt η hη hcη hsη v
      (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) = ψ.toLp 2 volume := by
    apply Lp.ext
    filter_upwards [scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η hη hcη hsη v
      (smoothTwoFormToH1 (w : SmoothH1TwoForm o))),
      twoFormGramValueL2_coe c S hK hKt η hη hcη hsη v (w : SmoothH1TwoForm o),
      ψ.coeFn_toLp 2 volume] with z hc hg hψ
    rw [hc, hg, hψ]
    rfl
  rw [he, Lp.toTemperedDistribution_toLp_eq]
  exact ψ.memSobolev

theorem twoForm_smooth_source_integer (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ K) (w : smoothTwoForms o) (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη hsη hS
        (smoothTwoFormToL2 (w : SmoothL2TwoForm o)))) : 𝓢'(FourSpace, ℂ)) := by
  have he := twoFormL2GramValue_H1 c S hS hK hKt η hη hcη hsη
    (smoothTwoFormToH1 (w : SmoothH1TwoForm o))
  have hJ := twoFormH1ToL2_smooth (w : SmoothH1TwoForm o)
  have htarget : twoFormL2GramValue c S hK hKt η hη hcη hsη hS
      (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
      twoFormGramVectorL2 c S hK hKt η hη hcη hsη (smoothTwoFormToH1 (w : SmoothH1TwoForm o)) :=
    (congrArg (twoFormL2GramValue c S hK hKt η hη hcη hsη hS) hJ).symm.trans he
  rw [htarget, twoFormGramVectorComponent]
  exact twoForm_smooth_gram_integer n c S hK hKt η hη hcη hsη (twoFormComponentIndex r) w

end
end PositiveEinsteinFour.Geometry
end


section

/-! Formal self-adjointness on a compact C2 amplitude against a local C2
section, with the actual density drift and skew connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantOperator_compact_adjoint
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x)
    (hsym : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hVsym : ∀ x ∈ U, ∀ k l, V x k l = V x l k) :
    (∫ x, ∑ k, ρ x * u x k * fourHeatCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      ∫ x, ∑ k, ρ x * v x k * fourHeatCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) u x k := by
  let W := fourHeatCovariantFlux A a ρ u
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 6,
    v x k * fourHeatCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 6, u x k * (ρ x * ∑ l : Fin 6, V x k l * v x l)
  have hW (i : Fin 4) (k : Fin 6) : ContDiff ℝ 1 (fun x => W i x k) :=
    fourHeatCovariantFlux_contDiff A a ρ u U hu hs hA ha hρ i k
  have hcW (i : Fin 4) (k : Fin 6) : HasCompactSupport (fun x => W i x k) :=
    fourHeatCovariantFlux_compact A a ρ u hc i k
  have hsW (i : Fin 4) (k : Fin 6) : tsupport (fun x => W i x k) ⊆ U :=
    (fourHeatCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      v x k * fourHeatCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeat_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 6, ρ x * v x k *
      fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 6) := fourHeatCovariantOperator_divergence A a ρ (V x) u x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx)
        (fun l => (hu l).contDiffAt) (hsym x hx)
      have hm (k : Fin 6) : ρ x * v x k *
          fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k =
          -(∑ i : Fin 4, v x k * fourHeatCovariantDerivative A (W i) i x k) +
            v x k * (ρ x * ∑ l, V x k l * u x l) := by
        calc
          _ = v x k * (ρ x * fourHeatCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) u x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => v x k * fourHeatCovariantDerivative A (W i) i x k),
        fourHeat_potential_pairing_swap u v ρ V U hs hVsym x]
    · have hz (k : Fin 6) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      have hD (i : Fin 4) (k : Fin 6) : fourHeatCovariantDerivative A u i x k = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A u i y k)
          (fun h => hx ((iUnion_subset hs) (fourHeatCovariantDerivative_support A u i k h)))
      have hDD (i j : Fin 4) (k : Fin 6) :
          fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y =>
          fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j y k)
        intro h
        obtain ⟨l, hl⟩ := mem_iUnion.mp (fourHeatCovariantDerivative_support A
          (fourHeatCovariantDerivative A u i) j k h)
        exact hx ((iUnion_subset hs) (fourHeatCovariantDerivative_support A u i l hl))
      have hDW (i : Fin 4) (k : Fin 6) : fourHeatCovariantDerivative A (W i) i x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A (W i) i y k)
        intro h
        exact hx ((iUnion_subset (hsW i)) (fourHeatCovariantDerivative_support A (W i) i k h))
      simp only [B, P, fourHeatCovariantOperator, hz, hD, hDD, hDW,
        zero_mul, mul_zero, Finset.sum_const_zero, neg_zero, add_zero]
  have hgreen := fourHeat_compact_flux_green A W v U hW hcW hsW
    (fun x hx k => (hv x hx k).of_le (by norm_num))
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      fourHeatCovariantDerivative A v i x k * W i x k) := by
    simpa only [mul_comm] using fourHeatCovariantDerivative_pairing_integrable A (W i) v U i
      (fun k => (hW i k).continuous) (hcW i) (hsW i)
      (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hj (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) :=
    fourHeatCovariantDerivative_left_integrable A u (fourHeatCovariantFlux A a ρ v i) U i
      (fun k => (hu k).of_le (by norm_num)) hc hs
      (fun x hx k => fourHeatCovariantFlux_contDiffAt A a ρ v x i k
        (fun j l => hA x hx j k l) (ha x hx i) (hρ x hx) (hv x hx))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hflux : (∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
      fourHeatCovariantDerivative A v i x k * W i x k) =
      ∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k := by
    rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_finsetSum _ (fun i _ => hj i)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact fourHeat_flux_pairing_swap A a ρ u v U hs hsym x
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  change _ = -(∫ x, B x) + (∫ x, P x)
  rw [hgreen, neg_neg, hflux]
  exact fourHeatCovariantOperator_weighted_green A a ρ V u v U
    (fun k => (hu k).of_le (by norm_num)) hc hs hv hA ha hρ hρ0 hV hskew hsym

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-coordinate rough contraction agrees with the actual one-form Hessian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_covariantField_chart {n : ℕ} (g : SmoothMetric M)
    (T : M → CovariantCoordinates n) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    covariantFieldFramed g T e = frameTensor (frameChartMatrix g c e)
      (covariantFieldCoordinates T c (chartAt FourSpace c e.base)) := by
  have hb := mem_chart_source FourSpace e.base
  have ht := covariantFieldCoordinates_transition T e.base c
    (chartAt FourSpace e.base e.base) ((chartAt FourSpace e.base).map_source hb)
    (by simpa only [(chartAt FourSpace e.base).left_inv hb] using he)
  have hz : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    change chartAt FourSpace c ((chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base e.base)) = _
    rw [(chartAt FourSpace e.base).left_inv hb]
  rw [hz] at ht
  rw [frameChartMatrix_eq, frameTensor_mul, ← ht]
  rfl

variable {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneFormSecond_coordinates (u : smoothCovariantFields M 1) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantFieldCoordinates (covariantFieldDerivative g (covariantFieldDerivative g u.val)) c z =
      covariantDerivative g c (covariantDerivative g c (covariantFieldCoordinates u.val c)) z := by
  rw [covariantFieldDerivative_coordinates u.property.derivative c z hz]
  apply covariantDerivative_congr
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact covariantFieldDerivative_coordinates u.property c w hw

variable [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.oneRoughTrace_as_actual {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (u : smoothCovariantFields M 1)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (k : Fin 4) :
    (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
      (D.frame x hx) ![i,i,k]) =
      frameTensor (D.point x).2 (oneFormSecondTrace (metricInChart g c (D.point x).1)⁻¹
        (covariantDerivative g c (covariantDerivative g c (covariantFieldCoordinates u.val c))
          (D.point x).1)) ![k] := by
  have hsource : (D.frame x hx).base ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target (D.in_chart x hx)
  have h := heat_covariantField_chart g
    (covariantFieldDerivative g (covariantFieldDerivative g u.val)) c (D.frame x hx) hsource
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hm, hb, oneFormSecond_coordinates u c _ (D.in_chart x hx)] at h
  simp_rw [h]
  have hi (i : Fin 4) : ![i,i,k] = Fin.cons i (Fin.cons i ![k]) := by
    ext j
    fin_cases j <;> rfl
  simp_rw [hi]
  rw [oneFormSecondTrace_frame, heat_orthonormal_inverse _ _ (D.orthonormal x hx)]

theorem HeatNormalFrameData.oneTensor_rough_at {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (covariantFieldCoordinates u.val c (D.point y).1)) i)
        j x ![k]) +
      (∑ i, heatNormalDrift g o e x i *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (covariantFieldCoordinates u.val c (D.point y).1)) i x ![k]) =
      -(∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (D.frame x hx) ![i,i,k]) := by
  have hgx : ∀ᶠ y in 𝓝 x,
      (D.point y).2ᵀ * metricInChart g c (D.point y).1 * (D.point y).2 = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.orthonormal y hy
  rw [D.oneRoughTrace_as_actual u x hx k]
  exact heatNormal_oneForm_rough_pullback g c D.point (covariantFieldCoordinates u.val c)
    x hP (fun z hz => u.property c z hz) (D.in_chart x hx) hgx
    (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
    (D.inverseMetric_transport x hx hs hd.ne') (D.drift_transport_at x hx hP hs hd) ![k]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Moving actual H1 lower-order fluxes into L2 forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped BigOperators SchwartzMap ContDiff

noncomputable section

local notation "L2" => Lp ℝ 2 (volume : Measure FourSpace)

theorem scalarComplexL2_compact_inner_derivative (f D : L2) (i : Fin 4)
    (hD : scalarCoordinateDerivative i (scalarComplexL2 f : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    inner ℝ f (twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
      (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i))) =
      -inner ℝ D (twoFormScalarTestL2 ψ hψ hcψ) := by
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  have hleft : (∫ z, f z * twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
      (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i)) z) =
      ∫ z, f z * partialDeriv ψ i z := by
    apply integral_congr_ae
    filter_upwards [((twoFormCutoffPartial_smooth ψ hψ i).continuous.memLp_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ (coordinateVector i))).coeFn_toLp] with z hz
    exact congrArg (fun t => f z * t) hz
  have hright : (∫ z, D z * twoFormScalarTestL2 ψ hψ hcψ z) = ∫ z, D z * ψ z := by
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => D z * t) hz
  rw [hleft, hright]
  exact scalarComplexL2_compact_weak_derivative f D i hD ψ hψ hcψ

theorem scalar_divergence_corrected_flux (F C D : Fin 4 → L2) (R : L2)
    (hD : ∀ i, scalarCoordinateDerivative i (scalarComplexL2 (C i) : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (D i) : 𝓢'(FourSpace, ℂ)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hF : (∑ i : Fin 4, inner ℝ (F i)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
        (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ)) :
    (∑ i : Fin 4, inner ℝ (F i + C i)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
        (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i)))) =
      inner ℝ (R - ∑ i : Fin 4, D i) (twoFormScalarTestL2 ψ hψ hcψ) := by
  have hC (i : Fin 4) := scalarComplexL2_compact_inner_derivative (C i) (D i) i
    (hD i) ψ hψ hcψ
  simp_rw [inner_add_left]
  rw [Finset.sum_add_distrib, hF]
  simp_rw [hC]
  rw [Finset.sum_neg_distrib, inner_sub_left, sum_inner]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary derivative of each localized coefficient, tested against
actual smooth compact scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff SchwartzMap

noncomputable section

private theorem scalarC1_compact_test (f : ↥(Euclidean.C1c (E := FourSpace)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (i : Fin 4) :
    inner ℝ (ScalarEuclideanSobolev.valueL2 f)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z) (twoFormCutoffPartial_smooth ψ hψ i)
        (hcψ.fderiv_apply ℝ (coordinateVector i))) =
      -inner ℝ (ScalarEuclideanSobolev.partialL2 f i) (twoFormScalarTestL2 ψ hψ hcψ) := by
  have h := scalarC1_weak_derivative f (hcψ.toSchwartzMap hψ) i
  change (∫ z, f.val z * partialDeriv ψ i z) = -(∫ z, partialDeriv f.val i z * ψ z) at h
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  have hl : (∫ z, ScalarEuclideanSobolev.valueL2 f z *
      twoFormScalarTestL2 (fun z => partialDeriv ψ i z) (twoFormCutoffPartial_smooth ψ hψ i)
        (hcψ.fderiv_apply ℝ (coordinateVector i)) z) = ∫ z, f.val z * partialDeriv ψ i z := by
    apply integral_congr_ae
    filter_upwards [ScalarEuclideanSobolev.valueL2_coe f,
      (((twoFormCutoffPartial_smooth ψ hψ i).continuous).memLp_of_hasCompactSupport
        (hcψ.fderiv_apply ℝ (coordinateVector i))).coeFn_toLp] with z hf hd
    exact congrArg₂ (· * ·) hf hd
  have hr : (∫ z, ScalarEuclideanSobolev.partialL2 f i z * twoFormScalarTestL2 ψ hψ hcψ z) =
      ∫ z, partialDeriv f.val i z * ψ z := by
    apply integral_congr_ae
    filter_upwards [ScalarEuclideanSobolev.partialL2_coe f i,
      (hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hf hq
    exact congrArg₂ (· * ·) hf hq
  rw [hl, hr]
  exact h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGram_weak_partial (c : M) (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (i : Fin 4)
    (u : TwoFormH1 o) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z) (twoFormCutoffPartial_smooth ψ hψ i)
        (hcψ.fderiv_apply ℝ (coordinateVector i))) =
      -inner ℝ (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i u)
        (twoFormScalarTestL2 ψ hψ hcψ) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((twoFormGramValueL2 c S hK hKt χ hχ hc hs v).continuous.inner continuous_const)
      ((twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i).continuous.inner continuous_const).neg) ?_
  intro w
  change inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) _ =
    -inner ℝ (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i (smoothTwoFormToH1 w)) _
  rw [twoFormGramValueL2_smooth, twoFormGramPartialL2_smooth]
  exact scalarC1_compact_test _ ψ hψ hcψ i

end
end PositiveEinsteinFour.Geometry
end


section

/-! At positive time the actual heat operator is in the range of every
power of the compact Hodge resolvent, with explicit multiplier bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatPowerWeight_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (μ : TwoFormSpectralValue (o := o) hRic) :
    |μ.val⁻¹ ^ n * twoFormHeatWeight hRic t μ| ≤
      Real.exp t * (n.factorial : ℝ) / (t : ℝ) ^ n := by
  have htR : 0 < (t : ℝ) := ht
  have hm := (twoFormSpectralValue_bounds hRic μ).1
  have hy : 0 ≤ (t : ℝ) * μ.val⁻¹ := mul_nonneg htR.le (inv_pos.mpr hm).le
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have he := (div_le_iff₀ hn).mp
    (Real.pow_div_factorial_le_exp ((t : ℝ) * μ.val⁻¹) hy n)
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-((t : ℝ) * μ.val⁻¹))).le
  have heq : (Real.exp ((t : ℝ) * μ.val⁻¹) * (n.factorial : ℝ)) *
      Real.exp (-((t : ℝ) * μ.val⁻¹)) = (n.factorial : ℝ) := by
    rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [heq] at he'
  have hw : twoFormHeatWeight hRic t μ =
      Real.exp t * Real.exp (-((t : ℝ) * μ.val⁻¹)) := by
    rw [twoFormHeatWeight, twoFormHeatRate, ← Real.exp_add]
    congr 1
    ring
  rw [hw, abs_of_pos (mul_pos (pow_pos (inv_pos.mpr hm) n)
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)))]
  calc
    _ = (Real.exp t / (t : ℝ) ^ n) *
        (((t : ℝ) * μ.val⁻¹) ^ n * Real.exp (-((t : ℝ) * μ.val⁻¹))) := by
      rw [mul_pow]
      field_simp [ne_of_gt htR]
    _ ≤ (Real.exp t / (t : ℝ) ^ n) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by ring

def twoFormHeatPowerSource (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (fun μ => μ.val⁻¹ ^ n * twoFormHeatWeight hRic t μ)
    (Real.exp t * (n.factorial : ℝ) / (t : ℝ) ^ n) (by positivity)
    (twoFormHeatPowerWeight_bound hRic t ht n)

theorem twoFormResolvent_power_coordinate (hRic : RicciThree g) (n : ℕ) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic ((twoFormShiftedResolvent hRic ^ n) f)) μ =
      μ.val ^ n • (twoFormSpectralEquiv hRic f) μ := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (twoFormSpectralEquiv hRic
        ((twoFormShiftedResolvent hRic ^ n) (twoFormShiftedResolvent hRic f))) μ = _
      rw [ih, twoFormShiftedResolvent_coordinate, smul_smul, ← pow_succ]

theorem twoFormHeatPowerSource_resolvent (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (f : TwoFormL2 o) :
    (twoFormShiftedResolvent hRic ^ n) (twoFormHeatPowerSource hRic t ht n f) =
      twoFormHeat hRic t f := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormResolvent_power_coordinate, twoFormHeat_coordinate]
  change μ.val ^ n • (twoFormSpectralEquiv hRic
    (twoFormSpectralMultiplier hRic _ _ _ _ f)) μ = _
  rw [twoFormSpectralMultiplier_coordinate, smul_smul]
  congr 1
  rw [← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1), one_pow, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The principal flux paired with a scalar test is the actual
metric-weighted pairing of the ordinary weak component derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormPrincipalCoefficient (c : M) (χ : FourSpace → ℝ) (i j : Fin 4) (z : FourSpace) : ℝ :=
  χ z * (chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j)

variable (c : M) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ (chartAt FourSpace c).target)

include hχ hs in
theorem twoFormPrincipalCoefficient_smooth (i j : Fin 4) :
    ContDiff ℝ ∞ (twoFormPrincipalCoefficient (g := g) c χ i j) :=
  scalarCutoff_contDiff χ _ hχ (fun z hz =>
    (chartVolumeDensity_contDiffAt g c z (hs hz)).mul
      (scalarPrincipalCoefficients_smooth g c z (hs hz) i j))

theorem twoFormFluxPair_basis_test (F : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (i j : Fin 4) (r : Fin 6) :
    inner ℝ (twoFormFluxPair (g := g) c χ hχ hc hs (EuclideanSpace.basisFun (Fin 6) ℝ r) i j F)
      (twoFormScalarTestL2 ψ hψ hcψ) =
    inner ℝ (twoFormVectorComponentL2 r F)
      (twoFormScalarTestL2 (fun z => twoFormPrincipalCoefficient (g := g) c χ i j z * ψ z)
        ((twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul hψ) hc.mul_right.mul_right) := by
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  apply integral_congr_ae
  filter_upwards [twoFormCoefficientPair_coe
      (twoFormFluxCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r) i j)
      (twoFormFluxCoefficient_smooth c χ hχ hs _ i j).continuous hc.mul_right.smul_right F,
    twoFormVectorComponentL2_coe r F,
    (hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp,
    (((twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul hψ).continuous.memLp_of_hasCompactSupport
      hc.mul_right.mul_right).coeFn_toLp] with z hp hv hq ht
  have hp' : twoFormFluxPair (g := g) c χ hχ hc hs (EuclideanSpace.basisFun (Fin 6) ℝ r)
      i j F z = inner ℝ (F z)
        (twoFormFluxCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r) i j z) := hp
  have hq' : twoFormScalarTestL2 ψ hψ hcψ z = ψ z := hq
  have ht' : twoFormScalarTestL2
      (fun z => twoFormPrincipalCoefficient (g := g) c χ i j z * ψ z)
      ((twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul hψ)
      hc.mul_right.mul_right z = twoFormPrincipalCoefficient (g := g) c χ i j z * ψ z := ht
  rw [hp', hv, hq', ht']
  simp only [twoFormFluxCoefficient, inner_smul_right, EuclideanSpace.inner_basisFun_real,
    twoFormPrincipalCoefficient]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form transport operator is the actual geometric Hodge Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.oneValue_as_actual (D : HeatNormalFrameData g o c e)
    (u : smoothCovariantFields M 1) (x : FourSpace) (hx : x ∈ ball 0 D.radius) (k : Fin 4) :
    heatNormalOneFormValue c D.point u x k = covariantFieldFramed g u.val (D.frame x hx) ![k] := by
  rw [heat_covariantField_chart g u.val c (D.frame x hx)
    ((chartAt FourSpace c).map_target (D.in_chart x hx))]
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hm, hb]
  rfl

theorem HeatNormalFrameData.oneRough_components_at (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      fourHeatOneCovariantDerivative (heatNormalFrameConnection g c D.point)
        (fourHeatOneCovariantDerivative (heatNormalFrameConnection g c D.point)
          (heatNormalOneFormValue c D.point u) i) j x k) +
      (∑ i, heatNormalDrift g o e x i *
        fourHeatOneCovariantDerivative (heatNormalFrameConnection g c D.point)
          (heatNormalOneFormValue c D.point u) i x k) =
      -(∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (D.frame x hx) ![i,i,k]) := by
  have hsk : ∀ᶠ y in 𝓝 x, ∀ i, (heatNormalFrameConnection g c D.point i y)ᵀ =
      -heatNormalFrameConnection g c D.point i y := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.connection_skew y hy
  have h := D.oneTensor_rough_at x hx hP hs hd u k
  simp_rw [heat_oneForm_covariant_second _ _ x _ _ k hsk,
    heat_oneForm_covariant_component _ _ x _ k (hsk.self_of_nhds _)] at h
  exact h

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatNormalFrameData.actual_one_operator_at (D : HeatNormalFrameData g o c e)
    (hRic : RicciThree g) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalOneFirst D x) (heatNormalOneZero D x)
      (heatNormalOneFormValue c D.point u) x k =
      heatNormalOneFormValue c D.point (smoothOneFormHodgeLaplacian (o := o) u) x k := by
  have hdet : (D.point x).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hA (i j l : Fin 4) : DifferentiableAt ℝ
      (fun y => heatNormalFrameConnection g c D.point i y j l) x :=
    (heatNormalFrameConnection_contDiffAt 1 g c D.point x hP (D.in_chart x hx) hdet i j l).differentiableAt one_ne_zero
  have hu (l : Fin 4) : ContDiffAt ℝ 2 (fun y => heatNormalOneFormValue c D.point u y l) x :=
    heatNormalOneFormValue_regular 2 c D.point u x hP (D.in_chart x hx) l
  have ha (i j : Fin 4) : (heatNormalMetric g o e x)⁻¹ i j =
      (heatNormalMetric g o e x)⁻¹ j i :=
    congrArg (fun A : Mat4 => A j i) (heatNormalInverse_symm g o e x)
  unfold heatNormalOneFirst heatNormalOneZero
  rw [← fourHeatOneCovariantOperator_eq _ _ _ _ _ x ha hA hu k]
  unfold fourHeatOneCovariantOperator
  rw [D.oneRough_components_at x hx hP hs hd u k]
  have hv : (∑ l : Fin 4, ((3 : ℝ) • (1 : Mat4)) k l *
      heatNormalOneFormValue c D.point u x l) = 3 * heatNormalOneFormValue c D.point u x k := by
    simp [Matrix.one_apply, mul_ite]
  rw [hv, D.oneValue_as_actual u x hx k,
    D.oneValue_as_actual (smoothOneFormHodgeLaplacian (o := o) u) x hx k]
  exact (smoothOneForm_Weitzenbock hRic u (D.frame x hx) k).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts converts the ordinary two-form principal flux
into the scalar chart divergence acting on compact tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (χ ψ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)

def twoFormPrincipalTest (i j : Fin 4) (z : FourSpace) : ℝ :=
  twoFormPrincipalCoefficient (g := g) c χ i j z * partialDeriv ψ j z

include hχ hs hψ in
theorem twoFormPrincipalTest_smooth (i j : Fin 4) :
    ContDiff ℝ ∞ (twoFormPrincipalTest (g := g) c χ ψ i j) :=
  (twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul (twoFormCutoffPartial_smooth ψ hψ j)

include hcψ in
theorem twoFormPrincipalTest_compact (i j : Fin 4) :
    HasCompactSupport (twoFormPrincipalTest (g := g) c χ ψ i j) :=
  (hcψ.fderiv_apply ℝ (coordinateVector j)).mul_left

def twoFormPrincipalDerivativeTestL2 (i j : Fin 4) : Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormScalarTestL2 (fun z => partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z)
    (twoFormCutoffPartial_smooth _ (twoFormPrincipalTest_smooth c χ ψ hχ hs hψ i j) i)
    ((twoFormPrincipalTest_compact c χ ψ hcψ i j).fderiv_apply ℝ (coordinateVector i))

def twoFormPrincipalDivergenceTestL2 : Lp ℝ 2 (volume : Measure FourSpace) :=
  ∑ i : Fin 4, ∑ j : Fin 4, twoFormPrincipalDerivativeTestL2 (g := g) c χ ψ hχ hs hψ hcψ i j

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
  {o : FrameOrientation g}

theorem twoFormPrincipalFlux_integrationByParts (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hcχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ K)
    (u : TwoFormH1 o) (r : Fin 6) :
    (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt χ hχ hcχ hχK
      (EuclideanSpace.basisFun (Fin 6) ℝ r) u j)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
    -inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hcχ hχK (twoFormComponentIndex r) u)
      (twoFormPrincipalDivergenceTestL2 (g := g) c χ ψ hχ (hχK.trans hKt) hψ hcψ) := by
  have hterm (i j : Fin 4) : inner ℝ
      (twoFormFluxPair (g := g) c χ hχ hcχ (hχK.trans hKt)
        (EuclideanSpace.basisFun (Fin 6) ℝ r) i j
        (twoFormGramPartialVectorL2 c S hK hKt χ hχ hcχ hχK i u))
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j))) =
      -inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hcχ hχK (twoFormComponentIndex r) u)
        (twoFormPrincipalDerivativeTestL2 (g := g) c χ ψ hχ (hχK.trans hKt) hψ hcψ i j) := by
    have hpair := twoFormFluxPair_basis_test (g := g) c χ hχ hcχ (hχK.trans hKt)
      (twoFormGramPartialVectorL2 c S hK hKt χ hχ hcχ hχK i u)
      (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
      (hcψ.fderiv_apply ℝ (coordinateVector j)) i j r
    refine hpair.trans ?_
    dsimp only [twoFormGramPartialVectorL2]
    rw [twoFormVectorComponentL2_assemble]
    have he := twoFormGram_weak_partial c S hK hKt χ hχ hcχ hχK (twoFormComponentIndex r) i u
      (twoFormPrincipalTest (g := g) c χ ψ i j)
      (twoFormPrincipalTest_smooth c χ ψ hχ (hχK.trans hKt) hψ i j)
      (twoFormPrincipalTest_compact c χ ψ hcψ i j)
    exact neg_eq_iff_eq_neg.mp he.symm
  change (∑ j : Fin 4, inner ℝ (∑ i : Fin 4, _) _) = _
  simp_rw [sum_inner]
  have ht := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hterm i j))
  rw [ht, Finset.sum_comm]
  simp only [twoFormPrincipalDivergenceTestL2, inner_sum, Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak rough two-form equation has an ordinary scalar
principal part with L2 forcing in every smooth local frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp in
theorem twoFormRough_principalWeakEquation (b : TwoFormFour) (u : TwoFormH1 o)
    (f : TwoFormL2 o) (hu : u = twoFormRoughSolution f) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, χ z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt χ hχ hc hs b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD⟩ := twoFormFluxCorrection_derivatives c S hS hK hKt χ hχ hc hs b u
  let F := fun j => twoFormDivergenceFlux (g := g) c χ hχ hc (hs.trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt χ hχ hc hs b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS χ hχ hc (hs.trans hKt) b
    (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
    (twoFormL2GramValue c S hK hKt χ hχ hc hs hS f)
    (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_⟩
  intro ψ hψ hcψ hψK hon
  have hF := twoFormRough_scalarWeakEquation c S hS χ ψ hχ hc hψ hcψ hon b
    hK hKt hs hψK U hU hUt hKU hp u f hu
  have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
  have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt χ hχ hc hs b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
      (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
      (twoFormPrincipalFlux_eq c S hS hK hKt χ hχ hc hs b u j)
  rw [heq] at he
  exact he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact principal test is precisely the density-weighted scalar
chart Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (χ ψ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψt : tsupport ψ ⊆ (chartAt FourSpace c).target)
  (hon : ∀ z ∈ tsupport ψ, χ z = 1)

theorem twoFormPrincipalTest_support (i j : Fin 4) :
    tsupport (twoFormPrincipalTest (g := g) c χ ψ i j) ⊆ tsupport ψ :=
  tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (coordinateVector j))

include hon in
theorem twoFormPrincipalTest_remove_cutoff (i j : Fin 4) :
    twoFormPrincipalTest (g := g) c χ ψ i j = fun z =>
      chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j * partialDeriv ψ j z := by
  funext z
  by_cases hz : z ∈ tsupport ψ
  · simp only [twoFormPrincipalTest, twoFormPrincipalCoefficient, hon z hz, one_mul]
  · have hd : partialDeriv ψ j z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((tsupport_fderiv_apply_subset ℝ (coordinateVector j)) h))
    simp only [twoFormPrincipalTest, hd, mul_zero]

include hon hψt hχ hs hψ in
theorem twoFormPrincipalDivergence_value (z : FourSpace) :
    (∑ i : Fin 4, ∑ j : Fin 4, partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z) =
      chartVolumeDensity g c z * scalarChartOperator g c ψ z := by
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · have hder (i : Fin 4) :
        partialDeriv (fun w => ∑ j : Fin 4, twoFormPrincipalTest (g := g) c χ ψ i j w) i z =
          ∑ j : Fin 4, partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z := by
      change (fderiv ℝ _ z) (coordinateVector i) = _
      rw [fderiv_fun_sum (fun j _ =>
        (twoFormPrincipalTest_smooth c χ ψ hχ hs hψ i j).differentiable (by simp) z)]
      simp only [_root_.sum_apply, partialDeriv]
    calc
      _ = ∑ i : Fin 4, partialDeriv (fun w => ∑ j : Fin 4,
          chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hder i]
        simp_rw [twoFormPrincipalTest_remove_cutoff c χ ψ hon]
      _ = _ := scalarChartOperator_divergence g c ψ z hz hψ.contDiffAt
  · have hp : z ∉ tsupport ψ := fun h => hz (hψt h)
    have hzero (i j : Fin 4) : partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp
        (twoFormPrincipalTest_support c χ ψ i j
          ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h)))
    simp only [hzero, Finset.sum_const_zero,
      scalarChartOperator_eq_zero_off_tsupport g c ψ hp, mul_zero]

include hon hψt in
theorem twoFormPrincipalDivergenceTestL2_coe :
    twoFormPrincipalDivergenceTestL2 (g := g) c χ ψ hχ hs hψ hcψ =ᵐ[volume]
      fun z => chartVolumeDensity g c z * scalarChartOperator g c ψ z := by
  let F := fun i j : Fin 4 => twoFormPrincipalDerivativeTestL2 (g := g) c χ ψ hχ hs hψ hcψ i j
  have ht : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i j : Fin 4,
      F i j z = partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (((twoFormCutoffPartial_smooth _
      (twoFormPrincipalTest_smooth c χ ψ hχ hs hψ i j) i).continuous).memLp_of_hasCompactSupport
        ((twoFormPrincipalTest_compact c χ ψ hcψ i j).fderiv_apply ℝ (coordinateVector i))).coeFn_toLp
  have hi := Filter.eventually_all.mpr (fun i : Fin 4 => Lp.coeFn_finsetSum Finset.univ (F i))
  change (∑ i : Fin 4, ∑ j : Fin 4, F i j) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 => ∑ j : Fin 4, F i j), hi, ht]
    with z hout hin hz
  rw [hout]
  change (∑ i : Fin 4, (∑ j : Fin 4, F i j) z) = _
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hin i]
      change (∑ j : Fin 4, F i j z) = _
      exact Finset.sum_congr rfl (fun j _ => hz i j)
    _ = _ := twoFormPrincipalDivergence_value c χ ψ hχ hs hψ hψt hon z

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual H1 density-weighted components and their chart-operator pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (r : Fin 6) (u : TwoFormH1 o)

def twoFormWeightedComponentL2 : Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormMassPair (g := g) c χ hχ hc (hs.trans hKt) (EuclideanSpace.basisFun (Fin 6) ℝ r)
    (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)

theorem twoFormWeightedComponent_H1 : MemSobolev 1 2
    (scalarComplexL2 (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u) : 𝓢'(FourSpace, ℂ)) :=
  twoFormGramCoefficient_memSobolev_one c S hK hKt χ hχ hc hs u
    (twoFormMassCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r))
    (twoFormMassCoefficient_smooth (g := g) c χ hχ (hs.trans hKt) _)
    hc.mul_right.smul_right

theorem twoFormWeightedComponent_coe :
    twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u =ᵐ[volume] fun z =>
      χ z * chartVolumeDensity g c z *
        twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z := by
  have hv := twoFormVectorComponentL2_coe r (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
  rw [twoFormGramVectorComponent] at hv
  have hp := twoFormCoefficientPair_coe
    (twoFormMassCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r))
    (twoFormMassCoefficient_smooth (g := g) c χ hχ (hs.trans hKt) _).continuous
    hc.mul_right.smul_right (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
  filter_upwards [hv, hp] with z hvz hpz
  have hp' : twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u z =
      inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u z)
        (twoFormMassCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r) z) := hpz
  rw [hp']
  simp only [twoFormMassCoefficient, inner_smul_right, EuclideanSpace.inner_basisFun_real]
  rw [hvz]

theorem twoFormWeightedComponent_operator_pairing
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ (chartAt FourSpace c).target)
    (hon : ∀ z ∈ tsupport ψ, χ z = 1) :
    inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u)
      (twoFormPrincipalDivergenceTestL2 (g := g) c χ ψ hχ (hs.trans hKt) hψ hcψ) =
    ∫ z, twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u z * scalarChartOperator g c ψ z := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  apply integral_congr_ae
  filter_upwards [twoFormWeightedComponent_coe c S hK hKt χ hχ hc hs r u,
    twoFormPrincipalDivergenceTestL2_coe c χ ψ hχ (hs.trans hKt) hψ hcψ hψt hon]
    with z hw hd
  rw [hw, hd]
  by_cases hz : z ∈ tsupport ψ
  · rw [hon z hz]
    ring
  · rw [scalarChartOperator_eq_zero_off_tsupport g c ψ hz]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every component of an actual weak rough two-form solution satisfies
the density-weighted scalar chart equation with actual L2 forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp in
theorem twoFormRough_weightedWeakEquation (r : Fin 6) (u : TwoFormH1 o)
    (f : TwoFormL2 o) (hu : u = twoFormRoughSolution f) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, χ z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hR⟩ := twoFormRough_principalWeakEquation c S hS hK hKt χ hχ hc hs
    U hU hUt hKU hp (EuclideanSpace.basisFun (Fin 6) ℝ r) u f hu
  refine ⟨-R, ?_⟩
  intro ψ hψ hcψ hψK hon
  have he := hR ψ hψ hcψ hψK hon
  rw [twoFormPrincipalFlux_integrationByParts c χ ψ hχ hψ hcψ S hK hKt hc hs u r,
    twoFormWeightedComponent_operator_pairing c S hK hKt χ hχ hc hs r u
      ψ hψ hcψ (hψK.trans hKt) hon] at he
  have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u z *
      scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
    rw [inner_neg_left]
    linarith only [he]
  rw [hv, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  apply integral_congr_ae
  filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
  exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local H2 regularity for weak rough two-form solutions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp in
theorem twoFormRough_weighted_H2 (r : Fin 6) (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ χ z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1, scalarRescaledPoint g c z₀ t y ∈ K ∧
        χ (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)) : 𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hF⟩ := twoFormRough_weightedWeakEquation c S hS hK hKt χ hχ hc hs
    U hU hUt hKU hp r u f hu
  apply scalarEuclidean_local_H2 g c z₀ {z | z ∈ K ∧ χ z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u) F
    (twoFormWeightedComponent_H1 c S hK hKt χ hχ hc hs r u)
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive frame and cutoff hypotheses for local H2 regularity are
constructed at every chart point. Only the actual weak equation remains. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormRough_actual_local_H2 (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) (c : M) (z₀ : ChartTarget c) :
    ∃ (S : Mat4) (_hS : Sᵀ * S = 1) (χ : FourSpace → ℝ)
      (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
      (hct : tsupport χ ⊆ (chartAt FourSpace c).target),
      ∀ r : Fin 6, ∃ (t : ℝ) (ht : 0 < t),
        (∀ y ∈ closedBall (0 : FourSpace) 1, χ (scalarRescaledPoint g c z₀ t y) = 1) ∧
        ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
          tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2
            (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
              (twoFormWeightedComponentL2 c S hc hct χ hχ hc (Subset.refl _) r u)) :
                𝓢'(FourSpace, ℂ))) := by
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hc, hs, hnear⟩ :=
    twoForm_regularity_cutoff o c z₀
  let hct : tsupport χ ⊆ (chartAt FourSpace c).target := hs.trans hUt
  refine ⟨S, hS, χ, hχ, hc, hct, ?_⟩
  intro r
  obtain ⟨t, ht, hpoint, hreg⟩ := twoFormRough_weighted_H2 c S hS hc hct χ hχ hc
    (Subset.refl _) U hU hUt hs hp r u f hu z₀ hnear
  exact ⟨t, ht, fun y hy => (hpoint y hy).2, hreg⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Removing the actual density and affine normalization from the local
H2 two-form component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (r : Fin 6) (u : TwoFormH1 o)
  (z₀ : ChartTarget c) (t : ℝ) (ht : t ≠ 0)
  (hpoint : ∀ y ∈ closedBall (0 : FourSpace) 1,
    scalarRescaledPoint g c z₀ t y ∈ K ∧ χ (scalarRescaledPoint g c z₀ t y) = 1)

include hpoint in
theorem twoFormWeightedComponent_rescaled_coe :
    (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y) *
      twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u
        (scalarRescaledPoint g c z₀ t y)) =ᵐ[volume.restrict (ball (0 : FourSpace) 1)]
      scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht) z₀
        (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u) := by
  let A := scalarRescalingLinearEquiv g c z₀ t ht
  let W := twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u
  have hmp : Measure.QuasiMeasurePreserving (fun y : FourSpace => A y + z₀) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hw := hmp.ae_eq_comp (twoFormWeightedComponent_coe c S hK hKt χ hχ hc hs r u)
  filter_upwards [ae_restrict_of_ae hw,
    ae_restrict_of_ae (scalarAffinePullbackL2_coe A z₀ W),
    ae_restrict_mem isOpen_ball.measurableSet] with y hw hy hball
  dsimp only [Function.comp_apply] at hw
  have hA := scalarRescalingLinearEquiv_apply g c z₀ t ht y
  change W (A y + z₀) = _ at hw
  rw [hA] at hw
  change scalarAffinePullbackL2 A z₀ W y = W (A y + z₀) at hy
  rw [hA] at hy
  rw [(hpoint y (ball_subset_closedBall hball)).2, one_mul] at hw
  exact (hy.trans hw).symm

include hpoint in
theorem twoFormH2_unweight_unscale
    (hreg : ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
      tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2
        (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht) z₀
          (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)) : 𝓢'(FourSpace, ℂ))))
    (β : FourSpace → ℝ) (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hsβ : tsupport β ⊆ closedBall (0 : FourSpace) (1 / 2)) :
    ∃ v : Lp ℂ 2 (volume : Measure FourSpace), MemSobolev 2 2 (v : 𝓢'(FourSpace, ℂ)) ∧
      (v : FourSpace → ℂ) =ᵐ[volume] fun z =>
        (β ((scalarRescalingLinearEquiv g c z₀ t ht).symm (z - z₀)) *
          twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z : ℝ) := by
  let A := scalarRescalingLinearEquiv g c z₀ t ht
  let ρ : FourSpace → ℝ := fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y)
  let b : FourSpace → ℝ := fun z => twoFormGramValueL2 c S hK hKt χ hχ hc hs
    (twoFormComponentIndex r) u z
  let w := scalarAffinePullbackL2 A z₀ (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)
  have hρ0 (y : FourSpace) (hy : y ∈ tsupport β) : ρ y ≠ 0 :=
    (chartVolumeDensity_pos g c _ (hKt (hpoint y
      (closedBall_subset_closedBall (by norm_num) (hsβ hy))).1)).ne'
  have hρ (y : FourSpace) (hy : y ∈ tsupport β) :
      ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y := by
    apply ContDiffAt.inv
    · exact (chartVolumeDensity_contDiffAt g c _ (hKt (hpoint y
        (closedBall_subset_closedBall (by norm_num) (hsβ hy))).1)).comp y (by
          unfold scalarRescaledPoint
          fun_prop)
    · exact hρ0 y hy
  obtain ⟨v, hv, he⟩ := scalar_H2_density_division ρ
    (fun y => b (scalarRescaledPoint g c z₀ t y)) w
    (twoFormWeightedComponent_rescaled_coe c S hK hKt χ hχ hc hs r u z₀ t ht hpoint)
    hreg β hβ hcβ hsβ hρ hρ0
  have he' : (v : FourSpace → ℂ) =ᵐ[volume] fun y => (β y * b (A y + z₀) : ℝ) := by
    filter_upwards [he] with y hy
    change v y = (β y * b (scalarRescaledPoint g c z₀ t y) : ℝ) at hy
    rw [scalarRescalingLinearEquiv_apply g c z₀ t ht y]
    exact hy
  exact scalar_H2_unscale A z₀ b β v hv he'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary localized two-form components have actual H2 representatives
on a neighborhood of each point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp in
theorem twoFormRough_H2_representative (r : Fin 6) (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ χ z = 1} ∈ 𝓝 z₀.val) :
    ∃ V : Set FourSpace, IsOpen V ∧ z₀.val ∈ V ∧ V ⊆ K ∧
      (∀ z ∈ V, χ z = 1) ∧
      ∃ v : Lp ℂ 2 (volume : Measure FourSpace), MemSobolev 2 2 (v : 𝓢'(FourSpace, ℂ)) ∧
        (v : FourSpace → ℂ) =ᵐ[volume.restrict V] fun z =>
          (twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨t, ht, hpoint, hreg⟩ := twoFormRough_weighted_H2 c S hS hK hKt χ hχ hc hs
    U hU hUt hKU hp r u f hu z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ closedBall (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
  obtain ⟨v, hv, he⟩ := twoFormH2_unweight_unscale c S hK hKt χ hχ hc hs r u z₀ t ht.ne'
    hpoint hreg β β.contDiff β.hasCompactSupport hsβ
  let V : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 4)
  have hV : IsOpen V := isOpen_ball.preimage (by fun_prop)
  have hzV : z₀.val ∈ V := by
    dsimp only [V]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hinside (z : FourSpace) (hz : z ∈ V) : z ∈ K ∧ χ z = 1 := by
    have hq : A.symm (z - z₀) ∈ closedBall (0 : FourSpace) 1 :=
      closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz)
    have hp := hpoint _ hq
    rwa [hinv] at hp
  refine ⟨V, hV, hzV, fun z hz => (hinside z hz).1, fun z hz => (hinside z hz).2, v, hv, ?_⟩
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hV.measurableSet] with z hz hzV
  rw [hz]
  have hβ : β (A.symm (z - z₀)) = 1 := β.one_of_mem_closedBall (ball_subset_closedBall hzV)
  rw [hβ, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Removing the actual density and affine normalization from the local
integer-order two-form component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (r : Fin 6) (u : TwoFormH1 o)
  (z₀ : ChartTarget c) (t : ℝ) (ht : t ≠ 0)
  (hpoint : ∀ y ∈ closedBall (0 : FourSpace) 1,
    scalarRescaledPoint g c z₀ t y ∈ K ∧ χ (scalarRescaledPoint g c z₀ t y) = 1)

include hpoint in
theorem twoFormInteger_unweight_unscale (n : ℕ)
    (hreg : ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
      tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
        (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht) z₀
          (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)) : 𝓢'(FourSpace, ℂ))))
    (β : FourSpace → ℝ) (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hsβ : tsupport β ⊆ ball (0 : FourSpace) (1 / 2)) :
    ∃ v : Lp ℂ 2 (volume : Measure FourSpace), MemSobolev (n : ℝ) 2 (v : 𝓢'(FourSpace, ℂ)) ∧
      (v : FourSpace → ℂ) =ᵐ[volume] fun z =>
        (β ((scalarRescalingLinearEquiv g c z₀ t ht).symm (z - z₀)) *
          twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z : ℝ) := by
  let A := scalarRescalingLinearEquiv g c z₀ t ht
  let ρ : FourSpace → ℝ := fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y)
  let b : FourSpace → ℝ := fun z => twoFormGramValueL2 c S hK hKt χ hχ hc hs
    (twoFormComponentIndex r) u z
  let w := scalarAffinePullbackL2 A z₀ (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)
  have hρ0 (y : FourSpace) (hy : y ∈ tsupport β) : ρ y ≠ 0 :=
    (chartVolumeDensity_pos g c _ (hKt (hpoint y
      (ball_subset_closedBall (ball_subset_ball (by norm_num) (hsβ hy)))).1)).ne'
  have hρ (y : FourSpace) (hy : y ∈ tsupport β) :
      ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y := by
    apply ContDiffAt.inv
    · exact (chartVolumeDensity_contDiffAt g c _ (hKt (hpoint y
        (ball_subset_closedBall (ball_subset_ball (by norm_num) (hsβ hy)))).1)).comp y (by
          unfold scalarRescaledPoint
          fun_prop)
    · exact hρ0 y hy
  obtain ⟨v, hv, he⟩ := scalar_integer_density_division n ρ
    (fun y => b (scalarRescaledPoint g c z₀ t y)) w
    (twoFormWeightedComponent_rescaled_coe c S hK hKt χ hχ hc hs r u z₀ t ht hpoint)
    (fun φ hcφ hsφ => hreg φ hcφ (hsφ.trans ball_subset_closedBall)) β hβ hcβ hsβ hρ hρ0
  have he' : (v : FourSpace → ℂ) =ᵐ[volume] fun y => (β y * b (A y + z₀) : ℝ) := by
    filter_upwards [he] with y hy
    change v y = (β y * b (scalarRescaledPoint g c z₀ t y) : ℝ) at hy
    rw [scalarRescalingLinearEquiv_apply g c z₀ t ht y]
    exact hy
  exact scalar_integer_unscale n A z₀ b β v hv he'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inner cutoffs of the actual two-form coefficients inherit the
regularity of their local representatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a)
  (hca : HasCompactSupport a) (hsa : tsupport a ⊆ K)
  (hon : ∀ z ∈ tsupport a, χ z = 1) (v : Fin 2 → Fin 4) (u : TwoFormH1 o)

include hon in
theorem twoFormGram_cutoff_distribution :
    (scalarComplexL2 (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) : 𝓢'(FourSpace, ℂ)) =
      smulLeftCLM ℂ (fun z => (a z : ℂ))
        (scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u) : 𝓢'(FourSpace, ℂ)) := by
  let φ : 𝓢(FourSpace, ℂ) := (hca.toSchwartzMap ha).postcompCLM Complex.ofRealCLM
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] Lp ℂ 2 (volume : Measure FourSpace) :=
    Complex.ofRealCLM.compLpL 2 volume
  let P := (scalarL2Multiply (φ.toLp (∞ : ℝ≥0∞) volume)).restrictScalars ℝ
  have hC (f : Lp ℝ 2 (volume : Measure FourSpace)) : C f = scalarComplexL2 f := rfl
  have he : C (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) =
      P (C (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u)) := by
    refine UniformSpace.Completion.induction_on u
      (isClosed_eq (C.continuous.comp (twoFormGramValueL2 c S hK hKt a ha hca hsa v).continuous)
        (P.continuous.comp (C.continuous.comp
          (twoFormGramValueL2 c S hK hKt χ hχ hc hs v).continuous))) ?_
    intro w
    apply Lp.ext
    filter_upwards [scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt a ha hca hsa v (smoothTwoFormToH1 w)),
      twoFormGramValueL2_coe c S hK hKt a ha hca hsa v w,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp (∞ : ℝ≥0∞) volume)
        (scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w))),
      φ.coeFn_toLp (∞ : ℝ≥0∞) volume,
      scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)),
      twoFormGramValueL2_coe c S hK hKt χ hχ hc hs v w] with z hl hal hp hφ hr hχv
    change scalarComplexL2 (twoFormGramValueL2 c S hK hKt a ha hca hsa v (smoothTwoFormToH1 w)) z =
      ((φ.toLp (∞ : ℝ≥0∞) volume) •
        scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) :
          Lp ℂ 2 volume) z
    rw [hl, hal, hp, Complex.ofReal_mul]
    change (a z * frameTensor (chartGramMatrix g c S z)
      (twoFormCoordinates o (w : smoothTwoForms o).val c z) v : ℂ) =
        φ.toLp (∞ : ℝ≥0∞) volume z * scalarComplexL2
          (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) z
    rw [hφ, hr, hχv]
    have hφz : φ z = (a z : ℂ) := rfl
    rw [hφz, Complex.ofReal_mul]
    by_cases hz : a z = 0
    · simp only [hz, zero_mul, Complex.ofReal_zero]
    · rw [hon z (subset_tsupport a hz), Complex.ofReal_one, one_mul]
  change (C (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) : 𝓢'(FourSpace, ℂ)) = _
  rw [he]
  exact scalarL2Multiply_distribution φ φ.hasTemperateGrowth (φ.memLp (∞ : ℝ≥0∞) volume)
    (C (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u))

include hon in
theorem twoFormGram_cutoff_memSobolev (n : ℕ) (V : Set FourSpace) (hV : MeasurableSet V)
    (w : Lp ℂ 2 (volume : Measure FourSpace)) (hw : MemSobolev (n : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)))
    (he : (w : FourSpace → ℂ) =ᵐ[volume.restrict V] fun z =>
      (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u z : ℂ)) (haV : tsupport a ⊆ V) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) : 𝓢'(FourSpace, ℂ)) := by
  rw [twoFormGram_cutoff_distribution c S hK hKt χ hχ hc hs a ha hca hsa hon v u]
  exact scalar_local_sobolev_transfer n _ w hw V hV he a ha hca haV

end
end PositiveEinsteinFour.Geometry
end


section

/-! All six actual two-form components have H2 representatives on one
common neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp in
theorem twoFormRough_common_H2 (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ χ z = 1} ∈ 𝓝 z₀.val) :
    ∃ V : Set FourSpace, IsOpen V ∧ z₀.val ∈ V ∧ V ⊆ K ∧ (∀ z ∈ V, χ z = 1) ∧
      ∃ w : Fin 6 → Lp ℂ 2 (volume : Measure FourSpace), ∀ r,
        MemSobolev 2 2 (w r : 𝓢'(FourSpace, ℂ)) ∧
        (w r : FourSpace → ℂ) =ᵐ[volume.restrict V] fun z =>
          (twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z : ℂ) := by
  have he (r : Fin 6) := twoFormRough_H2_representative c S hS hK hKt χ hχ hc hs
    U hU hUt hKU hp r u f hu z₀ hnear
  choose V hV hzV hVK hone w hw hweq using he
  let W : Set FourSpace := ⋂ r : Fin 6, V r
  refine ⟨W, isOpen_iInter_of_finite hV, mem_iInter.mpr hzV,
    (iInter_subset V 0).trans (hVK 0), fun z hz => hone 0 z (mem_iInter.mp hz 0), w, ?_⟩
  intro r
  exact ⟨hw r, ae_restrict_of_ae_restrict_of_subset (iInter_subset V r) (hweq r)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth partitions act linearly on the actual H1 chart
coefficients, so local regularity estimates can be assembled. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGram_cutoff_sum {ι : Type*} [Fintype ι]
    (c : M) (S : Mat4) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hsa : tsupport a ⊆ K) (b : ι → FourSpace → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hcb : ∀ i, HasCompactSupport (b i))
    (hsb : ∀ i, tsupport (b i) ⊆ K) (hsum : a = fun z => ∑ i : ι, b i z)
    (v : Fin 2 → Fin 4) (u : TwoFormH1 o) :
    twoFormGramValueL2 c S hK hKt a ha hca hsa v u =
      ∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v u := by
  let L : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
    twoFormGramValueL2 c S hK hKt a ha hca hsa v
  let R : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
    ∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v
  have he : L u = R u := by
    refine UniformSpace.Completion.induction_on u (isClosed_eq L.continuous R.continuous) ?_
    intro w
    change twoFormGramValueL2 c S hK hKt a ha hca hsa v (smoothTwoFormToH1 w) =
      R (smoothTwoFormToH1 w)
    simp only [R, _root_.sum_apply]
    let T : FourSpace → ℝ := fun z => frameTensor (chartGramMatrix g c S z)
      (twoFormCoordinates o (w : smoothTwoForms o).val c z) v
    apply Lp.ext
    have hbe : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i : ι,
        twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v (smoothTwoFormToH1 w) z =
          b i z * frameTensor (chartGramMatrix g c S z)
            (twoFormCoordinates o (w : smoothTwoForms o).val c z) v := by
      apply Filter.eventually_all.mpr
      intro i
      exact twoFormGramValueL2_coe c S hK hKt (b i) (hb i) (hcb i) (hsb i) v w
    filter_upwards [twoFormGramValueL2_coe c S hK hKt a ha hca hsa v w,
      Lp.coeFn_finsetSum Finset.univ (fun i : ι =>
        twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v (smoothTwoFormToH1 w)),
      hbe] with z haz hsz hbz
    have hsz' : (∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v
        (smoothTwoFormToH1 w)) z = ∑ i : ι,
      twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v (smoothTwoFormToH1 w) z := by
      simpa only [Finset.sum_apply] using hsz
    calc
      _ = a z * T z := haz
      _ = ∑ i : ι, b i z * T z := by rw [hsum]; exact Finset.sum_mul ..
      _ = ∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v
          (smoothTwoFormToH1 w) z := Finset.sum_congr rfl (fun i _ => (hbz i).symm)
      _ = _ := hsz'.symm
  simpa only [L, R, _root_.sum_apply] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! All alternating coordinates of inner cutoffs have actual H2 regularity.
This includes the coordinates used by the connection correction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)

include hS in
theorem twoFormGram_order_of_six (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ K) (u : TwoFormH1 o)
    (hreg : ∀ r : Fin 6, MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc hs (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)))
    (v : Fin 2 → Fin 4) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc hs v u) : 𝓢'(FourSpace, ℂ)) := by
  rw [twoFormGramValue_component_expansion c S hS hK hKt a ha hc hs v u]
  apply scalarReal_memSobolev_finset
  intro r _
  rw [scalarComplexL2_real_smul_distribution]
  exact (hreg r).smul _

variable (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp hχ hc hs in
theorem twoFormRough_inner_H2 (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ χ z = 1} ∈ 𝓝 z₀.val) :
    ∃ V : Set FourSpace, IsOpen V ∧ z₀.val ∈ V ∧ ∃ hVK : V ⊆ K,
      (∀ z ∈ V, χ z = 1) ∧
      ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
        (haV : tsupport a ⊆ V) (v : Fin 2 → Fin 4),
        MemSobolev 2 2 (scalarComplexL2
          (twoFormGramValueL2 c S hK hKt a ha hca (haV.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  obtain ⟨V, hV, hzV, hVK, hone, w, hw⟩ := twoFormRough_common_H2 c S hS hK hKt χ hχ hc hs
    U hU hUt hKU hp u f hu z₀ hnear
  refine ⟨V, hV, hzV, hVK, hone, ?_⟩
  intro a ha hca haV v
  apply twoFormGram_order_of_six c S hS hK hKt 2 a ha hca (haV.trans hVK) u
  intro r
  have hwr : MemSobolev ((2 : ℕ) : ℝ) 2 (w r : 𝓢'(FourSpace, ℂ)) := by
    simpa only [Nat.cast_ofNat] using (hw r).1
  simpa only [Nat.cast_ofNat] using twoFormGram_cutoff_memSobolev c S hK hKt χ hχ hc hs
    a ha hca (haV.trans hVK) (fun z hz => hone z (haV hz)) (twoFormComponentIndex r) u
    2 V hV.measurableSet (w r) hwr (hw r).2 haV

end
end PositiveEinsteinFour.Geometry
end


section

/-! Once the component coefficients are locally H2, the actual localized
covariant derivatives are H1 and their connection corrections are H2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev 2 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (v : Fin 2 → Fin 4) (i : Fin 4)

include hreg in
theorem twoFormGramConnection_memSobolev_two :
    MemSobolev 2 2 (scalarComplexL2 (twoFormGramConnectionL2 c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  change MemSobolev 2 2 (scalarComplexL2 (∑ k : Fin 2, ∑ q : Fin 4,
    twoFormGramValueL2 c S hK hKt (twoFormConnectionCutoff (g := g) c S η i q (v k))
      (twoFormConnectionCutoff_smooth c S hS hKt η hη (hηV.trans hVK) i q (v k))
      hcη.mul_right (tsupport_mul_subset_left.trans (hηV.trans hVK)) (Function.update v k q) u) :
        𝓢'(FourSpace, ℂ))
  apply scalarReal_memSobolev_finset 2
  intro k _
  apply scalarReal_memSobolev_finset 2
  intro q _
  exact hreg _ _ _ (tsupport_mul_subset_left.trans hηV) _

include hreg in
theorem twoFormGramDerivativeCorrection_memSobolev_two :
    MemSobolev 2 2 (scalarComplexL2 (twoFormGramDerivativeCorrection c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev 2 2 (C (_ + _))
  rw [map_add]
  exact (hreg _ _ _ ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hηV) v).add
    (twoFormGramConnection_memSobolev_two c S hS hK hKt hVK u hreg η hη hcη hηV v i)

include hreg in
theorem twoFormGramCovariant_memSobolev_one :
    MemSobolev 1 2 (scalarComplexL2 (twoFormGramCovariantL2 c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  have hvalue := hreg η hη hcη hηV v
  have hp : MemSobolev 1 2 (scalarComplexL2 (twoFormGramPartialL2 c S hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
    have hd := hvalue.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i)
    change MemSobolev (2 - 1) 2 (scalarCoordinateDerivative i (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η hη hcη (hηV.trans hVK) v u) : 𝓢'(FourSpace, ℂ))) at hd
    rw [twoFormGram_complex_derivative] at hd
    norm_num at hd ⊢
    exact hd
  have hc := (twoFormGramDerivativeCorrection_memSobolev_two c S hS hK hKt hVK u hreg
    η hη hcη hηV v i).mono (by norm_num : (1 : ℝ) ≤ 2)
  have he := eq_sub_of_add_eq (twoFormGramCovariant_add_correction c S hS hK hKt
    η hη hcη (hηV.trans hVK) v i u)
  rw [he]
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev 1 2 (C (_ - _))
  rw [map_sub]
  exact hp.sub hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local representatives in possibly different inner cutoffs give
integer Sobolev regularity for every compactly supported chart cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_local_sobolev_assembly (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hVK : V ⊆ K) (u : TwoFormH1 o)
    (hloc : ∀ r : Fin 6, ∀ x ∈ V,
      ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
        (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ x ∈ W ∧
          (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
            MemSobolev (n : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
            (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
              (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ))
    (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (haV : tsupport a ⊆ V) (v : Fin 2 → Fin 4) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hca (haV.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  apply twoFormGram_order_of_six c S hS hK hKt n a ha hca (haV.trans hVK) u
  intro r
  let X := {x : FourSpace // x ∈ tsupport a}
  have hx (x : X) := hloc r x (haV x.property)
  choose η hη hcη hηK W hW hxW hone w hw he using hx
  have hcover : tsupport a ⊆ ⋃ x : X, W x := by
    intro x hx
    exact mem_iUnion_of_mem ⟨x, hx⟩ (hxW ⟨x, hx⟩)
  obtain ⟨s, hs⟩ := hca.elim_finite_subcover W hW hcover
  let ι := {x : X // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : tsupport a ⊆ ⋃ i : ι, W i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨i, hi⟩ hxi
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (M := FourSpace) hca.isClosed (fun i : ι => W i.val)
      (fun i => hW i.val) hfinite
  let b : ι → FourSpace → ℝ := fun i z => a z * ρ i z
  have hb (i : ι) : ContDiff ℝ ∞ (b i) := ha.mul (ρ i).contMDiff.contDiff
  have hbc (i : ι) : HasCompactSupport (b i) := hca.mul_right
  have hbK (i : ι) : tsupport (b i) ⊆ K := tsupport_mul_subset_left.trans (haV.trans hVK)
  have hbW (i : ι) : tsupport (b i) ⊆ W i.val := tsupport_mul_subset_right.trans (hρ i)
  have hparts (i : ι) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt (b i) (hb i) (hbc i) (hbK i)
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormGram_cutoff_memSobolev c S hK hKt (η i.val) (hη i.val) (hcη i.val) (hηK i.val)
      (b i) (hb i) (hbc i) (hbK i) (fun z hz => hone i.val z (hbW i hz))
      (twoFormComponentIndex r) u n (W i.val) (hW i.val).measurableSet
      (w i.val) (hw i.val) (he i.val) (hbW i)
  have hsum : a = fun z => ∑ i : ι, b i z := by
    funext z
    by_cases hz : a z = 0
    · simp only [b, hz, zero_mul, Finset.sum_const_zero]
    · have hρz : (∑ i : ι, ρ i z) = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_tsupport a hz)
      change a z = ∑ i : ι, a z * ρ i z
      rw [← Finset.mul_sum, hρz, mul_one]
  rw [twoFormGram_cutoff_sum c S hK hKt a ha hca (haV.trans hVK) b hb hbc hbK hsum]
  exact scalarReal_memSobolev_finset n Finset.univ _ (fun i _ => hparts i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The connection correction of a locally H2 two-form has H1
divergence. The witnesses are actual Euclidean L2 functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

theorem twoFormCoefficientPair_memSobolev_two (b : FourSpace → TwoFormFour)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (f : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (hf : ∀ r : Fin 6, MemSobolev 2 2
      (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev 2 2 (scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hc f) :
      𝓢'(FourSpace, ℂ)) := by
  rw [twoFormCoefficientPair_distribution]
  have hs (s : Finset (Fin 6)) : MemSobolev 2 2 (∑ r ∈ s,
      smulLeftCLM ℂ (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero FourSpace ℂ 2 2
    | @insert r s hr ih =>
      rw [Finset.sum_insert hr]
      exact (scalar_memSobolev_schwartz_multiplier 2 (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))
        (by simpa only [Nat.cast_ofNat] using hf r)).add ih
  exact hs Finset.univ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev 2 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hreg in
theorem twoFormFluxCorrection_memSobolev_two (j : Fin 4) :
    MemSobolev 2 2 (scalarComplexL2 (twoFormFluxCorrection c S hS hK hKt
      η hη hcη (hηV.trans hVK) b u j) : 𝓢'(FourSpace, ℂ)) := by
  apply scalarReal_memSobolev_finset 2
  intro i _
  apply twoFormCoefficientPair_memSobolev_two
    (twoFormFluxCoefficient (g := g) c η b i j)
    (twoFormFluxCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b i j)
    hcη.mul_right.smul_right
  intro r
  rw [twoFormGramCorrectionVector_component]
  exact twoFormGramDerivativeCorrection_memSobolev_two c S hS hK hKt hVK u hreg
    η hη hcη hηV (twoFormComponentIndex r) i

include hreg in
theorem twoFormFluxCorrection_H1_derivatives :
    ∃ D : Fin 4 → Lp ℝ 2 (volume : Measure FourSpace),
      (∀ j, scalarCoordinateDerivative j (scalarComplexL2
        (twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j) :
          𝓢'(FourSpace, ℂ)) = (scalarComplexL2 (D j) : 𝓢'(FourSpace, ℂ))) ∧
      ∀ j, MemSobolev 1 2 (scalarComplexL2 (D j) : 𝓢'(FourSpace, ℂ)) := by
  have he (j : Fin 4) : ∃ D : Lp ℝ 2 (volume : Measure FourSpace),
      scalarCoordinateDerivative j (scalarComplexL2
        (twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j) :
          𝓢'(FourSpace, ℂ)) = (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) ∧
      MemSobolev 1 2 (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) := by
    simpa only [Nat.cast_one] using scalar_real_derivative_sobolev 1 _
      (by simpa only [Nat.cast_one, one_add_one_eq_two] using
        twoFormFluxCorrection_memSobolev_two c S hS hK hKt hVK u hreg η hη hcη hηV b j) j
  choose D hD hregD using he
  exact ⟨D, hD, hregD⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual lower-order source in the harmonic two-form equation
has H1 regularity after an inner chart cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (hχV : ∀ z ∈ V, χ z = 1)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev 2 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hreg in
theorem twoFormInnerNabla_component_H1 (i : Fin 4) (r : Fin 6) :
    MemSobolev 1 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
        𝓢'(FourSpace, ℂ)) := by
  dsimp only [twoFormGramNablaL2]
  rw [twoFormVectorComponentL2_assemble]
  exact twoFormGramCovariant_memSobolev_one c S hS hK hKt hVK u hreg η hη hcη hηV
    (twoFormComponentIndex r) i

include hχ hc hs hχV hreg in
theorem twoFormHarmonicDivergenceSource_H1 :
    MemSobolev 1 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev 1 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_one
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right
    intro r
    rw [map_sub]
    change MemSobolev 1 2 (C (_ - _))
    rw [map_sub]
    exact (twoFormPotential_chart_memSobolev_one c S hS hK hKt χ hχ hc hs
      η hη hcη (hηV.trans hVK) (fun z hz => hχV z (hηV hz)) u r).sub
      (twoFormGramVectorComponent_memSobolev_one c S hK hKt η hη hcη (hηV.trans hVK) u r)
  · apply scalarReal_memSobolev_sum
    intro i _
    exact twoFormCoefficientPair_memSobolev_one
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right _
      (twoFormInnerNabla_component_H1 c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth coefficient pairing at the integer orders needed by the
harmonic two-form bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped BigOperators SchwartzMap ENNReal ContDiff

noncomputable section

variable (b : FourSpace → TwoFormFour) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)

theorem twoFormCoefficientPair_memSobolev_integer (n : ℕ) (f : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (hf : ∀ r : Fin 6, MemSobolev (n : ℝ) 2
      (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hc f) :
      𝓢'(FourSpace, ℂ)) := by
  rw [twoFormCoefficientPair_distribution]
  have hs (s : Finset (Fin 6)) : MemSobolev (n : ℝ) 2 (∑ r ∈ s,
      smulLeftCLM ℂ (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero FourSpace ℂ (n : ℝ) 2
    | @insert r s hr ih =>
      rw [Finset.sum_insert hr]
      have hfr : MemSobolev (n : ℝ) 2
          (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) := by
        exact hf r
      have hm := scalar_memSobolev_schwartz_multiplier n (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) hfr
      have hm' := hm.add (by exact ih)
      exact hm'
  exact hs Finset.univ


end
end PositiveEinsteinFour.Geometry
end


section

/-! Integer-order control of the actual localized connection corrections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (v : Fin 2 → Fin 4) (i : Fin 4)

include hreg in
theorem twoFormGramConnection_memSobolev_integer :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramConnectionL2 c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  change MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ k : Fin 2, ∑ q : Fin 4,
    twoFormGramValueL2 c S hK hKt (twoFormConnectionCutoff (g := g) c S η i q (v k))
      (twoFormConnectionCutoff_smooth c S hS hKt η hη (hηV.trans hVK) i q (v k))
      hcη.mul_right (tsupport_mul_subset_left.trans (hηV.trans hVK)) (Function.update v k q) u) :
        𝓢'(FourSpace, ℂ))
  apply scalarReal_memSobolev_finset n
  intro k _
  apply scalarReal_memSobolev_finset n
  intro q _
  exact hreg _ _ _ (tsupport_mul_subset_left.trans hηV) _

include hreg in
theorem twoFormGramDerivativeCorrection_memSobolev_integer :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramDerivativeCorrection c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev (n : ℝ) 2 (C (_ + _))
  rw [map_add]
  exact (hreg _ _ _ ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hηV) v).add
    (twoFormGramConnection_memSobolev_integer n c S hS hK hKt hVK u hreg η hη hcη hηV v i)

theorem twoFormGramCovariant_memSobolev_integer
    (hregSucc : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramCovariantL2 c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  have hvalue := hregSucc η hη hcη hηV v
  have hp : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramPartialL2 c S hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
    have hd := hvalue.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i)
    change MemSobolev (((n + 1 : ℕ) : ℝ) - 1) 2 (scalarCoordinateDerivative i (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η hη hcη (hηV.trans hVK) v u) : 𝓢'(FourSpace, ℂ))) at hd
    rw [twoFormGram_complex_derivative] at hd
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hd
  have hc := (twoFormGramDerivativeCorrection_memSobolev_integer (n + 1) c S hS hK hKt hVK u
    hregSucc η hη hcη hηV v i).mono
      (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
  have he := eq_sub_of_add_eq (twoFormGramCovariant_add_correction c S hS hK hKt
    η hη hcη (hηV.trans hVK) v i u)
  rw [he]
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  exact hp.sub hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The harmonic equation has actual H1 forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (hχV : ∀ z ∈ V, χ z = 1)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev 2 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hχ hc hs hχV hU hKU hp hu hreg in
theorem twoFormHarmonic_principalWeakH1 (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev 1 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_H1_derivatives c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev 1 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev 1 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_sum
      intro j _
      exact hDH j
    exact (twoFormHarmonicDivergenceSource_H1 c S hS hK hKt hVK χ hχ hc hs hχV u hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hχ hc hs hχV hU hKU hp hu hreg in
theorem twoFormHarmonic_weightedWeakH1 (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev 1 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormHarmonic_principalWeakH1 c S hS hK hKt hVK
    χ hχ hc hs hχV U hU hUt hKU hp u hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev 1 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature potential preserves local integer Sobolev
regularity, with its outer cutoff constructed inside the given open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hreg in
theorem twoFormPotential_local_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))) : 𝓢'(FourSpace, ℂ)) := by
  obtain ⟨χ, hχ, hcχ, hχV, hone⟩ := exists_scalar_compact_cutoff hcη hV hηV
  rw [twoFormPotential_chart_pair c S hS hK hKt χ hχ hcχ (hχV.trans hVK)
    η hη hcη (hηV.trans hVK) hone]
  apply twoFormCoefficientPair_memSobolev_integer
    (twoFormPotentialCoefficient (g := g) c S η r)
    (twoFormPotentialCoefficient_smooth c S η hη ((hηV.trans hVK).trans hKt) r)
    (twoFormPotentialCoefficient_compact c S η hcη r) n
  intro k
  rw [twoFormGramVectorComponent]
  exact hreg χ hχ hcχ hχV (twoFormComponentIndex k)

end
end PositiveEinsteinFour.Geometry
end

end OAI
