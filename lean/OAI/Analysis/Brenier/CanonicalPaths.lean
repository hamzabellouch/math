import OAI.Analysis.Brenier.AtomicPaths
import OAI.Analysis.Brenier.InterceptContinuity
import OAI.Analysis.Brenier.InterceptEnergy
import OAI.Analysis.Brenier.PrefixSampling

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- Canonical closed-cell intercepts give the entire normalized path interface:
measurability is global, while differentiability and derivative continuity are
needed only on the open interval where the sites are distinct. -/
theorem exists_canonical_atomic_intercept_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y z : ι → E d) {κ : ℝ} {R : ℝ≥0}
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) 1,
      ContDiffAt ℝ 1 (fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
        (fun i => (1-q) • y i + q • z i)) t)
    (henergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
        (fun i => (1-q) • y i + q • z i)
      (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
        κ * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2) :
    ∃ c r : ι → ℝ → ℝ,
      (∀ i, Measurable (c i)) ∧
      (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
      (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
      (∀ t ∈ Ioo 0 1, ∀ i,
        (uniformMeasure K).real (CellGeometry.closedCell K
          (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
      (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
      ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
        κ * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2 := by
  let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
    (fun i => (1-q) • y i + q • z i)
  let c : ι → ℝ → ℝ := fun i t => (C t : ι → ℝ) i
  let L : ι → CellLaplacian.normalizedSpace m →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.proj i).comp (CellLaplacian.normalizedSpace m).subtypeL
  have hcoord : ∀ i t, t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (c i) (((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i) t := by
    intro i t ht
    exact (L i).hasFDerivAt.comp_hasDerivAt t
      ((hregular t ht).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨c, fun i => deriv (c i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (measurable_pi_apply i).comp
      ((measurable_intercepts_coe hK hconv hKi m hm hsum).comp (by fun_prop))
  · intro i
    have hci : ContDiffOn ℝ 1 (c i) (Ioo 0 1) := by
      intro t ht
      exact ((L i).contDiff.contDiffAt.comp t (hregular t ht)).contDiffWithinAt
    exact hci.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  · intro i t ht
    exact (hcoord i t ht).differentiableAt.hasDerivAt
  · intro t ht i
    exact congrFun (intercepts_spec hK hconv hKi m hm hsum
      (fun j => (1-t) • y j + t • z j) (hinj t ht)) i
  · intro t _
    exact (C t).property
  · intro t ht
    have heq : ∀ i, deriv (c i) t =
        ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i :=
      fun i => (hcoord i t ht).deriv
    simp_rw [heq]
    exact henergy t ht

end Problem358.FixedMassIntercepts

end

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- The canonical normalized intercept path supplies all measurability and mass
hypotheses of the interior potential estimate. Its scalar derivatives are the
coordinates of its derivative in the normalization subspace. -/
theorem canonical_atomic_potential_L2_bound_of_deriv_energy
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y z : ι → E d) {w κ : ℝ} {R : ℝ≥0}
    (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i))
    (hspeed : (∑ i, m i * ‖z i-y i‖ ^ 2) ≤ w ^ 2)
    (henergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
        (fun i => (1-q) • y i + q • z i)
      HasDerivAt C (deriv C t) t ∧
        (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
          κ * (R : ℝ) ^ 2 * w ^ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
      (fun i => (1-q) • y i + q • z i)
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => (1-b) • y i + b • z i) (C b) x -
       FiniteAffine.potential (fun i => (1-a) • y i + a • z i) (C a) x) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b-a) := by
  let := UniformSource.probability hK hKi
  let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
    (fun i => (1-q) • y i + q • z i)
  let c : ι → ℝ → ℝ := fun i t => (C t : ι → ℝ) i
  have hc : ∀ i, Measurable (c i) := by
    intro i
    exact (measurable_pi_apply i).comp
      ((measurable_intercepts_coe hK hconv hKi m hm hsum).comp (by fun_prop))
  have hcoord : ∀ i t, t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (c i) (((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i) t := by
    intro i t ht
    let L : CellLaplacian.normalizedSpace m →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (CellLaplacian.normalizedSpace m).subtypeL
    exact L.hasFDerivAt.comp_hasDerivAt t (henergy t ht).1
  apply atomic_potential_path_L2_bound_of_closed_masses hK.measurableSet
    y z m c (fun i => deriv (c i)) hw hκ hm hbounded hc
    (fun i => measurable_deriv (c i)) _ hinj _ hspeed _ ha hab hb
  · intro i t ht
    exact (hcoord i t ht).differentiableAt.hasDerivAt
  · intro t ht i
    exact congrFun (intercepts_spec hK hconv hKi m hm hsum
      (fun j => (1-t) • y j + t • z j) (hinj t ht)) i
  · intro t ht
    have heq : ∀ i, deriv (c i) t =
        ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i :=
      fun i => (hcoord i t ht).deriv
    simp_rw [heq]
    exact (henergy t ht).2

end Problem358.FixedMassIntercepts

end

noncomputable section

open Set MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- Positive prescribed masses along distinct affine site paths admit genuine
normalized intercepts with continuous derivatives and the uniform geometric
energy bound. All mass regularity and midpoint-coupling inputs are discharged. -/
theorem exists_actual_atomic_intercept_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y z : ι → E d) (R : ℝ≥0)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i)) :
    ∃ c r : ι → ℝ → ℝ,
      (∀ i, Measurable (c i)) ∧
      (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
      (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
      (∀ t ∈ Ioo 0 1, ∀ i,
        (uniformMeasure K).real (CellGeometry.closedCell K
          (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
      (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
      ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
        162 * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2 := by
  classical
  let Y : ℝ → (ι → E d) := fun t i => (1-t) • y i + t • z i
  let C := fun t => intercepts hK hconv hKi m hm hsum (Y t)
  let v : ι → E d := fun i => z i - y i
  have hmassC1 : ∀ t ∈ Ioo (0 : ℝ) 1,
      ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m) (Y t, C t) := by
    intro t ht
    apply CellGeometry.contDiffAt_normalizedMassMap_of_raw m (Y t, C t)
    apply CellGeometry.contDiffAt_uniformMassMap hK hconv (Y t) (C t) (hinj t ht)
    intro i
    have hi := congrFun (intercepts_spec hK hconv hKi m hm hsum (Y t) (hinj t ht)) i
    change (uniformMeasure K).real (CellGeometry.closedCell K (Y t) (C t) i) = m i at hi
    rw [hi]
    exact hm i
  apply exists_canonical_atomic_intercept_path hK hconv hKi m hm hsum y z
    (κ := 162) (R := R) hinj
  · intro t ht
    have hYc : ContDiffAt ℝ 1 Y t := by dsimp [Y]; fun_prop
    exact (contDiffAt_intercepts_of_normalizedMassC1 hK hconv hKi m hm hsum
      (Y t) (hinj t ht) (hmassC1 t ht)).comp t hYc
  · intro t ht
    have hYd : HasDerivAt Y v t := by
      apply hasDerivAt_pi.mpr
      intro i
      have heq : (fun q : ℝ => Y q i) = fun q => y i + q • (z i - y i) := by
        funext q
        dsimp [Y]
        module
      rw [heq]
      simpa only [v, one_smul] using!
        ((hasDerivAt_id t).smul_const (z i - y i)).const_add (y i)
    let e : ℝ := ∑ i, m i * ‖y i-z i‖ ^ 2
    have he : 0 ≤ e := Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
    have hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ Real.sqrt e ^ 2 := by
      rw [Real.sq_sqrt he]
      exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp only [v, norm_sub_rev])
    have henergy := intercepts_comp_deriv_energy_le_of_massC1_convex_midpoint
      hK hconv hKi m hm hsum Y v t hYd (hinj t ht) R R.property
      hbounded hspeed (hmassC1 t ht)
      (fun U V hU hcU hvU hV hcV hvV =>
        exists_convexBody_midpoint_coupling_of_pos hU hcU hvU hV hcV hvV)
    simpa only [Real.sq_sqrt he] using henergy.2

end Problem358.FixedMassIntercepts

end

end OAI
