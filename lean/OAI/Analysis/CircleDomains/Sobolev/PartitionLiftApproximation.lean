import OAI.Analysis.CircleDomains.Sobolev.LocalLiftSmoothing
import OAI.Analysis.CircleDomains.Sobolev.WeightedSobolevErrors
import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothPartition

namespace OAI

/-! Actual smooth approximants of the local real branches, preserving
interval bounds and prescribed weighted L2 derivative errors. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_partition_lift_approximants
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : ι → EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 (u j) (W j))
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ, ∀j,
      (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j)) ∧
      (∀a b : ℝ, (∀x ∈ W j, u j x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u j x))
        2 volume < ε j) := by
  classical
  suffices H : ∀j, ∃v : EuclideanPlane → ℝ,
      (ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v) ∧
      (∀a b : ℝ, (∀x ∈ W j, u j x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v x - u j x))
        2 volume < ε j) by
    choose v hv using H
    exact ⟨v, hv⟩
  intro j
  obtain ⟨V, φ, hV, hKV, hVW, hsmooth, _, hvalue, hgrad, _, hinterval, _⟩ :=
    exists_local_lift_sobolev_smoothing (hW j) (ρ.compact j).isCompact
      (hsub j) (hu j)
  let hw := (hu j).restrict hV hVW
  have hgrad' (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using hgrad i
  have herr (i : Fin 2) := tendsto_partition_derivative_error hV hw
    (fun n => (hsmooth n).1) hvalue hgrad' (ρ.smooth j) (ρ.compact j) hKV i
  have he : ∀ᶠ n in atTop, ∀i : Fin 2, eLpNorm (fun x =>
      ρ.weight j x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
        (hu j).weakGrad x i) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (φ n x - u j x))
      2 volume < ε j := by
    apply eventually_all.mpr
    intro i
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using
      (tendsto_order.1 (herr i)).2 (ε j) (hε j)
  obtain ⟨n, hn, hb⟩ := (he.and hinterval).exists
  exact ⟨φ n, hsmooth n, hb, hn⟩

theorem exists_partition_lift_approximants_with_accuracy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : ι → EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 (u j) (W j))
    (hc : ∀ j, ContinuousOn (u j) (W j))
    (δ : ι → ℝ) (hδ : ∀ j, 0 < δ j)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ, ∀j,
      (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j)) ∧
      (∀a b : ℝ, (∀x ∈ W j, u j x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      (∀ x ∈ tsupport (ρ.weight j), |v j x - u j x| < δ j) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u j x))
        2 volume < ε j) := by
  classical
  suffices H : ∀j, ∃v : EuclideanPlane → ℝ,
      (ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v) ∧
      (∀a b : ℝ, (∀x ∈ W j, u j x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v x ∈ Icc a b) ∧
      (∀ x ∈ tsupport (ρ.weight j), |v x - u j x| < δ j) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v x - u j x))
        2 volume < ε j) by
    choose v hv using H
    exact ⟨v, hv⟩
  intro j
  obtain ⟨V, φ, hV, hKV, hVW, hsmooth, _, hvalue, hgrad, _, hinterval, huniform⟩ :=
    exists_local_lift_sobolev_smoothing (hW j) (ρ.compact j).isCompact
      (hsub j) (hu j)
  let hw := (hu j).restrict hV hVW
  have hgrad' (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using hgrad i
  have herr (i : Fin 2) := tendsto_partition_derivative_error hV hw
    (fun n => (hsmooth n).1) hvalue hgrad' (ρ.smooth j) (ρ.compact j) hKV i
  have he : ∀ᶠ n in atTop, ∀i : Fin 2, eLpNorm (fun x =>
      ρ.weight j x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
        (hu j).weakGrad x i) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (φ n x - u j x))
      2 volume < ε j := by
    apply eventually_all.mpr
    intro i
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using
      (tendsto_order.1 (herr i)).2 (ε j) (hε j)
  obtain ⟨n, hn, hb, hv⟩ := (he.and (hinterval.and (huniform (hc j) (δ j) (hδ j)))).exists
  exact ⟨φ n, hsmooth n, hb, hv, hn⟩

end CircleDomainRigidity

end

end OAI
