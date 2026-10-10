import OAI.Analysis.CircleDomains.Sobolev.WeightedSobolevErrors
import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothPartition

namespace OAI

/-! Select one positive local smoothing on each compact partition core,
with prescribed weighted derivative error in both coordinate directions. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_partition_smooth_approximants
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ, ∀j,
      (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
        ∀x, v j x ∈ Icc 0 1) ∧
      (∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u x))
        2 volume < ε j) := by
  classical
  suffices H : ∀j, ∃v : EuclideanPlane → ℝ,
      (ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧ ∀x, v x ∈ Icc 0 1) ∧
      (∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v x - u x))
        2 volume < ε j) by
    choose v hv using H
    exact ⟨v, hv⟩
  intro j
  obtain ⟨V, φ, hV, hKV, hVW, hsmooth, _, hvalue, hgrad, _, hinterval⟩ :=
    exists_local_positive_sobolev_smoothing (hW j) (ρ.compact j).isCompact
      (hsub j) (hu j) (hunit j)
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
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (φ n x - u x))
      2 volume < ε j := by
    apply eventually_all.mpr
    intro i
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using
      (tendsto_order.1 (herr i)).2 (ε j) (hε j)
  obtain ⟨n, hn, hb⟩ := (he.and hinterval).exists
  exact ⟨φ n, hsmooth n, hb, hn⟩

end CircleDomainRigidity

end

end OAI
