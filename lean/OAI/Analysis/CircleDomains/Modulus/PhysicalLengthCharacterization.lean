import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationPushforward
import OAI.Analysis.CircleDomains.Topology.DyadicOpenCover

namespace OAI

/-! Uniqueness and compact-interval exhaustion of physical-domain arclength.
This identifies the dyadic construction with ordinary arclength on all open
domain-time components, including paths that revisit points. -/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem measure_eq_of_compact_time_restrictions {V : Set PathTime} (hV : IsOpen V)
    (μ ν : Measure PathTime) (hμ : μ Vᶜ = 0) (hν : ν Vᶜ = 0)
    (hlocal : ∀ a b : PathTime, a ≤ b → Icc a b ⊆ V →
      μ.restrict (Icc a b) = ν.restrict (Icc a b)) : μ = ν := by
  have hm : μ.restrict V = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hμ)
  have hn : ν.restrict V = ν := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hν)
  rw [← hm, ← hn, ← iUnion_insideDyadicCell hV]
  apply Measure.restrict_iUnion_congr.mpr
  intro p
  exact hlocal _ _ (dyadicLeft_le_right p.val.1 p.val.2) p.property

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalTimeLength_unique (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (μ : Measure PathTime)
    (hμ : μ (γ.val ⁻¹' U)ᶜ = 0)
    (hlocal : ∀ (a b : PathTime) (hab : a ≤ b)
      (hγ : γ.val ∈ pathsInsideOn U a b),
      μ.restrict (Icc a b) = rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)) :
    μ = physicalTimeLength e y₀ γ := by
  apply measure_eq_of_compact_time_restrictions (hU.preimage γ.val.continuous)
    μ _ hμ (physicalTimeLength_compl e hU y₀ γ)
  intro a b hab hγ
  exact (hlocal a b hab hγ).trans (physicalTimeLength_restrict_compact e hU y₀ γ hab hγ).symm

theorem physicalTimeLength_compact_mass (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    physicalTimeLength e y₀ γ (Icc a b) =
      eVariationOn (physicalSubpath e hab ⟨γ.val, hγ⟩) univ := by
  have h := congrArg (fun μ : Measure PathTime => μ univ)
    (physicalTimeLength_restrict_compact e hU y₀ γ hab hγ)
  rw [Measure.restrict_apply_univ,
    rectifiableLengthCode_univ (physicalSubpath_rectifiable e hU hab γ.val hγ y₀ γ.property)] at h
  exact h

theorem physicalTimeLength_exhaustion (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (a b : ℕ → PathTime)
    (hab : ∀ n, a n ≤ b n) (hγ : ∀ n, γ.val ∈ pathsInsideOn U (a n) (b n))
    (hmono : Monotone (fun n => Icc (a n) (b n))) {W : Set PathTime}
    (hW : (⋃ n, Icc (a n) (b n)) = W) :
    physicalTimeLength e y₀ γ W =
      ⨆ n, eVariationOn (physicalSubpath e (hab n) ⟨γ.val, hγ n⟩) univ := by
  rw [← hW, hmono.measure_iUnion]
  congr 1
  funext n
  exact physicalTimeLength_compact_mass e hU y₀ γ (hab n) (hγ n)

theorem physicalTimeLength_component_sum {ι : Type*} [Countable ι]
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (W : ι → Set PathTime) (hW : ∀ i, MeasurableSet (W i))
    (hdis : Pairwise (Disjoint on W)) (hcover : (⋃ i, W i) = γ.val ⁻¹' U)
    (a b : ι → ℕ → PathTime) (hab : ∀ i n, a i n ≤ b i n)
    (hγ : ∀ i n, γ.val ∈ pathsInsideOn U (a i n) (b i n))
    (hmono : ∀ i, Monotone (fun n => Icc (a i n) (b i n)))
    (hexh : ∀ i, (⋃ n, Icc (a i n) (b i n)) = W i) :
    physicalDomainLength e y₀ γ.val =
      ∑' i, ⨆ n, eVariationOn (physicalSubpath e (hab i n) ⟨γ.val, hγ i n⟩) univ := by
  rw [← physicalTimeLength_univ e y₀ γ]
  have hr : (physicalTimeLength e y₀ γ).restrict (γ.val ⁻¹' U) = physicalTimeLength e y₀ γ :=
    Measure.restrict_eq_self_of_ae_mem (physicalTimeLength_ae_mem e hU y₀ γ)
  have hm := congrArg (fun μ : Measure PathTime => μ univ) hr
  rw [Measure.restrict_apply_univ] at hm
  rw [← hm, ← hcover, measure_iUnion hdis hW]
  congr 1
  funext i
  exact physicalTimeLength_exhaustion e hU y₀ γ (a i) (b i) (hab i) (hγ i) (hmono i) (hexh i)

end CircleDomainRigidity

end

end OAI
