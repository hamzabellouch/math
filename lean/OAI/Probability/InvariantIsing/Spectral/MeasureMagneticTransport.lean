import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalTransport
import OAI.Probability.InvariantIsing.Magnetic.MagneticPartitionContinuity

namespace OAI

/-! The field transportation bound extends from finite spectral laws to
every compact spectral law by uniform transform approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace InvariantIsing

theorem measureMagnetic_transport_le {A B : Type*} [Fintype A] [Fintype B]
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (w : A → B → ℝ) (γ c : A → ℝ) (δ d : B → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hγ : ∀ i, 0 ≤ γ i) (hδ : ∀ j, 0 < δ j)
    (hγsum : ∑ i, γ i=1) (hδsum : ∑ j, δ j=1)
    (hrow : ∀ i, ∑ j, w i j=γ i) (hcol : ∀ j, ∑ i, w i j=δ j) :
    (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal ≤
      (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) δ d).toReal+
        ∑ i, ∑ j, w i j* |c i-d j| := by
  let ε := fun k : ℕ => (1 : ℝ)/(k+1)
  let D (k : ℕ) : CompactSpectralPartition ν a b (ε k) := Classical.choice
    (exists_compact_spectral_partition ν a b (ε k) hcompact hbound (by dsimp [ε]; positivity))
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 := compact_partition_magnetic_tendsto ν a b ε D (hbound ha).2 ha hb hbound hε
    γ c hγ hγsum
  have h2 := compact_partition_magnetic_tendsto ν a b ε D (hbound ha).2 ha hb hbound hε
    δ d (fun j => (hδ j).le) hδsum
  apply le_of_tendsto_of_tendsto h1 (h2.add_const _)
  apply Eventually.of_forall
  intro k
  let ρ := fun i : (D k).Positive => (D k).weight i
  let lam := fun i : (D k).Positive => (D k).value i
  have hρ i : 0 < ρ i := i.property
  have hs : ∑ i, ρ i=1 := (D k).weight_sum
  have heq : measureR ((D k).law : Measure ℝ) (D k).edge=finiteR ρ lam hρ hs := by
    funext x
    exact measureR_finiteSpectralMeasure ρ lam hρ hs (D k).upper (D k).le_upper x
  dsimp only
  rw [heq]
  exact finiteMagneticFunctional_transport_le ρ lam hρ hs w γ c δ d hw hγ hδ
    hγsum hδsum hrow hcol

end InvariantIsing

end

end OAI
