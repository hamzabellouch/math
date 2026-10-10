import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.RawPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.TightCapFamily
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Actual weak density and pair-product limits of the cap approximations

The equality of the pair limit with the product of density limits is the
subsequent velocity-averaging step, not an assumption of this extraction.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

private theorem uniformIntegrable_comp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ) (a : ℕ → ℕ) :
    UniformIntegrable (fun n => f (a n)) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  exact ⟨hu.comp a,C,fun n => hC (a n)⟩

theorem TightCapFamily.exists_weak_limits (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  let f := fun N => torusPhysical q (F.approximation N).solution.value
  have hfm (N) : Measurable (f N) :=
    torusPhysical_measurable (F.approximation N).solution.measurable_value q
  have hfn (N) (z) : 0 ≤ f N z :=
    torusPhysical_nonneg (fun u => ((F.approximation N).solution.value_bounds u).1) q z
  have hpairUI := CollisionCompactness.pairProduct_uniformIntegrable hfm hfn F.pairs_ui
  have hpairTight := CollisionCompactness.pairProduct_unifTight hfm hfn F.pairs_tight
  obtain ⟨a,g,ha,hg⟩ := (hDP F.time F.time_pos.le).1 f hfm F.density_ui F.density_tight
  obtain ⟨b,W,hb,hW⟩ := (hDP F.time F.time_pos.le).2
    (fun n => CollisionCompactness.pairProduct (f (a n)))
    (fun n => CollisionCompactness.pairProduct_measurable (hfm (a n)))
    (uniformIntegrable_comp hpairUI a) (hpairTight.comp a)
  have hg' := hg.comp hb.tendsto_atTop
  refine ⟨a ∘ b,g,W,ha.comp hb,hg',hW,?_,?_⟩
  · exact hg'.nonneg (fun n => ae_of_all _ (hfn (a (b n))))
  · exact hW.nonneg (fun n => ae_of_all _ (CollisionCompactness.pairProduct_nonneg (hfn (a (b n)))))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The physical cap limit retains its outer-annulus majorants -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.weak_limit_outer_bound {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ}
    (hg : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g) (J : ℕ) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume F.time, ∀ᵐ v : Velocity,
      u ∉ AnnularEnvelope.torusTail s₀ η J → g (u,v) ≤
        (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q v := by
  let A := 2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J
  let s : Set ((ℝ × Position) × Velocity) := {p | p.1 ∉ AnnularEnvelope.torusTail s₀ η J}
  have hs : MeasurableSet s := (AnnularEnvelope.torusTail_measurable s₀ η J).compl.preimage measurable_fst
  have hum : Measurable (fun p : (ℝ × Position) × Velocity => A*H q p.2) := by
    unfold H singularity
    fun_prop
  have hui : Integrable (fun p : (ℝ × Position) × Velocity => A*H q p.2)
      ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    ((integrable_H hq).const_mul A).comp_snd _
  have hfi n : Integrable (torusPhysical q (F.approximation (φ n)).solution.value)
      ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.density_ui.memLp (φ n))
  have hb n : ∀ᵐ p ∂(AnnularEnvelope.timePositionVolume F.time).prod (volume : Measure Velocity),
      p ∈ s → torusPhysical q (F.approximation (φ n)).solution.value p ≤ A*H q p.2 := by
    have hm := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
    have hset : MeasurableSet {p : (ℝ × Position) × Velocity |
        p ∈ s → torusPhysical q (F.approximation (φ n)).solution.value p ≤ A*H q p.2} := by
      convert hs.compl.union (measurableSet_le hm hum) using 1
      ext p
      simp only [mem_union,mem_compl_iff,mem_ofPred_eq,imp_iff_not_or]
    exact (Measure.ae_prod_iff_ae_ae hset).mpr
      ((F.approximation (φ n)).outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
        hsmall hq F.time_pos.le F.time_le J)
  exact Measure.ae_ae_of_ae_prod (hg.le_on hfi hs hum hui.restrict hb)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
