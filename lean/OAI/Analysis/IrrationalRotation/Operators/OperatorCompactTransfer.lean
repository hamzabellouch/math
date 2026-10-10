import Mathlib.Analysis.InnerProductSpace.Adjoint
import OAI.Analysis.IrrationalRotation.Model.CompactTransfer
import OAI.Analysis.IrrationalRotation.Analysis.CompactTransfer
import OAI.Analysis.IrrationalRotation.Analysis.StrongLusin
import OAI.Analysis.IrrationalRotation.Rotation.DiagonalContinuity
import OAI.Analysis.IrrationalRotation.Analysis.CappedRatios
import OAI.Analysis.IrrationalRotation.Rotation.UnrestrictedDiagonal
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.CStarAlgebra.Basic

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal lp

noncomputable section
namespace Invariant233.CompactTransfer

local instance operatorCompactTransferSecondCountableTopology :
    SecondCountableTopology (SequenceHilbert ℤ) := by
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs := (Set.countable_range b).isSeparable.span (R := ℂ) |>.closure
  have : TopologicalSpace.SeparableSpace (SequenceHilbert ℤ) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      simpa only [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] using hs)
  infer_instance

def cappedDiagonal {X : Type*} (F : ℤ → X → ℝ)
    (hF : ∀ i x, 0 < F i x) (B : ℝ) (hB : 0 ≤ B) (t : X × X) :
    SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ :=
  SequenceHilbert.diagonal (fun i => ((min B (F i t.2 / F i t.1) : ℝ) : ℂ)) B hB (by
    intro i
    have hn : 0 ≤ min B (F i t.2 / F i t.1) :=
      le_min hB (div_nonneg (hF i t.2).le (hF i t.1).le)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] using
      (min_le_left B (F i t.2 / F i t.1)))

theorem uniform_marginal_budget {X ι : Type*}
    [MeasurableSpace X] (μ : Measure X) (νs : ι → Measure (X × X))
    (hfirst : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.snd)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, hfirst⟩ := hfirst (ε / 2) hhalf
  obtain ⟨δ₂, hδ₂, hsecond⟩ := hsecond (ε / 2) hhalf
  refine ⟨(min δ₁ δ₂ : ℝ≥0), ?_, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_min hδ₁ hδ₂))
  intro A hA hμ i
  have hμ₁ : μ A < (δ₁ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_left δ₁ δ₂)
  have hμ₂ : μ A < (δ₂ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_right δ₁ δ₂)
  have h₁ := hfirst A hA hμ₁ i
  have h₂ := hsecond A hA hμ₂ i
  rw [Measure.map_apply measurable_fst hA] at h₁
  rw [Measure.map_apply measurable_snd hA] at h₂
  have heq₁ : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set X) := by ext t; simp
  have heq₂ : Prod.snd ⁻¹' A = (Set.univ : Set X) ×ˢ A := by ext t; simp
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  calc
    νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤
        ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
      add_le_add h₁.le h₂.le
    _ = ε := by rw [← ENNReal.coe_add, add_halves]

theorem capped_operator_relation_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (C : ℝ) (hC : 0 ≤ C) (hpn : ∀ x, ‖p x‖ ≤ C)
    (B : ℝ) (hB : 0 ≤ B)
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        (νs i : Measure (X × X)) (A ×ˢ Set.univ) +
        (νs i : Measure (X × X)) (Set.univ ×ˢ A) ≤ ε)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0 := by
  classical
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun i => (b.repr_symm_single i).symm
  apply ae_mem_of_closed_approximation hν
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
  obtain ⟨Q, hQ, hμQ, hpQ, hFQ⟩ :=
    StrongLusin.exists_compact_strong_and_continuousOn μ p hC hpn b
      (fun i => by simpa only [hb] using hpm i) F hFm hδ
  let S : Set (X × X) := {t | t ∈ Q ×ˢ Q ∧
    (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0}
  have hScompact : IsCompact S := by
    apply isCompact_diagonal_relation_on Q hQ p
      (fun t i => ((min B (F i t.2 / F i t.1) : ℝ) : ℂ)) B C hB
      (fun t i => ?_) hpQ (fun i => ?_) hpn
    · have hn : 0 ≤ min B (F i t.2 / F i t.1) :=
        le_min hB (div_nonneg (hF i t.2).le (hF i t.1).le)
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] using
        (min_le_left B (F i t.2 / F i t.1))
    · exact continuousOn_capped_ratio (F i) Q (hFQ i)
        (fun x _ => (hF i x).ne') B
  refine ⟨S, hScompact.isClosed, fun _ ht => ht.2,
    Filter.Eventually.of_forall ?_⟩
  intro i
  have hsub : ∀ᵐ t ∂(νs i : Measure (X × X)), t ∈ Sᶜ → t ∈ (Q ×ˢ Q)ᶜ := by
    filter_upwards [hzero i] with t ht
    intro hbad hQpair
    exact hbad ⟨hQpair, ht⟩
  apply (measure_mono_ae hsub).trans
  rw [Set.compl_prod_eq_union]
  exact (measure_union_le _ _).trans
    (hδsmall Qᶜ hQ.isClosed.measurableSet.compl hμQ i)

theorem cappedDiagonal_eq_ratioDiagonal {X : Type*} (F : ℤ → X → ℝ)
    (hF : ∀ i x, 0 < F i x) (B : ℝ) (hB : 0 ≤ B) (t : X × X)
    (hcap : ∀ i, F i t.2 / F i t.1 ≤ B) :
    cappedDiagonal F hF B hB t = ratioDiagonal F t := by
  have hnorm : ∀ i, ‖((F i t.2 / F i t.1 : ℝ) : ℂ)‖ ≤ B := by
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hF i t.2).le (hF i t.1).le)] using hcap i
  unfold ratioDiagonal
  rw [SequenceHilbert.boundedDiagonal_eq _ B hB hnorm]
  apply SequenceHilbert.diagonal_congr
  intro i
  simp only [min_eq_right (hcap i)]

theorem compact_operator_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hfirst : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.snd))
    (B : ℝ) (hB : 0 < B)
    (hcapn : ∀ i k, ∀ᵐ t ∂(νs i : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hcap : ∀ k, ∀ᵐ t ∂(ν : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0 := by
  have hsmall := uniform_marginal_budget μ
    (fun i => (νs i : Measure (X × X))) hfirst hsecond
  have hbounded : ∀ x, ‖p x‖ ≤ (1 : ℝ) :=
    fun x => IsStarProjection.norm_le (p x) (hp x)
  have hzerocap : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB.le t).comp (p t.1)) = 0 := by
    intro i
    filter_upwards [ae_all_iff.mpr (hcapn i), hzero i] with t ht hz
    rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht]
  have hresult := capped_operator_relation_transfer μ p F hF hFm hpm
    1 zero_le_one hbounded B hB.le hν hsmall hzerocap
  filter_upwards [ae_all_iff.mpr hcap, hresult] with t ht hz
  rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht] at hz

end Invariant233.CompactTransfer

end

end OAI
