import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ScalarConductivity

end ScalarConductivity

namespace ScalarConductivity
open Filter Topology

theorem scalar_relation_strong_closed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {E F : V} {En Fn : ℕ → V} {sn : ℕ → ℝ}
    (hs : ∀ n, sn n ∈ Set.Icc a b)
    (hE : Tendsto En atTop (𝓝 E)) (hF : Tendsto Fn atTop (𝓝 F))
    (hres : Tendsto (fun n => Fn n - sn n • En n) atTop (𝓝 0)) :
    ∃ s ∈ Set.Icc a b, F = s • E := by
  obtain ⟨s, hs', φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc a b) hs
  have hsmem : s ∈ Set.Icc a b := by
    simpa only [isClosed_Icc.closure_eq] using hs'
  refine ⟨s, hsmem, ?_⟩
  have hlim' : Tendsto (fun n => Fn (φ n) - sn (φ n) • En (φ n))
      atTop (𝓝 (F - s • E)) :=
    (hF.comp hφ.tendsto_atTop).sub (hlim.smul (hE.comp hφ.tendsto_atTop))
  have hz : F - s • E = 0 :=
    tendsto_nhds_unique hlim' (hres.comp hφ.tendsto_atTop)
  exact sub_eq_zero.mp hz

end ScalarConductivity

namespace ScalarConductivity
open Filter Topology

def commonScalar {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : ℝ) (E F : V) : ℝ := by
  classical
  exact if E = 0 then a else inner ℝ E F / ‖E‖ ^ 2

theorem commonScalar_of_relation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a b s : ℝ} {E F : V}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (hF : F = s • E) :
    commonScalar a E F ∈ Set.Icc a b ∧ F = commonScalar a E F • E := by
  subst F
  by_cases hE : E = 0
  · simp [commonScalar, hE, hab]
  · have hn : ‖E‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hE)
    have hval : commonScalar a E (s • E) = s := by
      simp only [commonScalar, ite_eq_right hE, inner_smul_right, real_inner_self_eq_norm_sq]
      exact mul_div_cancel_right₀ s hn
    simpa only [hval, and_true] using hs

theorem measurable_commonScalar
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {E F : X → V} (a : ℝ)
    (hE : Measurable E) (hF : Measurable F) :
    Measurable (fun x => commonScalar a (E x) (F x)) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun hE measurable_const) measurable_const
    ((hE.inner hF).div (hE.norm.pow_const 2))

theorem scalar_relation_ae_strong_closed
    {X V : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b) {E F : X → V}
    (hEm : Measurable E) (hFm : Measurable F)
    {En Fn : ℕ → X → V} {sn : ℕ → X → ℝ}
    (hs : ∀ n, ∀ᵐ x ∂μ, sn n x ∈ Set.Icc a b)
    (hE : ∀ᵐ x ∂μ, Tendsto (fun n => En n x) atTop (𝓝 (E x)))
    (hF : ∀ᵐ x ∂μ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (hres : ∀ᵐ x ∂μ,
      Tendsto (fun n => Fn n x - sn n x • En n x) atTop (𝓝 0)) :
    ∃ s : X → ℝ, Measurable s ∧
      (∀ᵐ x ∂μ, s x ∈ Set.Icc a b ∧ F x = s x • E x) := by
  refine ⟨fun x => commonScalar a (E x) (F x),
    measurable_commonScalar a hEm hFm, ?_⟩
  filter_upwards [ae_all_iff.mpr hs, hE, hF, hres] with x hsx hEx hFx hrx
  obtain ⟨s, hs', hrel⟩ := scalar_relation_strong_closed hsx hEx hFx hrx
  exact commonScalar_of_relation hab hs' hrel

end ScalarConductivity

end
end

end OAI
