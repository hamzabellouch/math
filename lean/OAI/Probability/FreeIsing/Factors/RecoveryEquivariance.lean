import Mathlib

namespace OAI

open MeasureTheory

namespace Problem367

variable {W X G : Type*} [MeasurableSpace W] [MeasurableSpace X]

theorem ae_equivariant_of_joint_recovery [MeasurableEq X]
    {η : Measure (W × X)} {μ : Measure W}
    {T : W → W} {S : X → X} {F : W → X}
    (hμ : Measure.map Prod.fst η = μ)
    (hT : Measurable T) (hS : Measurable S) (hF : Measurable F)
    (hjoint : Measure.QuasiMeasurePreserving
      (fun p : W × X => (T p.1, S p.2)) η η)
    (hrecover : ∀ᵐ p ∂η, p.2 = F p.1) :
    ∀ᵐ w ∂μ, F (T w) = S (F w) := by
  rw [← hμ]
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_eq_fun (hF.comp hT) (hS.comp hF))).2
  have htrans := hjoint.ae hrecover
  filter_upwards [hrecover, htrans] with p hp hTp
  exact hTp.symm.trans (congrArg S hp)

theorem ae_equivariant_family_of_joint_recovery [MeasurableEq X]
    {η : Measure (W × X)} {μ : Measure W}
    {T : G → W → W} {S : G → X → X} {F : W → X}
    (hμ : Measure.map Prod.fst η = μ)
    (hT : ∀ g, Measurable (T g)) (hS : ∀ g, Measurable (S g))
    (hF : Measurable F)
    (hjoint : ∀ g, Measure.QuasiMeasurePreserving
      (fun p : W × X => (T g p.1, S g p.2)) η η)
    (hrecover : ∀ᵐ p ∂η, p.2 = F p.1) :
    ∀ g, ∀ᵐ w ∂μ, F (T g w) = S g (F w) :=
  fun g => ae_equivariant_of_joint_recovery hμ (hT g) (hS g) hF
    (hjoint g) hrecover

theorem map_eq_second_marginal_of_joint_recovery
    {η : Measure (W × X)} {μ : Measure W} {F : W → X}
    (hμ : Measure.map Prod.fst η = μ) (hF : Measurable F)
    (hrecover : ∀ᵐ p ∂η, p.2 = F p.1) :
    Measure.map F μ = Measure.map Prod.snd η := by
  rw [← hμ, Measure.map_map hF measurable_fst]
  apply Measure.map_congr
  filter_upwards [hrecover] with p hp
  exact hp.symm

end Problem367

end OAI
