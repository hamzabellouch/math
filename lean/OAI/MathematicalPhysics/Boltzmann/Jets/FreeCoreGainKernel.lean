import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Jets.JetEnvelopeTimeIntegral
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

/-! # The actual free cold core supplies a normalized positive gain kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def coreKernel (η K α γ s d : ℝ) (a : Bool) : Kernel (ℝ × JetPrototype.Space) Velocity :=
  (Kernel.const _ (volume : Measure Velocity)).withDensity
    (fun p v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d p.1 a (p.2,v)))

instance coreKernel_sFinite (η K α γ s d : ℝ) (a : Bool) :
    IsSFiniteKernel (coreKernel η K α γ s d a) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem coreKernel_apply (η K α γ s d : ℝ) (a : Bool) (p : ℝ × JetPrototype.Space) :
    coreKernel η K α γ s d a p = volume.withDensity
      (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d p.1 a (p.2,v))) :=
  Kernel.withDensity_apply _
    (JetFreeTransport.measurable_uncurried_free η K α γ s d a).ennreal_ofReal p

def normalizedCoreKernel (η K α γ s d q : ℝ) (a : Bool) :
    Kernel ((ℝ × JetPrototype.Space) × Velocity) Velocity :=
  ChartKernel.inputKernel (coreKernel η K α γ s d a) q

instance normalizedCoreKernel_sFinite (η K α γ s d q : ℝ) (a : Bool) :
    IsSFiniteKernel (normalizedCoreKernel η K α γ s d q a) :=
  ChartKernel.inputKernel_sFinite _ _

theorem normalizedCoreKernel_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 ≤ t)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedCoreKernel η K α γ s d q a ((t,x),v) univ ≤
      ENNReal.ofReal (amplitude K α γ s t)*
        SheetTotal.bound q (2*Real.exp (16*(|JetPrototype.sign a|+α)^2)) := by
  rw [normalizedCoreKernel,ChartKernel.inputKernel_mass,coreKernel_apply]
  exact normalized_gain_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a x hv

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
