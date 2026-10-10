import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-!
The unit-disk specialization of the classical crosscut separation theorem.
Published statement: M. D. Contreras and S. Díaz-Madrigal, *Fractional iteration
in the disk algebra: prime ends and composition operators*, Rev. Mat.
Iberoamericana 21 (2005), 911–928, §3, p. 918, first paragraph defining
crosscuts: the complement has two connected components and each component's
boundary inside the domain is the crosscut.
https://ems.press/content/serial-article-files/38137
-/

open Set Function

namespace CircleDomainRigidity

/-- Exactly two open connected components, with the stated relative frontier.
The endpoints belong to the circle and the open arc belongs to the disk. -/
def UnitDiskCrosscutSeparation : Prop :=
  ∀ p : C(PathTime, ℂ), Injective p → ‖p 0‖ = 1 → ‖p 1‖ = 1 →
    (∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) →
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Metric.ball 0 1 \ range p ∧
      frontier U ∩ Metric.ball 0 1 = range p ∩ Metric.ball 0 1 ∧
      frontier V ∩ Metric.ball 0 1 = range p ∩ Metric.ball 0 1

end CircleDomainRigidity

end OAI
