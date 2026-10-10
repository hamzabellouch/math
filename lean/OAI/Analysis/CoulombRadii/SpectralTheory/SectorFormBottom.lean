import Mathlib
import OAI.Analysis.CoulombRadii.Packets.CoreScreenedFieldPacketIntegral
import OAI.Analysis.CoulombRadii.Packets.PacketDensityReal
import OAI.Analysis.CoulombRadii.FieldAnalysis.NearCoulombFiveHalves

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def sectorFormBottom {M : ℕ} (S : Nuclei M) (n : ℕ) : EReal :=
  sInf {e : EReal | ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧ e = (form S ψ : EReal)}

def unrestrictedFormBottom {M : ℕ} (S : Nuclei M) : EReal := ⨅ n, sectorFormBottom S n

lemma unrestrictedFormBottom_le_trial {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    (ha : Antisymmetric ψ) (hm : mass ψ = 1) : unrestrictedFormBottom S ≤ (form S ψ : EReal) :=
  (iInf_le _ n).trans (sInf_le ⟨ψ,ha,hm,rfl⟩)

theorem radial_packet_core_trial {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) + ε := by
  have hi := compact_density_integrable ρ hp hm ht K hK hs
  obtain ⟨n,ψ,ha,hmass,he⟩ := packet_core_trial S u hu hmu g hg hgc ρ hp hm hi ht
    K A hK hA hs hsu hsep ε hε
  have hD := radial_packetDensity_pair_le g hg hrad ρ hp hm hi
    (density_coulomb_pair_integrable ρ hp hm hi ht)
  exact ⟨n,ψ,ha,hmass,by linarith⟩

theorem trial_in_hole {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ))) :
    unrestrictedFormBottom S ≤ ((form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) : ℝ) : EReal) := by
  let B : ℝ := form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2))
  change unrestrictedFormBottom S ≤ (B:EReal)
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hpz : 0 < z-B := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hz)
  obtain ⟨n,ψ,ha,hmass,he⟩ := radial_packet_core_trial S u hu hmu g hg hgc hrad ρ hp hm ht
    K A hK hA hs hsu hsep (z-B) hpz
  have hel : form S ψ ≤ z := by change form S ψ ≤ B+(z-B) at he; linarith
  exact (unrestrictedFormBottom_le_trial S ψ ha hmass).trans (EReal.coe_le_coe hel)

lemma vacuum_trial_in_hole {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1) : unrestrictedFormBottom S ≤ (form S u : EReal) :=
  unrestrictedFormBottom_le_trial S u hu hmu
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
