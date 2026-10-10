import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinaryModelConfig
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Zero-energy input functions have zero literal analyzing coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem input_ae_zero_of_energy_zero {V : Type*} [NormedAddCommGroup V]
    (g : ℝ×ℝ → V) (hg : MemLp g 2 (volume.prod volume))
    (hzero : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0) :
    g=ᵐ[volume.prod volume] 0 := by
  have hsq : (fun z => ‖g z‖^2)=ᵐ[volume.prod volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖g z‖)
      (hg.integrable_norm_pow (by norm_num : (2:ℕ)≠0))).mp hzero
  filter_upwards [hsq] with z hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinaryCoefficient_zero_of_energy_zero (P : SourceLabeledLattice N κ Label Item)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume))
    (hzero : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0)
    (j : Fin N) (l : P.labels j) (a : Item j l) : P.ordinaryCoefficient g j l a=0 := by
  have h := input_ae_zero_of_energy_zero g hg hzero
  apply WithLp.ofLp_injective
  funext k
  have hi : (∫ z, g z k*conj (P.physicalPacket 0 j l a k z) ∂volume.prod volume)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h] with z hz
    simp only [hz,Pi.zero_apply,WithLp.ofLp_zero,zero_mul]
  simp only [ordinaryCoefficient,analyzingCoefficient,WithLp.ofLp_toLp,WithLp.ofLp_zero,
    Pi.zero_apply,hi,mul_zero]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
