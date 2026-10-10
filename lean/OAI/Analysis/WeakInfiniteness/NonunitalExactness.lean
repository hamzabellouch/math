import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalHeredity
import OAI.Analysis.WeakInfiniteness.TensorIdealCut

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter Topology

universe algebraUniverse

variable {A B : Type algebraUniverse} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem exact_of_injective
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (K : ComplexHilbert.{algebraUniverse}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hψ : Function.Injective ψ) (hB : Exact B) : Exact A := by
  intro C D _ _ q hq z hz
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let I := kernelAlgebra q
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let l := CStarAlgebra.approximateUnit I
  have hl := CStarAlgebra.increasingApproximateUnit I
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  let e : I → C := Subtype.val
  have he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1 := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with i hi hn
    refine ⟨?_, hn⟩
    obtain ⟨x, hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i = star (e x) * e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  have hmem : (minimalMapLeft φ z).val ∈
      tensorKernelIdeal (A := B) q := by
    apply hB C D q hq
    intro π
    exact hz (π.precompLeft φ)
  have hcuts := tensorCutNonunital_tendsto_zero_on_ideal l e he q happ
    (minimalMapLeft φ z) hmem
  have hcutz : Tendsto (fun i => tensorCutNonunital (e i) z) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp hcuts
    convert hn using 1
    funext i
    rw [← minimalMapLeft_tensorCutNonunital]
    exact (norm_minimalMapLeft φ K ψ hφ hψ _).symm
  exact tensor_mem_ideal_of_nonunitalCuts l e q (fun i => i.property) z hcutz

end

end WeakPureInfiniteness
end

end OAI
