import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.GlobalRellich
import OAI.Geometry.PrescribedPotential.HigherMetricOperator
import OAI.Geometry.PrescribedPotential.HigherResolvent
import OAI.Geometry.PrescribedPotential.QuantitativeResolvent

namespace OAI

/-! Even Rellich. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def shiftedOrder (m : ℝ) (k : ℕ) :
    D.localizers.Sobolev ((k : ℝ)+2) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  (m^2 : ℝ) • D.localizers.lower ((k : ℝ)+2) (k : ℝ) - D.completedLOrder k

lemma shiftedOrder_embed (m : ℝ) (k : ℕ) (f : Smooth A) :
    D.shiftedOrder m k (D.localizers.embed ((k : ℝ)+2) f) =
      D.localizers.embed (k : ℝ) ((m^2 : ℝ) • f - complexL g f) := by
  simp only [shiftedOrder,sub_apply,smul_apply,
    D.localizers.lower_embed (by linarith : (k : ℝ) ≤ (k : ℝ)+2),
    D.completedLOrder_embed, map_sub, map_smul]

lemma shiftedOrder_lower (m : ℝ) (k : ℕ) (u : D.localizers.Sobolev ((k : ℝ)+2)) :
    D.localizers.lower (k : ℝ) 0 (D.shiftedOrder m k u) =
      D.shiftedOperator m (D.localizers.lower ((k : ℝ)+2) 2 u) := by
  simp only [shiftedOrder,shiftedOperator,sub_apply,
    smul_apply,map_sub,map_smul,D.completedLOrder_lower]
  rw [D.localizers.lower_lower (by linarith : (k : ℝ) ≤ (k : ℝ)+2) (Nat.cast_nonneg k),
    D.localizers.lower_lower (by linarith [Nat.cast_nonneg (α := ℝ) k] :
      (2 : ℝ) ≤ (k : ℝ)+2) (by norm_num : (0 : ℝ) ≤ 2)]

lemma resolventOrder_left (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (k : ℕ) (R : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+2))
    (hR : ∀ f, D.localizers.lower ((k : ℝ)+2) 2 (R f) =
      D.completedResolvent m hm he (D.localizers.lower (k : ℝ) 0 f))
    (u : D.localizers.Sobolev ((k : ℝ)+2)) : R (D.shiftedOrder m k u) = u := by
  apply D.localizers.lower_injective (by linarith [Nat.cast_nonneg (α := ℝ) k] :
    (2 : ℝ) ≤ (k : ℝ)+2)
  rw [hR,D.shiftedOrder_lower,D.completedResolvent_left]

lemma lower_resolvent_factor (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (k j : ℕ) (hjk : (j : ℝ) = (k : ℝ)+2)
    (R : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+2))
    (hR : ∀ f, D.localizers.lower ((k : ℝ)+2) 2 (R f) =
      D.completedResolvent m hm he (D.localizers.lower (k : ℝ) 0 f)) :
    D.localizers.lower ((j : ℝ)+2) (j : ℝ) =
      (D.localizers.lower ((k : ℝ)+2) (j : ℝ) ∘L R) ∘L
        D.localizers.lower ((k : ℝ)+2) (k : ℝ) ∘L
        (D.localizers.lower (j : ℝ) ((k : ℝ)+2) ∘L D.shiftedOrder m j) := by
  apply DFunLike.coe_injective
  apply (D.localizers.embed_dense ((j : ℝ)+2)).equalizer (by fun_prop) (by fun_prop)
  funext f
  simp only [ContinuousLinearMap.coe_comp,Function.comp_apply,D.shiftedOrder_embed,
    D.localizers.lower_embed (by linarith only [hjk] : (j : ℝ) ≤ (j : ℝ)+2),
    D.localizers.lower_embed (by linarith only [hjk] : (k : ℝ)+2 ≤ (j : ℝ)),
    D.localizers.lower_embed (by linarith : (k : ℝ) ≤ (k : ℝ)+2)]
  rw [← D.shiftedOrder_embed m k,D.resolventOrder_left m hm he k R hR]
  exact (D.localizers.lower_embed (by linarith only [hjk] : (j : ℝ) ≤ (k : ℝ)+2) f).symm

lemma lower_compact_step (k j : ℕ) (hjk : (j : ℝ) = (k : ℝ)+2)
    (hK : IsCompactOperator (D.localizers.lower ((k : ℝ)+2) (k : ℝ))) :
    IsCompactOperator (D.localizers.lower ((j : ℝ)+2) (j : ℝ)) := by
  obtain ⟨m,hm,he⟩ := D.exists_completedError_small
  obtain ⟨R,hR⟩ := D.completedResolvent_order m hm he k
  rw [D.lower_resolvent_factor m hm he k j hjk R hR]
  exact (hK.comp_clm (D.localizers.lower (j : ℝ) ((k : ℝ)+2) ∘L D.shiftedOrder m j)).clm_comp
    (D.localizers.lower ((k : ℝ)+2) (j : ℝ) ∘L R)

 

def CompactLower (s t : ℝ) : Prop := IsCompactOperator (D.localizers.lower s t)

 
theorem lower_even_compact (n : ℕ) :
    IsCompactOperator (D.localizers.lower (((2*n : ℕ) : ℝ)+2) ((2*n : ℕ) : ℝ)) := by
  change D.CompactLower (((2*n : ℕ) : ℝ)+2) ((2*n : ℕ) : ℝ)
  induction n with
  | zero =>
    simp only [mul_zero,Nat.cast_zero,zero_add]
    exact D.lower_compact
  | succ n ih =>
    exact D.lower_compact_step (2*n) (2*(n+1)) (by push_cast; ring) ih

end GluingData
end GlobalElliptic

end
end

end OAI
