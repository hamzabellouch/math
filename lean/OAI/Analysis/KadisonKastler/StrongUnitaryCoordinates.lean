import OAI.Analysis.KadisonKastler.StrongContractionLimits
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Polish

namespace OAI

/-! # A closed Polish coordinate model of the unitary group

Both the operator and its adjoint are evaluated on a fixed dense sequence.
The range is closed: coordinate limits extend to contractions, and the
inverse and adjoint identities pass to strong limits.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryCoordinates (ξ : ℕ → H) (u : unitary (H →L[ℂ] H)) :
    (ℕ → H) × (ℕ → H) :=
  (fun n => (u : H →L[ℂ] H) (ξ n), fun n => (star u : H →L[ℂ] H) (ξ n))

theorem unitaryCoordinates_injective (ξ : ℕ → H) (hξ : DenseRange ξ) :
    Function.Injective (unitaryCoordinates ξ) := by
  intro u v h
  apply Subtype.ext
  apply DFunLike.coe_injective
  apply hξ.equalizer (u : H →L[ℂ] H).continuous (v : H →L[ℂ] H).continuous
  exact congrArg Prod.fst h

private theorem unitary_norm_le_one (u : unitary (H →L[ℂ] H)) :
    ‖(u : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [Unitary.norm_map, one_mul, le_refl]

theorem isClosed_range_unitaryCoordinates (ξ : ℕ → H) (hξ : DenseRange ξ) :
    IsClosed (Set.range (unitaryCoordinates ξ)) := by
  apply IsSeqClosed.isClosed
  intro z p hz hp
  choose u hu using hz
  have hleft (j : ℕ) :
      Tendsto (fun n => (u n : H →L[ℂ] H) (ξ j)) atTop (𝓝 (p.1 j)) := by
    have ht := tendsto_pi_nhds.mp ((continuous_fst.tendsto p).comp hp) j
    change Tendsto (fun n => (z n).1 j) atTop (𝓝 (p.1 j)) at ht
    convert ht using 1
    funext n
    exact congrFun (congrArg Prod.fst (hu n)) j
  have hright (j : ℕ) :
      Tendsto (fun n => (star (u n) : H →L[ℂ] H) (ξ j)) atTop (𝓝 (p.2 j)) := by
    have ht := tendsto_pi_nhds.mp ((continuous_snd.tendsto p).comp hp) j
    change Tendsto (fun n => (z n).2 j) atTop (𝓝 (p.2 j)) at ht
    convert ht using 1
    funext n
    exact congrFun (congrArg Prod.snd (hu n)) j
  obtain ⟨U, _, hlimU⟩ := exists_strong_limit_of_dense_contractions ξ hξ
    (fun n => (u n : H →L[ℂ] H)) (fun n => unitary_norm_le_one (u n))
    (fun j => (hleft j).cauchySeq)
  obtain ⟨V, _, hlimV⟩ := exists_strong_limit_of_dense_contractions ξ hξ
    (fun n => (star (u n) : H →L[ℂ] H)) (fun n => unitary_norm_le_one (star (u n)))
    (fun j => (hright j).cauchySeq)
  have hstar : star U = V := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℂ
    intro x
    have ht := (hlimV y).inner (𝕜 := ℂ)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
    have ht' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).inner
      (𝕜 := ℂ) (hlimU x)
    simp only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at ht ⊢
    exact (tendsto_nhds_unique ht ht').symm
  have hUV : U * V = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have ht := tendsto_mul_contractions
      (fun n => (u n : H →L[ℂ] H)) (fun n => (star (u n) : H →L[ℂ] H))
      U V (fun n => unitary_norm_le_one (u n)) hlimU hlimV x
    have hz : (fun n : ℕ => ((u n : H →L[ℂ] H) *
        (star (u n) : H →L[ℂ] H)) x) = fun _ => (1 : H →L[ℂ] H) x := by
      funext n
      exact congrArg (fun T : H →L[ℂ] H => T x) (u n).property.2
    change Tendsto (fun n => ((u n : H →L[ℂ] H) *
      (star (u n) : H →L[ℂ] H)) x) atTop (𝓝 ((U * V) x)) at ht
    rw [hz] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hVU : V * U = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have ht := tendsto_mul_contractions
      (fun n => (star (u n) : H →L[ℂ] H)) (fun n => (u n : H →L[ℂ] H))
      V U (fun n => unitary_norm_le_one (star (u n))) hlimV hlimU x
    simp only [Unitary.coe_star_mul_self] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let w : unitary (H →L[ℂ] H) := ⟨U, by rw [Unitary.mem_iff, hstar]; exact ⟨hVU, hUV⟩⟩
  refine ⟨w, ?_⟩
  apply Prod.ext
  · funext j
    exact tendsto_nhds_unique (hlimU (ξ j)) (hleft j)
  · funext j
    change star U (ξ j) = p.2 j
    rw [hstar]
    exact tendsto_nhds_unique (hlimV (ξ j)) (hright j)

/-- This is the strong-star coordinate model, not the operator-norm topology. -/
def StrongUnitarySpace (ξ : ℕ → H) := Set.range (unitaryCoordinates ξ)

instance (ξ : ℕ → H) : TopologicalSpace (StrongUnitarySpace ξ) :=
  inferInstanceAs (TopologicalSpace (Set.range (unitaryCoordinates ξ)))

instance (ξ : ℕ → H) : MetrizableSpace (StrongUnitarySpace ξ) :=
  inferInstanceAs (MetrizableSpace (Set.range (unitaryCoordinates ξ)))

theorem strongUnitarySpace_polish [SeparableSpace H] (ξ : ℕ → H) (hξ : DenseRange ξ) :
    PolishSpace (StrongUnitarySpace ξ) :=
  (isClosed_range_unitaryCoordinates ξ hξ).polishSpace

end

end KadisonKastler

end OAI
