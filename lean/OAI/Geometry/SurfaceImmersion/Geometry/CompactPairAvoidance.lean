import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairDerivative

namespace OAI

/-! Absence of coincidences on a compact pair set persists under small
translations with a bounded scalar cutoff. -/
noncomputable section
open Set Filter Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]

theorem compact_pair_avoidance_stability {f : M → ProjectionTarget 3} (hf : Continuous f)
    (χ : M → ℝ) (hχ : ∀ x, χ x ∈ Icc 0 1)
    {K : Set (M × M)} (hK : IsCompact K) (havoid : ∀ z ∈ K, f z.1 ≠ f z.2) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      surfaceTranslation f χ a z.1 ≠ surfaceTranslation f χ a z.2 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1,by norm_num,by simp⟩
  have hc : Continuous (fun z : M × M => ‖f z.1-f z.2‖) :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  have hpos : 0 < ‖f z.1-f z.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (havoid z hz))
  refine ⟨_,hpos,?_⟩
  intro a ha w hw heq
  change f w.1+χ w.1 • a = f w.2+χ w.2 • a at heq
  have hd : f w.1-f w.2 = (χ w.2-χ w.1) • a := by
    calc
      f w.1-f w.2 = (f w.1+χ w.1 • a)-(f w.2+χ w.1 • a) := by abel
      _ = (f w.2+χ w.2 • a)-(f w.2+χ w.1 • a) := by rw [heq]
      _ = (χ w.2-χ w.1) • a := by module
  have hb : |χ w.2-χ w.1| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ w.1).2,(hχ w.2).1],
    by linarith [(hχ w.1).1,(hχ w.2).2]⟩
  have hnorm : ‖f w.1-f w.2‖ ≤ ‖a‖ := by
    rw [hd,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg a)).trans_eq (one_mul _)
  exact (not_lt_of_ge (hmin hw)) (hnorm.trans_lt ha)

variable [T2Space M]
theorem compact_finite_pair_avoidance_stability {f : M → ProjectionTarget 3} (hf : Continuous f)
    (χ : M → ℝ) (hχ : ∀ x, χ x ∈ Icc 0 1)
    {K : Set (M × M)} (hK : IsCompact K) {S : Set M} (hS : S.Finite)
    (havoid : ∀ z ∈ K, z.1 ∈ S ∨ z.2 ∈ S → f z.1 ≠ f z.2) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      z.1 ∈ S ∨ z.2 ∈ S → surfaceTranslation f χ a z.1 ≠ surfaceTranslation f χ a z.2 := by
  have hclosed : IsClosed {z : M × M | z.1 ∈ S ∨ z.2 ∈ S} :=
    (hS.isClosed.preimage continuous_fst).union (hS.isClosed.preimage continuous_snd)
  obtain ⟨δ,hδ,hstable⟩ := compact_pair_avoidance_stability hf χ hχ
    (hK.inter_right hclosed) (fun z hz => havoid z hz.1 hz.2)
  exact ⟨δ,hδ,fun a ha z hz hS => hstable a ha z ⟨hz,hS⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
