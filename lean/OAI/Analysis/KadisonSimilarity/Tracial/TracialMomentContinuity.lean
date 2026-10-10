import OAI.Analysis.BoundedHochschild.AlternatingMoments

namespace OAI

/-! Continuity of the mixed moments on operator-norm bounded sets. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild HochschildPatching HochschildUltrapower Filter Topology
open scoped ComplexOrder

variable {B I J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

lemma gnsTendsto_smul {f : J → B} {l : Filter J} {b : B}
    (h : GNSTendsto τ f l b) (c : ℂ) :
    GNSTendsto τ (fun j => c • f j) l (c • b) := by
  have ht := h.const_mul ‖c‖
  simpa only [GNSTendsto, ← smul_sub, map_smul, norm_smul, mul_zero] using ht

include h1 in
lemma gnsTendsto_centered {f : J → B} {l : Filter J} {b : B}
    (h : GNSTendsto τ f l b) :
    GNSTendsto τ (fun j => f j - τ (f j) • 1) l (b - τ b • 1) := by
  have ht := trace_tendsto_of_gns τ h1 h
  have hs : GNSTendsto τ (fun j => τ (f j) • 1) l (τ b • 1) := by
    have hh := ((ht.sub_const (τ b)).norm).mul_const ‖τ.toPreGNS 1‖
    simpa only [GNSTendsto, ← sub_smul, map_smul, norm_smul, sub_self,
      norm_zero, zero_mul] using hh
  exact h.sub τ hs

omit [PartialOrder B] [StarOrderedRing B] in
lemma wordCoeff_norm_le_bound (F : I → B) {C : ℝ} (hC : 1 ≤ C)
    (hF : ∀ i, ‖F i‖ ≤ C) (a : Option I) : ‖wordCoeff F a‖ ≤ C := by
  cases a with
  | none => exact (IsStarProjection.norm_le (1 : B) (IsStarProjection.one B)).trans hC
  | some i => exact hF i

lemma gnsTendsto_wordCoeff {F : J → I → B} {G : I → B} {l : Filter J}
    (h : ∀ i, GNSTendsto τ (fun j => F j i) l (G i)) (a : Option I) :
    GNSTendsto τ (fun j => wordCoeff (F j) a) l (wordCoeff G a) := by
  cases a with
  | none => exact GNSTendsto.const τ 1 l
  | some i => exact h i

include tr in
lemma gnsTendsto_integerEval {F : J → I → B} {G : I → B} {l : Filter J}
    (h : ∀ i, GNSTendsto τ (fun j => F j i) l (G i))
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ j i, ‖F j i‖ ≤ C)
    (u : unitary B) (a : Option I) (w : List (IntAtom I)) :
    GNSTendsto τ (fun j => integerEval (F j) u a w) l (integerEval G u a w) := by
  have hprod : ∀ v : List (IntAtom I), GNSTendsto τ
      (fun j => (v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff (F j) b.2)).prod) l
      ((v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff G b.2)).prod) := by
    intro v
    induction v with
    | nil => exact GNSTendsto.const τ 1 l
    | cons b v ih =>
      have hb := (GNSTendsto.const τ ((u ^ b.1 : unitary B) : B) l).mul τ tr
        (gnsTendsto_wordCoeff τ h b.2) ‖((u ^ b.1 : unitary B) : B)‖ (fun _ => le_rfl)
      have hn (j) : ‖((u ^ b.1 : unitary B) : B) * wordCoeff (F j) b.2‖ ≤ C := by
        rw [CStarRing.norm_coe_unitary_mul]
        exact wordCoeff_norm_le_bound _ hC (hF j) _
      exact hb.mul τ tr ih C hn
  exact (gnsTendsto_wordCoeff τ h a).mul τ tr (hprod w) C
    (fun j => wordCoeff_norm_le_bound _ hC (hF j) a)

include h1 tr in
/-- Vanishing moments persist when each coefficient is approximated in trace norm
with a common operator-norm bound. -/
theorem integer_moment_zero_of_bounded_limits
    {F : ℕ → I → B} {G : I → B}
    (h : ∀ i, GNSTendsto τ (fun j => F j i) atTop (G i))
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ j i, ‖F j i‖ ≤ C)
    (u : unitary B) (a : Option I) (w : List (IntAtom I))
    (hz : ∀ j, τ (integerEval (F j) u a w) = 0) :
    τ (integerEval G u a w) = 0 := by
  have ht := trace_tendsto_of_gns τ h1 (gnsTendsto_integerEval τ tr h hC hF u a w)
  have hh : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (τ (integerEval G u a w))) := by
    simpa only [hz] using ht
  exact tendsto_nhds_unique hh tendsto_const_nhds

end KadisonSimilarity

end

end OAI
