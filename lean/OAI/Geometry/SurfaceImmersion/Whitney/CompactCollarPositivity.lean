import Mathlib

namespace OAI

/-! Strict inequalities on a compact curve set propagate to a collar,
uniformly in a compact angular parameter. -/
noncomputable section
open Set
open scoped Topology

namespace ClosedSurfaceR4.CollarVelocity

variable {E A : Type*} [TopologicalSpace E] [T2Space E]
  [TopologicalSpace A]

theorem compact_collar_positive {K C Ω : Set E} {J : Set A}
    (hK : IsCompact K) (hC : IsClosed C) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hJ : IsCompact J) {F : E × A → ℝ} (hF : ContinuousOn F (Ω ×ˢ univ))
    (hpos : ∀ x ∈ K ∩ C, ∀ t ∈ J, 0 < F (x, t)) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧
      ∀ x ∈ K ∩ W, ∀ t ∈ J, 0 < F (x, t) := by
  let O : Set (E × A) := (Ω ×ˢ univ) ∩ F ⁻¹' Ioi 0
  have hO : IsOpen O := hF.isOpen_inter_preimage (hΩ.prod isOpen_univ) isOpen_Ioi
  have hKC : IsCompact (K ∩ C) := hK.inter_right hC
  have hsub : (K ∩ C) ×ˢ J ⊆ O := by
    intro z hz
    exact ⟨⟨hKΩ hz.1.1, mem_univ _⟩, hpos z.1 hz.1 z.2 hz.2⟩
  obtain ⟨N, V, hN, _, hKN, hJV, hNV⟩ := generalized_tube_lemma hKC hJ hO hsub
  let W := (K \ N)ᶜ
  have hW : IsOpen W := (hK.isClosed.sdiff hN).isOpen_compl
  refine ⟨W, hW, ?_, ?_⟩
  · intro x hx hbad
    exact hbad.2 (hKN ⟨hbad.1, hx⟩)
  · intro x hx t ht
    have hxN : x ∈ N := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    exact (hNV ⟨hxN, hJV ht⟩).2

/-- The collar and allowed translation size are chosen before the eventual
angle translation function or its derivatives. -/
theorem compact_collar_positive_small_shift {K C Ω : Set E} {J : Set A}
    (hK : IsCompact K) (hC : IsClosed C) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hJ : IsCompact J) {F : E × (A × ℝ) → ℝ}
    (hF : ContinuousOn F (Ω ×ˢ univ))
    (hpos : ∀ x ∈ K ∩ C, ∀ t ∈ J, 0 < F (x, (t, 0))) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ t ∈ J, ∀ h : ℝ, |h| < ε → 0 < F (x, (t, h)) := by
  let O : Set (E × (A × ℝ)) := (Ω ×ˢ univ) ∩ F ⁻¹' Ioi 0
  have hO : IsOpen O := hF.isOpen_inter_preimage (hΩ.prod isOpen_univ) isOpen_Ioi
  have hKC : IsCompact (K ∩ C) := hK.inter_right hC
  have hsub : (K ∩ C) ×ˢ (J ×ˢ ({0} : Set ℝ)) ⊆ O := by
    intro z hz
    have h0 : z.2.2 = 0 := hz.2.2
    refine ⟨⟨hKΩ hz.1.1, mem_univ _⟩, ?_⟩
    rw [show z = (z.1, (z.2.1, 0)) from Prod.ext rfl (Prod.ext rfl h0)]
    exact hpos z.1 hz.1 z.2.1 hz.2.1
  obtain ⟨N, V, hN, hV, hKN, hJV, hNV⟩ :=
    generalized_tube_lemma hKC (hJ.prod isCompact_singleton) hO hsub
  obtain ⟨A₀, I, _, hI, hJA, h0I, hAI⟩ :=
    generalized_tube_lemma hJ isCompact_singleton hV hJV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hI 0 (h0I (mem_singleton 0))
  let W := (K \ N)ᶜ
  refine ⟨W, (hK.isClosed.sdiff hN).isOpen_compl, ?_, ε, hε, ?_⟩
  · intro x hx hbad
    exact hbad.2 (hKN ⟨hbad.1, hx⟩)
  · intro x hx t ht h hh
    have hxN : x ∈ N := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    have hhI : h ∈ I := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hh)
    exact (hNV ⟨hxN, hAI ⟨hJA ht, hhI⟩⟩).2

end ClosedSurfaceR4.CollarVelocity

end

end OAI
