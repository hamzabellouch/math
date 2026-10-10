import OAI.Geometry.SurfaceImmersion.Whitney.CompactCollarPositivity

namespace OAI

/-! Uniform collar positivity for the normal invariant used by later curves. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalInvariant (D S : E × ℝ → ℝ) (b c k : E → ℝ) (z : E × ℝ) : ℝ :=
  (D z * b z.1 + S z * c z.1) ^ 2 + k z.1 * b z.1 ^ 2

lemma normalInvariant_smoothOn {D S : E × ℝ → ℝ} {b c k : E → ℝ} {Ω : Set E}
    (hD : ContDiffOn ℝ ∞ D (Ω ×ˢ univ)) (hS : ContDiffOn ℝ ∞ S (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω) :
    ContDiffOn ℝ ∞ (normalInvariant D S b c k) (Ω ×ˢ univ) := by
  have hbf : ContDiffOn ℝ ∞ (fun z : E × ℝ => b z.1) (Ω ×ˢ univ) :=
    hb.comp contDiffOn_fst (fun z hz => hz.1)
  have hcf : ContDiffOn ℝ ∞ (fun z : E × ℝ => c z.1) (Ω ×ˢ univ) :=
    hc.comp contDiffOn_fst (fun z hz => hz.1)
  have hkf : ContDiffOn ℝ ∞ (fun z : E × ℝ => k z.1) (Ω ×ˢ univ) :=
    hk.comp contDiffOn_fst (fun z hz => hz.1)
  exact (((hD.mul hbf).add (hS.mul hcf)).pow 2).add (hkf.mul (hbf.pow 2))

theorem boundary_invariant_collar {K C Ω : Set E} {J : Set ℝ}
    (hK : IsCompact K) (hC : IsClosed C) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hJ : IsCompact J) {D S β : E × ℝ → ℝ} {b c k : E → ℝ}
    (hD : ContDiffOn ℝ ∞ D (Ω ×ˢ univ)) (hS : ContDiffOn ℝ ∞ S (Ω ×ˢ univ))
    (hβ : ContDiffOn ℝ ∞ β (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω)
    (hzero : ∀ x ∈ K ∩ C, ∀ t ∈ J, β (x, t) = 0)
    (hboundary : ∀ x ∈ K ∩ C, 0 < normalInvariant D S b c k (x, 0)) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ t ∈ J, ∀ h : ℝ, |h| < ε →
        0 < normalInvariant D S b c k (x, β (x, t) + h) := by
  let A : Set (E × (ℝ × ℝ)) := Ω ×ˢ univ
  have hp : ContDiffOn ℝ ∞ (fun z : E × (ℝ × ℝ) => (z.1, z.2.1)) A :=
    contDiffOn_fst.prodMk (contDiffOn_fst.comp contDiffOn_snd (fun _ _ => mem_univ _))
  have hb' : ContDiffOn ℝ ∞ (fun z : E × (ℝ × ℝ) => β (z.1, z.2.1)) A :=
    hβ.comp hp (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hh : ContDiffOn ℝ ∞ (fun z : E × (ℝ × ℝ) => z.2.2) A :=
    contDiffOn_snd.comp contDiffOn_snd (fun _ _ => mem_univ _)
  have hshift : ContDiffOn ℝ ∞
      (fun z : E × (ℝ × ℝ) => (z.1, β (z.1, z.2.1) + z.2.2)) A :=
    contDiffOn_fst.prodMk (hb'.add hh)
  have hF : ContDiffOn ℝ ∞
      (fun z : E × (ℝ × ℝ) => normalInvariant D S b c k
        (z.1, β (z.1, z.2.1) + z.2.2)) A :=
    (normalInvariant_smoothOn hD hS hb hc hk).comp hshift
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  apply compact_collar_positive_small_shift hK hC hΩ hKΩ hJ hF.continuousOn
  intro x hx t ht
  simpa only [hzero x hx t ht, add_zero] using hboundary x hx

end ClosedSurfaceR4.CollarVelocity

end

end OAI
