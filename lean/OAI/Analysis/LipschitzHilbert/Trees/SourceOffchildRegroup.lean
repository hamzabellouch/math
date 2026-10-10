import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketRegroup

namespace OAI

/-! Removing a child top before grouping packets gives exactly the
removed-child top-band family. The masses and transition coefficients
continue to use the original full top collection. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sourcePacketAmplitude_regroup_offchild {N : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) (child : Finset ι) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (packets.filter (fun q => assigned q ∉ child)) assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter (fun p => p.1 ∉ child))
      Prod.fst (fun p => stop p.1 p.2)
      (fun p => ∑ q ∈ packets.filter (fun q => (assigned q,lengthIndex q) = p), value q)
      phase a x level cell := by
  rw [g.sourcePacketAmplitude_regroup tops slope precision cutoff weight K gap
    (packets.filter (fun q => assigned q ∉ child)) assigned
    (fun q hq => hassigned q (Finset.mem_filter.mp hq).1) lengthIndex stop value
    phase a x level cell]
  rw [g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst Prod.snd stop]
  rw [g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap
    ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter (fun p => p.1 ∉ child))
    Prod.fst Prod.snd stop]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1 ∈ child
  · have hempty : ((packets.filter (fun q => assigned q ∉ child)).filter
        (fun q => (assigned q,lengthIndex q) = p)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨hq,hkey⟩ := Finset.mem_filter.mp hq
      have heq : assigned q = p.1 := congrArg Prod.fst hkey
      exact (Finset.mem_filter.mp hq).2 (heq.symm ▸ hp)
    simp only [hempty,Finset.sum_empty,smul_zero,hp,not_true_eq_false,ite_false]
  · have hfilter : ((packets.filter (fun q => assigned q ∉ child)).filter
        (fun q => (assigned q,lengthIndex q) = p)) =
        packets.filter (fun q => (assigned q,lengthIndex q) = p) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hq,_⟩,heq⟩
        exact ⟨hq,heq⟩
      · rintro ⟨hq,heq⟩
        refine ⟨⟨hq,?_⟩,heq⟩
        have heq' : assigned q = p.1 := congrArg Prod.fst heq
        rw [heq']
        exact hp
    simp only [hfilter,hp,not_false_eq_true,ite_true]

end LipschitzHilbert.AngularGrid

end

end OAI
