import Mathlib
import OAI.Analysis.Commutator.BaireSmallPiece
import OAI.Analysis.Commutator.MinimalOrbit

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.CompactInvariant

variable {G X E : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [MetricSpace E] [CompleteSpace E]

theorem minimal_norm_compact (j : X ≃ E) (hj : Continuous j.symm)
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y≤r})
    (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
    {C K : Set X} (hcomp : IsCompact K)
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    (hsep : IsSeparable (j '' K)) : IsCompact (j '' K) := by
  classical
  have hclosed : IsClosed (j '' K) := by
    have he : j '' K=j.symm ⁻¹' K := by
      ext y
      simp only [mem_image,mem_preimage]
      constructor
      · rintro ⟨x,hx,rfl⟩; simpa only [j.symm_apply_apply] using hx
      · intro hy; exact ⟨j.symm y,hy,j.apply_symm_apply y⟩
    rw [he]
    exact hK.prop.2.2.1.preimage hj
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_,hclosed.isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨U,hU,hUn,hd⟩ := BaireSmallPiece.exists_open_piece j hcomp hK.prop.2.1 hsep hball ε hε
  obtain ⟨u,huK,huU⟩ := hUn
  obtain ⟨t,ht⟩ := minimal_finite_open_cover hcomp hK hU ⟨u,huK,huU⟩
  let T : Set E := (fun g : G => j (g⁻¹ • u)) '' (t : Set G)
  refine ⟨T,t.finite_toSet.image _,?_⟩
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨g,hg,hgx⟩ := mem_iUnion₂.mp (ht hx)
  refine mem_iUnion₂.mpr ⟨j (g⁻¹ • u),⟨g,hg,rfl⟩,?_⟩
  change dist (j x) (j (g⁻¹ • u))<ε
  rw [←hiso g x (g⁻¹ • u)]
  simp only [smul_inv_smul]
  exact hd (g • x) ⟨hK.prop.2.2.2 g x hx,hgx⟩ u ⟨huK,huU⟩

end Kadison.CompactInvariant

end

end
end

end OAI
