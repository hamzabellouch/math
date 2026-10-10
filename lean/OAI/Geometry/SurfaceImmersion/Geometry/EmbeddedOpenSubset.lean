import OAI.Geometry.SurfaceImmersion.Whitney.CompactCurveArc

namespace OAI

/-! Open subarcs remain open in the ambient curve. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem embedded_open_subset {f : X → Y} (hf : IsEmbedding f)
    {U S : Set X} (hU : IsOpen (f '' U)) (hS : IsOpen S) (hSU : S ⊆ U) :
    IsOpen (f '' S) := by
  obtain ⟨V,hV,hVS⟩ := hf.isInducing.isOpen_iff.mp hS
  have heq : f '' S = (f '' U) ∩ V := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hSU hx,rfl⟩,by rw [← hVS] at hx; exact hx⟩
    · rintro ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,by rw [← hVS]; exact hy,rfl⟩
  rw [heq]
  exact hU.inter hV

variable {Z : Type*} [TopologicalSpace Z]

def CompactCurveArc.openSubarc (A : CompactCurveArc Z) (u v : ℝ) : Set Z :=
  A.map '' {t | u < (t:ℝ) ∧ (t:ℝ) < v}

def CompactCurveArc.closedSubarc (A : CompactCurveArc Z) (u v : ℝ) : Set Z :=
  A.map '' {t | u ≤ (t:ℝ) ∧ (t:ℝ) ≤ v}

lemma CompactCurveArc.openSubarc_open (A : CompactCurveArc Z) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) : IsOpen (A.openSubarc u v) := by
  apply embedded_open_subset A.embedding.isEmbedding A.interior_open
  · exact isOpen_Ioo.preimage continuous_subtype_val
  · intro t ht
    exact ⟨hu.trans_lt ht.1,ht.2.trans_le hv⟩

lemma CompactCurveArc.closedSubarc_compact (A : CompactCurveArc Z) (u v : ℝ) :
    IsCompact (A.closedSubarc u v) := by
  exact (IsClosed.isCompact (isClosed_Icc.preimage continuous_subtype_val)).image A.embedding.continuous

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
