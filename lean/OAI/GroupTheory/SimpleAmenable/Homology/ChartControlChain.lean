import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.PrimitiveCovariance
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlTransfer
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateFamilyCompare
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ControlCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ChartControlChain

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem small_control_action_chain (c : alternatingGroup α →* H)
    (f : TrackStar α →* H) (g : ℕ → TrackStar α →* H) (n : ℕ)
    (hstart : SmallControlled c f (g 0))
    (hstep : ∀ k, k < n → ∀ (I : ControlAlphabet α) s, ∀ x ∈ f.range,
      g k (universalMap (subtypeAlternatingHom I.val) s)*x*
          (g k (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        g (k+1) (universalMap (subtypeAlternatingHom I.val) s)*x*
          (g (k+1) (universalMap (subtypeAlternatingHom I.val) s))⁻¹) :
    SmallControlled c f (g n) := by
  have h (k : ℕ) (hk : k ≤ n) : SmallControlled c f (g k) := by
    induction k with
    | zero => exact hstart
    | succ k ih =>
      intro I s x hx
      dsimp only [MonoidHom.comp_apply]
      rw [← hstep k (by omega) I s x hx]
      exact ih (by omega) I s x hx
  exact h n le_rfl

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem chartCoordinateSector_eq_window (hlarge : 15 < m+1)
    (n : ℕ) (h : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hP : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (v : κ → ι) (j : κ → Fin 2) (u : κ → CutRing × CutRing)
    (hv : ∀ i, P (v i) = (coordinateTestIndex (j i),u i))
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i=0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i=0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (spatialTranslate (u i) (coordinatePrimitive a (j i))).val) V.val) :
    B.fullGeometricSector hlarge P hP V = B.windowSector hlarge n h q V := by
  let Q := fun i => (coordinateTestIndex (j i),u i)
  have heq : P ∘ v = Q := funext hv
  have hQ : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q := by
    intro I hI b hb
    rw [← heq]
    exact PrimitiveFamilyLaw.reindex B I b hb P (hP I hI b hb) v
  have hVQ : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    simpa only [Q,primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hV
  rw [← B.fullGeometricSector_subfamily hlarge P Q v heq hP hQ V hVQ]
  exact B.coordinateFamilySector_eq_window hlarge n h q j u hs he hQ V hV

theorem chart_chain_disjoint_control (hlarge : 20 ≤ m+1)
    (f g : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f) (hg : B.AlignedSmallSupported g)
    (c : ℕ → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (n : ℕ) (hc : B.AlignedSmallSupported (c n))
    (d : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hstart : SmallControlled B.c f (c 0))
    (hstep : ∀ k, k < n → ∀ (I : ControlAlphabet (Fin (m+1))) s, ∀ x ∈ f.range,
      c k (universalMap (subtypeAlternatingHom I.val) s)*x*
          (c k (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        c (k+1) (universalMap (subtypeAlternatingHom I.val) s)*x*
          (c (k+1) (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
    (hfinish : SmallControlled B.c g d) (hsplit : ∀ s t, Commute (c n s) (d t)) :
    ∀ s t, Commute (f s) (g t) := by
  apply small_control_disjoint _ B.c B.constant_aligned B.disjoint_aligned
    (by simpa using hlarge) f g (c n) d hf hg hc
    (small_control_action_chain B.c f c n hstart hstep) hfinish hsplit

end InitialCoverSystem
end ChartControlChain

end SimpleAmenable
end
end

end OAI
