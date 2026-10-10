import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.UniformPropagationBounds
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlTransfer
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullSector

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceControlCalculus
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

abbrev AlignedSmallSupported (f : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)) : Prop :=
  SmallSupported (sourceAlignedGroup a r m hm M B.t) f

theorem control_trans (hlarge : 20 ≤ m+1)
    (f g k : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f) (hk : B.AlignedSmallSupported k)
    (hfg : SmallControlled B.c f g) (hgk : SmallControlled B.c g k) :
    SmallControlled B.c f k :=
  small_control_trans _ B.c B.constant_aligned B.disjoint_aligned (by simpa using hlarge)
    B.constant_small_supported f g k hf hk hfg hgk

theorem control_chain (hlarge : 20 ≤ m+1)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (F : ℕ → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (T : ℕ) (hf : B.AlignedSmallSupported f)
    (hF : ∀ i, i ≤ T → B.AlignedSmallSupported (F i))
    (h₀ : SmallControlled B.c f (F 0))
    (hstep : ∀ i, i < T → SmallControlled B.c (F i) (F (i+1))) :
    SmallControlled B.c f (F T) := by
  have hh : ∀ i, i ≤ T → SmallControlled B.c f (F i) := by
    intro i
    induction i with
    | zero => intro _; exact h₀
    | succ i ih =>
      intro hi
      exact B.control_trans hlarge f (F i) (F (i+1)) hf (hF _ (by omega))
        (ih (by omega)) (hstep i (by omega))
  exact hh T le_rfl

theorem axisSector_supported (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val) :
    B.AlignedSmallSupported (B.axisSector hlarge n h j k hk p V) :=
  B.fullGeometricSector_supported hlarge _ _ V hV

theorem axisInterval_chain_control (hlarge : 20 ≤ m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (T : ℕ) (w : ℕ → ℤ) (u v : ℕ → CutRing)
    (hlabel : ∀ i, (w i ≤ endpointLabel (u i) ∧ endpointLabel (u i) < w i+k) ∧
      (w i ≤ endpointLabel (v i) ∧ endpointLabel (v i) < w i+k))
    (hstep : ∀ i, i < T → |w (i+1)-w i|+(k:ℤ) ≤ n)
    (hinc : ∀ i, i < T → coordinateInterval a j (u i) (v i) ≤
      coordinateInterval a j (u (i+1)) (v (i+1)))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (h₀ : SmallControlled B.c f (B.axisSector (by omega) n h j k hk (w 0)
      (coordinateInterval a j (u 0) (v 0)))) :
    SmallControlled B.c f (B.axisSector (by omega) n h j k hk (w T)
      (coordinateInterval a j (u T) (v T))) := by
  apply B.control_chain hlarge f
    (fun i => B.axisSector (by omega) n h j k hk (w i) (coordinateInterval a j (u i) (v i))) T hf
  · intro i _
    exact B.axisSector_supported (by omega) n h j k hk (w i) _
      (axisInterval_resolved j k (w i) (u i) (v i) (hlabel i).1 (hlabel i).2)
  · exact h₀
  · intro i hi
    have hh := hstep i hi
    have h₁ := le_abs_self (w (i+1)-w i)
    have h₂ := neg_le_abs (w (i+1)-w i)
    apply B.axisSector_overlap_control (by omega) n h j k k hk hk (w i) (w (i+1))
      (min (w i) (w (i+1))) (min_le_left _ _) ?_ (min_le_right _ _) ?_ _ _ (hinc i hi)
      (axisInterval_resolved j k (w i) (u i) (v i) (hlabel i).1 (hlabel i).2)
      (axisInterval_resolved j k (w (i+1)) (u (i+1)) (v (i+1)) (hlabel (i+1)).1 (hlabel (i+1)).2)
    · omega
    · omega

end InitialCoverSystem
end SourceControlCalculus

section ActualOldAxisBridge
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem old_axis_bridge_control (hlarge : 20 ≤ m+1) {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
      ∀ (j : Fin 2) (s : ℕ) (hs : s ≤ n) (p q : ℤ),
      ((q-p).natAbs:ℝ) ≤ (K+1)*(n:ℝ) →
      ∀ u v U V : CutRing, ordinary u ≤ ordinary v →
      ordinary U ≤ ordinary u-δ → ordinary v+δ ≤ ordinary V →
      ordinary V-ordinary U < 1 →
      (p ≤ endpointLabel u ∧ endpointLabel u < p+s) →
      (p ≤ endpointLabel v ∧ endpointLabel v < p+s) →
      (q ≤ endpointLabel U ∧ endpointLabel U < q+(n/8:ℕ)) →
      (q ≤ endpointLabel V ∧ endpointLabel V < q+(n/8:ℕ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      SmallControlled B.c f (B.axisSector (by omega) n h j s hs p (coordinateInterval a j u v)) →
      SmallControlled B.c f (B.axisSector (by omega) n h j (n/8) (Nat.div_le_self n 8) q
        (coordinateInterval a j U V)) := by
  obtain ⟨N,hN,hgeo⟩ := old_window_bridge_geometry hK hδ 0
  refine ⟨N,hN,?_⟩
  intro n hn h j s hs p q hpq u v U V huv hU hV hlen hlu hlv hlU hlV f hf hstart
  obtain ⟨T,w,u',v',hw₀,hwT,_,hlabel,hstep,hinc,hnest,herror⟩ :=
    hgeo n hn p q hpq (ordinary u) (ordinary v) huv
  have horder (i : ℕ) : ordinary (u' i) ≤ ordinary (v' i) := by
    have hh := hinc i (show ordinary u ∈ Set.Icc (ordinary u) (ordinary v) from ⟨le_rfl,huv⟩)
    exact hh.1.le.trans hh.2.le
  have hbounds (i : ℕ) (hi : i ≤ T) :
      ordinary U ≤ ordinary (u' i) ∧ ordinary (v' i) ≤ ordinary V := by
    have h₁ := herror i hi (show ordinary (u' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
      from ⟨le_rfl,horder i⟩)
    have h₂ := herror i hi (show ordinary (v' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
      from ⟨horder i,le_rfl⟩)
    exact ⟨hU.trans h₁.1.le,h₂.2.le.trans hV⟩
  have hlength (i : ℕ) (hi : i ≤ T) : ordinary (v' i)-ordinary (u' i) < 1 := by
    obtain ⟨h₁,h₂⟩ := hbounds i hi
    linarith
  have hlabels₀ : (p ≤ endpointLabel (u' 0) ∧ endpointLabel (u' 0) < p+(n/8:ℕ)) ∧
      (p ≤ endpointLabel (v' 0) ∧ endpointLabel (v' 0) < p+(n/8:ℕ)) := by
    simpa only [hw₀] using hlabel 0
  have hfirstinc : coordinateInterval a j u v ≤ coordinateInterval a j (u' 0) (v' 0) := by
    apply coordinateInterval_mono j u v (u' 0) (v' 0)
    · exact (hinc 0 (show ordinary u ∈ Set.Icc (ordinary u) (ordinary v) from ⟨le_rfl,huv⟩)).1.le
    · exact huv
    · exact (hinc 0 (show ordinary v ∈ Set.Icc (ordinary u) (ordinary v) from ⟨huv,le_rfl⟩)).2.le
    · exact hlength 0 (Nat.zero_le _)
  have hfirst := B.axisSector_overlap_control (by omega : 15 < m+1) n h j s (n/8) hs
    (Nat.div_le_self n 8) p p p le_rfl (by omega) le_rfl
    (by omega)
    (coordinateInterval a j u v) (coordinateInterval a j (u' 0) (v' 0)) hfirstinc
    (axisInterval_resolved j s p u v hlu hlv)
    (axisInterval_resolved j (n/8) p (u' 0) (v' 0) hlabels₀.1 hlabels₀.2)
  have hF₀ := B.axisSector_supported (by omega : 15 < m+1) n h j (n/8)
    (Nat.div_le_self n 8) p (coordinateInterval a j (u' 0) (v' 0))
    (axisInterval_resolved j (n/8) p (u' 0) (v' 0) hlabels₀.1 hlabels₀.2)
  have h₀ := B.control_trans hlarge f _ _ hf hF₀ hstart hfirst
  have hchain : SmallControlled B.c f (B.axisSector (by omega) n h j (n/8)
      (Nat.div_le_self n 8) (w T) (coordinateInterval a j (u' T) (v' T))) := by
    refine B.axisInterval_chain_control hlarge n h j (n/8) (Nat.div_le_self n 8) T w u' v'
      hlabel ?_ ?_ f hf ?_
    · intro i _
      have hh := hstep i
      simp only [mul_zero,Nat.cast_zero,add_zero] at hh
      exact hh.le
    · intro i hi
      apply coordinateInterval_mono j (u' i) (v' i) (u' (i+1)) (v' (i+1))
      · exact (hnest i (show ordinary (u' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
          from ⟨le_rfl,horder i⟩)).1.le
      · exact horder i
      · exact (hnest i (show ordinary (v' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
          from ⟨horder i,le_rfl⟩)).2.le
      · exact hlength (i+1) (by omega)
    · simpa only [hw₀] using h₀
  rw [hwT] at hchain
  have hlastinc : coordinateInterval a j (u' T) (v' T) ≤ coordinateInterval a j U V :=
    coordinateInterval_mono j (u' T) (v' T) U V (hbounds T le_rfl).1 (horder T)
      (hbounds T le_rfl).2 hlen
  have hlast : SmallControlled B.c
      (B.axisSector (by omega) n h j (n/8) (Nat.div_le_self n 8) q (coordinateInterval a j (u' T) (v' T)))
      (B.axisSector (by omega) n h j (n/8) (Nat.div_le_self n 8) q (coordinateInterval a j U V)) :=
    B.fullGeometricSector_small_control (by omega) _ _ _ _ hlastinc
  exact B.control_trans hlarge f _ _ hf
    (B.axisSector_supported (by omega) n h j (n/8) (Nat.div_le_self n 8) q _
      (axisInterval_resolved j (n/8) q U V hlU hlV)) hchain hlast

end InitialCoverSystem
end ActualOldAxisBridge

end SimpleAmenable
end
end

end OAI
