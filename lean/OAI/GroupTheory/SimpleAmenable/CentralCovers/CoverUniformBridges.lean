import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ChartControlChain
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricCharts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoverUniformBridges
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem old_axis_bridge_control_cover_uniform (hlarge : 20 ≤ m+1) {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M), ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
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
  intro M B n hn h j s hs p q hpq u v U V huv hU hV hlen hlu hlv hlU hlV f hf hstart
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

theorem old_rectangle_bridge_control_cover_uniform (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M), ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p q : Fin 2 → ℤ),
      (∀ j, ((q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      ∀ u v U V : Fin 2 → CutRing,
      (∀ j, ordinary (u j) ≤ ordinary (v j)) →
      (∀ j, ordinary (U j) ≤ ordinary (u j)-δ) →
      (∀ j, ordinary (v j)+δ ≤ ordinary (V j)) →
      (∀ j, ordinary (V j)-ordinary (U j) < 1) →
      (∀ j, p j ≤ endpointLabel (u j) ∧ endpointLabel (u j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+s j) →
      (∀ j, q j ≤ endpointLabel (U j) ∧ endpointLabel (U j) < q j+(n/8:ℕ)) →
      (∀ j, q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+(n/8:ℕ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n h j (s j) (hs j) (p j) (coordinateInterval a j (u j) (v j)))) →
      SmallControlled B.c f (B.windowSector (by omega) n h q (coordinateRectangle a U V)) := by
  obtain ⟨N,hN,hbridge⟩ := old_axis_bridge_control_cover_uniform (a := a) (r := r) (hm := hm) hlarge hK hδ
  refine ⟨N,hN,?_⟩
  intro M B n hn h s hs p q hpq u v U V huv hU hV hlen hlu hlv hlU hlV f hf hstart
  have hc (j : Fin 2) : SmallControlled B.c f
      (B.windowSector (by omega) n h q (coordinateInterval a j (U j) (V j))) := by
    have hh := hbridge M B n hn h j (s j) (hs j) (p j) (q j) (hpq j)
      (u j) (v j) (U j) (V j) (huv j) (hU j) (hV j) (hlen j)
      (hlu j) (hlv j) (hlU j) (hlV j) f hf (hstart j)
    rw [B.axisSector_in_window (by omega) n h j (n/8) (Nat.div_le_self n 8)
      (q j) q le_rfl (by omega) (coordinateInterval a j (U j) (V j))
      (axisInterval_resolved j (n/8) (q j) (U j) (V j) (hlU j) (hlV j))] at hh
    exact hh
  apply B.fullGeometricSector_intersection_control (by omega) (coordinateWindowPrimitives n q)
    (fun I _ b hb => h I b hb q) (coordinateInterval a 0 (U 0) (V 0))
    (coordinateInterval a 1 (U 1) (V 1)) ?_ ?_ f (hc 0) (hc 1)
  · exact coordinateLabelWindow_resolved n q 0 (U 0) (V 0)
      ⟨(hlU 0).1,by have h' := (hlU 0).2; omega⟩
      ⟨(hlV 0).1,by have h' := (hlV 0).2; omega⟩
  · exact coordinateLabelWindow_resolved n q 1 (U 1) (V 1)
      ⟨(hlU 1).1,by have h' := (hlU 1).2; omega⟩
      ⟨(hlV 1).1,by have h' := (hlV 1).2; omega⟩

theorem old_rectangle_bridge_to_chart_cover_uniform (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M) (h : B.TangentChartLaws k q u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p : Fin 2 → ℤ),
      ∀ L V : Fin 2 → CutRing,
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+s j) →
      ∀ (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing),
      (∀ j, ((pointLabel z j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      (∀ j, ordinary (l j)+ordinary (pointCoordinate z j) ≤ ordinary (L j)-δ) →
      (∀ j, ordinary (V j)+δ ≤ ordinary (v j)+ordinary (pointCoordinate z j)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (s j) (hs j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.fullGeometricSector (by omega)
        (translatedTemplate (tangentChartTemplate a k q d (signedShortSteps u e)) z)
        (h d e z) (spatialTranslate z (coordinateRectangle a l v))) := by
  obtain ⟨N,hN,hbridge⟩ := old_rectangle_bridge_control_cover_uniform (a := a) (r := r) (hm := hm) hlarge hK hδ
  refine ⟨max N (8*k),le_trans hN (le_max_left _ _),?_⟩
  intro M B h n hn g s hs p L V hLV hL hV d e z hpq hlo hup f hf hc
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hkn : k ≤ n/8 := (Nat.le_div_iff_mul_le (by omega : 0 < 8)).mpr (by omega)
  rw [B.tangentChartSector_eq_window (by omega) k q u h n (by omega) g d e z l v hl hv,
    spatialTranslate_coordinateRectangle]
  apply hbridge M B n hnN g s hs p (fun j => pointLabel z j+q j) hpq L V
    (fun j => l j+pointCoordinate z j) (fun j => v j+pointCoordinate z j) hLV
  · intro j
    simpa only [map_add] using hlo j
  · intro j
    simpa only [map_add] using hup j
  · intro j
    simpa only [map_add,add_sub_add_right_eq_sub] using hlen j
  · exact hL
  · exact hV
  · intro j
    simp only [endpointLabel_add,pointLabel]
    have hh := hl j
    omega
  · intro j
    simp only [endpointLabel_add,pointLabel]
    have hh := hv j
    omega
  · exact hf
  · exact hc

theorem tangent_chart_chain_control_cover_uniform (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ (d : Fin 2) (e : Fin 5) (j : Fin 2),
      -ordinary r < ordinary (l j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary (v j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M) (h : B.TangentChartLaws k q u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p : Fin 2 → ℤ),
      ∀ L V : Fin 2 → CutRing,
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+s j) →
      ∀ (d : Fin 2) (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
      (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) →
      (∀ i, i < T → ∀ j, ((pointLabel (z i) j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      (∀ i, i < T → ∀ j, ordinary (l j)+ordinary (pointCoordinate (z i) j) ≤ ordinary (L j)-δ) →
      (∀ i, i < T → ∀ j, ordinary (V j)+δ ≤ ordinary (v j)+ordinary (pointCoordinate (z i) j)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (s j) (hs j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z 0) true) →
      SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z T) true) := by
  obtain ⟨N,hN,hbridge⟩ := old_rectangle_bridge_to_chart_cover_uniform (m := m) (r := r) (hm := hm) hlarge hK hδ k q u l v hl hv hlen
  refine ⟨N,hN,?_⟩
  intro M B h n hn g s hs p L V hLV hL hV d T z e hz hpq hlo hup f hf hc hstart
  apply small_control_action_chain B.c f
    (fun i => B.tangentSign (by omega) k q u h d (z i) true) T hstart
  intro i hi I t x hx
  rw [hz i hi]
  exact B.tangentSign_step_action hlarge hr k q u h d (e i) (z i) l v hl hv hlv hlen hbox
    (hbox' d (e i)) f hf
    (hbridge M B h n hn g s hs p L V hLV hL hV d (e i) (z i) (hpq i hi) (hlo i hi) (hup i hi) f hf hc)
    I t x hx

theorem tangent_transport_uniform_cover_uniform (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u v : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (huv : u*v=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    {A C D E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p : Fin 2 → ℤ) (L V : Fin 2 → CutRing),
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j) →
      ∀ w : CutRing, |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w:ℝ)| ≤ C*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing),
      (∀ j, |(pointLabel z₀ j+symmetricWindowStart s j-p j:ℝ)| ≤ E*(n:ℝ)) →
      (∀ j, |ordinary (L j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      (∀ j, |ordinary (V j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
        (symmetricWindowStart s) u h d z₀ true) →
      SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
        (symmetricWindowStart s) u h d (z₀+tangentOffset a d w) true) := by
  obtain ⟨K,hK,N₁,hN₁,hgeo⟩ := uniform_tangent_chart_geometry a u v s huv hs hshort hA hC hD hE
  have hl := fun j => (symmetricWindow_labels s j).1
  have hv := fun j => (symmetricWindow_labels s j).2.2
  have hlen : ∀ _ : Fin 2, ordinary s-ordinary (-s) < 1 := by
    intro j
    rw [map_neg]
    linarith [hr.2]
  have hbox (j : Fin 2) : -ordinary r < ordinary (-s) ∧ ordinary s < ordinary r := by
    rw [map_neg]
    constructor <;> linarith [hr.1]
  obtain ⟨N₂,hN₂,hchain⟩ := tangent_chart_chain_control_cover_uniform (m := m) (r := r) (hm := hm) hlarge hr hK
    (by linarith : 0 < ordinary s/4) (symmetricWindowLength s) (symmetricWindowStart s) u
    (fun _ => -s) (fun _ => s) hl hv (fun _ => by rw [map_neg]; linarith) hlen hbox
    (fun d e j => (symmetric_chart_overlap_boxes a r s u hs hsr hshort d e j).2)
  refine ⟨max N₁ N₂,hN₂.trans (le_max_right _ _),?_⟩
  intro M B h n hn g t ht p L V hLV hL hV w hw hw' d z₀ hp hLo hVo f hf hc hstart
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  obtain ⟨T,z,e,hz0,hzT,hstep,hpq,hlo,hup⟩ := hgeo n hn₁ w hw hw' d z₀
    (symmetricWindowStart s) p L V hp hLo hVo
  have hh := hchain M B h n hn₂ g t ht p L V hLV hL hV d T z e hstep
    (fun i _ => hpq i) (fun i _ => by simpa only [map_neg] using hlo i)
    (fun i _ => hup i) f hf hc (by simpa only [hz0] using hstart)
  simpa only [hzT] using hh

end InitialCoverSystem
end CoverUniformBridges

end SimpleAmenable
end
end

end OAI
