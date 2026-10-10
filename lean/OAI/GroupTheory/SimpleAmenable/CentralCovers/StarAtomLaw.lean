import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ChartControlChain
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LabelShiftedCharts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section StarAtomLaw

variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q]

theorem assignmentProjection_central :
    (assignmentProjection (E := E) (Ω := Ω)).ker ≤
      Subgroup.center (Ω → UniversalExtension E) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  funext ω
  have hω : universalProjection E (x ω) = 1 := congrFun (show assignmentProjection x = 1 from hx) ω
  exact Subgroup.mem_center_iff.mp (universalProjection_central E hω) (y ω)

variable [Fintype Ω]

theorem centralOn_of_star_atoms (q : H →* Q) (v : (Ω → E) →* Q)
    (hv : Function.Injective v) (f : Ω → UniversalExtension E →* H)
    (hc : Pairwise fun i j => ∀ s t, Commute (f i s) (f j t))
    (hf : ∀ ω, q.comp (f ω) = (v.comp (sectorMask {ω})).comp (universalProjection E)) :
    CentralOn q (⨆ ω, (f ω).range) := by
  classical
  let ρ := MonoidHom.noncommPiCoprod f hc
  have hρ : q.comp ρ = v.comp assignmentProjection := by
    apply MonoidHom.pi_ext
    intro ω s
    change q (MonoidHom.noncommPiCoprod f hc (Pi.mulSingle ω s)) =
      v (assignmentProjection (Pi.mulSingle ω s))
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    rw [show q (f ω s) = v (sectorMask {ω} (universalProjection E s)) from
      DFunLike.congr_fun (hf ω) s]
    congr 1
    ext ν
    by_cases he : ν = ω
    · subst ν
      simp [assignmentProjection,sectorMask]
    · simp [assignmentProjection,sectorMask,he]
  rw [← MonoidHom.noncommPiCoprod_range f (hcomm := hc),centralOn_iff]
  rintro x ⟨s,rfl⟩ hx y ⟨t,rfl⟩
  have hs : assignmentProjection s = 1 := by
    apply hv
    have he := DFunLike.congr_fun hρ s
    change q (ρ s) = v (assignmentProjection s) at he
    rw [← he,hx,map_one]
  have hz := assignmentProjection_central (E := E) (Ω := Ω) hs
  exact (show Commute s t from (Subgroup.mem_center_iff.mp hz t).symm).map ρ

end StarAtomLaw

section ChartOverlapBridge
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem old_rectangle_bridge_to_chart (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
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
  obtain ⟨N,hN,hbridge⟩ := B.old_rectangle_bridge_control hlarge hK hδ
  refine ⟨max N (8*k),le_trans hN (le_max_left _ _),?_⟩
  intro n hn g s hs p L V hLV hL hV d e z hpq hlo hup f hf hc
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hkn : k ≤ n/8 := (Nat.le_div_iff_mul_le (by omega : 0 < 8)).mpr (by omega)
  rw [B.tangentChartSector_eq_window (by omega) k q u h n (by omega) g d e z l v hl hv,
    spatialTranslate_coordinateRectangle]
  apply hbridge n hnN g s hs p (fun j => pointLabel z j+q j) hpq L V
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

theorem tangent_chart_chain_control (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ (d : Fin 2) (e : Fin 5) (j : Fin 2),
      -ordinary r < ordinary (l j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary (v j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
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
  obtain ⟨N,hN,hbridge⟩ := B.old_rectangle_bridge_to_chart hlarge hK hδ k q u h l v hl hv hlen
  refine ⟨N,hN,?_⟩
  intro n hn g s hs p L V hLV hL hV d T z e hz hpq hlo hup f hf hc hstart
  apply small_control_action_chain B.c f
    (fun i => B.tangentSign (by omega) k q u h d (z i) true) T hstart
  intro i hi I t x hx
  rw [hz i hi]
  exact B.tangentSign_step_action hlarge hr k q u h d (e i) (z i) l v hl hv hlv hlen hbox
    (hbox' d (e i)) f hf
    (hbridge n hn g s hs p L V hLV hL hV d (e i) (z i) (hpq i hi) (hlo i hi) (hup i hi) f hf hc)
    I t x hx

end InitialCoverSystem
end ChartOverlapBridge

end SimpleAmenable
end
end

end OAI
