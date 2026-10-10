import OAI.Geometry.EinsteinFour.OrientationCoverCore

namespace OAI

/-! The actual orientation cover has a continuous free deck involution and
exactly two points over each base point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev orientationCoverProjection : OrientationCover M → M :=
  (orientationCoverCore (M := M)).proj

def orientationCoverDeck (x : OrientationCover M) : OrientationCover M := ⟨x.proj, !x.snd⟩

@[simp] theorem orientationCoverDeck_proj (x : OrientationCover M) :
    (orientationCoverDeck x).proj = x.proj := rfl

@[simp] theorem orientationCoverDeck_deck (x : OrientationCover M) :
    orientationCoverDeck (orientationCoverDeck x) = x := by
  cases x with
  | mk a s => exact congrArg (TotalSpace.mk a) (Bool.not_not s)

theorem orientationCoverDeck_free (x : OrientationCover M) : orientationCoverDeck x ≠ x := by
  intro h
  have hb : (!x.snd) = x.snd := congrArg TotalSpace.snd h
  exact Bool.not_ne_self x.snd hb

theorem orientationCover_fibers (x y : OrientationCover M) :
    orientationCoverProjection x = orientationCoverProjection y ↔
      x = y ∨ x = orientationCoverDeck y := by
  constructor
  · intro h
    cases x with
    | mk a s =>
      cases y with
      | mk b t =>
        change a = b at h
        subst b
        cases s <;> cases t <;> simp [orientationCoverDeck]
  · rintro (rfl | rfl) <;> rfl

theorem orientationCoverProjection_surjective :
    Function.Surjective (orientationCoverProjection (M := M)) := fun x => ⟨⟨x, false⟩, rfl⟩

def orientationCoverFiberEquiv (x : M) :
    {y : OrientationCover M // orientationCoverProjection y = x} ≃ Bool where
  toFun y := y.val.snd
  invFun s := ⟨⟨x, s⟩, rfl⟩
  left_inv y := by
    rcases y with ⟨⟨a, s⟩, h⟩
    change a = x at h
    subst a
    rfl
  right_inv _ := rfl

theorem orientationCover_fiber_card (x : M) :
    Nat.card {y : OrientationCover M // orientationCoverProjection y = x} = 2 := by
  rw [Nat.card_congr (orientationCoverFiberEquiv x)]
  exact Nat.card_eq_fintype_card

theorem orientationCoverDeck_localTriv (i : atlas FourSpace M) (x : OrientationCover M) :
    (orientationCoverCore (M := M)).localTriv i (orientationCoverDeck x) =
      ((orientationCoverCore (M := M)).localTriv i x).map id Bool.not := by
  let d := orientationTransitionDet ((orientationCoverCore (M := M)).indexAt x.proj) i x.proj
  change (x.proj, if 0 < d then !x.snd else !(!x.snd)) =
    (x.proj, !(if 0 < d then x.snd else !x.snd))
  by_cases h : 0 < d <;> simp [h]


theorem continuous_orientationCoverDeck : Continuous (orientationCoverDeck (M := M)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let Z := orientationCoverCore (M := M)
  let e := Z.localTrivAt x.proj
  have hx : x ∈ e.source := Z.mk_mem_localTrivAt_source x.proj x.snd
  have hdx : orientationCoverDeck x ∈ e.source :=
    Z.mk_mem_localTrivAt_source x.proj (!x.snd)
  let N : M × Bool → M × Bool := fun p => (p.1, !p.2)
  have hN : Continuous N := continuous_fst.prodMk (by fun_prop)
  have he : e (orientationCoverDeck x) = N (e x) :=
    orientationCoverDeck_localTriv _ x
  have htarget : N (e x) ∈ e.target := he ▸ e.map_source hdx
  have hec : ContinuousAt (fun y => e y) x := e.toOpenPartialHomeomorph.continuousAt hx
  have hNc : ContinuousAt (fun y => N (e y)) x := hN.continuousAt.comp hec
  have hic : ContinuousAt (fun p => e.toOpenPartialHomeomorph.symm p) (N (e x)) :=
    e.toOpenPartialHomeomorph.symm.continuousAt htarget
  have hcomp : ContinuousAt (fun y => e.toOpenPartialHomeomorph.symm (N (e y))) x :=
    ContinuousAt.comp (f := fun y => N (e y)) (g := fun p => e.toOpenPartialHomeomorph.symm p) hic hNc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  have hdy : orientationCoverDeck y ∈ e.source := hy
  have hcomm : e (orientationCoverDeck y) = N (e y) := orientationCoverDeck_localTriv _ y
  rw [← hcomm]
  exact (e.toOpenPartialHomeomorph.left_inv hdy).symm

def orientationCoverDeckHomeomorph : OrientationCover M ≃ₜ OrientationCover M where
  toFun := orientationCoverDeck
  invFun := orientationCoverDeck
  left_inv := orientationCoverDeck_deck
  right_inv := orientationCoverDeck_deck
  continuous_toFun := continuous_orientationCoverDeck
  continuous_invFun := continuous_orientationCoverDeck

instance orientationCover_t2Space [T2Space M] : T2Space (OrientationCover M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hne
  by_cases hbase : x.proj = y.proj
  · let Z := orientationCoverCore (M := M)
    let e := Z.localTrivAt x.proj
    have hx : x ∈ e.source := Z.mk_mem_localTrivAt_source x.proj x.snd
    have hy : y ∈ e.source := e.mem_source.mpr (hbase ▸ Z.mem_localTrivAt_baseSet x.proj)
    have hxy : e x ≠ e y := fun heq => hne (e.toOpenPartialHomeomorph.injOn hx hy heq)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hxy) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (orientationCover_isCoveringMap.continuous).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) (orientationCover_isCoveringMap.continuous).continuousAt

end
end PositiveEinsteinFour.Geometry

end OAI
