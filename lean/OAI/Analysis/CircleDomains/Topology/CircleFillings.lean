import OAI.Analysis.CircleDomains.Topology.CirclePatching

namespace OAI

/-!
# Simultaneous smooth fillings of circle coordinates

Connected collars and one active staircase per disk give actual real
rank-one extensions. Their projections patch into the retained circle
maps. The construction requires only the existing local branches and
does not assert any unproved period or winding statement.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def IsFilledCircleFamily {I L : Type*}
    (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ))
    (v F : L → (ℝ × ℝ) → UnitAddCircle) : Prop :=
  (∀ l, SmoothCircleOn (F l) Ω) ∧
  (∀ l x, (∀ i, x ∉ D i) → F l x = v l x) ∧
  (∀ i, ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l, F l x = v l x) ∧
  ∀ i l m, l ≠ m → ∀ x ∈ D i,
    planarWedge (circleGradient (F l) x) (circleGradient (F m) x) = 0

/-- One common small width produces real rank-one collar extensions
on all disks before any global projection or patching is performed. -/
theorem eventually_exists_rank_one_collar_families
    {I L : Type*} [Fintype I] [Fintype L]
    (D : I → Set (ℝ × ℝ))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (u : I → L → (ℝ × ℝ) → ℝ)
    (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (active : I → L) {h : ℝ} (hh : 0 < h) (θ : L → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice h (θ l))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ g : I → L → (ℝ × ℝ) → ℝ,
      (∀ i l, ContDiff ℝ ∞ (g i l)) ∧
      (∀ i, ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
        g i l x = shiftedStaircase h δ (θ l) (u i l x)) ∧
      ∀ i l m, l ≠ m → ∀ x,
        planarWedge (planarGradient (g i l) x) (planarGradient (g i m) x) = 0 := by
  classical
  choose C hCc hCconn hCfront hCO hCavoid using fun i =>
    exists_inactive_connected_collar (hfrontc i) (hfrontconn i) (hO i) (hDO i)
      (u i) (hu i) (active i) hh θ (havoid i)
  choose z hz using fun i => (hfrontconn i).nonempty
  have hzC (i : I) : z i ∈ C i := subset_of_mem_nhdsSet (hCfront i) (hz i)
  have hconst : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i l, l ≠ active i →
      ∀ x ∈ C i, shiftedStaircase h δ (θ l) (u i l x) =
        shiftedStaircase h δ (θ l) (u i l (z i)) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro l
    by_cases hl : l = active i
    · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
    · exact (eventually_constant_staircase_on_collar (hCc i) (hCconn i).isPreconnected
        (u i l) ((hu i l).continuousOn.mono (hCO i)) hh (hCavoid i l hl)).mono
        (fun δ hδ _ x hx => hδ.2 x hx (z i) (hzC i))
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < h / 4 := by
    exact (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < h / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hconst, hsmall] with δ hδ hδsmall
  have hlocal (i : I) : ∃ g : L → (ℝ × ℝ) → ℝ,
      (∀ l, ContDiff ℝ ∞ (g l)) ∧
      (∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
        g l x = shiftedStaircase h δ (θ l) (u i l x)) ∧
      ∀ l m, l ≠ m → ∀ x,
        planarWedge (planarGradient (g l) x) (planarGradient (g m) x) = 0 := by
    have hfrontInt : frontier (D i) ⊆ interior (C i) :=
      subset_interior_iff_mem_nhdsSet.mpr (hCfront i)
    let w : L → (ℝ × ℝ) → ℝ := fun l x => shiftedStaircase h δ (θ l) (u i l x)
    have hw : ContDiffOn ℝ ∞ (w (active i)) (interior (C i)) :=
      (contDiff_shiftedStaircase hh hδsmall.1 hδsmall.2 (θ (active i))).comp_contDiffOn
        ((hu i (active i)).mono (interior_subset.trans (hCO i)))
    obtain ⟨g, hg, hgw, _, hzero⟩ := exists_rank_one_collar_extension (active i)
      isOpen_interior isClosed_frontier hfrontInt w (fun l => w l (z i)) hw
      (fun l hl x hx => hδ i l hl x (interior_subset hx))
    exact ⟨g, hg, hgw, hzero⟩
  choose g hg hagree hzero using hlocal
  exact ⟨g, hg, hagree, hzero⟩

/-- Actual circle maps are filled simultaneously from their real collar
branches. The agreement is on full neighborhoods of the boundaries. -/
theorem eventually_exists_filled_circle_coordinates
    {I L : Type*} [Fintype I] [Fintype L]
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (u : I → L → (ℝ × ℝ) → ℝ)
    (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (active : I → L) {h : ℝ} (hh : 0 < h) (θ : L → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice h (θ l)))
    (v : ℝ → L → (ℝ × ℝ) → UnitAddCircle) (Ω : Set (ℝ × ℝ))
    (hv : ∀ δ, 0 < δ → δ < h / 4 → ∀ l, SmoothCircleOn (v δ l) (Ω \ ⋃ i, D i))
    (hbranch : ∀ δ i l x, x ∈ O i →
      (shiftedStaircase h δ (θ l) (u i l x) : UnitAddCircle) = v δ l x) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : L → (ℝ × ℝ) → UnitAddCircle,
      IsFilledCircleFamily D Ω (v δ) F := by
  classical
  have hlocal := eventually_exists_rank_one_collar_families D hfrontc hfrontconn
    O hO hDO u hu active hh θ havoid
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < h / 4 := by
    exact (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < h / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hlocal, hsmall] with δ hδ hδsmall
  obtain ⟨g, hg, hagree, hzero⟩ := hδ
  have hpair : Pairwise (Disjoint on D) := fun i j hij =>
    (hdisj hij).mono subset_closure subset_closure
  have hproj (i : I) : ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
      (g i l x : UnitAddCircle) = v δ l x := by
    filter_upwards [hagree i, (hO i).mem_nhdsSet.mpr (hDO i)] with x hx hxO l
    exact (congrArg ((↑) : ℝ → UnitAddCircle) (hx l)).trans (hbranch δ i l x hxO)
  have hagreeAt (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (D i)) (l : L) :
      (fun y => (g i l y : UnitAddCircle)) =ᶠ[𝓝 x] v δ l :=
    ((hproj i).filter_mono (nhds_le_nhdsSet hx)).mono (fun _ hy => hy l)
  let F : L → (ℝ × ℝ) → UnitAddCircle := fun l =>
    patchOpenRegions D (fun i x => (g i l x : UnitAddCircle)) (v δ l)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro l
    exact smoothCircleOn_patchOpenRegions D hD hpair (v δ l) (hv δ hδsmall.1 hδsmall.2 l)
      (fun i => g i l) (fun i => hg i l) (fun i x hx => hagreeAt i x hx.2 l)
  · intro l x hx
    exact patchOpenRegions_eq_of_notMem D (fun i x => (g i l x : UnitAddCircle)) (v δ l) hx
  · intro i
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    have houtside : ∀ j, x ∉ D j := by
      intro j hxj
      by_cases hji : j = i
      · subst j
        rw [(hD i).frontier_eq] at hx
        exact hx.2 hxj
      · exact Set.disjoint_left.mp (hdisj hji) (subset_closure hxj) (frontier_subset_closure hx)
    apply eventually_all.mpr
    intro l
    exact patchOpenRegions_eventuallyEq_outside D (fun i x => (g i l x : UnitAddCircle))
      (v δ l) hD houtside (fun j hj => hagreeAt j x hj l)
  · intro i l m hlm x hx
    exact circle_patch_wedges_eq_zero_inside D hD hpair (v δ) g hg
      (fun i l m hlm x _ => hzero i l m hlm x) hx l m hlm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
