import OAI.Analysis.CircleDomains.Topology.ConnectedCollars
import OAI.Analysis.CircleDomains.Selection.FinitePatching
import OAI.Analysis.CircleDomains.Modulus.FiniteWedgeCosts

namespace OAI

/-!
# Simultaneous smooth coordinate fillings

Compact connected collars are chosen inside the supplied real-branch
domains and away from all inactive lattices. A single sufficiently small
width makes every inactive staircase constant there. Rank-one collar
extensions then patch into the retained coordinates across all the
pairwise disjoint filling disks. No lifting theorem is assumed.
-/

open Set Filter Function
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

def IsFilledCoordinateFamily {I L : Type*}
    (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ))
    (v F : L → (ℝ × ℝ) → ℝ) : Prop :=
  (∀ l, ContDiffOn ℝ ∞ (F l) Ω) ∧
  (∀ l x, (∀ i, x ∉ D i) → F l x = v l x) ∧
  (∀ i, ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l, F l x = v l x) ∧
  ∀ i l m, l ≠ m → ∀ x ∈ D i,
    planarWedge (planarGradient (F l) x) (planarGradient (F m) x) = 0

theorem IsFilledCoordinateFamily.eventuallyEq_outside
    {I L : Type*} [Fintype I] {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → ℝ} (hF : IsFilledCoordinateFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) {x : ℝ × ℝ} (hx : ∀ i, x ∉ D i) (l : L) :
    F l =ᶠ[𝓝 x] v l := by
  by_cases hb : ∃ i, x ∈ frontier (D i)
  · obtain ⟨i, hi⟩ := hb
    exact ((hF.2.2.1 i).filter_mono (nhds_le_nhdsSet hi)).mono (fun _ h => h l)
  · have hc (i : I) : x ∉ closure (D i) := by
      intro hi
      apply hb
      refine ⟨i, ?_⟩
      rw [(hD i).frontier_eq]
      exact ⟨hi, hx i⟩
    have hn : ∀ᶠ y in 𝓝 x, ∀ i, y ∉ closure (D i) :=
      eventually_all.mpr (fun i => isClosed_closure.isOpen_compl.mem_nhds (hc i))
    filter_upwards [hn] with y hy
    exact hF.2.1 l y (fun i hi => hy i (subset_closure hi))

/-- The actual pairwise wedge magnitude cannot increase under the
filling: it is unchanged off the disks and vanishes inside them. -/
theorem IsFilledCoordinateFamily.abs_wedge_le
    {I L : Type*} [Fintype I] {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → ℝ} (hF : IsFilledCoordinateFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) (l m : L) (hlm : l ≠ m) (x : ℝ × ℝ) :
    |planarWedge (planarGradient (F l) x) (planarGradient (F m) x)| ≤
      |planarWedge (planarGradient (v l) x) (planarGradient (v m) x)| := by
  by_cases hi : ∃ i, x ∈ D i
  · obtain ⟨i, hi⟩ := hi
    rw [hF.2.2.2 i l m hlm x hi, abs_zero]
    exact abs_nonneg _
  · have heq (j : L) := (hF.eventuallyEq_outside hD (not_exists.mp hi) j).fderiv_eq (𝕜 := ℝ)
    simp only [planarGradient, heq, le_refl]

/-- The open collar can be chosen to avoid every inactive lattice even
when the real branches are smooth only on their supplied open domains. -/
theorem exists_inactive_connected_collar
    {L : Type*} [Fintype L] {A O : Set (ℝ × ℝ)}
    (hAc : IsCompact A) (hAconn : IsConnected A) (hO : IsOpen O) (hAO : A ⊆ O)
    (u : L → (ℝ × ℝ) → ℝ) (hu : ∀ l, ContDiffOn ℝ ∞ (u l) O)
    (active : L) {h : ℝ} (hh : 0 < h) (θ : L → ℝ)
    (havoid : ∀ l, l ≠ active → Disjoint (u l '' A) (shiftedLattice h (θ l))) :
    ∃ C : Set (ℝ × ℝ), IsCompact C ∧ IsConnected C ∧ C ∈ 𝓝ˢ A ∧ C ⊆ O ∧
      ∀ l, l ≠ active → Disjoint (u l '' C) (shiftedLattice h (θ l)) := by
  classical
  let V : Set (ℝ × ℝ) := O ∩ ⋂ l : L,
    if l = active then O else O ∩ (u l) ⁻¹' (shiftedLattice h (θ l))ᶜ
  have hVo : IsOpen V := hO.inter (isOpen_iInter_of_finite fun l => by
    by_cases hl : l = active
    · simpa only [ite_eq_left hl] using hO
    · simpa only [ite_eq_right hl] using (hu l).continuousOn.isOpen_inter_preimage hO
        (isClosed_shiftedLattice hh (θ l)).isOpen_compl)
  have hAV : A ⊆ V := by
    intro x hx
    refine ⟨hAO hx, mem_iInter.mpr fun l => ?_⟩
    by_cases hl : l = active
    · simpa only [ite_eq_left hl] using hAO hx
    · simp only [ite_eq_right hl, mem_inter_iff, mem_preimage, mem_compl_iff]
      exact ⟨hAO hx, fun h => Set.disjoint_left.mp (havoid l hl) ⟨x, hx, rfl⟩ h⟩
  obtain ⟨C, hCc, hCconn, hCA, hCV⟩ :=
    exists_compact_connected_neighborhood hAc hAconn hVo hAV
  refine ⟨C, hCc, hCconn, hCA, (fun x hx => (hCV hx).1), ?_⟩
  intro l hl
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hy
  have hv := mem_iInter.mp (hCV hx).2 l
  simp only [ite_eq_right hl, mem_inter_iff, mem_preimage, mem_compl_iff] at hv
  exact hv.2 hy

/-- A common eventual width works for all disks and all inactive
coordinates. The old coordinates need only be smooth off the filling
interiors; on the collars their actual real staircase branches are supplied. -/
theorem eventually_exists_filled_coordinates
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
    (v : ℝ → L → (ℝ × ℝ) → ℝ) (Ω : Set (ℝ × ℝ))
    (hv : ∀ δ, 0 < δ → δ < h / 4 → ∀ l x, x ∈ Ω →
      (∀ i, x ∉ D i) → ContDiffAt ℝ ∞ (v δ l) x)
    (hbranch : ∀ δ i l, EqOn (v δ l)
      (fun x => shiftedStaircase h δ (θ l) (u i l x)) (O i)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : L → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily D Ω (v δ) F := by
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
    have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
    exact hp.and ((eventually_lt_nhds (by positivity : (0 : ℝ) < h / 4)).filter_mono
      nhdsWithin_le_nhds)
  filter_upwards [hconst, hsmall] with δ hδ hδsmall
  let w : I → L → (ℝ × ℝ) → ℝ := fun i l x =>
    shiftedStaircase h δ (θ l) (u i l x)
  let c : I → L → ℝ := fun i l => w i l (z i)
  have hlocal (i : I) : ∃ g : L → (ℝ × ℝ) → ℝ,
      (∀ l, ContDiff ℝ ∞ (g l)) ∧
      (∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l, g l x = v δ l x) ∧
      ∀ l m, l ≠ m → ∀ x,
        planarWedge (planarGradient (g l) x) (planarGradient (g m) x) = 0 := by
    have hfrontInt : frontier (D i) ⊆ interior (C i) :=
      subset_interior_iff_mem_nhdsSet.mpr (hCfront i)
    have hw : ContDiffOn ℝ ∞ (w i (active i)) (interior (C i)) :=
      (contDiff_shiftedStaircase hh hδsmall.1 hδsmall.2 (θ (active i))).comp_contDiffOn
        ((hu i (active i)).mono (interior_subset.trans (hCO i)))
    obtain ⟨g, hg, hgw, _, hzero⟩ := exists_rank_one_collar_extension (active i)
      isOpen_interior isClosed_frontier hfrontInt (w i) (c i) hw
      (fun l hl x hx => hδ i l hl x (interior_subset hx))
    refine ⟨g, hg, ?_, hzero⟩
    filter_upwards [hgw, hCfront i] with x hx hxC l
    exact (hx l).trans ((hbranch δ i l ((hCO i) hxC)).symm)
  choose g hg hagree hzero using hlocal
  have hpair : Pairwise (Disjoint on D) := fun i j hij =>
    (hdisj hij).mono subset_closure subset_closure
  let F : L → (ℝ × ℝ) → ℝ := fun l => patchOpenRegions D (fun i => g i l) (v δ l)
  have hagreeAt (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (D i)) (l : L) :
      g i l =ᶠ[𝓝 x] v δ l :=
    ((hagree i).filter_mono (nhds_le_nhdsSet hx)).mono (fun _ h => h l)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro l
    exact contDiffOn_patchOpenRegions D (fun i => g i l) (v δ l) hD hpair
      (hv δ hδsmall.1 hδsmall.2 l)
      (fun i _ _ => (hg i l).contDiffAt)
      (fun i x hx => hagreeAt i x hx.2 l)
  · intro l x hx
    exact patchOpenRegions_eq_of_notMem D (fun i => g i l) (v δ l) hx
  · intro i
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    have houtside : ∀ j, x ∉ D j := by
      intro j hxj
      by_cases hji : j = i
      · subst j
        have hxnot := hx
        rw [(hD i).frontier_eq] at hxnot
        exact hxnot.2 hxj
      · exact Set.disjoint_left.mp (hdisj hji) (subset_closure hxj)
          (frontier_subset_closure hx)
    apply eventually_all.mpr
    intro l
    exact patchOpenRegions_eventuallyEq_outside D (fun j => g j l) (v δ l) hD houtside
      (fun j hj => hagreeAt j x hj l)
  · intro i l m hlm x hx
    exact patchOpenRegions_wedges_eq_zero_inside D g (v δ) hD hpair
      (fun i l m hlm x _ => hzero i l m hlm x) hx l m hlm

/-- A physical Jordan disk in the real coordinates used for the energy
and patching calculation. -/
def realJordanInterior (H : ℂ ≃ₜ ℂ) : Set (ℝ × ℝ) :=
  Complex.equivRealProdCLM '' jordanInterior H

theorem realJordanInterior_geometry (H : ℂ ≃ₜ ℂ) :
    IsOpen (realJordanInterior H) ∧
      IsCompact (frontier (realJordanInterior H)) ∧
      IsConnected (frontier (realJordanInterior H)) := by
  let e := Complex.equivRealProdCLM.toHomeomorph
  have hfront : frontier (realJordanInterior H) = e '' frontier (jordanInterior H) :=
    (e.image_frontier _).symm
  refine ⟨e.isOpenMap _ (jordanInterior_isOpen H), ?_, ?_⟩
  · rw [hfront]
    exact ((isCompact_closure_jordanInterior H).of_isClosed_subset
      isClosed_frontier frontier_subset_closure).image e.continuous
  · rw [hfront]
    exact (isConnected_frontier_jordanInterior H).image e e.continuous.continuousOn

theorem pairwise_disjoint_realJordan_closures
    {I : Type*} (H : I → ℂ ≃ₜ ℂ)
    (hH : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    Pairwise (Disjoint on fun i => closure (realJordanInterior (H i))) := by
  let e := Complex.equivRealProdCLM.toHomeomorph
  intro i j hij
  change Disjoint (closure (e '' jordanInterior (H i)))
    (closure (e '' jordanInterior (H j)))
  rw [← e.image_closure, ← e.image_closure]
  exact Set.disjoint_image_of_injective e.injective (hH hij)

/-- Concrete finite-Jordan-disk version of the filling theorem. The
compact connected collars and all inactive constants are constructed. -/
theorem eventually_exists_filled_jordan_coordinates
    {I L : Type*} [Fintype I] [Fintype L]
    (H : I → ℂ ≃ₜ ℂ)
    (hH : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hHO : ∀ i, frontier (realJordanInterior (H i)) ⊆ O i)
    (u : I → L → (ℝ × ℝ) → ℝ)
    (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (active : I → L) {h : ℝ} (hh : 0 < h) (θ : L → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (realJordanInterior (H i))) (shiftedLattice h (θ l)))
    (v : ℝ → L → (ℝ × ℝ) → ℝ) (Ω : Set (ℝ × ℝ))
    (hv : ∀ δ, 0 < δ → δ < h / 4 → ∀ l x, x ∈ Ω →
      (∀ i, x ∉ realJordanInterior (H i)) → ContDiffAt ℝ ∞ (v δ l) x)
    (hbranch : ∀ δ i l, EqOn (v δ l)
      (fun x => shiftedStaircase h δ (θ l) (u i l x)) (O i)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : L → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily (fun i => realJordanInterior (H i)) Ω (v δ) F :=
  eventually_exists_filled_coordinates (fun i => realJordanInterior (H i))
    (fun i => (realJordanInterior_geometry (H i)).1)
    (pairwise_disjoint_realJordan_closures H hH)
    (fun i => (realJordanInterior_geometry (H i)).2.1)
    (fun i => (realJordanInterior_geometry (H i)).2.2)
    O hO hHO u hu active hh θ havoid v Ω hv hbranch

/-- Once the grid and collars are fixed, a frequently good actual cost
has an arbitrarily late index at which all smooth fillings are possible. -/
theorem exists_good_width_filled_coordinates
    {I L : Type*} (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ))
    (v : ℝ → L → (ℝ × ℝ) → ℝ) {h : ℝ} (hh : 0 < h)
    (hfill : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : L → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily D Ω (v δ) F)
    (cost : ℕ → ℝ) {η : ℝ} (hcost : ∃ᶠ k in atTop, cost k < η)
    (K : ℕ) :
    ∃ (k : ℕ) (F : L → (ℝ × ℝ) → ℝ),
      K ≤ k ∧ cost k < η ∧ IsFilledCoordinateFamily D Ω (v (staircaseWidth h k)) F := by
  have hwidth : Tendsto (staircaseWidth h) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨staircaseWidth_tendsto_zero h,
      Filter.Eventually.of_forall (staircaseWidth_pos hh)⟩
  obtain ⟨k, hgood, hlate, F, hF⟩ :=
    (hcost.and_eventually ((eventually_ge_atTop K).and (hwidth.eventually hfill))).exists
  exact ⟨k, F, hlate, hgood, hF⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
