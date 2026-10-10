import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleFillings

namespace OAI

/-! Simultaneous real and circle fillings using the same rank-one collar
extensions. Exact real values are retained for the designated real coordinates. -/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem eventually_exists_mixed_filled_coordinates
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (active : I → Fin n) {h : ℝ} (hh : 0 < h) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice h (θ l)))
    (v : ℝ → Fin n → (ℝ × ℝ) → UnitAddCircle)
    (Ω : Set (ℝ × ℝ)) (M : Fin n → Set (ℝ × ℝ))
    (hv : ∀ δ, 0 < δ → δ < h / 4 → ∀ l,
      SmoothCircleOn (v δ l) ((Ω ∩ interior (M l)) \ ⋃ i, D i))
    (hbranch : ∀ δ i l x, x ∈ O i →
      (shiftedStaircase h δ (θ l) (u i l x) : UnitAddCircle) = v δ l x)
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (w : ℝ → J → (ℝ × ℝ) → ℝ)
    (hw : ∀ δ, 0 < δ → δ < h / 4 → ∀ j x, x ∈ Ω →
      (∀ i, x ∉ D i) → ContDiffAt ℝ ∞ (w δ j) x)
    (hwbranch : ∀ δ i j, EqOn (w δ j)
      (fun x => shiftedStaircase h δ (θ (ι j)) (u i (ι j) x)) (O i))
    (hwproj : ∀ δ j x, (w δ j x : UnitAddCircle) = v δ (ι j) x) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D Ω M (v δ) F ∧
      ∃ W : J → (ℝ × ℝ) → ℝ, IsFilledCoordinateFamily D Ω (w δ) W ∧
        ∀ j x, (W j x : UnitAddCircle) = F (ι j) x := by
  classical
  have hlocal := eventually_exists_rank_one_collar_families D hfrontc hfrontconn
    O hO hDO u hu active hh θ havoid
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < h / 4 :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < h / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hlocal, hsmall] with δ hδ hδsmall
  obtain ⟨g, hg, hagree, hzero⟩ := hδ
  have hpair : Pairwise (Disjoint on D) := fun i j hij =>
    (hdisj hij).mono subset_closure subset_closure
  have hproj (i : I) : ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
      (g i l x : UnitAddCircle) = v δ l x := by
    filter_upwards [hagree i, (hO i).mem_nhdsSet.mpr (hDO i)] with x hx hxO l
    exact (congrArg ((↑) : ℝ → UnitAddCircle) (hx l)).trans (hbranch δ i l x hxO)
  have hagreeAt (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (D i)) (l : Fin n) :
      (fun y => (g i l y : UnitAddCircle)) =ᶠ[𝓝 x] v δ l :=
    ((hproj i).filter_mono (nhds_le_nhdsSet hx)).mono (fun _ hy => hy l)
  let F : Fin n → (ℝ × ℝ) → UnitAddCircle := fun l =>
    patchOpenRegions D (fun i x => (g i l x : UnitAddCircle)) (v δ l)
  have hF : IsMaskedFilledCircleFamily D Ω M (v δ) F := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro l
      exact smoothCircleOn_patchOpenRegions D hD hpair (v δ l) (hv δ hδsmall.1 hδsmall.2 l)
        (fun i => g i l) (fun i => hg i l) (fun i x hx => hagreeAt i x hx.2 l)
    · intro l x hx
      exact False.elim hx
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
  let W : J → (ℝ × ℝ) → ℝ := fun j =>
    patchOpenRegions D (fun i => g i (ι j)) (w δ j)
  have hrealAt (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (D i)) (j : J) :
      g i (ι j) =ᶠ[𝓝 x] w δ j := by
    have he : ∀ᶠ y in 𝓝ˢ (frontier (D i)), g i (ι j) y = w δ j y := by
      filter_upwards [hagree i, (hO i).mem_nhdsSet.mpr (hDO i)] with y hy hyO
      exact (hy (ι j)).trans (hwbranch δ i j hyO).symm
    exact he.filter_mono (nhds_le_nhdsSet hx)
  refine ⟨F, hF, W, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    exact contDiffOn_patchOpenRegions D (fun i => g i (ι j)) (w δ j) hD hpair
      (hw δ hδsmall.1 hδsmall.2 j)
      (fun i _ _ => (hg i (ι j)).contDiffAt)
      (fun i x hx => hrealAt i x hx.2 j)
  · intro j x hx
    exact patchOpenRegions_eq_of_notMem D (fun i => g i (ι j)) (w δ j) hx
  · intro i
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    have houtside : ∀ k, x ∉ D k := by
      intro k hxk
      by_cases hki : k = i
      · subst k
        rw [(hD i).frontier_eq] at hx
        exact hx.2 hxk
      · exact Set.disjoint_left.mp (hdisj hki) (subset_closure hxk) (frontier_subset_closure hx)
    change ∀ᶠ y in 𝓝 x, ∀ j, W j y = w δ j y
    apply eventually_all.mpr
    intro j
    exact patchOpenRegions_eventuallyEq_outside D (fun k => g k (ι j)) (w δ j) hD houtside
      (fun k hk => hrealAt k x hk j)
  · intro i j k hjk x hx
    exact patchOpenRegions_wedges_eq_zero_inside D (fun i j => g i (ι j)) (w δ) hD hpair
      (fun i j k hjk x _ => hzero i (ι j) (ι k) (fun h => hjk (hι h)) x) hx j k hjk
  · intro j x
    by_cases hm : ∃ i, x ∈ D i
    · obtain ⟨i, hi⟩ := hm
      change ((patchOpenRegions D (fun i => g i (ι j)) (w δ j) x : ℝ) : UnitAddCircle) =
        patchOpenRegions D (fun i x => (g i (ι j) x : UnitAddCircle)) (v δ (ι j)) x
      exact (congrArg ((↑) : ℝ → UnitAddCircle)
        (patchOpenRegions_eq_of_mem D (fun i => g i (ι j)) (w δ j) hpair hi)).trans
        (patchOpenRegions_eq_of_mem D (fun i x => (g i (ι j) x : UnitAddCircle))
          (v δ (ι j)) hpair hi).symm
    · change ((patchOpenRegions D (fun i => g i (ι j)) (w δ j) x : ℝ) : UnitAddCircle) =
        patchOpenRegions D (fun i x => (g i (ι j) x : UnitAddCircle)) (v δ (ι j)) x
      exact (congrArg ((↑) : ℝ → UnitAddCircle)
        (patchOpenRegions_eq_of_notMem D (fun i => g i (ι j)) (w δ j) (not_exists.mp hm))).trans
        ((hwproj δ j x).trans
          (patchOpenRegions_eq_of_notMem D (fun i x => (g i (ι j) x : UnitAddCircle))
            (v δ (ι j)) (not_exists.mp hm)).symm)

theorem eventually_fill_actual_mixed_cutoff
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G : Set (ℝ × ℝ)} (hG : IsOpen G) (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (r : J → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (fun l => circleCutoff (f l) χ (shiftedStaircase (reciprocalGridStep N) δ (θ l))) F ∧
      ∃ W : J → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ
            (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)))) W ∧
        ∀ j x, (W j x : UnitAddCircle) = F (ι j) x := by
  refine eventually_exists_mixed_filled_coordinates D hD hdisj hfrontc hfrontconn
    O hO hDO u hu active (reciprocalGridStep_pos N) θ havoid
    (fun δ l => circleCutoff (f l) χ (shiftedStaircase (reciprocalGridStep N) δ (θ l)))
    (G ∪ ⋃ i, D i) M ?_ ?_ ι hι (fun δ j => cutoffStaircase (r j) χ
      (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)))) ?_ ?_ ?_
  · intro δ hδ hδh l z hz a ha
    have hzG : z ∈ G := hz.1.1.resolve_right hz.2
    exact smoothCircleOn_reciprocal_cutoff (hf l) χ hχ N hδ hδh (θ l) z ⟨hzG, hz.1.2⟩ a ha
  · intro δ i l x hx
    have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ l) (r + 1) =
        shiftedStaircase (reciprocalGridStep N) δ (θ l) r + 1 := by
      simpa only [reciprocalGridStep, Nat.cast_succ] using
        shiftedStaircase_add_one (Nat.succ_pos N) δ (θ l) r
    have heq := circleCutoff_eq_lift (f l) χ hP (hproj i l x hx)
    exact (congrArg ((↑) : ℝ → UnitAddCircle)
      (cutoffStaircase_of_one (u := u i l)
        (P := shiftedStaircase (reciprocalGridStep N) δ (θ l)) (hχone i x hx))).symm.trans heq.symm
  · intro δ hδ hδh j x hx houtside
    have hxG : x ∈ G := hx.resolve_right (fun hi => let ⟨i, hi⟩ := mem_iUnion.mp hi; houtside i hi)
    have hrc := (hr j x hxG).contDiffAt (hG.mem_nhds hxG)
    exact hrc.add (hχ.contDiffAt.mul
      (((contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh (θ (ι j))).contDiffAt.comp x hrc).sub hrc))
  · intro δ i j x hx
    rw [cutoffStaircase_of_one (hχone i x hx)]
    exact congrArg (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j))) (hreal i j hx).symm
  · intro δ j x
    have hP (t : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)) (t + 1) =
        shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)) t + 1 := by
      simpa only [reciprocalGridStep, Nat.cast_succ] using
        shiftedStaircase_add_one (Nat.succ_pos N) δ (θ (ι j)) t
    exact (circleCutoff_eq_lift (f (ι j)) χ hP (hrproj j x)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
