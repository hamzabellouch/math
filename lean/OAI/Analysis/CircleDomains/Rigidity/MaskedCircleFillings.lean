import OAI.Analysis.CircleDomains.Topology.CircleCutoffFillings
import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleEnergy
import OAI.Analysis.CircleDomains.Rigidity.MaskedWedgeCost

namespace OAI

/-!
# Circle fillings with coordinate-specific masks

Real collar branches still give one simultaneous rank-one filling.
Smoothness is required only on each coordinate's own mask. The common
boundary agreement and zero-wedge identities hold on all filling disks.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def IsMaskedFilledCircleFamily {I : Type*} {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ)) (M : Fin n → Set (ℝ × ℝ))
    (v F : Fin n → (ℝ × ℝ) → UnitAddCircle) : Prop :=
  (∀ l, SmoothCircleOn (F l) (Ω ∩ interior (M l))) ∧
    IsFilledCircleFamily D ∅ v F

theorem eventually_exists_masked_filled_circle_coordinates
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
      (shiftedStaircase h δ (θ l) (u i l x) : UnitAddCircle) = v δ l x) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D Ω M (v δ) F := by
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
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
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

theorem eventually_fill_actual_masked_circle_cutoff
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G : Set (ℝ × ℝ)} (M : Fin n → Set (ℝ × ℝ))
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
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (fun l => circleCutoff (f l) χ (shiftedStaircase (reciprocalGridStep N) δ (θ l))) F := by
  apply eventually_exists_masked_filled_circle_coordinates D hD hdisj hfrontc hfrontconn
    O hO hDO u hu active (reciprocalGridStep_pos N) θ havoid
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

theorem IsMaskedFilledCircleFamily.masked_wedges_eq_zero
    {I : Type*} {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) {i : I} {z : ℝ × ℝ} (hz : z ∈ D i) :
    maskedCircleWedges M F z = 0 := by
  unfold maskedCircleWedges
  apply Finset.sum_eq_zero
  intro p _
  rw [abs_wedge_indicators]
  by_cases hm : z ∈ M (upperPair p).1 ∩ M (upperPair p).2
  · rw [indicator_of_mem hm, hF.2.2.2.2 i _ _ (upperPair_ne p) z hz, abs_zero]
  · rw [indicator_of_notMem hm]

theorem IsMaskedFilledCircleFamily.masked_wedges_eq_outside
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) (hD : ∀ i, IsOpen (D i))
    {z : ℝ × ℝ} (hz : ∀ i, z ∉ D i) : maskedCircleWedges M F z = maskedCircleWedges M v z := by
  have hgrad (l : Fin n) := circleGradient_congr_of_eventuallyEq (hF.2.eventuallyEq_outside hD hz l)
  unfold maskedCircleWedges
  apply Finset.sum_congr rfl
  intro p _
  rw [abs_wedge_indicators, abs_wedge_indicators]
  by_cases hm : z ∈ M (upperPair p).1 ∩ M (upperPair p).2
  · simp only [indicator_of_mem hm, hgrad]
  · simp only [indicator_of_notMem hm]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
