import OAI.Analysis.CircleDomains.Sobolev.CircleFilledEnergy

namespace OAI

/-!
# Filling the actual descended circle cutoff

The collar functions are genuine local lifts of the original circle
coordinates. On the one-plateau of the cutoff their staircases project
to the actual modified maps. Smooth rank-one filling therefore applies
to those maps, rather than to a separately specified surrogate.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem eventually_fill_actual_circle_cutoff
    {I L : Type*} [Fintype I] [Fintype L]
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G : Set (ℝ × ℝ)}
    (f : L → (ℝ × ℝ) → UnitAddCircle) (hf : ∀ l, SmoothCircleOn (f l) G)
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (u : I → L → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → L) (θ : L → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : L → (ℝ × ℝ) → UnitAddCircle,
      IsFilledCircleFamily D (G ∪ ⋃ i, D i)
        (fun l => circleCutoff (f l) χ (shiftedStaircase (reciprocalGridStep N) δ (θ l))) F := by
  apply eventually_exists_filled_circle_coordinates D hD hdisj hfrontc hfrontconn
    O hO hDO u hu active (reciprocalGridStep_pos N) θ havoid
  · intro δ hδ hδh l z hz a ha
    have hzG : z ∈ G := hz.1.resolve_right hz.2
    exact smoothCircleOn_reciprocal_cutoff (hf l) χ hχ N hδ hδh (θ l) z hzG a ha
  · intro δ i l x hx
    have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ l) (r + 1) =
        shiftedStaircase (reciprocalGridStep N) δ (θ l) r + 1 := by
      simpa only [reciprocalGridStep, Nat.cast_succ] using
        shiftedStaircase_add_one (Nat.succ_pos N) δ (θ l) r
    have heq := circleCutoff_eq_lift (f l) χ hP (hproj i l x hx)
    exact (congrArg ((↑) : ℝ → UnitAddCircle)
      (cutoffStaircase_of_one (u := u i l)
        (P := shiftedStaircase (reciprocalGridStep N) δ (θ l)) (hχone i x hx))).symm.trans heq.symm

/-- The actual filling agrees with the original circle coordinates on
a full neighborhood of every retained closed core avoiding the disks. -/
theorem IsFilledCircleFamily.eventuallyEq_original_on_core
    {I L : Type*} [Fintype I] [Fintype L]
    {D : I → Set (ℝ × ℝ)} {Ω K : Set (ℝ × ℝ)}
    (hD : ∀ i, IsOpen (D i)) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (f : L → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (P : L → ℝ → ℝ) (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    {F : L → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsFilledCircleFamily D Ω (fun l => circleCutoff (f l) χ (P l)) F) :
    ∀ᶠ x in 𝓝ˢ K, ∀ l, F l x = f l x := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  have hzero := hχzero.filter_mono (nhds_le_nhdsSet hx)
  apply eventually_all.mpr
  intro l
  filter_upwards [hF.eventuallyEq_outside hD (hKD x hx) l, hzero] with y hy hχy
  exact hy.trans (circleCutoff_eq_of_zero (f l) χ (P l) hχy)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
