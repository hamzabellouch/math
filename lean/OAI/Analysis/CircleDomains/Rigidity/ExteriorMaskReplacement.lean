import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleFillings

namespace OAI

/-! Values outside a closed mask can be replaced by a constant on a
closed set separated from that mask and the retained core. This supplies
honest real branches for absent coordinates without changing any masked
differential, any masked cutoff cost, or any retained value. -/

open Set Filter Function MeasureTheory Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def exteriorMaskReplacement (W : Set (ℝ × ℝ)) (c : UnitAddCircle)
    (f : (ℝ × ℝ) → UnitAddCircle) : (ℝ × ℝ) → UnitAddCircle :=
  W.piecewise (fun _ => c) f

 theorem exteriorMaskReplacement_eventuallyEq
    {W A : Set (ℝ × ℝ)} (hW : IsClosed W) (hWA : Disjoint W A)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle) :
    exteriorMaskReplacement W c f =ᶠ[𝓝ˢ A] f := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  have hxW : x ∉ W := fun h => Set.disjoint_left.mp hWA h hx
  filter_upwards [hW.isOpen_compl.mem_nhds hxW] with y hy
  exact piecewise_eq_of_notMem W _ _ hy

 theorem exteriorMaskReplacement_smooth
    {W M G : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle)
    (hf : SmoothCircleOn f (G ∩ interior M)) :
    SmoothCircleOn (exteriorMaskReplacement W c f) (G ∩ interior M) := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  obtain ⟨u, hu, huf⟩ := smoothCircleOn_iff_local_lifts.mp hf x hx
  exact ⟨u, hu, huf.trans ((exteriorMaskReplacement_eventuallyEq hW hWM c f).filter_mono
    (nhds_le_nhdsSet (interior_subset hx.2))).symm⟩

 theorem exteriorMaskReplacement_gradient
    {W M : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle) {x : ℝ × ℝ} (hx : x ∈ M) :
    circleGradient (exteriorMaskReplacement W c f) x = circleGradient f x :=
  circleGradient_congr_of_eventuallyEq
    ((exteriorMaskReplacement_eventuallyEq hW hWM c f).filter_mono (nhds_le_nhdsSet hx))

 theorem exteriorMaskReplacement_memLp
    {W M G : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (hG : MeasurableSet G) (hM : MeasurableSet M) (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle)
    (hf : MeasureTheory.MemLp (circleGradient f) 2 (MeasureTheory.volume.restrict (G ∩ M))) :
    MeasureTheory.MemLp (circleGradient (exteriorMaskReplacement W c f)) 2
      (MeasureTheory.volume.restrict (G ∩ M)) := by
  apply MemLp.ae_eq (hf_Lp := hf)
  filter_upwards [MeasureTheory.ae_restrict_mem₀
    ((hG.inter hM).nullMeasurableSet)] with x hx
  · exact (exteriorMaskReplacement_gradient hW hWM c f hx.2).symm

 theorem exteriorMaskReplacement_cutoff_gradient
    {W M : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (P : ℝ → ℝ) {x : ℝ × ℝ} (hx : x ∈ M) :
    circleGradient (circleCutoff (exteriorMaskReplacement W c f) χ P) x =
      circleGradient (circleCutoff f χ P) x := by
  apply circleGradient_congr_of_eventuallyEq
  filter_upwards [(exteriorMaskReplacement_eventuallyEq hW hWM c f).filter_mono
    (nhds_le_nhdsSet hx)] with y hy
  simp only [circleCutoff, cutoffStaircase, hy]

 theorem exteriorMaskReplacement_masked_wedges
    {n : ℕ} (W M : Fin n → Set (ℝ × ℝ)) (hW : ∀ l, IsClosed (W l))
    (hWM : ∀ l, Disjoint (W l) (M l)) (c : Fin n → UnitAddCircle)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (N : ℕ) (δ : ℝ) (θ : Fin n → ℝ) :
    maskedCircleWedges M (circleCutoffFamily
      (fun l => exteriorMaskReplacement (W l) (c l) (f l)) χ N δ θ) =
      maskedCircleWedges M (circleCutoffFamily f χ N δ θ) := by
  funext x
  unfold maskedCircleWedges
  apply Finset.sum_congr rfl
  intro p _
  rw [abs_wedge_indicators, abs_wedge_indicators]
  by_cases hx : x ∈ M (upperPair p).1 ∩ M (upperPair p).2
  · simp only [indicator_of_mem hx, circleCutoffFamily]
    rw [exteriorMaskReplacement_cutoff_gradient (hW _) (hWM _) _ _ _ _ hx.1,
      exteriorMaskReplacement_cutoff_gradient (hW _) (hWM _) _ _ _ _ hx.2]
  · simp only [indicator_of_notMem hx]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
