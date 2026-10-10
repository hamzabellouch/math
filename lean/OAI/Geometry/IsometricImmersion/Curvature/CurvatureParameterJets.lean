import OAI.Geometry.IsometricImmersion.Volterra.VolterraParameterJets

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem iteratedDeriv_eq_of_derivative_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) (H : ℕ → ℝ → E)
    (hd : ∀ n y, y ∈ s → HasDerivAt (H n) (H (n + 1) y) y) :
    ∀ n y, y ∈ s → iteratedDeriv n (H 0) y = H n y := by
  intro n
  induction n with
  | zero => intro y hy; simp only [iteratedDeriv_zero]
  | succ n hn =>
      intro y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n (H 0) =ᶠ[𝓝 y] H n := by
        filter_upwards [hs.mem_nhds hy] with t ht
        exact hn t ht
      exact ((hd n y hy).congr_of_eventuallyEq hev).deriv

theorem curvatureYDerivative_slice_hasDerivAt
    {K : Coord → ℝ} (hK : ContDiffOn ℝ ∞ K square)
    (n : ℕ) {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => curvatureYDerivative K n (coordinatePoint x t))
      (curvatureYDerivative K (n + 1) (coordinatePoint x y)) y := by
  have hd : DifferentiableAt ℝ (curvatureYDerivative K n) (coordinatePoint x y) :=
    ((curvatureYDerivative_smooth hK n).contDiffAt
      (coordinate_square_isOpen.mem_nhds (coordinatePoint_mem_square hx hy))).differentiableAt
        (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)

theorem coordinateCurvatureFamily_jet_apply
    {K : Coord → ℝ} (hK : ContDiffOn ℝ ∞ K square)
    (r : ℝ) (hr1 : r < 1) (n : ℕ) (x : Icc (-r) r)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv n (coordinateCurvatureFamily K r) y x =
      curvatureYDerivative K n (coordinatePoint x y) := by
  have heval := iteratedDeriv_clm_comp (ContinuousMap.evalCLM ℝ x) n
    ((coordinateCurvatureFamily_contDiffOn hK r hr1).contDiffAt
      (isOpen_Ioo.mem_nhds hy))
  have hev : (fun t => coordinateCurvatureFamily K r t x) =ᶠ[𝓝 y]
      (fun t => K (coordinatePoint x t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact coordinateCurvatureFamily_apply hK r hr1 ht x
  have hs := iteratedDeriv_eq_of_derivative_sequence isOpen_Ioo
    (fun j t => curvatureYDerivative K j (coordinatePoint x t))
    (fun j t ht => curvatureYDerivative_slice_hasDerivAt hK j
      (compact_x_mem_square_interval hr1 x) ht) n y hy
  calc
    iteratedDeriv n (coordinateCurvatureFamily K r) y x =
        iteratedDeriv n (fun t => coordinateCurvatureFamily K r t x) y := heval.symm
    _ = iteratedDeriv n (fun t => K (coordinatePoint x t)) y := hev.iteratedDeriv_eq n
    _ = curvatureYDerivative K n (coordinatePoint x y) := hs

theorem coordinateCurvatureFamily_jet_contDiffOn
    {K : Coord → ℝ} (hK : ContDiffOn ℝ ∞ K square)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ContDiffOn ℝ ∞ (intervalFamilyJet r hr (coordinateCurvatureFamily K r) n)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  have hmem : MapsTo (fun p : ℝ × ℝ => coordinatePoint p.1 p.2)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) square := by
    intro p hp
    exact coordinatePoint_mem_square
      ⟨(neg_lt_neg hr1).trans hp.1.1, hp.1.2.trans hr1⟩ hp.2
  have hc := (curvatureYDerivative_smooth hK n).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  unfold intervalFamilyJet
  rw [intervalExtension_apply_of_mem r hr _ ⟨hp.1.1.le, hp.1.2.le⟩]
  exact coordinateCurvatureFamily_jet_apply hK r hr1 n _ hp.2

end SmoothLocal.ODE

end

end OAI
