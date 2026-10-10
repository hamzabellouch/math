import OAI.Probability.SLE.Geometry.UnitWindowPlanarExit

namespace OAI

/-! The published finite-window conformal exit input, proved from the
original planar Wiener law and bounded harmonic localization. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target RibbonCoordinates

lemma unitWindowExitArc_subset_planar (D : Set ℂ) (g : ℂ → ℂ) (w : ℂ) (positive : Bool) :
    unitWindowExitArc D g w (if positive then 1 else -1) ⊆
      planarHalfPlaneExitArc D g w 1 positive := by
  rintro b ⟨τ,hτ,x,hx,hl⟩
  obtain ⟨hS,hS1,hp,he⟩ := unitWindowFirstExit_planar hτ
  refine ⟨unitWindowStop τ,hS,hS1,hp,he,x,?_,?_⟩
  · cases positive <;> simp only [Bool.false_eq_true,↓reduceIte] at hx ⊢ <;> linarith
  · exact (unitWindow_map_limit_iff w b g hτ.1 (x:ℂ)).mp hl

theorem actual_halfPlaneConformalExitLaw : PublishedHalfPlaneConformalExitLaw := by
  intro W hW D g f hD _hDH hg hf hgH hfD hfg _hgf w hw
  refine ⟨?_,?_,?_⟩
  · have hl := halfPlane_finite_exit_limit W hW hD hg hf hgH hfD hfg w hw 1
    filter_upwards [hl] with b hb
    intro τ hτ
    obtain ⟨hS,hS1,hp,he⟩ := unitWindowFirstExit_planar hτ
    obtain ⟨x,hx,hm⟩ := hb (unitWindowStop τ) hS hS1 hp he
    exact ⟨x,hx,(unitWindow_map_limit_iff w b g hτ.1 (x:ℂ)).mpr hm⟩
  · have hh := (measure_mono (unitWindowExitArc_subset_planar D g w false)).trans
      (planarHalfPlaneExitArc_bound W hW hD w hw hg hgH 1 false)
    simpa only [Bool.false_eq_true,↓reduceIte,halfPlaneExitWeight] using hh
  · have hh := (measure_mono (unitWindowExitArc_subset_planar D g w true)).trans
      (planarHalfPlaneExitArc_bound W hW hD w hw hg hgH 1 true)
    simpa only [↓reduceIte,halfPlaneExitWeight] using hh

end SLEExactGauge

end

end OAI
