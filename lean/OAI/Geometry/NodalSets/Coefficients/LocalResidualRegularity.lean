import OAI.Geometry.NodalSets.Elliptic.FiniteLinearity
import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
  {D : Set Coord} {m J K k0 : ℕ}

lemma sourceFlux_zero
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ) (i : Fin 4) :
    sourceFlux g w (fun _ ↦ 0) i = 0 := by
  funext x
  simp [sourceFlux,coordPartial]

lemma sourceFlux_eventuallyEq
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    {u v : Coord → ℂ} {x : Coord} (he : u =ᶠ[𝓝 x] v) (i : Fin 4) :
    sourceFlux g w u i =ᶠ[𝓝 x] sourceFlux g w v i := by
  filter_upwards [Filter.eventually_all.mpr (fun j ↦ coordPartial_eventuallyEq he j)] with z hz
  simp only [sourceFlux,hz]

lemma LocalCompactWaveData.supported_flux_smooth
    (a : LocalCompactWaveData g w S D m J K k0)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ a.E) (i : Fin 4) :
    ContDiff ℝ ∞ (sourceFlux g w u i) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport u
  · obtain ⟨hg,hw,_⟩ := a.germ x (hs hx)
    apply (sourceFlux_smooth_at a.G a.smooth_G a.W a.smooth_W u hu x
      (a.positive_G x) i).congr_of_eventuallyEq
    filter_upwards [hg,hw] with z hz hwz
    simp only [sourceFlux,sourcePrincipal,hz,hwz]
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hz : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    have he := sourceFlux_eventuallyEq g w hz i
    filter_upwards [he] with z hz
    simpa only [sourceFlux_zero,Pi.zero_apply] using hz

lemma LocalCompactWaveData.supported_residual_smooth
    (a : LocalCompactWaveData g w S D m J K k0)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ a.E)
    (hw : ∀ x ∈ tsupport u, w x ≠ 0) (lam : ℂ) :
    ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w u x+lam*u x) := by
  have hf (i : Fin 4) := a.supported_flux_smooth u hu hs i
  have hd : ContDiff ℝ ∞ (complexDivergence (sourceFlux g w u)) :=
    ContDiff.sum (fun i _ ↦ coordPartial_contDiff (hf i) i)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport u
  · have hwe := (a.germ x (hs hx)).2.1
    have hws : ContDiffAt ℝ ∞ w x := a.smooth_W.contDiffAt.congr_of_eventuallyEq hwe.symm
    exact (((Complex.ofRealCLM.contDiff.contDiffAt.comp x hws).inv
      (Complex.ofReal_ne_zero.mpr (hw x hx))).mul hd.contDiffAt).add
        (contDiffAt_const.mul hu.contDiffAt)
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    filter_upwards [he,sourceOperator_eventuallyEq g w he] with z hz ho
    simp only [ho,hz,sourceWeightedOperator_zero,Pi.zero_apply,mul_zero,add_zero]

theorem LocalCompactWaveData.wave_residual_regular
    (a : LocalCompactWaveData g w S D m J K k0) (hw : ∀ x ∈ a.E, w x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ t : a.cover.Parameter × Fin 3,
      (∀ i, ContDiff ℝ ∞ (sourceFlux g w (a.beams.wave (n:ℝ) t) i)) ∧
      ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w (a.beams.wave (n:ℝ) t) x+
        ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*a.beams.wave (n:ℝ) t x) := by
  filter_upwards [a.estimates] with n hn
  intro t
  have ht := hn t
  exact ⟨a.supported_flux_smooth _ ht.1 ht.2.2.1,
    a.supported_residual_smooth _ ht.1 ht.2.2.1 (fun x hx ↦ hw x (ht.2.2.1 hx)) _⟩

end
end Yau.Geometry

end OAI
