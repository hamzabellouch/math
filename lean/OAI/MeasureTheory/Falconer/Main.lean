import OAI.MeasureTheory.Falconer.Shells.TwoRootApproximations
import OAI.MeasureTheory.Falconer.Estimates.SourceAssemblyParameters
import OAI.MeasureTheory.Falconer.Frostman.NormalizedRootSetup
import OAI.MeasureTheory.Falconer.Shells.ShellReconstruction

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem manuscript_main (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    0 < volume (distanceSet E) := by
  obtain ⟨δ,s,hδ,hδ1,hs,Q,hQ,hcent,μ,ν,_,_,hμE,hνE,_,_,hμQ,hνQ,
    C,hC,hball₀,hball₁,K,hK,hμrad,hνrad⟩ := exists_normalized_root_setup E hE hd
  obtain ⟨β,lam,sig,kap,hβ,hlam,hlamδ,hsig,hkap,hkapβ,hgap,hratio⟩ :=
    exists_source_assembly_parameters hδ hδ1
  obtain ⟨Ψ,hΨ,hpos,hsupp,hone⟩ := exists_assembly_shell_cutoff
  have hp1 : 1 < 1+δ/8 := by linarith
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hμrad' : ∀ᵐ x ∂(μ:Measure Plane),
      sourceDensityNorm (1+δ/8) ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K := by
    filter_upwards [(μ:Measure Plane).support_mem_ae] with x hx
    exact hμrad x hx
  have hνrad' : ∀ᵐ y ∂(ν:Measure Plane),
      sourceDensityNorm (1+δ/8) ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K := by
    filter_upwards [(ν:Measure Plane).support_mem_ae] with y hy
    exact hνrad y hy
  have hlo : 100 ≤ dist (Q 0).center (Q 1).center := by rw [hcent]; norm_num
  have hhi : dist (Q 0).center (Q 1).center ≤ 2000 := by rw [hcent]; norm_num
  obtain ⟨hτ,happrox⟩ := two_root_has_shell_approximations Q hQ hlo hhi μ ν hμQ hνQ
    hδ hδ1 hβ hlam hlamδ hsig hkap hkapβ hgap hratio hC.le hC.le hball₀ hball₁
    hpq hK hμrad' hνrad' hΨ hpos hsupp hone
  have hac := shell_criterion ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩ happrox
  have hsep : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane),
      90 ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ 2010 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμQ,
      Measure.quasiMeasurePreserving_snd.ae hνQ] with z hx hy
    exact separated_unit_roots_distance Q hQ hlo hhi z.1 z.2 hx hy
  have hcompact : IsCompact ((fun x : Plane => s • x) '' E) := hE.image (by fun_prop)
  have hcarry₀ : (μ:Measure Plane) ((fun x : Plane => s • x) '' E)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hμE) (μ:Measure Plane).support_mem_ae
  have hcarry₁ : (ν:Measure Plane) ((fun x : Plane => s • x) '' E)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hνE) (ν:Measure Plane).support_mem_ae
  apply distanceSet_positive_of_dilate E hs
  exact positive_distance_volume_of_weighted_ac (μ:Measure Plane) (ν:Measure Plane)
    hcompact hcarry₀ hcarry₁ (by norm_num : (0:ℝ) < 90) (by norm_num : (0:ℝ) < 2010) hsep hac

theorem mainTarget_proved : MainTarget := manuscript_main

end PlanarFalconer

end OAI
