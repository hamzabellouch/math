import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.ExistsMetricSignQuasimodesSubregions
import OAI.Geometry.SmoothYau.Geometry.BoxProfileIntegralPos

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_supported_nodal_quasimodes_subregions
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ R : Set NormalWaveSpace, R ⊆ K →
        (∀ y ∈ R, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (J : Type) [Fintype J] (P Cₛ : J → Set (Fin 3 → ℝ)) (ℓ : J → ℝ),
        (∀ a, 0 < ℓ a) → (∀ a, IsOpen (P a)) → (∀ a, Convex ℝ (P a)) →
        (Pairwise fun a b => Disjoint (P a) (P b)) →
        (∀ a, MeasurableSet (Cₛ a)) → (∀ a, IsFiniteMeasure (volume.restrict (Cₛ a))) →
        (∀ a, normalWaveEquiv '' P a ⊆ R) →
        (∀ a, ∀ x ∈ Cₛ a, x ∈ P a ∧
          profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
          ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a)) ∈ P a) →
        0 < ∑ a, ℓ a*(volume (Cₛ a)).toReal →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            SignTests.signCertificate P (fun a => ε/(n*ℓ a)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            36*Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_metric_sign_quasimodes_subregions_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,C,hC,N,hN,?_⟩
  intro n hn S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog R hRK hb
    J _ P Cₛ ℓ hℓ hP hPc hPd hCₛ hfin hPK hregion hmass
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans hn)
  let d : J → ℝ := fun a => ε/(n*ℓ a)
  let ν : J → Measure NormalWaveSpace := fun a => coordinateRegionMeasure (Cₛ a)
  have hd : ∀ a, 0 < d a := fun a => div_pos hε (mul_pos hn0 (hℓ a))
  have hν : ∀ a, IsFiniteMeasure (ν a) := fun a => coordinateRegionMeasure_finite (Cₛ a)
  have htotal : (∑ a, (d a)⁻¹*(ν a univ).toReal) =
      (n/ε)*(∑ a, ℓ a*(volume (Cₛ a)).toReal) := by
    simp only [ν,coordinateRegionMeasure_univ,d,inv_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; ring
  have hpos : 0 < ∑ a, (d a)⁻¹*(ν a univ).toReal := by
    rw [htotal]; exact mul_pos (div_pos hn0 hε) hmass
  have hreg (a : J) : ∀ᵐ y ∂ν a, y ∈ R ∧ profileFrequencyScale g φ y ≤ ℓ a ∧
      ℓ a ≤ 2*profileFrequencyScale g φ y ∧
      ∀ j, packetAxisShift y n ε (ℓ a) j ∈ R := by
    apply coordinateRegionMeasure_ae (hCₛ a)
    intro x hx
    have hr := hregion a x hx
    refine ⟨hPK a ⟨x,hr.1,rfl⟩,hr.2.1,hr.2.2.1,?_⟩
    intro j
    have hh := hPK a ⟨x+Pi.single j (ε/(n*ℓ a)),hr.2.2.2 j,rfl⟩
    simpa only [normalWaveEquiv_axis_shift,packetAxisShift] using hh
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore⟩ := hdata n hn S hS E hES hEK w hw W hW hW0
    hWlower hWupper hwbound hlog R hRK hb J ℓ (fun a => (d a)⁻¹)
    (fun a => (inv_pos.mpr (hd a)).le) ν hν hpos hreg
  have hcore (a : J) (x) (hx : x ∈ Cₛ a) (j : Fin 3) :
      x ∈ P a ∧ x+Pi.single j (d a) ∈ P a :=
    ⟨(hregion a x hx).1,(hregion a x hx).2.2.2 j⟩
  have hsc := coordinate_region_score_le_certificate P Cₛ d hd hcore hν (hw.continuous.add hu.continuous)
  have hnod := coordinate_region_score_le_nodal P Cₛ d hd hP hPc hPd hcore hν (hw.continuous.add hu.continuous)
  have he : (p₀/2)*(∑ a, (d a)⁻¹*(ν a univ).toReal) =
      (p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal) := by rw [htotal]; ring
  rw [he] at hscore
  have hlt := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity :
    0 ≤ (p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal))).mpr hscore
  exact ⟨u,hu,huc,hus,hder,hjet,hlt.trans_le hsc,hlt.trans_le hnod⟩

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
open BoxIntegral

theorem exists_supported_box_nodal_quasimodes_subregions
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ K →
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
    (∀ J ∈ partition, 0 < ℓ J) ∧
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (∀ y ∈ normalWaveEquiv '' Box.Icc I, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(16*ε))*n*(∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x))) <
            SignTests.signCertificate
              (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
              (fun a => ε/(n*ℓ a.val)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(16*ε))*n*(∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x))) <
            36*Measure.hausdorffMeasure 2 ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_supported_nodal_quasimodes_subregions g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit I hIK
  let L : (Fin 3 → ℝ) → ℝ := fun x => profileFrequencyScale g φ (normalWaveEquiv x)
  have hL : Continuous L := Real.continuous_sqrt.comp
    ((continuous_profileFrequencyEnergy g hφ).comp normalWaveEquiv.continuous)
  have hL1 : ∀ x, 1 ≤ L x := fun x => profileFrequencyScale_ge_one g φ _
  obtain ⟨partition,hπ,ℓ,hℓ⟩ := exists_profile_box_partition I L hL.continuousOn
    (fun x _ => zero_lt_one.trans_le (hL1 x))
  let J := {J : Box (Fin 3) // J ∈ partition.boxes}
  let P : J → Set (Fin 3 → ℝ) := fun a => Box.Ioo a.val
  let Cₛ : J → Set (Fin 3 → ℝ) := fun a => Box.Icc (middleBox a.val)
  have hmass := middleBox_partition_mass I L hL.continuousOn partition hπ ℓ
    (fun a ha x hx => (hℓ a ha).2 x hx |>.2)
  have hmasspos : 0 < ∑ a : J, ℓ a.val*(volume (Cₛ a)).toReal := by
    exact (div_pos (box_profile_integral_pos I L hL.continuousOn (fun x _ => hL1 x)) (by norm_num)).trans_le hmass
  have hshifts : ∀ᶠ n : ℝ in atTop, ∀ a : J, ∀ x ∈ Cₛ a, ∀ j : Fin 3,
      x+Pi.single j (ε/(n*ℓ a.val)) ∈ P a := by
    rw [Filter.eventually_all]
    intro a
    exact middleBox_eventually_shift_mem a.val hε (hℓ a.val a.property).1
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.1 hshifts
  refine ⟨partition,hπ,ℓ,fun a ha => (hℓ a ha).1,?_⟩
  intro m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,C,hC,max N N₁,hN.trans (le_max_left _ _),?_⟩
  intro n hn S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog hb
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans ((le_max_left _ _).trans hn))
  have hPK (a : J) : normalWaveEquiv '' P a ⊆ normalWaveEquiv '' Box.Icc I := by
    rintro y ⟨x,hx,rfl⟩
    exact ⟨x,Box.le_iff_Icc.mp (partition.le_of_mem a.property) (Box.Ioo_subset_Icc a.val hx),rfl⟩
  have hregion (a : J) (x : Fin 3 → ℝ) (hx : x ∈ Cₛ a) :
      x ∈ P a ∧ profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a.val ∧
      ℓ a.val ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
      ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a.val)) ∈ P a := by
    have hxp := middleBox_Icc_subset a.val hx
    have hscale := (hℓ a.val a.property).2 x (Box.Ioo_subset_Icc a.val hxp)
    refine ⟨hxp,hscale.2,?_,hN₁ n ((le_max_right _ _).trans hn) a x hx⟩
    change ℓ a.val ≤ 2*L x
    linarith [hscale.1]
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ :=
    hdata n ((le_max_left _ _).trans hn) S hS E hES hEK w hw W hW hW0
      hWlower hWupper hwbound hlog (normalWaveEquiv '' Box.Icc I) hIK hb J P Cₛ (fun a => ℓ a.val)
      (fun a => (hℓ a.val a.property).1) (fun a => box_Ioo_open a.val)
      (fun a => box_Ioo_convex a.val) (partition_Ioo_disjoint I partition)
      (fun a => (middleBox a.val).measurableSet_Icc)
      (fun a => isFiniteMeasure_restrict.mpr ((middleBox a.val).measure_Icc_lt_top volume).ne)
      hPK hregion hmasspos
  have hle : (p₀/(16*ε))*n*(∫ x in Box.Icc I, L x) ≤
      (p₀/(2*ε))*n*(∑ a : J, ℓ a.val*(volume (Cₛ a)).toReal) := by
    calc
      _ = (p₀/(2*ε))*n*((∫ x in Box.Icc I, L x)/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  exact ⟨u,hu,huc,hus,hder,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩


end YauCounterexamples
end

end OAI
