import Mathlib
import OAI.Geometry.SmoothYau.NodalMeasure.ExistsSupportedBoxNodalQuasimodes
import OAI.Geometry.SmoothYau.Smoothness.SourceSignBox
import OAI.Geometry.SmoothYau.Smoothness.ThreeCoupledCleanChartJets

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
open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_spherical_chart_quasimodes
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    (A : ℝ) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
        (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
      ∀ m D : ℕ, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
            ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*(n:ℝ)^(j+4)*
              Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x)) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
                (n:ℝ)*(n+2)*u y) x‖ ≤ C*((n:ℝ)^(D+1))⁻¹*
              Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x))) ∧
          (∀ y ∈ sphericalExceptionalInChart φ n,
            1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
              (((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
            (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
            (fun a => ε/((n:ℝ)*ℓ a.val))
            (((roundPower sourceAxisOne sourceAxisTwo n ∘
              (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal (A*(n:ℝ)) < 36*Measure.hausdorffMeasure 2
            ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩
              {x | ((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) (normalWaveEquiv x)=0}) := by
  let G := sphereChartMetric g sourcePole
  let K := sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo s
  let O := {y | sphericalRadius sourceAxisOne sourceAxisTwo
    ((chartAt (Euclidean 3) sourcePole).symm y) < r}
  have hs : s < 1 := by linarith
  have hK : IsCompact K := sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole hs
  have hO : IsOpen O := sphericalCoverage_open sourcePole sourceAxisOne sourceAxisTwo r
  have hKO : K ⊆ O := sphericalCoverage_subset_open sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole hs hsr
  obtain ⟨ε,hε,hε1,p₀,hp₀,hproduce⟩ :=
    exists_supported_box_nodal_quasimodes_subregions G hK hO hKO
  let a := p₀/(16*ε)
  have ha : 0 < a := div_pos hp₀ (mul_pos (by norm_num) hε)
  obtain ⟨φ,hφ,hsp,hclose,hin,hout,hnc,hcrit,hinside,hmass⟩ :=
    exists_global_spherical_wave_profile g₀ hg₀ g hg t ⟨ht,by linarith⟩ (A/a) zero_lt_one
  let ψ := φ ∘ (chartAt (Euclidean 3) sourcePole).symm
  have hψ : ContDiff ℝ ∞ ψ := spherical_chart_pullback_smooth hφ sourcePole
  have hKP : K ⊆ sourceProfileCoverage := sphericalCoverage_mono sourcePole sourceAxisOne sourceAxisTwo
    (by linarith)
  have hIK : normalWaveEquiv '' Box.Icc sourceSignBox ⊆ K := by
    intro y hy
    apply (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole hs y).mpr
    exact ((sourceSignBox_band y hy).2).le.trans (by linarith)
  obtain ⟨partition,hπ,ℓ,hℓ,hproduce⟩ := hproduce ψ hψ (fun x hx => hnc x (hKP hx))
    (fun x hx => hcrit x (hKP hx)) sourceSignBox hIK
  have hmass' : A < a*(∫ x in Box.Icc sourceSignBox, profileFrequencyScale G ψ (normalWaveEquiv x)) :=
    (div_lt_iff₀ ha).mp hmass |>.trans_eq (mul_comm _ _)
  have hK' : IsCompact (normalWaveEquiv.symm '' K) := hK.image normalWaveEquiv.symm.continuous
  obtain ⟨R,hR⟩ := hK'.isBounded.subset_closedBall (0 : Fin 3 → ℝ)
  let S := closedBall (0 : Fin 3 → ℝ) R
  obtain ⟨T₀,hT₀,H,hH,hinputs⟩ := spherical_background_input_bounds hφ (isCompact_closedBall (0 : Fin 3 → ℝ) R)
  refine ⟨φ,hφ,hin,hout,partition,hπ,ℓ,hℓ,ε,hε,?_⟩
  intro m D
  obtain ⟨c₀,hc₀,C,hC,N,hN,hproduce⟩ := hproduce m D T₀ H hT₀.le hH.le
  refine ⟨C,hC,?_⟩
  have hfreq : ∀ᶠ n : ℕ in atTop, N ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually (eventually_ge_atTop N)
  have hsign := spherical_background_sign_small hφ.continuous sourceSignBox
    (fun y hy => (sourceSignBox_band y hy).2.trans (by linarith)) hin hc₀
  have hexcept := spherical_exceptional_eventually_coverage hφ.continuous
    (show 0 < t by linarith) hts hs hout
  filter_upwards [hfreq,eventually_ge_atTop (2:ℕ),hsign,hexcept] with n hn hn2 hsign hexcept
  obtain ⟨hW,hW0,hwjet,hlog⟩ := hinputs n hn2
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ := hproduce n hn S (convex_closedBall _ _)
    (sphericalExceptionalInChart φ n) (hexcept.trans hR) hexcept
    (roundPower sourceAxisOne sourceAxisTwo n ∘ (chartAt (Euclidean 3) sourcePole).symm)
    (spherical_chart_pullback_smooth (roundPower_smooth sourceAxisOne sourceAxisTwo n) sourcePole)
    (sphericalChartWeight φ n) hW hW0 (fun y _ => sphericalChartWeight_lower φ n y)
    (fun y hy => sphericalChartWeight_upper φ n y hy) hwjet hlog hsign
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le (hN.trans hn)
  have hle : A*(n:ℝ) ≤ a*(n:ℝ)*(∫ x in Box.Icc sourceSignBox,
      profileFrequencyScale G ψ (normalWaveEquiv x)) := by nlinarith [mul_pos (sub_pos.mpr hmass') hn0]
  exact ⟨u,hu,huc,hus,hder,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩


end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_spherical_global_quasimodes
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
        (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
      ∀ (ι : Type) [Fintype ι] (p : ι → Sphere 3) (K : ι → Set (Euclidean 3)),
        (∀ i, IsCompact (K i)) → ∀ m D : ℕ, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        ∃ u : Euclidean 3 → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
            ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
          (∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
            |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
            Real.sqrt (coordinateGradientPair g
              (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
              (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ)) ∧
          (∀ i, ∀ y ∈ K i, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
              (chartAt (Euclidean 3) (p i)).symm) y‖ ≤
              C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) (p i)).symm y) ∧
            ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
              (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
              sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
              (chartAt (Euclidean 3) (p i)).symm) y‖ ≤
              C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) (p i)).symm y)) ∧
          ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
            (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
            (fun a => ε/((n:ℝ)*ℓ a.val))
            (((roundPower sourceAxisOne sourceAxisTwo n ∘
              (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal (A*(n:ℝ)) < 36*Measure.hausdorffMeasure 2
            ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩
              {x | ((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨φ,hφ,hin,hout,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    exists_spherical_chart_quasimodes g₀ hg₀ g hg ht hts hsr hr A
  refine ⟨φ,hφ,hin,hout,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro ι _ p K hK m D
  obtain ⟨C₀,hC₀,hproduce⟩ := hproduce (max m 1) D
  have hbound (i : ι) := spherical_wave_background_chart_bounds g g₀ hg₀ hF hext hφ
    (fun q hq hz => hin q hz (hFt q hq)) (p i) (hK i) (by linarith : r<1) m D hC₀
  choose Cs hCs hb using hbound
  let C := 1+∑ i, Cs i
  have hC : 0 < C := by
    have hh : 0 ≤ ∑ i, Cs i := Finset.sum_nonneg (fun i _ => (hCs i).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hh
  have hCi (i : ι) : Cs i ≤ C := by
    have hh : Cs i ≤ ∑ j, Cs j := Finset.single_le_sum (fun j _ => (hCs j).le) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Cc,hCc,hcenter⟩ := spherical_wave_centered_first_jet g₀ hg₀
    (by linarith : r < 1) C₀ hC₀
  have hfreq : ∀ᶠ n : ℕ in atTop, max 1 (2*Cc) ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (max 1 (2*Cc)))
  have hcover := spherical_global_exceptional_coverage hφ.continuous
    (by linarith : 0 < t) (by linarith : t < 3/10) hout
  refine ⟨C,hC,?_⟩
  filter_upwards [hproduce,eventually_all.mpr hb,hfreq,hcover,eventually_ge_atTop (2:ℕ)]
    with n hproduce hb hfreq hcover hn
  obtain ⟨u,hu,hc,hs,hj,hjet,hscore,hnod⟩ := hproduce
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn1
  have hnC : 2*Cc ≤ (n:ℝ)^2 := by
    have hCc' := (le_max_right (1:ℝ) (2*Cc)).trans hfreq
    nlinarith
  have hcenter' := hcenter u hu hc hs φ n hn1
    (fun y j hj1 => (hj y j (hj1.trans (le_max_right _ _))).1)
  have hlow := spherical_global_jet_lower g g₀ hg₀ hin hFt hext hmetric hn Cc hnC hcover
    hu hc hcenter' hjet
  refine ⟨u,hu,hc,hs,hlow,?_,hscore,hnod⟩
  intro i y hy j hjm
  have hbd := hb i u hu hc hs (fun y j hjm => hj y j (hjm.trans (le_max_left _ _))) y hy j hjm
  exact ⟨hbd.1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hCi i) (by positivity)) (sphericalWeight_pos _ _ _).le),
    hbd.2.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCi i) (by positivity)) (by positivity))
        (sphericalWeight_pos _ _ _).le)⟩


end YauCounterexamples
end

end OAI
