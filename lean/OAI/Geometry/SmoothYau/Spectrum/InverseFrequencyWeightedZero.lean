import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ExistsSphericalScalarProducer
import OAI.Geometry.SmoothYau.Geometry.ChartGradientProjectionCongrNhds

namespace OAI

noncomputable section
open Set Filter Function Manifold BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace
namespace YauCounterexamples

lemma inverseFrequency_weighted_zero (L C : ℝ) (h : ℕ) :
    Tendsto (fun n => (L*inverseFrequency n^(h+3))*(1+C)*(n:ℝ)^h) atTop (𝓝 0) := by
  have he : (fun n => L*(1+C)*inverseFrequency n^3) =ᶠ[atTop]
      (fun n => (L*inverseFrequency n^(h+3))*(1+C)*(n:ℝ)^h) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    symm
    calc
      _ = L*(1+C)*inverseFrequency n^3*((n:ℝ)⁻¹^h*(n:ℝ)^h) := by
        simp only [inverseFrequency,pow_add]; ring
      _ = _ := by rw [← mul_pow,inv_mul_cancel₀ hn0,one_pow,mul_one]
  apply Tendsto.congr' he
  simpa using (inverseFrequency_pow_zero 3 (by omega)).const_mul (L*(1+C))

local instance : Fact (Module.finrank ℝ (Euclidean 4) = 4) := ⟨by simp [Euclidean]⟩

lemma spherical_exterior_conjugating_margin
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    {r a b : ℝ} (hr0 : 0 < r) (hra : r < a) (hb0 : 0 ≤ b) (hb2 : b^2 < 1)
    {F : Set (Sphere 3)} (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {u : Euclidean 3 → ℝ} (huc : HasCompactSupport u)
    (hus : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r})
    (n : ℕ) (hn : 1 ≤ n) (w : Sphere 3 → ℝ)
    (hwl : ∀ q, 1/2 ≤ w q) (hwG : ∀ q, coordinateGradientPair g w w q ≤ (1-b^2)/16)
    (q : Sphere 3) (hqa : a ≤ sphericalRadius sourceAxisOne sourceAxisTwo q)
    (hqb : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ b) :
    let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
    U q^2*coordinateGradientPair g w w q < w q^2*coordinateGradientPair g U U q := by
  dsimp only
  have hgq := fun v z => (hext q (fun hf => (not_le_of_gt hra) (hqa.trans (hFr q hf))) v z).trans (hg₀ q v z)
  have he := spherical_wave_exterior_germ huc hus n (hra.le.trans hqa)
  rw [he.eq_of_nhds,coordinateGradientPair_congr_nhds_cutoff g he]
  apply roundPower_conjugating_margin g q hgq sourceAxisOne sourceAxisTwo n hn
    source_axes_orthonormal.1 source_axes_orthonormal.2.1 source_axes_orthonormal.2.2
    (t := b^2)
  · rw [Complex.normSq_eq_norm_sq,←sphericalRadius_eq_planar_norm]
    exact sq_pos_of_pos (hr0.trans_le (hra.le.trans hqa))
  · rw [Complex.normSq_eq_norm_sq,←sphericalRadius_eq_planar_norm]
    nlinarith [sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q]
  · exact hb2
  · exact hwl q
  · exact (hwG q).trans (by linarith)

lemma spherical_cutoff_control_bounds
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (β χ v : Sphere 3 → ℝ)
    (hχrange : ∀ q, χ q ∈ Icc (0:ℝ) 1) {η G b Λ : ℝ}
    (hηhalf : η < 1/2) (hvsmall : ∀ q, |v q-1| ≤ η)
    (hGl : G*η < 1/32) (hGgrad : G*η < (1-b^2)/16) (hb0 : 0 ≤ b)
    (hΛ : 1 ≤ Λ)
    (hctrl : ∀ q, |weightedLaplacian g β (cutoffFactor χ v) q| ≤ G*η ∧
      Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q) ≤ G*η) :
    (∀ q, 1/2 ≤ cutoffFactor χ v q ∧ cutoffFactor χ v q ≤ 2) ∧
    (∀ q, coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q ≤ (1-b^2)/16) ∧
    (∀ q, |Λ⁻¹*cutoffFactor χ v q*weightedLaplacian g β (cutoffFactor χ v) q| ≤ 1/16) := by
  let w := cutoffFactor χ v
  have hwsmall (q : Sphere 3) : |w q-1| ≤ 1/2 := by
    change |1+χ q*(v q-1)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (hχrange q).1]
    exact (mul_le_mul_of_nonneg_right (hχrange q).2 (abs_nonneg _)).trans
      (by simpa using (hvsmall q).trans hηhalf.le)
  have hwl (q : Sphere 3) : 1/2 ≤ w q := by have := (abs_le.mp (hwsmall q)).1; linarith
  have hwu (q : Sphere 3) : w q ≤ 2 := by have := (abs_le.mp (hwsmall q)).2; linarith
  have hwp (q : Sphere 3) : 0 < w q := by linarith [hwl q]
  refine ⟨fun q => ⟨hwl q,hwu q⟩,?_,?_⟩
  · intro q
    have hp0 := coordinateGradientPair_nonneg g w q
    have hs0 := Real.sqrt_nonneg (coordinateGradientPair g w w q)
    have hs2 := Real.sq_sqrt hp0
    have hsle : Real.sqrt (coordinateGradientPair g w w q) ≤ G*η := (hctrl q).2
    have hs1 : Real.sqrt (coordinateGradientPair g w w q) ≤ 1 := by
      calc
        _ ≤ (1-b^2)/16 := hsle.trans hGgrad.le
        _ ≤ 1/16 := div_le_div_of_nonneg_right (sub_le_self 1 (pow_nonneg hb0 2)) (by norm_num)
        _ ≤ 1 := by norm_num
    nlinarith
  · intro q
    have hΛ0 : 0 ≤ Λ⁻¹ := inv_nonneg.mpr (zero_le_one.trans hΛ)
    have hΛi : Λ⁻¹ ≤ 1 := by
      simpa using (inv_le_inv₀ (zero_lt_one.trans_le hΛ) (show (0:ℝ)<1 by norm_num)).mpr hΛ
    change |Λ⁻¹*w q*weightedLaplacian g β w q| ≤ _
    rw [abs_mul,abs_mul,abs_of_nonneg hΛ0,abs_of_pos (hwp q)]
    calc
      _ ≤ (1*2)*(G*η) := mul_le_mul (mul_le_mul hΛi (hwu q) (hwp q).le (by norm_num))
        (hctrl q).1 (abs_nonneg _) (by norm_num)
      _ ≤ 1/16 := by linarith

lemma cutoff_raw_bounded_by_near_one
    (χ v : Sphere 3 → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ χ)
    (hv : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v)
    (t : CoordinateTest (Euclidean 3) (Sphere 3)) (h : ℕ) {B D η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B) (hDB : D ≤ B)
    (hctrl : ∀ y ∈ t.compactSet, ∀ k ≤ h,
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘
        (chartAt (Euclidean 3) t.center).symm) y‖ ≤ D*η) :
    ∀ y ∈ t.compactSet, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (cutoffFactor χ v ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ 1+B := by
  intro y hy j hj
  have hw : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (cutoffFactor χ v) :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hnear (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ B :=
    (hctrl y hy k hk).trans ((mul_le_mul_of_nonneg_right hDB hη0).trans
      (by simpa using mul_le_mul_of_nonneg_left hη1 hB))
  exact raw_jets_of_near_one (chartAt (Euclidean 3) t.center).open_target (t.inTarget hy)
    (fun y hy => (contDiffAt_inChart hw t.center hy).contDiffWithinAt) h hB hnear j hj

theorem exists_spherical_exact_stage
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r a b : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r)
    (hra : r < a) (hab : a < b) (hb : b < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g N) :
    ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ᶠ n : ℕ in atTop, ∃ ĝ ∈ N, ∃ u : Sphere 3 → ℝ,
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ q, -laplaceBeltrami ĝ u q=sphereFrequency n*u q) ∧
      (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm) (chartAt (Euclidean 3) q q) ≠ 0) ∧
      (∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q →
        (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=roundPower sourceAxisOne sourceAxisTwo n q) ∧
      ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
        (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val)
        (fun j => ε/((n:ℝ)*ℓ j.val))
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) := by
  classical
  have hr0 : 0 < r := by linarith
  have hr : r < 3/10 := hra.trans (hab.trans hb)
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b < 1 := by linarith
  have hb2 : b^2 < 1 := by nlinarith
  have hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r :=
    fun q hq => (hFt q hq).le.trans (hts.le.trans hsr.le)
  obtain ⟨χ,hχ,hχrange,hχa,hχb⟩ := exists_spherical_radial_cutoff hab
  obtain ⟨tests,h,δ,hδ,hreal⟩ := cutoff_exactification_in_smooth_neighborhood
    (by simp [Euclidean]) g N hN χ hχ
  have hs0 : Module.finrank ℝ (Euclidean 3) < 2*(2*(2:ℝ)) := by norm_num [Euclidean]
  let atlas := Classical.choice (nonempty_compactMetricAtlas g 2 hs0)
  let i₀ : CoordIndex (Euclidean 3) := ⟨0,by simp [Euclidean]⟩
  obtain ⟨G,hG,hglobal⟩ := atlas.global_cutoff_raw_controls i₀ χ hχ
  choose D hD hDJ using fun z : CoordinateTest (Euclidean 3) (Sphere 3) =>
    cutoffFactor_compact_raw χ hχ z.center z.isCompact z.inTarget (h+1)
  let B := 1+∑ z ∈ tests.toFinset, D z
  have hB : 0 < B := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun z _ => (hD z).le))
  have hDB (z : CoordinateTest (Euclidean 3) (Sphere 3)) (hz : z ∈ tests) : D z ≤ B := by
    have hh := Finset.single_le_sum (fun z (_ : z ∈ tests.toFinset) => (hD z).le)
      (List.mem_toFinset.mpr hz)
    change D z ≤ 1+_
    linarith
  obtain ⟨C,hC,hproj⟩ := spherical_annular_projection_uniform g₀ g hg₀ hr0 hra hab.le hb1
    hFr hext tests h (show 0 ≤ 1+B by linarith)
  obtain ⟨partition,hpart,ℓ,hℓ,ε,hε,hscalar⟩ := exists_spherical_scalar_producer
    g₀ hg₀ g hg ht hts hsr hr hF hFt hext hmetric A
  obtain ⟨L,hL,hpacket⟩ := hscalar (tests++atlas.coveringRawTests i₀) (h+2) (h+3)
  let η (n : ℕ) := L*inverseFrequency n^(h+3)
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa [η] using (inverseFrequency_pow_zero (h+3) (by omega)).const_mul L
  have hGη : Tendsto (fun n => G*η n) atTop (𝓝 0) := by simpa using hη.const_mul G
  have hrate := inverseFrequency_weighted_zero L C h
  refine ⟨partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  filter_upwards [hpacket,eventually_ge_atTop (2:ℕ),hη.eventually (gt_mem_nhds hδ),
    hη.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<1/32 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<(1-b^2)/16 by positivity)),
    hrate.eventually (gt_mem_nhds hδ)] with n hp hn hηδ hηhalf hGl hGgrad hηrate
  obtain ⟨u,hu,huc,hus,hreg,hβ,hz,hpos,hweighted,hβs,hzs,v,hv,hvp,hve,hsmall,hraw,hscore⟩ := hp
  let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
  let β := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) U
  let z := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) U
  let w := cutoffFactor χ v
  have hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U :=
    (roundPower_smooth _ _ _).add (sphericalWaveLift_smooth hu huc)
  have hw : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hη0 : 0 ≤ η n := mul_nonneg hL.le (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _)
  have hη1 : η n ≤ 1 := by linarith
  have hvhalf (q : Sphere 3) : |v q-1| ≤ 1/2 := (hsmall q).2.2.trans hηhalf.le
  have hΛ : 1 ≤ sphereFrequency n := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    unfold sphereFrequency; nlinarith
  have hctrl := hglobal β v hβ hv (η n) hη0 hη1
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).2.2)
  obtain ⟨hwb,hwG,hsmallw⟩ := spherical_cutoff_control_bounds g β χ v hχrange
    hηhalf (fun q => (hsmall q).2.2) hGl hGgrad hb0 hΛ hctrl
  have hwl (q) : 1/2 ≤ w q := (hwb q).1
  have hwu (q) : w q ≤ 2 := (hwb q).2
  have hwp (q) : 0 < w q := by linarith [hwl q]
  let O := {q : Sphere 3 | sphericalRadius sourceAxisOne sourceAxisTwo q < a}
  let Fout := {q : Sphere 3 | b < sphericalRadius sourceAxisOne sourceAxisTwo q}
  have hO : IsOpen O := isOpen_lt (sphericalRadius_continuous _ _) continuous_const
  have hFo : IsOpen Fout := isOpen_lt continuous_const (sphericalRadius_continuous _ _)
  have hann {q : Sphere 3} (hq : q ∉ O ∪ Fout) :
      a ≤ sphericalRadius sourceAxisOne sourceAxisTwo q ∧ sphericalRadius sourceAxisOne sourceAxisTwo q ≤ b := by
    simpa only [O,Fout,mem_union,mem_ofPred_eq,not_or,not_lt] using hq
  have hres := spherical_wave_residual_support g g₀ hg₀ hF hFr hext hu huc hus hn
  have hcoeffout (q : Sphere 3) (hq : q ∈ Fout) : β q=1 ∧ z q=1 := by
    have hnres : q ∉ tsupport (fun q => laplaceBeltrami g U q+sphereFrequency n*U q) :=
      fun hh => (not_le_of_gt (hra.trans hab |>.trans hq)) (hres hh)
    exact ⟨sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => β q-1) (fun hh => hnres (hβs hh))),
      sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => z q-1) (fun hh => hnres (hzs hh)))⟩
  have hmargin (q : Sphere 3) (hq : q ∉ O ∪ Fout) :
      U q^2*coordinateGradientPair g w w q < w q^2*coordinateGradientPair g U U q := by
    obtain ⟨hqa,hqb⟩ := hann hq
    exact spherical_exterior_conjugating_margin g₀ hg₀ g hr0 hra hb0 hb2 hFr hext huc hus
      n (by omega) w hwl hwG q hqa hqb
  have hwJ (t : CoordinateTest (Euclidean 3) (Sphere 3)) (ht : t ∈ tests)
      (y : Euclidean 3) (hy : y ∈ t.compactSet) (j : ℕ) (hj : j ≤ h+1) :
      ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ 1+B := by
    apply cutoff_raw_bounded_by_near_one χ v hχ hv t (h+1) hη0 hη1 hB.le (hDB t ht)
      (fun y hy => hDJ t v hv y hy (η n) hη0
        (fun k hk => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy k (by omega)).2.2)) y hy j hj
  obtain ⟨ĝ,hĝ,f,hf,hfe,hfU,hfZ,hfsgn,hfout⟩ := hreal β z U v (sphereFrequency n) O Fout
    hβ hz hU hv hΛ (fun q => (hpos q).1) hχrange hvhalf
    (fun q => (hsmall q).2.1.trans hηhalf.le) hweighted hve hO hFo
    (fun q hq => hχa q hq.le) (fun q hq => hχb q hq.le) hcoeffout hsmallw hmargin
    (η n) C (n:ℝ) hη0 hηδ.le hC.le (by exact_mod_cast (show 1≤n by omega)) hηrate
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).2.1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j hj).2.2)
    (fun t ht y hy hout i j k hk => hproj w hw hwl hwu hwJ hwG huc hus n (by omega)
      t ht y hy (hann hout).1 (hann hout).2 i j k hk)
  refine ⟨ĝ,hĝ,f,hf,hfe,?_,?_,?_⟩
  · intro q hq
    have hUq := (hfZ q).mp hq
    have he : f = fun q => U q/w q := funext hfU
    rw [he]
    exact regular_quotient_at_zero g hU hw (fun q => (hwp q).ne') q hUq (hreg q hUq)
  · intro q hq
    exact ⟨(hfout q hq).1,(hfout q hq).2.trans
      (spherical_wave_exterior_germ huc hus n ((hra.trans hab).le.trans hq.le)).eq_of_nhds⟩
  · have he : ((f ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)=
        fun y => (w ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)))⁻¹*
          (((U ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) y) := by
      funext y
      simp only [Function.comp_apply,hfU,div_eq_mul_inv]
      exact mul_comm _ _
    rw [he,SignTests.signCertificate_pos_mul _ _ _ _ (fun y => inv_pos.mpr (hwp _))]
    exact hscore

end YauCounterexamples
end

end OAI
