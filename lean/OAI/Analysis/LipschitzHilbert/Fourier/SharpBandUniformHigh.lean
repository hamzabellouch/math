import OAI.Analysis.LipschitzHilbert.Fourier.SharpBandHighAll
import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeParameters

namespace OAI

/-! The source time/width choices and exponential absorption give the
uniform high-disparity restricted estimate for every sharp truncation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem actual_sharp_band_uniform_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C L0 : ℝ, 0<C ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ) (F E ratio : ℝ),
      0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤C*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨A,K,Q,Lbase,hA,hK,hQ,hLbase,hraw⟩ :=
    actual_sharp_band_high_all hVariation hLL hH p hp
  obtain ⟨Lpar,hpar⟩ := eventually_atTop.1 eventually_sharpSourceParameters
  obtain ⟨Ldec,hdec⟩ := eventually_atTop.1 (eventually_remainder_decay K Q hK)
  let L0 := max Lbase (max Lpar Ldec)
  refine ⟨A+1,L0,by linarith,hLbase.trans (le_max_left _ _),?_⟩
  intro L hL epsilon R w he heR hRquarter hw field hfield hfieldBound f g F E ratio
    hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hLp : Lpar≤L := (le_trans (le_max_left Lpar Ldec) (le_max_right Lbase (max Lpar Ldec))).trans hL
  have hLd : Ldec≤L := (le_trans (le_max_right Lpar Ldec) (le_max_right Lbase (max Lpar Ldec))).trans hL
  obtain ⟨hL1,_,hm10⟩ := hpar L hLp
  have hR : 0<R := he.trans_le heR
  let T := min R (sharpSourceTime L)
  let m := sharpSourceWidthRatio L
  let W := m*w
  have hT : 0<T := lt_min hR (sharpSourceTime_pos L)
  have hTR : T≤R := min_le_left _ _
  have hTS : T≤sharpSourceTime L := min_le_right _ _
  have htime : T/2≤Real.exp (-(L^(97/100:ℝ))) := by
    change T/2≤sharpSourceTime L
    linarith
  have hlogRT : Real.log (R/T)≤L := by
    by_cases hRS : R≤sharpSourceTime L
    · simp only [T,min_eq_left hRS,div_self hR.ne',Real.log_one]
      exact le_trans (by norm_num) hL1
    · rw [show T=sharpSourceTime L from min_eq_right (le_of_not_ge hRS)]
      exact sharpSourceTime_log L R hL1 hR (by linarith)
  have hgeometry := sharpSourceWidthRatio_geometry L w hw hm10
  have hmpos : 0<m := sharpSourceWidthRatio_pos L
  have hbound := hraw L hLb epsilon T R W w m he heR hT hTR (hTR.trans hRquarter)
    hlogRT htime (mul_pos hmpos hw) hw hgeometry.1 hgeometry.2 le_rfl
    (by change m≤2*m; linarith) rfl field hfield hfieldBound f g F E ratio
    hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  exact absorb_sharp_remainders _ A K Q F E ratio L hK (by linarith) hF hr heq hlog
    (hdec L hLd) hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
