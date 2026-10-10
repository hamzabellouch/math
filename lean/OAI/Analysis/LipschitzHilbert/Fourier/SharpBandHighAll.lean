import OAI.Analysis.LipschitzHilbert.Estimates.SharpRemainderDecay
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertEndpointCases

namespace OAI

/-! Uniformity in the inner endpoint and in the band width. All four
relative positions of the inner, very-short and packet cutoffs are covered. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem restricted_remainder_mono (F E f e k K q Q : ℝ)
    (hf0 : 0≤f) (he0 : 0≤e) (hf : f≤F) (he : e≤E)
    (hk0 : 0≤k) (hk : k≤K) (hq0 : 0≤q) (hq : q≤Q) :
    k*min (4*f) e+q*f^(2/3:ℝ)*e^(1/3:ℝ)≤
      K*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ) := by
  have hF0 : 0≤F := hf0.trans hf
  have hE0 : 0≤E := he0.trans he
  have hQ0 : 0≤Q := hq0.trans hq
  apply add_le_add
  · exact mul_le_mul hk (min_le_min (by linarith) he) (by positivity) (hk0.trans hk)
  · exact mul_le_mul
      (mul_le_mul hq (Real.rpow_le_rpow hf0 hf (by norm_num)) (by positivity) (hq0.trans hq))
      (Real.rpow_le_rpow he0 he (by norm_num)) (by positivity) (by positivity)

theorem actual_sharp_band_high_all (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ A K Q L0 : ℝ, 0<A ∧ 0≤K ∧ 0<Q ∧ 16≤L0 ∧
    ∀ L : ℝ, L0≤L → ∀ epsilon T R W w m : ℝ,
      0<epsilon → epsilon≤R → 0<T → T≤R → T≤1/4 → Real.log (R/T)≤L →
      T/2≤Real.exp (-(L^(97/100:ℝ))) → 0<W → 0<w → w≤W →
      5*(w/W)≤1/2 → Real.exp (L^(9/10:ℝ))≤m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ) (F E ratio : ℝ),
      0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+K*(1+L)*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ) := by
  obtain ⟨D,A,L0,hD,hA,hL0,hfin⟩ := actual_cutoff_band_high hVariation hLL
    hilbertAnnularSymbol p 1 2 (1/2) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hilbertAnnularSymbol_support hp
  obtain ⟨B1,C1,hB1,hC1,hdecomp⟩ := hilbertTimeDecomposition_bound hH
  obtain ⟨B2,hB2,hmidlong⟩ := hilbertMiddleLong_bound
  obtain ⟨C2,hC2,hshortlong⟩ := hilbertShortLong_bound hH
  let P := verticalProjectionCost p
  let P' := verticalProjectionCost (verticalDerivativeProfile p)
  let B := B1+B2
  let K := P*B+2*P+2*D*P'
  let Q := (C1+C2)*P
  have hP : 0<P := verticalProjectionCost_pos p
  have hP' : 0<P' := verticalProjectionCost_pos _
  have hB : 0≤B := add_nonneg hB1 hB2
  have hK : 0≤K := by dsimp [K]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  refine ⟨A,K,Q,L0,hA,hK,hQ,hL0,?_⟩
  intro L hL epsilon T R W w m he heR hT hTR hTquarter hlogRT htime hW hw hwW hratio hmlo hmhi hWeq
    field hfield hfieldBound f g F E ratio hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  let S := schwartzVerticalProjection p w 0 f
  let H := kernelPairing (sharpTimeKernel epsilon R) u S g
  let rem := K*(1+L)*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ)
  have hL0' : 0≤L := by linarith only [hL0,hL]
  have hu : LipschitzWith 2 u := by simpa only [u,mul_one] using product_slope_lipschitz field hfield
  have hub (z) : |u z|≤1 := (hfieldBound _).trans (by norm_num)
  have hwidth : r-l≤1/4 := by linarith only [hstrip]
  have hlog0 : 0≤Real.log (R/T) := Real.log_nonneg ((one_le_div hT).2 hTR)
  have hmodel0 : 0≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by positivity
  have hpromote (z : ℂ) (k q : ℝ) (hk0 : 0≤k) (hk : k≤K*(1+L)) (hq0 : 0≤q) (hq : q≤Q)
      (hb : ‖z‖≤k*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)+
        q*(∫ z, ‖f z‖ ∂planeMeasure)^(2/3:ℝ)*(∫ z, ‖g z‖ ∂planeMeasure)^(1/3:ℝ)) : ‖z‖≤rem := by
    exact hb.trans (restricted_remainder_mono F E _ _ k (K*(1+L)) q Q
      (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
      hf1 hg1 hk0 hk hq0 hq)
  have hbase (b s : ℝ) (hb : b≤B) (hs : s≤D*w) :
      P*(b+2*Real.log (R/T))+2*s*P'/w≤K*(1+L) := by
    have hsmall : 2*s*P'/w≤2*D*P' := by
      calc
        _ ≤ 2*(D*w)*P'/w := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hP'.le) hw.le
        _ = _ := by field_simp
    have hc0 : P*B+2*D*P'≤K := by dsimp [K]; linarith only [hP]
    have hc1 : 2*P≤K := by
      dsimp [K]
      nlinarith only [mul_nonneg hP.le hB, mul_nonneg hD.le hP'.le]
    calc
      _ ≤ P*(B+2*L)+2*D*P' := add_le_add
        (mul_le_mul_of_nonneg_left (by linarith) hP.le) hsmall
      _ = (P*B+2*D*P')+(2*P)*L := by ring
      _ ≤ K+K*L := add_le_add hc0 (mul_le_mul_of_nonneg_right hc1 hL0')
      _ = _ := by ring
  have hQ1 : C1*P≤Q := by dsimp [Q]; nlinarith only [mul_pos hC2 hP]
  have hQ2 : C2*P≤Q := by dsimp [Q]; nlinarith only [mul_pos hC1 hP]
  have hfinish (N : ℕ) (hlength : ∀ j : Fin N, D*w≤(T/2)/(2:ℝ)^j.val)
      (herr : ‖H-kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u S g‖≤rem) :
      ‖H‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+rem := by
    have hmain := hfin L hL N (T/2) W w (by positivity) hW hw hwW hratio (by norm_num) htime
      hlength field hfield hfieldBound f g F E ratio hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2
      l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
    exact (norm_le_insert' H _).trans (add_le_add hmain herr)
  change ‖H‖≤_
  rw [add_assoc]
  change ‖H‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+rem
  by_cases hET : T≤epsilon
  · have hb := sharpHilbertProjection_long_pairing epsilon R he heR u hu p w hw f g hf hg
      l r hwidth hfstrip hgstrip
    have hlogE : Real.log (R/epsilon)≤Real.log (R/T) := by
      apply Real.log_le_log (div_pos (he.trans_le heR) he)
      exact div_le_div_of_nonneg_left (he.trans_le heR).le hT hET
    have hk0 : 0≤P*(2*Real.log (R/epsilon)) :=
      mul_nonneg hP.le (mul_nonneg (by norm_num) (Real.log_nonneg ((one_le_div he).2 heR)))
    have hk : P*(2*Real.log (R/epsilon))≤K*(1+L) := by
      apply le_trans _ (hbase 0 0 hB (by positivity))
      calc
        _ ≤ P*(2*Real.log (R/T)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlogE (by norm_num)) hP.le
        _ = _ := by ring
    have hh := hpromote H _ 0 hk0 hk le_rfl hQ.le (by simpa only [zero_mul,add_zero] using hb)
    exact hh.trans (le_add_of_nonneg_left hmodel0)
  · have heT : epsilon≤T := (lt_of_not_ge hET).le
    by_cases hTD : T≤D*w
    · have hb := hshortlong epsilon T R he heT hTR hTquarter (3/2) 3 (Or.inl rfl)
        (by norm_num [Real.holderConjugate_iff]) u hu hub p w hw f g hf hg l r hwidth hfstrip hgstrip
      have hk0 : 0≤P*(2*Real.log (R/T))+2*T*P'/w := by positivity
      have hk := hbase 0 T hB hTD
      have hh := hpromote H _ (C2*P) hk0 (by simpa only [zero_add] using hk) (by positivity) hQ2
        (by norm_num only [one_div_div] at hb; exact hb)
      exact hh.trans (le_add_of_nonneg_left hmodel0)
    · have hDT : D*w≤T := (lt_of_not_ge hTD).le
      by_cases heD : epsilon≤D*w
      · obtain ⟨N,hlo,_,hb⟩ := hdecomp epsilon (D*w) T R he heD hDT hTR (hDT.trans hTquarter)
        have herr := hb (3/2) 3 (Or.inl rfl) (by norm_num [Real.holderConjugate_iff])
          u hu hub p w hw f g hf hg l r hwidth hfstrip hgstrip
        have hk0 : 0≤P*(B1+2*Real.log (R/T))+2*(D*w)*P'/w := by positivity
        apply hfinish N (dyadic_time_lower N T (D*w) hT hlo)
        exact hpromote _ _ (C1*P) hk0 (hbase B1 (D*w) (by dsimp [B]; linarith only [hB2]) le_rfl)
          (by positivity) hQ1 (by norm_num only [one_div_div] at herr; exact herr)
      · obtain ⟨N,hlo,_,hb⟩ := hmidlong epsilon T R he heT hTR
        have herr := hb u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
        have hk0 : 0≤P*(B2+2*Real.log (R/T)) := by positivity
        have hk : P*(B2+2*Real.log (R/T))≤K*(1+L) := by
          simpa only [mul_zero,zero_mul,zero_div,add_zero] using
            hbase B2 0 (by dsimp [B]; linarith only [hB1]) (by positivity)
        apply hfinish N (dyadic_time_lower N T (D*w) hT ((lt_of_not_ge heD).le.trans hlo))
        exact hpromote _ _ 0 hk0 hk le_rfl hQ.le (by simpa only [zero_mul,add_zero] using herr)

end LipschitzHilbert.PacketRepresentation

end

end OAI
