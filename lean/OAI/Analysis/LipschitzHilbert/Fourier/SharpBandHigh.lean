import OAI.Analysis.LipschitzHilbert.Estimates.HilbertTimeDecomposition

namespace OAI

/-! The high-disparity packet theorem now bounds the actual sharp
Hilbert truncation, with its three explicit analytic remainder terms. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem dyadic_time_lower (N : ℕ) (T s : ℝ) (hT : 0<T)
    (hs : s≤T/(2:ℝ)^N) (j : Fin N) : s≤(T/2)/(2:ℝ)^j.val := by
  rw [div_div,←pow_succ']
  apply hs.trans
  apply (div_le_div_iff₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).2
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hT.le

theorem actual_sharp_band_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ D A B C L0 : ℝ, 0<D ∧ 0<A ∧ 0≤B ∧ 0<C ∧ 16≤L0 ∧
    ∀ L : ℝ, L0≤L → ∀ epsilon T R W w m : ℝ,
      0<epsilon → epsilon≤D*w → D*w≤T → T≤R → D*w≤1/4 →
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
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        (verticalProjectionCost p*(B+2*Real.log (R/T))+
          2*D*verticalProjectionCost (verticalDerivativeProfile p))*min (4*F) E+
        (C*verticalProjectionCost p)*F^(2/3:ℝ)*E^(1/3:ℝ) := by
  obtain ⟨D,A,L0,hD,hA,hL0,hfin⟩ := actual_cutoff_band_high hVariation hLL
    hilbertAnnularSymbol p 1 2 (1/2) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hilbertAnnularSymbol_support hp
  obtain ⟨B,C,hB,hC,hdecomp⟩ := hilbertTimeDecomposition_bound hH
  refine ⟨D,A,B,C,L0,hD,hA,hB,hC,hL0,?_⟩
  intro L hL epsilon T R W w m he heD hDT hTR hsmall htime hW hw hwW hratio hmlo hmhi hWeq
    field hfield hfieldBound f g F E ratio hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  have hT : 0<T := (mul_pos hD hw).trans_le hDT
  have hu : LipschitzWith 2 (fun z : ℝ×ℝ => field (planeCoordinates z)) := by
    simpa only [mul_one] using product_slope_lipschitz field hfield
  obtain ⟨N,hlo,_,herror⟩ := hdecomp epsilon (D*w) T R he heD hDT hTR hsmall
  have herr := herror (3/2) 3 (Or.inl rfl)
    (by norm_num [Real.holderConjugate_iff] : (3/2:ℝ).HolderConjugate 3)
    (fun z => field (planeCoordinates z)) hu (fun z => (hfieldBound _).trans (by norm_num))
    p w hw f g hf hg l r (by linarith) hfstrip hgstrip
  have hmain := hfin L hL N (T/2) W w (by positivity) hW hw hwW hratio (by norm_num) htime
    (dyadic_time_lower N T (D*w) hT hlo) field hfield hfieldBound f g F E ratio hF hE hr heq hlog
    hf hg hf1 hg1 hf2 hg2 l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
  have hlogR : 0≤Real.log (R/T) := Real.log_nonneg ((one_le_div hT).2 hTR)
  have hCp := verticalProjectionCost_pos p
  have hCd := verticalProjectionCost_pos (verticalDerivativeProfile p)
  have hcoef : 0≤verticalProjectionCost p*(B+2*Real.log (R/T))+
      2*(D*w)*verticalProjectionCost (verticalDerivativeProfile p)/w := by positivity
  have hmass : min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)≤min (4*F) E :=
    min_le_min (mul_le_mul_of_nonneg_left hf1 (by norm_num)) hg1
  have hpow : (C*verticalProjectionCost p)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/(3/2:ℝ))*
      (∫ z, ‖g z‖ ∂planeMeasure)^(1/(3:ℝ))≤
      (C*verticalProjectionCost p)*F^(2/3:ℝ)*E^(1/3:ℝ) := by
    norm_num only [one_div_div] at *
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (integral_nonneg fun _ => norm_nonneg _) hf1 (by norm_num)) (by positivity))
      (Real.rpow_le_rpow (integral_nonneg fun _ => norm_nonneg _) hg1 (by norm_num))
      (by positivity) (by positivity)
  have herr' := herr.trans (add_le_add (mul_le_mul_of_nonneg_left hmass hcoef) hpow)
  have hcoeffeq : 2*(D*w)*verticalProjectionCost (verticalDerivativeProfile p)/w=
      2*D*verticalProjectionCost (verticalDerivativeProfile p) := by field_simp
  rw [hcoeffeq] at herr'
  have htriangle := norm_le_insert'
    (kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
      (schwartzVerticalProjection p w 0 f) g)
    (kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) (fun z => field (planeCoordinates z))
      (schwartzVerticalProjection p w 0 f) g)
  exact htriangle.trans ((add_le_add hmain herr').trans_eq (by ring))

end LipschitzHilbert.PacketRepresentation

end

end OAI
