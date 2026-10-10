import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolFormL1
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedHighConvolution

namespace OAI

/-! The original normalized symbol form has the full source high-disparity
saving. All constants precede the scales, bins, and finite row family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_symbol_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (hq : 4≤q)
    (A B cEta CEta a b Cprofile Csymbol F c0 : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0<cEta) (hCEta : 0≤CEta)
    (ha : 0<a) (hb : 0<b) (haQuarter : a/2≤1/4)
    (hCp : 0<Cprofile) (hCs : 0<Csymbol) (horder : 207≤order) (hF : 0≤F) (hc0 : 0<c0)
    (hsmall : (2*Real.pi*A)/cEta<(a/2)/4)
    (hcoverSmall : 6*max (2*b) ((2*Real.pi*A)/cEta+a/2)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta (a/2) (2*b))
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hprofiles : ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤Cprofile ∧
      planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤Cprofile) :
    ∃ K L0 : ℝ, 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → w≤width → topLength≤Real.exp (-(L^(97/100:ℝ))) →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, c0/w≤|2*Real.pi*center k|) → (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
      (∀ j l, |theta j l|+w/(topLength/(2:ℝ)^j.val)≤1) →
    ∀ (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ),
      (∀ i k, symbolCoefficientBound (S i k) q≤Csymbol) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field →
    ∀ (f : κ → ℝ×ℝ → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) →
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      0<(volume.prod volume).real Fset →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0<ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖normalizedSymbolSumL1 chiA chiB (annularCutoff a b ha hb) topLength width w htop hwidth
        labels theta center S (fun z => field (planeCoordinates z)) f g‖≤
        K*L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨_mask,L0,_hmask,hL0,hhigh⟩ := exists_normalized_high_convolution hVariation hLL
    A B cEta CEta (a/2) (2*b) Cprofile F c0 M order hA hB hcEta hCEta
    (by positivity) haQuarter (by positivity) hCp hF hc0 horder hsmall hcoverSmall num
  let chi := annularCutoff a b ha hb
  have hchi : ∀ s, |chi s|≤1 := by
    intro s
    rw [abs_of_nonneg (annularCutoff_nonneg a b ha hb s)]
    exact annularCutoff_le_one a b ha hb s
  have hnormal : 0<selectorNormalizer chi Csymbol := selectorNormalizer_pos chi Csymbol hCs
  have hI : 0≤∫ nu : SymbolSpace, symbolWeight q nu := integral_nonneg (fun nu => (symbolWeight_pos q nu).le)
  let K := selectorNormalizer chi Csymbol*((∫ nu : SymbolSpace, symbolWeight q nu)+1)
  refine ⟨K,L0,by dsimp only [K]; positivity,hL0,?_⟩
  intro L hL N κ Label _ topLength width w htop hwidth hw hW hshort labels theta center
    hfrequencyLo hfrequency hlo hhi hlocal hunitRange S hS field hfield
    f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hFpos hgs hfs
    l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq
  have hgint (k : κ) : Integrable (fun z => g z k) planeMeasure := by
    have hI' : Integrable (E.indicator (fun _ => (1:ℝ))) (volume.prod volume) :=
      (integrable_indicator_iff hE).2 (integrableOn_const (μ:=volume.prod volume) hEfin)
    have hmeas : Measurable (fun z => g z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hgm)
    apply hI'.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z∈E
    · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (g z) k).trans (hgb z)
    · simp only [Set.indicator_of_notMem hz,hgs z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]
  have hu : Measurable (fun z => field (planeCoordinates z)) :=
    (product_slope_lipschitz field hfield).continuous.measurable
  have hconv (nu : SymbolSpace) :
      ‖normalizedConvolutionSum chiA chiB q nu topLength width htop hwidth labels theta center
        (fun j l k s => scaledUnitSelector chi Csymbol (S ⟨j,l⟩ k) q nu
          (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) (fun z => field (planeCoordinates z)) fData g‖≤
        L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
    refine hhigh L hL N κ Label chiA chiB q nu hchiA hchiB (hprofiles nu).1 (hprofiles nu).2
      topLength width w htop hwidth hw hW hshort labels theta center
      hfrequencyLo hfrequency hlo hhi hlocal hunitRange
      (fun j l k s => scaledUnitSelector chi Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) ?_ ?_ ?_ ?_ ?_
      field hfield fData g hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hFpos hgs hfs
      l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq
    · intro j l k
      exact scaledUnitSelector_measurable chi Csymbol (S ⟨j,l⟩ k) q nu _ _
    · intro j l k s
      exact scaledUnitSelector_bound chi hchi Csymbol hCs (S ⟨j,l⟩ k) q (hS ⟨j,l⟩ k) nu _ _ s
    · intro j l k s hs
      have hh := (scaledUnitSelector_annular_support a b ha hb Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s
        (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) hs).1
      simpa only [mul_div_assoc,abs_sub_comm] using hh
    · intro j l k s hs
      exact (scaledUnitSelector_annular_support a b ha hb Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s
        (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) hs).2
    · intro j l k s t
      exact scaledUnitSelector_lipschitz chi hchi Csymbol hCs (S ⟨j,l⟩ k) q (by omega)
        (hS ⟨j,l⟩ k) nu _ _ (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) s t
  have hout := normalized_symbol_sum_bound_l1 chiA chiB chi hchi Csymbol hCs q hq
    topLength width w htop hwidth labels theta center S hS _ hu f fData g hfint hf hgm hgint
    (L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E)) hconv
  apply hout.trans
  have hbnd : (∫ nu : SymbolSpace, symbolWeight q nu)≤(∫ nu : SymbolSpace, symbolWeight q nu)+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbnd
    (show 0≤selectorNormalizer chi Csymbol*L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*
      Real.sqrt ((volume.prod volume).real E) by
      exact mul_nonneg (mul_nonneg (mul_nonneg hnormal.le (Real.rpow_nonneg (by linarith [hL0.trans hL]) _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  dsimp only [K]
  convert hmul using 1 <;> ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
