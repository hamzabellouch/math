import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolFormL1
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBasicConvolution

namespace OAI

/-! The basic model estimate for the original finite normalized symbol
form, using the actual annular selectors and the common Fourier average. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_symbol_basic_l1 (hVariation : LepingleInput)
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (hq : 4≤q)
    (A B cEta CEta a b Cprofile Csymbol : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0<cEta) (hCEta : 0≤CEta)
    (ha : 0<a) (hb : 0<b) (haQuarter : a/2≤1/4)
    (hCp : 0<Cprofile) (hCs : 0<Csymbol) (horder : 207≤order)
    (hsmall : (2*Real.pi*A)/cEta<(a/2)/4)
    (hcoverSmall : 6*max (2*b) ((2*Real.pi*A)/cEta+a/2)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta (a/2) (2*b))
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hprofiles : ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤Cprofile ∧
      planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤Cprofile) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
    ∀ (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ),
      (∀ i k, symbolCoefficientBound (S i k) q≤Csymbol) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f : κ → ℝ×ℝ → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) →
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖normalizedSymbolSumL1 chiA chiB (annularCutoff a b ha hb) topLength width w htop hwidth
        labels theta center S u f g‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨Kb,hKb,hbasic⟩ := exists_normalized_basic_convolution hVariation
    A B cEta CEta (a/2) (2*b) Cprofile M order hA hB hcEta hCEta
    (by positivity) haQuarter (by positivity) hCp horder hsmall hcoverSmall num
  let chi := annularCutoff a b ha hb
  have hchi : ∀ s, |chi s|≤1 := by
    intro s
    rw [abs_of_nonneg (annularCutoff_nonneg a b ha hb s)]
    exact annularCutoff_le_one a b ha hb s
  have hnormal : 0<selectorNormalizer chi Csymbol := selectorNormalizer_pos chi Csymbol hCs
  have hI : 0≤∫ nu : SymbolSpace, symbolWeight q nu := integral_nonneg (fun nu => (symbolWeight_pos q nu).le)
  let K := selectorNormalizer chi Csymbol*Kb*((∫ nu : SymbolSpace, symbolWeight q nu)+1)
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  intro N κ Label _ topLength width w F htop hwidth hw hW hF labels theta center
    hfrequency hlo hhi hlocal S hS u hu f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
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
  have hconv (nu : SymbolSpace) :
      ‖normalizedConvolutionSum chiA chiB q nu topLength width htop hwidth labels theta center
        (fun j l k s => scaledUnitSelector chi Csymbol (S ⟨j,l⟩ k) q nu
          (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) u fData g‖≤
        Kb*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
    apply hbasic N κ Label chiA chiB q nu hchiA hchiB (hprofiles nu).1 (hprofiles nu).2
      topLength width width 1 w F htop hwidth (by norm_num)
      (by rw [div_self hwidth.ne',abs_one]) hw hW hF labels theta center hfrequency hlo hhi hlocal
      (fun j l k s => scaledUnitSelector chi Csymbol (S ⟨j,l⟩ k) q nu
        (w/(topLength/(2:ℝ)^j.val)) (theta j l) s)
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
    · intro j l k s t _
      exact scaledUnitSelector_lipschitz chi hchi Csymbol hCs (S ⟨j,l⟩ k) q (by omega)
        (hS ⟨j,l⟩ k) nu _ _ (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) s t
    · exact hu
    · exact hfm
    · exact hgm
    · exact hfb
    · exact hgb
    · exact hE
    · exact hFset
    · exact hEfin
    · exact hFfin
    · exact hgs
    · exact hfs
  have hout := normalized_symbol_sum_bound_l1 chiA chiB chi hchi Csymbol hCs q hq
    topLength width w htop hwidth labels theta center S hS u hu f fData g hfint hf hgm hgint
    (Kb*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E)) hconv
  apply hout.trans
  have hbnd : (∫ nu : SymbolSpace, symbolWeight q nu)≤(∫ nu : SymbolSpace, symbolWeight q nu)+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbnd
    (show 0≤selectorNormalizer chi Csymbol*Kb*Real.sqrt ((volume.prod volume).real Fset)*
      Real.sqrt ((volume.prod volume).real E) by positivity)
  dsimp only [K]
  convert hmul using 1 <;> ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
