import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularReversePairing
import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedLatticeSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedLatticeAverage

namespace OAI

/-! Reverse disparity for the actual normalized finite convolution sum,
with the constructed angular models and common lattice average. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_reverse_convolution (hVariation : LepingleInput)
    (A B cEta CEta cb radius C : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0<cEta) (hCEta : 0≤CEta)
    (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hr : 0≤radius) (hC : 0<C)
    (horder : 207≤order) (hsmall : (2*Real.pi*A)/cEta<cb/4)
    (hcoverSmall : 6*max radius ((2*Real.pi*A)/cEta+cb)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta cb radius) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace),
      (∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B) →
      (∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) →
      (planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤C) →
      (planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤C) →
    ∀ (topLength width scale ratioBound w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      1≤ratioBound → |scale/width|≤ratioBound → 0<w → w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
    ∀ (b : ∀ j, labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/(topLength/(2:ℝ)^j.val)≤|theta j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-theta j l|≤radius*(w/(topLength/(2:ℝ)^j.val))) →
      (∀ j l k s t, |s-t|≤w/(topLength/(2:ℝ)^j.val) →
        ‖b j l k s-b j l k t‖≤|s-t|/(w/(topLength/(2:ℝ)^j.val))) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    let length := fun i : LatticeRow labels => topLength/(2:ℝ)^i.1.val
    let KA := fun (i : LatticeRow labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chiA) (length i) width (theta i.1 i.2)
        (2*Real.pi*center k) (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne')
      nu q (length i) (theta i.1 i.2)
    let KB := fun (i : LatticeRow labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chiB) (length i) width (theta i.1 i.2)
        (2*Real.pi*center k) (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne')
      nu q width (center k)
    ‖∑ i : LatticeRow labels, ∑ k, ∫ z, b i.1 i.2 k (u z)*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (fun x => f x k)) z*
      star (g z k) ∂volume.prod volume‖≤
        K*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,_hCD,_hCS,_hCT,_hCZ,hreverse⟩ := PacketLatticeData.exists_angular_reverse_pairing
    hVariation (2*Real.pi*A) cEta CEta cb (2*Real.pi*B) radius M
    (by positivity) hcEta hCEta (by positivity) hcb hcbQuarter hsmall hr hcoverSmall num
  let budget : ℝ := ((2:ℝ)^order*C)*3^(2*order)
  let bound : ℝ := max 1 budget
  have hbound_one : 1≤bound := le_max_left _ _
  have hbudget : budget≤bound := le_max_right _ _
  let cost := num.reverseUnitCost M CD CS CT CZ*(2*bound)^4
  let K := 3*max 1 cost
  have hK : 0<K := mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  refine ⟨K,hK,?_⟩
  intro N κ Label _ chiA chiB q nu hchiA hchiB hprofile hprofileB topLength width scale ratioBound
    w F htop hwidth hratio hscale hw hW hF labels theta center hfreq hlo hhi hlocal
    b hb hb1 haway hradius hnear u hu f g hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
    length KA KB
  have hf : MemLp f 2 (volume.prod volume) := (bounded_supported_input f hfm hfb Fset hFset hFfin hfs).1
  have hf1 (k : κ) : Integrable (fun z => f z k) (volume.prod volume) := by
    have hI : Integrable (Fset.indicator (fun _ => (1:ℝ))) (volume.prod volume) :=
      (integrable_indicator_iff hFset).2 (integrableOn_const (μ:=volume.prod volume) hFfin)
    have hfk : Measurable (fun z => f z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hfm)
    apply hI.mono' hfk.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z∈Fset
    · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (f z) k).trans (hfb z)
    · simp only [Set.indicator_of_notMem hz,hfs z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]
  apply normalized_lattice_average_bound (planarInverseSchwartz chiA) (planarInverseSchwartz chiB)
    q nu topLength width scale ratioBound C order htop hwidth hC (by omega) hratio hscale
    labels theta center hprofile hprofileB b hb hb1 u hu f g hf hf1
    (fun k => (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hgm))
    (fun k z => (PiLp.norm_apply_le (g z) k).trans (hgb z))
    (K*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
      ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ))
  intro origin S
  dsimp only
  let P := finiteNormalizedPacketLattice (planarInverseSchwartz chiA) q nu topLength width scale
    ratioBound C order htop hwidth hC (by omega) hratio hscale labels origin theta center S hprofile
  let alt := fun (j : Fin N) (l : P.labels j) (_a : finiteSiteFiber labels S j l.val) (_k : κ) =>
    analysisProfile (planarInverseSchwartz chiB) q nu
  let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound :=
    fun _ _ _ _ => hprofileB
  have hspec := normalizedPacketLattice_spectrum (Item:=fun j l => finiteSiteFiber labels S j l) chiA q nu topLength width scale ratioBound C order
    htop hwidth hC (by omega) hratio hscale labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile A B hchiA w cEta CEta hw hlo hhi
  have haspec := normalizedAnalysisFamily_spectrum (Item:=fun j l => finiteSiteFiber labels S j l) chiA q nu topLength width scale ratioBound C order
    htop hwidth hC (by omega) hratio hscale labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile A B w cEta CEta hw hlo hhi chiB hprofileB hchiB
  have hresult := hreverse N κ Label (fun j l => finiteSiteFiber labels S j l) P Finset.univ w F
    hw hW hF horder hfreq hlocal
    (fun j l a k xi et hs => (hspec j l a k xi et hs).1)
    (fun j l a k xi et hs => (hspec j l a k xi et hs).2) alt hAlt
    (fun j l a k xi et hs => (haspec j l a k xi et hs).1)
    (fun j l a k xi et hs => (haspec j l a k xi et hs).2)
    b hb hb1 haway hradius hnear bound hbound_one
    (by change budget≤bound; exact hbudget)
    g f hgm hfm hgb hfb E Fset hE hFset hEfin hFfin hgs hfs u hu
  calc
    _ ≤ 3*(cost*Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := hresult.2
    _ = (3*cost)*(Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by ring
    _ ≤ K*(Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (le_max_right 1 cost) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
