import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularHighPairing
import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedLatticeSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedLatticeAverage

namespace OAI

/-! High-disparity recovery after the common lattice average. The
polynomial loss from the three angular grids is absorbed in L. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_high_convolution (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (A B cEta CEta cb radius C F c0 : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0<cEta) (hCEta : 0≤CEta)
    (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hr : 0≤radius) (hC : 0<C)
    (hF : 0≤F) (hc0 : 0<c0) (horder : 207≤order)
    (hsmall : (2*Real.pi*A)/cEta<cb/4)
    (hcoverSmall : 6*max radius ((2*Real.pi*A)/cEta+cb)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta cb radius) :
    ∃ mask L0 : ℝ, 0≤mask ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace),
      (∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B) →
      (∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) →
      (planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤C) →
      (planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤C) →
    ∀ (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → w≤width → topLength≤Real.exp (-(L^(97/100:ℝ))) →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, c0/w≤|2*Real.pi*center k|) → (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
      (∀ j l, |theta j l|+w/(topLength/(2:ℝ)^j.val)≤1) →
    ∀ (b : ∀ j, labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/(topLength/(2:ℝ)^j.val)≤|theta j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-theta j l|≤radius*(w/(topLength/(2:ℝ)^j.val))) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖≤|s-t|/(w/(topLength/(2:ℝ)^j.val))) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      0<(volume.prod volume).real Fset →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0<ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
    let length := fun i : LatticeRow labels => topLength/(2:ℝ)^i.1.val
    let KA := fun (i : LatticeRow labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chiA) (length i) width (theta i.1 i.2)
        (2*Real.pi*center k) (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne')
      nu q (length i) (theta i.1 i.2)
    let KB := fun (i : LatticeRow labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chiB) (length i) width (theta i.1 i.2)
        (2*Real.pi*center k) (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne')
      nu q width (center k)
    ‖∑ i : LatticeRow labels, ∑ k, ∫ z, b i.1 i.2 k (field (planeCoordinates z))*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (fun x => f x k)) z*
      star (g z k) ∂volume.prod volume‖≤
        L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  let cone := max 1 radius
  have hcone : 1≤cone := le_max_left _ _
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (2*cone+1) (by norm_num : (1:ℝ)<2)
  obtain ⟨mask,Lbase,hmask,hbase,hhigh⟩ := PacketLatticeData.exists_angular_high_pairing
    hVariation hLL (2*Real.pi*A) cEta CEta cb (2*Real.pi*B) radius F c0 cone 1 21
    12 ⌈cone⌉₊ M J (by positivity) hcEta hCEta (by positivity) hcb hcbQuarter hsmall
    hr hF hc0 hcone (le_max_right _ _) (Nat.le_ceil cone) (by norm_num) (by norm_num)
    (by norm_num) hJ.le hcoverSmall num
  let budget : ℝ := ((2:ℝ)^order*C)*3^(2*order)
  let L0 := max Lbase budget
  refine ⟨mask,L0,hmask,hbase.trans (le_max_left _ _),?_⟩
  intro L hL N κ Label _ chiA chiB q nu hchiA hchiB hprofile hprofileB topLength width w
    htop hwidth hw hW hshort labels theta center hfrequencyLo hfrequency hlo hhi hlocal hunitRange
    b hb hb1 haway hradius hLip field hfield f g hfm hgm hfb hgb E Fset hE hFset hEfin hFfin
    hFpos hgs hfs l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq
    hwidthLo hwidthHi hwidthEq length KA KB
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hL16 : 16≤L := hbase.trans hLb
  have hL1 : 1≤L := by linarith
  have hLp : 0<L := by linarith
  let rb := 4*L^(mask+2)
  let scale := 4*(L^(mask+2)*width)
  have hrb : 1≤rb := by
    have hp : 1≤L^(mask+2) := Real.one_le_rpow hL1 (by linarith)
    dsimp only [rb]
    linarith
  have hs : |scale/width|≤rb := by
    have he : scale/width=rb := by dsimp only [scale,rb]; field_simp
    rw [he,abs_of_nonneg (by linarith : 0≤rb)]
  have hbudget : budget≤L := (le_max_right _ _).trans hL
  have hB : 6*L^(-21:ℝ)*ratio*(volume.prod volume).real Fset≤
      L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
    have hroot : Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E)=
        ratio*(volume.prod volume).real Fset := by
      rw [hratioEq,Real.sqrt_mul (sq_nonneg ratio),Real.sqrt_sq hratio.le]
      calc
        _ = ratio*(Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Fset)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt measureReal_nonneg]
    have hp : 6*L^(-21:ℝ)≤L^(-20:ℝ) := by
      calc
        _ ≤ L*L^(-21:ℝ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = L^(1:ℝ)*L^(-21:ℝ) := by rw [Real.rpow_one]
        _ = L^(-20:ℝ) := by rw [← Real.rpow_add hLp]; norm_num
    calc
      _ = (6*L^(-21:ℝ))*(ratio*(volume.prod volume).real Fset) := by ring
      _ ≤ L^(-20:ℝ)*(ratio*(volume.prod volume).real Fset) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg hratio.le measureReal_nonneg)
      _ = _ := by rw [←hroot]; ring
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
  have hu : Measurable (fun z => field (planeCoordinates z)) :=
    (product_slope_lipschitz field hfield).continuous.measurable
  apply le_trans (normalized_lattice_average_bound (planarInverseSchwartz chiA) (planarInverseSchwartz chiB)
    q nu topLength width scale rb C order htop hwidth hC (by omega) hrb hs
    labels theta center hprofile hprofileB b hb hb1 _ hu f g hf hf1
    (fun k => (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hgm))
    (fun k z => (PiLp.norm_apply_le (g z) k).trans (hgb z))
    (6*L^(-21:ℝ)*ratio*(volume.prod volume).real Fset) ?_) hB
  intro origin S
  dsimp only
  let P := finiteNormalizedPacketLattice (planarInverseSchwartz chiA) q nu topLength width scale
    rb C order htop hwidth hC (by omega) hrb hs labels origin theta center S hprofile
  let alt := fun (j : Fin N) (l : P.labels j) (_a : finiteSiteFiber labels S j l.val) (_k : κ) =>
    analysisProfile (planarInverseSchwartz chiB) q nu
  let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound :=
    fun _ _ _ _ => hprofileB
  have hspec := normalizedPacketLattice_spectrum (Item:=fun j l => finiteSiteFiber labels S j l) chiA q nu topLength width scale rb C order
    htop hwidth hC (by omega) hrb hs labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile A B hchiA w cEta CEta hw hlo hhi
  have haspec := normalizedAnalysisFamily_spectrum (Item:=fun j l => finiteSiteFiber labels S j l) chiA q nu topLength width scale rb C order
    htop hwidth hC (by omega) hrb hs labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile A B w cEta CEta hw hlo hhi chiB hprofileB hchiB
  exact (hhigh L hLb N κ Label (fun j l => finiteSiteFiber labels S j l) P Finset.univ w hw hW
    horder (by change 6+2*(8*12+1)≤order; omega) rfl rfl
    (by change budget≤L^(1:ℝ); simpa only [Real.rpow_one] using hbudget) hshort
    hfrequencyLo hfrequency hlocal hunitRange
    (fun j l a k xi et hn => (hspec j l a k xi et hn).1)
    (fun j l a k xi et hn => (hspec j l a k xi et hn).2) alt hAlt
    (fun j l a k xi et hn => (haspec j l a k xi et hn).1)
    (fun j l a k xi et hn => (haspec j l a k xi et hn).2)
    b hb hb1 haway hradius hLip field hfield g f hgm hfm hgb hfb E Fset
    hE hFset hEfin hFfin hFpos hgs hfs l r ratio widthScale hstrip hEstrip hFstrip
    hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq).2

end LipschitzHilbert.PacketRepresentation

end

end OAI
