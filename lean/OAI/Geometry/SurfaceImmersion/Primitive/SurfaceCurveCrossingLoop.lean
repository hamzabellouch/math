import OAI.Geometry.SurfaceImmersion.Whitney.ActualSurfaceCollarProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceFrozenCoefficients
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteScalarBounds
import OAI.Geometry.SurfaceImmersion.Primitive.ActualProfileCurveCover
import OAI.Geometry.SurfaceImmersion.Primitive.ProfileCrossingChoice

namespace OAI

/-! One supported loop preserves a finite family of later curves. The
boundary collars are fixed before selecting the compact interior and the
large transverse derivative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity PhaseGeometry SurfaceJetCoordinates

variable {ι : Type*} [Finite ι]

theorem actual_supported_curve_crossing_loop {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    {K : ι → Set Base} (hK : ∀ i, IsCompact (K i)) (hKT : ∀ i, K i ⊆ T)
    {P : Set Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ i, K i) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ i, K i) ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0)
    {E : Set Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c k : ι → Base → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (hk : ∀ i, ContDiff ℝ ∞ (k i))
    (hbc : ∀ i, ∀ x ∈ K i, b i x ≠ 0 ∨ c i x ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (hkb : ∀ i, ∀ x ∈ K i, -B ≤ k i x)
    (hold : ∀ i, ∀ x ∈ K i, a x = 0 →
      0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x))*b i x +
        Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x)*c i x)^2 + k i x*(b i x)^2) :
    ∃ Z : TopologicalSpace.Opens GeometricJet,
      jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
    ∃ l : Loop (jetDomain Z),
      (∀ J, l.amplitude J = a (decode J).1) ∧
      (∃ W : Set GeometricJet, IsOpen W ∧ jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
        ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
    ∃ e₁ e₂ : GeometricJet → Vec, ∃ α : GeometricJet × ℝ → ℝ,
      ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧ ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
      (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
      (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
    (∀ x ∈ T, ∀ t : ℝ, surfaceCircularProfile F a e₁ e₂ α (x,t) ∈ regularBoundaryProfiles) ∧
    ∃ η : ℝ, 0 < η ∧
      (∀ z : ℝ, 0 < z → z < η →
      ∀ i, ∀ x ∈ K i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      k i x ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      realSecondForm G (b i x,c i x) (b i x,c i x) p ≠ 0 ∧
      normalize (realSecondForm G (b i x,c i x) (b i x,c i x) p) ≠
        -profilePreferred (realBoundaryProfile G z p)) ∧
      ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p =
        κ*gramDet (coordDeriv dx G p) (coordDeriv dy G p) →
      -B ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        0 < orderedCrossing G (1,r) (1,s) p κ ∧
        0 < orderedCrossing G (1,s) (1,r) p κ ∧
        ((0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
          0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
         (0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ realSecondForm G (1,s) (1,s) p ∧
           ∃ w : Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
             0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
             0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ w)) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hadapt,sLo,sHi,D,hsLo,hsHi,hD,hfamily⟩ :=
    actual_surface_collar_profile_family hF ha hT hU hTU hn hI hN hHess haT hboundary
  obtain ⟨A,hA,hCA,hAe⟩ := hadapt
  let C₀ : Set Base := {p ∈ T | a p = 0}
  have hC : IsCompact C₀ := hT.inter_right (isClosed_eq ha.continuous continuous_const)
  have hcol (i : ι) := surface_zero_amplitude_collar hF ha hΩ (hK i)
    (fun _ hx => hTΩ (image_mono (hKT i) hx)) hC.isClosed (fun x hx => hx.2) h₁ h₂ hframe hA hCA
    (fun j hj => (hAe j hj).2) (hb i).contDiffOn (hc i).contDiffOn (hk i).contDiffOn
    (fun x hx => hold i x hx.1 hx.2.2)
  choose W hW hCW ε hε hcollar using hcol
  obtain ⟨δ,hδ,hδε⟩ := finite_positive_lower hε
  obtain ⟨V,hV,hCV,hconstruct⟩ := hfamily δ hδ
  let W₀ : Set Base := V ∩ ⋂ i, W i
  have hW₀ : IsOpen W₀ := hV.inter (isOpen_iInter_of_finite hW)
  have hCW₀ : C₀ ⊆ W₀ := fun x hx => ⟨hCV hx,mem_iInter.mpr (fun i => hCW i hx)⟩
  obtain ⟨V₀,hV₀,hCV₀,_,hV₀W⟩ := compact_open_thickening hC hW₀ hCW₀
  let L : Set Base := ⋃ i, K i
  have hL : IsCompact L := isCompact_iUnion hK
  have hLT : L ⊆ T := iUnion_subset hKT
  let I : Set Base := (L \ V₀) ∪ E
  have hIc : IsCompact I := (hL.diff hV₀).union hE.isCompact
  have hIT : I ⊆ T := union_subset (fun _ hx => hLT hx.1) hET
  have haI : ∀ x ∈ I, 0 < a x := by
    intro x hx
    rcases hx with hx | hx
    · apply lt_of_le_of_ne (haT x (hLT hx.1))
      intro hz
      exact hx.2 (hCV₀ ⟨hLT hx.1,hz.symm⟩)
    · exact haE x hx
  let P₀ := (P ∩ I) ∪ E
  have hP₀ : P₀.Finite := (hP.inter_of_left I).union hE
  have hP₀I : P₀ ⊆ I := union_subset inter_subset_right subset_union_right
  have hlocalI : ∀ p ∈ I \ P₀, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ I ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0 := by
    intro p hp
    have hpE : p ∉ E := fun h => hp.2 (Or.inr h)
    have hpL : p ∈ L := (hp.1.resolve_right hpE).1
    obtain ⟨N,hN,hpN,f,hf,hzero,hderiv⟩ := hlocal p ⟨hpL,fun h => hp.2 (Or.inl ⟨h,hp.1⟩)⟩
    refine ⟨N ∩ Eᶜ,hN.inter hE.isClosed.isOpen_compl,⟨hpN,hpE⟩,f,hf.mono inter_subset_left,?_,hderiv⟩
    intro x hx
    have hxL := hx.1.resolve_right hx.2.2
    exact hzero x ⟨hxL.1,hx.2.1⟩
  let X (i : ι) := ↥(K i ×ˢ Icc (0 : ℝ) 1)
  let (i : ι) : CompactSpace (X i) := isCompact_iff_compactSpace.mp ((hK i).prod isCompact_Icc)
  let C (i : ι) : Set (X i) := {w | w.val.1 ∈ closure V₀}
  let Q (i : ι) : Set (X i) := {w | w.val.1 ∉ V₀}
  have hC' (i : ι) : IsClosed (C i) := isClosed_closure.preimage (continuous_fst.comp continuous_subtype_val)
  have hQ' (i : ι) : IsClosed (Q i) := hV₀.isClosed_compl.preimage (continuous_fst.comp continuous_subtype_val)
  have hcover (i : ι) : ∀ w : X i, w ∈ C i ∨ w ∈ Q i := by
    intro w
    by_cases h : w.val.1 ∈ V₀
    · exact Or.inl (subset_closure h)
    · exact Or.inr h
  have hthreshold (i : ι) := compact_actual_profile_curve_cover (hC' i) (hQ' i) (hcover i)
    sLo B D hsLo hB hD
  choose H hH htransfer using hthreshold
  obtain ⟨Hbase,hHbase,hHHbase⟩ := finite_positive_upper H
  let Y := ↥(E ×ˢ Icc (0 : ℝ) 1)
  let : CompactSpace Y := isCompact_iff_compactSpace.mp (hE.isCompact.prod isCompact_Icc)
  obtain ⟨Hcross,hHcross,hcross⟩ := compact_actual_profile_crossings (X := Y)
    sLo sHi B D slopeBound hsLo hsHi hB hD hSlope
  obtain ⟨Hnormal,hHnormal,hnormal⟩ := compact_actual_profile_crossing_choice (X := Y)
    sLo sHi B D slopeBound hsLo hsHi hB hD hSlope
  let H₀ := max Hbase (max Hcross Hnormal)
  have hH₀ : 0 < H₀ := hHbase.trans_le (le_max_left _ _)
  have hHH₀ (i : ι) : H i ≤ H₀ := (hHHbase i).trans (le_max_left _ _)
  have hCrossH : Hcross ≤ H₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hNormalH : Hnormal ≤ H₀ := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,hsmall,hprofile,hturn⟩ :=
    hconstruct I P₀ hIc hIT haI hP₀ hP₀I hlocalI H₀ hH₀.le
  have hgood (i : ι) : ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ w : X i, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α w.val‖ < η →
      k i w.val.1 ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      realSecondForm G (b i w.val.1,c i w.val.1) (b i w.val.1,c i w.val.1) p ≠ 0 ∧
      normalize (realSecondForm G (b i w.val.1,c i w.val.1) (b i w.val.1,c i w.val.1) p) ≠
        -profilePreferred (realBoundaryProfile G z p) := by
    let J : X i → BoundaryProfile := fun w => surfaceCircularProfile F a e₁ e₂ α w.val
    have hJ : Continuous J := by
      exact ((surfaceCircularProfile_smoothOn hF ha hΩ hZΩ h₁ h₂ hα).continuousOn.mono
        (fun w hw => ⟨hTZ (mem_image_of_mem _ (hKT i hw.1)),mem_univ _⟩)).domRestrict
    have hd (w : X i) := hprofile w.val.1 (hKT i w.property.1) w.val.2
    have hturn' : ∀ w ∈ Q i, profileCoefficients (J w) 3 = 0 →
        H i+2 < |profileCoefficients (J w) 2| := by
      intro w hw hz
      have hh := hturn w.val.1 (Or.inl ⟨mem_iUnion.mpr ⟨i,w.property.1⟩,hw⟩) w.val.2 w.property.2 hz
      linarith [hHH₀ i]
    apply htransfer i J hJ (fun w => (hd w).1) (fun w => (hd w).2.1)
      (fun w => (hd w).2.2.2) hturn'
      (fun w => b i w.val.1) (fun w => c i w.val.1) (fun w => k i w.val.1)
      ((hb i).continuous.comp (continuous_fst.comp continuous_subtype_val))
      ((hc i).continuous.comp (continuous_fst.comp continuous_subtype_val))
      ((hk i).continuous.comp (continuous_fst.comp continuous_subtype_val))
      (fun w => hbc i w.val.1 w.property.1) (fun w => hkb i w.val.1 w.property.1)
    intro w hw
    have hWmem : w.val.1 ∈ W i := mem_iInter.mp (hV₀W hw).2 i
    have hVmem : w.val.1 ∈ V := (hV₀W hw).1
    have hθ := (hsmall w.val.1 hVmem w.val.2).trans_le (hδε i)
    obtain ⟨hS,hD'⟩ := surfaceCircularProfile_frozen_coefficients hF ha hΩ hZΩ h₁ h₂ hframe hα
      (hTZ (mem_image_of_mem _ (hKT i w.property.1))) w.val.2
    change 0 < (profileCoefficients _ 1 * _ + profileCoefficients _ 0 * _)^2 + _
    rw [hS,hD']
    exact hcollar i w.val.1 ⟨w.property.1,hWmem⟩ _ hθ
  choose η hη hgood' using hgood
  obtain ⟨η₀,hη₀,hη₀η⟩ := finite_positive_lower hη
  let J : Y → BoundaryProfile := fun w => surfaceCircularProfile F a e₁ e₂ α w.val
  have hJ : Continuous J :=
    ((surfaceCircularProfile_smoothOn hF ha hΩ hZΩ h₁ h₂ hα).continuousOn.mono
      (fun w hw => ⟨hTZ (mem_image_of_mem _ (hET hw.1)),mem_univ _⟩)).domRestrict
  have hd (w : Y) := hprofile w.val.1 (hET w.property.1) w.val.2
  have ht (w : Y) (hz : profileCoefficients (J w) 3 = 0) :=
    hturn w.val.1 (Or.inr w.property.1) w.val.2 w.property.2 hz
  obtain ⟨ηc,hηc,hcross'⟩ := hcross J hJ (fun w => (hd w).1) (fun w => (hd w).2.1)
    (fun w => (hd w).2.2.1) (fun w => (hd w).2.2.2)
    (fun w hz => lt_of_le_of_lt (add_le_add hCrossH le_rfl) (ht w hz))
  obtain ⟨ηn,hηn,hnormal'⟩ := hnormal J hJ (fun w => (hd w).1) (fun w => (hd w).2.1)
    (fun w => (hd w).2.2.1) (fun w => (hd w).2.2.2)
    (fun w hz => lt_of_le_of_lt (add_le_add hNormalH le_rfl) (ht w hz))
  let ηall := min η₀ (min ηc ηn)
  have hηall : 0 < ηall := lt_min hη₀ (lt_min hηc hηn)
  have hηcurve : ηall ≤ η₀ := min_le_left _ _
  have hηcross : ηall ≤ ηc := (min_le_right _ _).trans (min_le_left _ _)
  have hηnormal : ηall ≤ ηn := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Z,hTZ,fun j hj => hΩ (hZΩ hj),l,hamp,hzero,e₁,e₂,α,h₁.mono hZΩ,h₂.mono hZΩ,
    hα,hper,hvel,(fun x hx t => (hprofile x hx t).1),ηall,hηall,?_,?_⟩
  · intro z hz hzη i x hx t ht G hG p herr hcurv
    exact hgood' i z hz (hzη.trans_le (hηcurve.trans (hη₀η i))) ⟨(x,t),hx,ht⟩ G hG p
      (herr.trans_le (hηcurve.trans (hη₀η i))) hcurv
  · intro z hz hzη x hx t ht G hG p herr κ hκ hcurv r s hr hs
    obtain ⟨hleft,hright⟩ := hcross' z hz (hzη.trans_le hηcross) ⟨(x,t),hx,ht⟩
      G hG p (herr.trans_le hηcross) κ hκ hcurv r s hr hs
    exact ⟨hleft,hright,hnormal' z hz (hzη.trans_le hηnormal) ⟨(x,t),hx,ht⟩
      G hG p (herr.trans_le hηnormal) hcurv r s hr hs⟩

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
