import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityForestIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceDensitySpatialCost

namespace OAI

/-! The actual high-density removal step, with the manuscript's small
power loss and an exact remainder of density at most the new threshold. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_density_removal_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hcbQuarter : cb≤1/4)
    (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M R K : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (initial : Finset P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau eta density sigma radius Lip F : ℝ),
      0<eta → 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤density → 0≤sigma → 1≤radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤sigma^2*T.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
      let removed := initial.filter (fun q => eta<P.ordinaryDensity 0 cell grid w tau E u q)
      let remaining := initial\removed
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      remaining⊆initial ∧
      (∀ q∈remaining, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧
      IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
        (625*densityRadiusConstant^2)*P.ordinaryTreeConstant C ((2*R+1)*M) K Lip*
          sigma*density*(1+eta^(-(1/20:ℝ)))*(2*(volume.prod volume).real E/eta) := by
  obtain ⟨C,hC,hIntegral⟩ := exists_density_forest_integral hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K hR horder initial c cell grid w tau eta density sigma
    radius Lip F heta hw hW hF hfreq htime hLip hdensity hsigma hwide hK hlocal
    hrow hspectrum hbin hsize selector hsel hbound haway hsupport hradius hnear E hE hEfin u hu hden
    removed remaining V
  classical
  have hsub : removed⊆initial := Finset.filter_subset _ _
  have hlarge (q : P.PacketIndex) (hq : q∈removed) :
      eta<P.ordinaryDensity 0 cell grid w tau E u q := (Finset.mem_filter.mp hq).2
  obtain ⟨forest⟩ := P.exists_ordinary_density_forest removed cell grid w tau eta hw hW heta E u hE hEfin hu hlarge
  have h := hIntegral N κ Label Item P M R K (densitySpatialCount eta) hR horder
    removed initial hsub c cell grid w tau eta density sigma radius Lip F E u forest
    (densitySpatialCount_covers eta) hw hW hF hfreq htime hLip hdensity hsigma hwide hK hlocal
    (fun q hq => hrow q (hsub hq)) (fun q hq => hspectrum q (hsub hq))
    (fun q hq => hbin q (hsub hq)) hsize selector hsel hbound
    (fun i q _ k hn => haway q.1 q.2.1 k (forest.top i).slope hn) hsupport hradius
    (fun i j l k s hs => hnear j l k s (forest.top i).slope hs) hE hu
    (fun q hq => hden q (hsub hq))
  have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=∑ q∈removed, V q z := by
    have hs := Finset.sum_sdiff hsub (f:=fun q => V q z)
    change (∑ q∈initial, V q z)-(∑ q∈initial\removed, V q z)=_
    rw [←hs]
    abel
  refine ⟨Finset.sdiff_subset,?_,?_,?_⟩
  · intro q hq
    have hq' := Finset.mem_sdiff.mp hq
    by_contra hn
    exact hq'.2 (Finset.mem_filter.mpr ⟨hq'.1,lt_of_not_ge hn⟩)
  · have hefun := funext heval
    rw [hefun]
    exact h.1
  · simp only [heval]
    apply h.2.trans
    have hTree : 0≤P.ordinaryTreeConstant C ((2*R+1)*M) K Lip := by
      have ht := transverseTailConstant_nonneg
      have ha := P.absoluteConstant_pos
      have hp := P.profileBound_pos
      dsimp [ordinaryTreeConstant]
      positivity
    have hBudget : 0≤2*(volume.prod volume).real E/eta :=
      div_nonneg (mul_nonneg (by norm_num) measureReal_nonneg) heta.le
    have hcount := mul_le_mul_of_nonneg_right (densitySpatialCost_le heta)
      (mul_nonneg (mul_nonneg (mul_nonneg hTree hsigma) hdensity) hBudget)
    convert hcount using 1 <;> ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
