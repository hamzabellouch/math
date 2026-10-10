import OAI.Analysis.LipschitzHilbert.Trees.SourceCrossAdjointEnergy
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniversalAdjointEnergy
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAdjointPolarization
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelCostPolynomial

namespace OAI

/-! A uniform polynomial energy bound for the actual cross-profile sum.
The remaining cost conditions concern only explicit fixed geometric data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_uniform_cross_energy (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    ordinaryDensityUpper^(1/4:ℝ)≤L → P.profileBound≤L^p → P.referenceEnvelopeConstant≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q‖^2
        ∂volume.prod volume)≤(L^(3*p+6))^2*(volume.prod volume).real E := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_adjoint_energy hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d h₁eq h₂eq h₃eq h₄eq h₅eq alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofile habsolute
  have hLpos : 0<L := by linarith
  have hLone : 1≤L := by linarith
  have hDensityPos : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
  have hscale : 2*L^p≤L^(p+1) := by
    rw [Real.rpow_add hLpos,Real.rpow_one]
    nlinarith [Real.rpow_nonneg hLpos.le p]
  let Q := fun (c : ℂ) (hc : ‖c‖=1) => P.polarize alt hAlt c hc
  have hFor (c : ℂ) (hc : ‖c‖=1) :
      ∀ S : Finset P.PacketIndex, S⊆initial →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
      ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
        (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
        (∫ z, ‖(Q c hc).ordinaryAdjointSum S d.selector u g z‖^2 ∂volume.prod volume)≤
          (L^(3*p+5))^2*(volume.prod volume).real E := by
    let dp := d.polarize alt hAlt c hc hSpectrum hMargin hBin
    have hunitp : dp.unitModelCost CD CS CT≤L := hunit
    have hprofilep : (Q c hc).profileBound≤L^(p+1) :=
      (mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ)≤2)).trans hscale
    have habsoluteEq : (Q c hc).referenceEnvelopeConstant=2*P.referenceEnvelopeConstant := by
      dsimp only [Q,polarize,referenceEnvelopeConstant]
      ring
    have habsolutep : (Q c hc).referenceEnvelopeConstant≤L^(p+1) := by
      rw [habsoluteEq]
      exact (mul_le_mul_of_nonneg_left habsolute (by norm_num : (0:ℝ)≤2)).trans hscale
    have hcost := dp.modelCost_le_rpow CD CS CT L L (p+1) hCS.le hLone le_rfl
      (by linarith) hunitp hprofilep habsolutep
    have hcost' : dp.modelCost CD CS CT≤L^(3*p+4) := by
      convert hcost using 1
      congr 1
      ring
    have hcU : dp.modelCost CD CS CT*ordinaryDensityUpper^(1/4:ℝ)≤L^(3*p+5) := by
      calc
        _ ≤ L^(3*p+4)*L := mul_le_mul hcost' hU (Real.rpow_nonneg hDensityPos.le _) (Real.rpow_nonneg hLpos.le _)
        _ = L^(3*p+4)*L^(1:ℝ) := by rw [Real.rpow_one]
        _ = L^((3*p+4)+1) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring
    intro S hS g hg hg1 E hE hEfin hgs u hu
    have h := hAll N κ Label Item (Q c hc) initial dp h₁eq h₂eq h₃eq h₄eq h₅eq
      S hS g hg hg1 E hE hEfin hgs u hu
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (dp.modelCost_pos CD CS CT).le
        (Real.rpow_nonneg hDensityPos.le _)) hcU 2) measureReal_nonneg)
  have h₁ := hFor 1 (by simp)
  have h₂ := hFor (-1) (by simp)
  have h₃ := hFor Complex.I (by simp)
  have h₄ := hFor (-Complex.I) (by simp)
  have hfinal : 4*(L^(3*p+5))^2≤(L^(3*p+6))^2 := by
    have hn : 2*L^(3*p+5)≤L^(3*p+6) := by
      calc
        _ ≤ L^(3*p+5)*L := by nlinarith [Real.rpow_nonneg hLpos.le (3*p+5)]
        _ = L^(3*p+5)*L^(1:ℝ) := by rw [Real.rpow_one]
        _ = L^((3*p+5)+1) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring
    have hs := pow_le_pow_left₀ (by positivity) hn 2
    nlinarith
  intro S hS g hg hg1 E hE hEfin hgs u hu
  let A := (Q 1 (by simp)).ordinaryAdjointSum S d.selector u g
  let B := (Q (-1) (by simp)).ordinaryAdjointSum S d.selector u g
  let C := (Q Complex.I (by simp)).ordinaryAdjointSum S d.selector u g
  let D := (Q (-Complex.I) (by simp)).ordinaryAdjointSum S d.selector u g
  let X := fun z => ∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q
  have hA := ((Q 1 (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hB := ((Q (-1) (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hC := ((Q Complex.I (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hD := ((Q (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hX := (P.crossSum_memLp alt hAlt 0 d.selector u g 2 S).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hp (z : ℝ×ℝ) : ‖X z‖^2≤‖A z‖^2+‖B z‖^2+‖C z‖^2+‖D z‖^2 :=
    four_polarization_norm_sq _ _ _ _ _ (P.cross_adjoint_polarization alt hAlt S d.selector
      d.measurable d.bounded u hu g hg hg1 z)
  calc
    _ ≤ ∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2+‖D z‖^2 ∂volume.prod volume :=
      integral_mono hX (((hA.add hB).add hC).add hD) hp
    _ = (∫ z, ‖A z‖^2 ∂volume.prod volume)+(∫ z, ‖B z‖^2 ∂volume.prod volume)+
        (∫ z, ‖C z‖^2 ∂volume.prod volume)+(∫ z, ‖D z‖^2 ∂volume.prod volume) := by
      have hab : (∫ z, ‖A z‖^2+‖B z‖^2 ∂volume.prod volume)=
          (∫ z, ‖A z‖^2 ∂volume.prod volume)+(∫ z, ‖B z‖^2 ∂volume.prod volume) := integral_add hA hB
      have habc : (∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2 ∂volume.prod volume)=
          (∫ z, ‖A z‖^2+‖B z‖^2 ∂volume.prod volume)+(∫ z, ‖C z‖^2 ∂volume.prod volume) :=
        integral_add (hA.add hB) hC
      calc
        _ = (∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2 ∂volume.prod volume)+
            (∫ z, ‖D z‖^2 ∂volume.prod volume) := integral_add ((hA.add hB).add hC) hD
        _ = _ := by rw [habc,hab]
    _ ≤ (L^(3*p+5))^2*(volume.prod volume).real E+(L^(3*p+5))^2*(volume.prod volume).real E+
        (L^(3*p+5))^2*(volume.prod volume).real E+(L^(3*p+5))^2*(volume.prod volume).real E :=
      add_le_add (add_le_add (add_le_add (h₁ S hS g hg hg1 E hE hEfin hgs u hu)
        (h₂ S hS g hg hg1 E hE hEfin hgs u hu))
        (h₃ S hS g hg hg1 E hE hEfin hgs u hu)) (h₄ S hS g hg hg1 E hE hEfin hgs u hu)
    _ = (4*(L^(3*p+5))^2)*(volume.prod volume).real E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfinal measureReal_nonneg

end LipschitzHilbert.PacketLatticeData

end

end OAI
