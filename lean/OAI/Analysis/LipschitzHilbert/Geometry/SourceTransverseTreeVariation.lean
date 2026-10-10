import OAI.Analysis.LipschitzHilbert.Geometry.SourceTransversePacketEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeMaximal

namespace OAI

/-! The transverse order-103 tree estimate needed by the ordinary-tree
argument. It uses only the published scalar Lepingle input and retains
one integrable transverse decay power. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem integral_from_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (C : ℝ) (hC : 0≤C)
    (hfm : AEStronglyMeasurable f μ) (hf : ∀ x, 0≤f x)
    (hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ)≤ENNReal.ofReal C) :
    Integrable f μ ∧ (∫ x, f x ∂μ)≤C := by
  have hi : Integrable f μ := ⟨hfm,(hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hf)).mpr (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hlin

namespace SourceLatticePacket

theorem exists_transverse_physical_tree_variation (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
        P.physicalTreeVariation t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤C*P.absoluteConstant^2*
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  let lower := (cEta*cb-cStar)/(2*Real.pi)
  let upper := (CEta*Cb+cStar)/(2*Real.pi)
  have hlower : 0<lower := div_pos (sub_pos.mpr hgap) (by positivity)
  have hupper : 0≤upper := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  obtain ⟨K,hK,hvar⟩ := scaled_dyadic_hilbert_annular_variation hL hlower hupper
  let A := (4*Real.pi)^2*Real.pi*(16:ℝ)^103
  have hA : 0<A := mul_pos (mul_pos (sq_pos_of_pos (by positivity)) Real.pi_pos)
    (pow_pos (by norm_num) _)
  have hKr : 0<(K:ℝ) := by exact_mod_cast hK
  refine ⟨(K:ℝ)*A*Real.pi,mul_pos (mul_pos hKr hA) Real.pi_pos,?_⟩
  intro N κ ι _ _ P t w b hw horder c hZ hspectrum hselector
  let f := fun y j k => packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)
  let M := fun y => A*P.absoluteConstant^2*
    ∑ j, P.length j*∑ u, ‖c j u‖^2*
      lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y
  have hPy (j : Fin N) (u : ι j) : |P.width*(P.snappedSite j u).2-b|≤2*P.width := by
    have he := snappedLatticeSite_vertical (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) P.width_pos (P.site j u)
    change |P.actualZ j u-P.width*(P.snappedSite j u).2|≤P.width at he
    calc
      _ ≤ |P.width*(P.snappedSite j u).2-P.actualZ j u|+|P.actualZ j u-b| := abs_sub_le _ _ _
      _ ≤ P.width+P.width := add_le_add (by simpa only [abs_sub_comm] using he) (hZ j u)
      _ = _ := by ring
  have hraw (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
      P.physicalPacket t j u k (x,y+t*x)=P.raw 0 j u k y x := by
    have hh : P.raw 0 j u k y = planarSchwartzSlice
        (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale 0) y t :=
      P.raw_eq_physical_slice 0 j u k y t
    simpa only [planarCovariantJet,ite_true,planarSchwartzSlice_apply] using
      (congrArg (fun g : SchwartzMap ℝ ℂ => g x) hh).symm
  have hpartial (y x : ℝ) (n : ℕ) : P.physicalTreePartial t c n (x,y+t*x)=
      hilbertPartialBandSum (f y) n x := by
    rw [hilbertPartialBandSum_eq_packetPartialSum]
    apply congrArg (fun v : Fin N → EuclideanSpace ℂ κ => packetPartialSum v n)
    funext j
    ext k
    simp only [planarFixedSynthesis,WithLp.ofLp_toLp,f,packetSynthesis_apply,hraw]
  have hlow (y : ℝ) (j : Fin N) (k : κ) (ξ : ℝ) (hξ : |ξ|<(lower/P.topLength)*(2:ℝ)^j.val) :
      𝓕 (f y j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ ξ fun u =>
      (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).1 ξ hξ
  have hhigh (y : ℝ) (j : Fin N) (k : κ) (ξ : ℝ) (hξ : (upper/P.topLength)*(2:ℝ)^j.val < |ξ|) :
      𝓕 (f y j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ ξ fun u =>
      (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).2 ξ hξ
  have hline (y : ℝ) := hvar P.topLength P.topLength_pos N κ (f y) (hlow y) (hhigh y)
  have henergy (y : ℝ) : polynomialWeight b (2*P.width) 103 y^2*
      (∑ j, ∑ k, ∫ x, ‖f y j k x‖^2)≤M y := by
    have h := transverse_lattice_slice_energy c (fun j u k => P.raw 0 j u k y)
      (fun j u => P.length j*(P.snappedSite j u).1)
      (fun j u => P.width*(P.snappedSite j u).2) P.snappedSite P.length
      0 0 b P.width y P.absoluteConstant P.width_pos P.length_pos P.snappedSite_injective
      (by intros; ring) (by intros; ring) hPy (by
        intro j u k x
        apply (P.raw_absolute_lattice_envelope 0 j u k y x).trans
        apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
        exact mul_le_mul (lineEnvelope_antitone _ _ _ (by omega : 1≤P.order))
          (lineEnvelope_antitone _ _ _ horder)
          (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    simpa only [f,M,A,mul_assoc,mul_left_comm,mul_comm] using h
  let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
    P.physicalTreeVariation t c z^2
  have hEc : Continuous E := by
    have hp : Continuous (fun z : ℝ×ℝ => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)) := by
      unfold polynomialWeight
      fun_prop
    exact (hp.pow 2).mul ((P.physicalTreeVariation_continuous t c).pow 2)
  have hEeq (x y : ℝ) : ENNReal.ofReal (E (x,y+t*x))=
      ENNReal.ofReal (polynomialWeight b (2*P.width) 103 y^2)*
        ENNReal.ofReal (finiteCubicVariation (fun n => hilbertPartialBandSum (f y) n x) N)^(2/3:ℝ) := by
    simp only [E,physicalTreeVariation,hpartial,cubicVariation_sq]
    rw [show y+t*x-t*x=y by ring,ENNReal.ofReal_mul (sq_nonneg _),
      ←ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num : (0:ℝ)≤2/3)]
  have hM : Integrable M := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _
  have hM0 (y : ℝ) : 0≤M y := by
    exact mul_nonneg (mul_nonneg hA.le (sq_nonneg _)) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (P.length_pos j).le (Finset.sum_nonneg fun u _ =>
        mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _)))
  have hIntM : (∫ y, M y)=A*P.absoluteConstant^2*Real.pi*
      ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
    dsimp only [M]
    rw [integral_const_mul,integral_finsetSum _ (fun j _ =>
      (integrable_finsetSum _ fun u _ =>
        (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _).const_mul _)]
    simp_rw [integral_const_mul,integral_finsetSum _ (fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _),
      integral_const_mul,integral_lineEnvelope_one _ P.width P.width_pos]
    simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
  have hlin : (∫⁻ z, ENNReal.ofReal (E z) ∂volume.prod volume)≤
      (K:ℝ≥0∞)*ENNReal.ofReal (∫ y, M y) := by
    rw [←(slopeShear_measurePreserving t).lintegral_comp hEc.measurable.ennreal_ofReal]
    rw [lintegral_prod_symm (fun z : ℝ×ℝ => ENNReal.ofReal (E (slopeShear t z)))
      ((hEc.measurable.comp (slopeShear t).measurable).ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ y, (K:ℝ≥0∞)*ENNReal.ofReal (M y) := by
        apply lintegral_mono
        intro y
        change (∫⁻ x, ENNReal.ofReal (E (x,y+t*x)))≤_
        simp_rw [hEeq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc
          _ ≤ ENNReal.ofReal (polynomialWeight b (2*P.width) 103 y^2)*
              ((K:ℝ≥0∞)*ENNReal.ofReal _) := mul_le_mul_right (hline y) _
          _ = (K:ℝ≥0∞)*ENNReal.ofReal (polynomialWeight b (2*P.width) 103 y^2*_) := by
            rw [ENNReal.ofReal_mul (sq_nonneg _)]; ac_rfl
          _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal (henergy y)) _
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp),
          ←ofReal_integral_eq_lintegral_ofReal hM (Filter.Eventually.of_forall hM0)]
  have hsum0 : 0≤∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos j).le) P.width_pos.le
  apply integral_from_lintegral (volume.prod volume) E _
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKr.le hA.le) Real.pi_pos.le)
      (sq_nonneg P.absoluteConstant)) hsum0)
    hEc.aestronglyMeasurable (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hIntM] at hlin
  have hkc : ENNReal.ofReal (K:ℝ)=(K:ℝ≥0∞) := by simp
  rw [←hkc,←ENNReal.ofReal_mul K.coe_nonneg] at hlin
  convert hlin using 1
  congr 1
  ac_rfl

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
