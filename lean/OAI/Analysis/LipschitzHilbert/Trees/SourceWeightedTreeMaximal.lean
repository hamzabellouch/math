import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.ScaledAnnularVariation
import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedAnnularVariation
import OAI.Analysis.LipschitzHilbert.Estimates.IntervalOscillation
import OAI.Analysis.LipschitzHilbert.Estimates.VariationContinuous

namespace OAI

/-! Polynomially weighted interval-maximal synthesis on actual separated
source trees, conditional only on the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem continuous_interval_max {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => intervalOscillation (fun n => F n x) N 0 N) := by
  classical
  let v := fun (q : Fin (N+1)×Fin (N+1)) (x : X) =>
    if 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N then ‖F q.2 x-F q.1 x‖ else 0
  have hv (q) : Continuous (v q) := by
    by_cases hq : 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N
    · simpa only [v,ite_eq_left hq,Pi.sub_apply] using ((hF q.2).sub (hF q.1)).norm
    · simp only [v,ite_eq_right hq]; exact continuous_const
  have h := Continuous.finset_sup' Finset.univ_nonempty (fun q _ => hv q)
  convert h using 1
  funext x
  simp only [intervalOscillation,v,Finset.sup'_apply]

private theorem interval_max_le_variation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : intervalOscillation F N 0 N≤cubicVariation F N := by
  obtain ⟨a,b,_,hab,hb,heq⟩ := exists_intervalOscillation_eq F N 0 N (Nat.zero_le _)
  rw [heq]
  exact increment_le_cubicVariation F N a b hab hb

private theorem integral_of_nonnegative_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (C : ℝ) (hC : 0≤C)
    (hfm : AEStronglyMeasurable f μ) (hf : ∀ x, 0≤f x)
    (hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ)≤ENNReal.ofReal C) :
    Integrable f μ ∧ (∫ x, f x ∂μ)≤C := by
  have hi : Integrable f μ := ⟨hfm,(hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hf)).mpr (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hlin

private theorem interval_max_sum_le {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    (F : I → ℕ → E) (N : ℕ) :
    intervalOscillation (fun n => ∑ i, F i n) N 0 N≤
      ∑ i, intervalOscillation (F i) N 0 N := by
  classical
  unfold intervalOscillation
  apply Finset.sup'_le
  intro q _
  split_ifs with hq
  · rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact increment_le_intervalOscillation (F i) N 0 N q.1 q.2
      (Nat.zero_le _) hq.2.1 hq.2.2 le_rfl
  · exact Finset.sum_nonneg fun i _ => intervalOscillation_nonneg (F i) N 0 N


namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def physicalTreePartial (P : SourceLatticePacket N κ ι) (t : ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  packetPartialSum (fun j => planarFixedSynthesis (c j) (P.physicalPacket t j) z) n

def physicalTreeVariation (P : SourceLatticePacket N κ ι) (t : ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  cubicVariation (fun n => P.physicalTreePartial t c n z) N

def physicalTreeMaximal (P : SourceLatticePacket N κ ι) (t : ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  intervalOscillation (fun n => P.physicalTreePartial t c n z) N 0 N

theorem physicalTreePartial_continuous (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) (n : ℕ) :
    Continuous (P.physicalTreePartial t c n) := by
  classical
  unfold physicalTreePartial packetPartialSum
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    unfold planarFixedSynthesis
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_finsetSum _ fun u _ =>
      continuous_const.mul (P.physicalPacket t j u k).continuous
  · simp only [ite_eq_right hj]; exact continuous_const

theorem physicalTreeVariation_continuous (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) : Continuous (P.physicalTreeVariation t c) :=
  continuous_cubicVariation _ (P.physicalTreePartial_continuous t c) N

theorem physicalTreeMaximal_continuous (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) : Continuous (P.physicalTreeMaximal t c) :=
  continuous_interval_max _ (P.physicalTreePartial_continuous t c) N

/-- A stronger cubic-variation estimate implies the actual interval
maximum. All polynomial and Fourier scales remain those of the source. -/
theorem exists_weighted_physical_tree_variation (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w a b r : ℝ), 0<w → 0<r →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j (_u : ι j), P.length j≤r) →
      (∀ j u, |P.actualX j u-a|≤r) →
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => treeProductPolynomial a b r P.width t z^2 *
        P.physicalTreeVariation t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤C*P.absoluteConstant^2 *
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  let lower := (cEta*cb-cStar)/(2*Real.pi)
  let upper := (CEta*Cb+cStar)/(2*Real.pi)
  have hlower : 0<lower := div_pos (sub_pos.mpr hgap) (by positivity)
  have hupper : 0≤upper := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  obtain ⟨K,hK,hvar⟩ := scaled_dyadic_hilbert_annular_variation hL hlower hupper
  refine ⟨(K:ℝ)*(4*Real.pi)^2*256*Real.pi^2,by positivity,?_⟩
  intro N κ ι _ _ P t w a b r hw hr c hlen hX hZ hspectrum hselector
  let f := fun y j k => packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)
  let M := fun y => (4*Real.pi)^2*P.absoluteConstant^2*256*Real.pi *
    ∑ j, P.length j*∑ u, ‖c j u‖^2*
      lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y
  have hPx (j) (u : ι j) : |P.length j*(P.snappedSite j u).1-a|≤2*r := by
    have he := snappedLatticeSite_horizontal (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) (P.length_pos j) (P.site j u)
    change |P.actualX j u-P.length j*(P.snappedSite j u).1|≤P.length j at he
    calc
      _ ≤ |P.length j*(P.snappedSite j u).1-P.actualX j u|+|P.actualX j u-a| :=
        abs_sub_le _ _ _
      _ ≤ P.length j+r := add_le_add (by simpa only [abs_sub_comm] using he) (hX j u)
      _ ≤ 2*r := by linarith [hlen j u]
  have hPy (j) (u : ι j) : |P.width*(P.snappedSite j u).2-b|≤2*P.width := by
    have he := snappedLatticeSite_vertical (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) P.width_pos (P.site j u)
    change |P.actualZ j u-P.width*(P.snappedSite j u).2|≤P.width at he
    calc
      _ ≤ |P.width*(P.snappedSite j u).2-P.actualZ j u|+|P.actualZ j u-b| := abs_sub_le _ _ _
      _ ≤ P.width+P.width := add_le_add (by simpa only [abs_sub_comm] using he) (hZ j u)
      _ = _ := by ring
  have hraw (j) (u : ι j) (k) (y x : ℝ) :
      P.physicalPacket t j u k (x,y+t*x) = P.raw 0 j u k y x := by
    have hh : P.raw 0 j u k y = planarSchwartzSlice
        (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale 0) y t :=
      P.raw_eq_physical_slice 0 j u k y t
    simpa only [planarCovariantJet,ite_true,planarSchwartzSlice_apply] using
      (congrArg (fun f : SchwartzMap ℝ ℂ => f x) hh).symm
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
  have hline (y : ℝ) :
      (∫⁻ x, ENNReal.ofReal (polynomialWeight a (2*r) 1 x^2) *
        ENNReal.ofReal (finiteCubicVariation (fun n => hilbertPartialBandSum (f y) n x) N)^(2/3:ℝ)) ≤
      (K:ℝ≥0∞)*ENNReal.ofReal (∑ j, ∑ k, ∫ x,
        ‖polynomialLocalization a (2*r) 1 (f y j k) x‖^2) := by
    have h := hvar P.topLength P.topLength_pos N κ
      (fun j k => polynomialLocalization a (2*r) 1 (f y j k))
      (fun j k => polynomialLocalization_low _ _ _ _ _ _ (hlow y j k) (hhigh y j k))
      (fun j k => polynomialLocalization_high _ _ _ _ _ _ (hlow y j k) (hhigh y j k))
    simpa only [hilbertPartialBandSum_polynomialLocalization,
      ennreal_finiteCubicVariation_smul_square] using h
  have henergy (y : ℝ) : polynomialWeight b (2*P.width) 1 y^2 *
      (∑ j, ∑ k, ∫ x, ‖polynomialLocalization a (2*r) 1 (f y j k) x‖^2)≤M y := by
    have h := weighted_packet_energy c (fun j u k => P.raw 0 j u k y)
      (fun j u => P.length j*(P.snappedSite j u).1)
      (fun j u => P.width*(P.snappedSite j u).2) P.snappedSite P.length
      0 0 a (2*r) P.width y P.absoluteConstant (by positivity) P.width_pos P.length_pos
      (fun j u => by linarith [hlen j u]) P.snappedSite_injective
      (by intros; ring) (by intros; ring) hPx (by
        intro j u k x
        apply (P.raw_absolute_lattice_envelope 0 j u k y x).trans
        apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
        exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
          (lineEnvelope_antitone _ _ _ P.order_ge_three)
          (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans
    have he (j) (u : ι j) := polynomialWeight_sq_mul_envelope y
      (P.width*(P.snappedSite j u).2) b P.width (2*P.width) 1 1 P.width_pos
      (mul_pos (by norm_num) P.width_pos) (by linarith [P.width_pos]) (hPy j u)
    simp only [Nat.reduceAdd,Nat.reduceMul,pow_one] at he
    dsimp only [M]
    calc
      _ = ((4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi) *
          ∑ j, P.length j*∑ u, ‖c j u‖^2*
            (polynomialWeight b (2*P.width) 1 y^2*
              lineEnvelope (P.width*(P.snappedSite j u).2) P.width 3 y) := by
        simp only [Finset.mul_sum]; ring_nf
      _ ≤ ((4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi) *
          ∑ j, P.length j*∑ u, ‖c j u‖^2*
            (16*lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (P.length_pos j).le
        exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (he j u) (sq_nonneg _)
      _ = _ := by simp only [Finset.mul_sum]; ring_nf
  let E := fun z => treeProductPolynomial a b r P.width t z^2 *
    P.physicalTreeVariation t c z^2
  have hEc : Continuous E := by
    have hp : Continuous (treeProductPolynomial a b r P.width t) := by
      unfold treeProductPolynomial polynomialWeight; fun_prop
    exact (hp.pow 2).mul ((P.physicalTreeVariation_continuous t c).pow 2)
  have hEeq (x y : ℝ) : ENNReal.ofReal (E (x,y+t*x))=
      ENNReal.ofReal (polynomialWeight b (2*P.width) 1 y^2) *
        (ENNReal.ofReal (polynomialWeight a (2*r) 1 x^2) *
          ENNReal.ofReal (finiteCubicVariation (fun n => hilbertPartialBandSum (f y) n x) N)^(2/3:ℝ)) := by
    simp only [E,treeProductPolynomial,physicalTreeVariation,hpartial,cubicVariation_sq]
    rw [show y+t*x-t*x=y by ring,mul_pow,ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      ENNReal.ofReal_mul (sq_nonneg _),←ENNReal.ofReal_rpow_of_nonneg
        (finiteCubicVariation_nonneg _ _) (by norm_num : (0:ℝ)≤2/3)]
    ac_rfl
  have hM : Integrable M := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _
  have hM0 (y : ℝ) : 0≤M y := by
    dsimp only [M]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (P.length_pos j).le (Finset.sum_nonneg fun u _ =>
        mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _)))
  have hIntM : (∫ y, M y)=((4*Real.pi)^2*P.absoluteConstant^2*256*Real.pi^2)*
      ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
    dsimp only [M]
    rw [integral_const_mul,integral_finsetSum _ (fun j _ =>
      (integrable_finsetSum _ fun u _ =>
        (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _).const_mul _)]
    simp_rw [integral_const_mul,integral_finsetSum _ (fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _),
      integral_const_mul,integral_lineEnvelope_one _ P.width P.width_pos]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hlin : (∫⁻ z, ENNReal.ofReal (E z) ∂volume.prod volume)≤
      (K:ℝ≥0∞)*ENNReal.ofReal (∫ y, M y) := by
    rw [←(slopeShear_measurePreserving t).lintegral_comp (hEc.measurable.ennreal_ofReal)]
    rw [lintegral_prod_symm (fun z : ℝ×ℝ => ENNReal.ofReal (E (slopeShear t z)))
      ((hEc.measurable.comp (slopeShear t).measurable).ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ y, (K:ℝ≥0∞)*ENNReal.ofReal (M y) := by
        apply lintegral_mono
        intro y
        change (∫⁻ x, ENNReal.ofReal (E (x,y+t*x))) ≤ _
        simp_rw [hEeq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc
          _ ≤ ENNReal.ofReal (polynomialWeight b (2*P.width) 1 y^2)*
              ((K:ℝ≥0∞)*ENNReal.ofReal _) := mul_le_mul_right (hline y) _
          _ = (K:ℝ≥0∞)*ENNReal.ofReal (polynomialWeight b (2*P.width) 1 y^2*_) := by
            rw [ENNReal.ofReal_mul (sq_nonneg _)]; ac_rfl
          _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal (henergy y)) _
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp),
          ←ofReal_integral_eq_lintegral_ofReal hM (Filter.Eventually.of_forall hM0)]
  have hsum0 : 0≤∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos j).le) P.width_pos.le
  apply integral_of_nonnegative_lintegral (volume.prod volume) E _ (by positivity)
    hEc.aestronglyMeasurable (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hIntM] at hlin
  convert hlin using 1
  have hkc : ENNReal.ofReal (K:ℝ)=(K:ℝ≥0∞) := by simp
  rw [←hkc,←ENNReal.ofReal_mul K.coe_nonneg]
  congr 1
  ring

/-- The maximum is the literal maximum of all interval sums, including
empty intervals. It inherits the stronger variation energy estimate. -/
theorem exists_weighted_physical_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w a b r : ℝ), 0<w → 0<r →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j (_u : ι j), P.length j≤r) →
      (∀ j u, |P.actualX j u-a|≤r) →
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => treeProductPolynomial a b r P.width t z^2 *
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤C*P.absoluteConstant^2 *
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hbound⟩ := exists_weighted_physical_tree_variation hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ ι _ _ P t w a b r hw hr c hlen hX hZ hspectrum hselector
  obtain ⟨hi,hb⟩ := hbound N κ ι P t w a b r hw hr c hlen hX hZ hspectrum hselector
  have hp (z : ℝ×ℝ) : P.physicalTreeMaximal t c z≤P.physicalTreeVariation t c z :=
    interval_max_le_variation _ N
  have hle (z : ℝ×ℝ) : treeProductPolynomial a b r P.width t z^2*P.physicalTreeMaximal t c z^2≤
      treeProductPolynomial a b r P.width t z^2*P.physicalTreeVariation t c z^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (intervalOscillation_nonneg _ _ _ _) (hp z) 2) (sq_nonneg _)
  have hc : Continuous (fun z => treeProductPolynomial a b r P.width t z^2*P.physicalTreeMaximal t c z^2) := by
    have hwc : Continuous (treeProductPolynomial a b r P.width t) := by
      unfold treeProductPolynomial polynomialWeight; fun_prop
    exact (hwc.pow 2).mul ((P.physicalTreeMaximal_continuous t c).pow 2)
  have him : Integrable (fun z => treeProductPolynomial a b r P.width t z^2*P.physicalTreeMaximal t c z^2)
      (volume.prod volume) := hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg (treeProductPolynomial a b r P.width t z))
          (sq_nonneg (P.physicalTreeMaximal t c z)))] using hle z)
  exact ⟨him,(integral_mono him hi hle).trans hb⟩

end SourceLatticePacket


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

def physicalTreePartial (P : SourceLabeledLattice N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  packetPartialSum (fun j => planarFixedSynthesis
    (fun q : Σ l : P.labels j, Item j l => c j q.1 q.2)
    (fun q k => P.physicalPacket t j q.1 q.2 k) z) n

def physicalTreeMaximal (P : SourceLabeledLattice N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  intervalOscillation (fun n => P.physicalTreePartial t c n z) N 0 N

theorem physicalTreePartial_continuous (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) :
    Continuous (P.physicalTreePartial t c n) := by
  classical
  unfold physicalTreePartial packetPartialSum
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    unfold planarFixedSynthesis
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_finsetSum _ fun u _ =>
      continuous_const.mul (P.physicalPacket t j u.1 u.2 k).continuous
  · simp only [ite_eq_right hj]; exact continuous_const

theorem physicalTreeMaximal_continuous (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Continuous (P.physicalTreeMaximal t c) :=
  continuous_interval_max _ (P.physicalTreePartial_continuous t c) N

/-- Slots partition every partial sum, so maximal synthesis costs only
one fixed label-count factor. -/
theorem exists_weighted_labeled_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a b r : ℝ), 0<w → 0<r →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j (l : P.labels j) (_u : Item j l), P.length j≤r) →
      (∀ j l u, |P.actualX j l u-a|≤r) →
      (∀ j l u, |P.actualZ j l u-b|≤P.width) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j) (_u : Item j l), cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => treeProductPolynomial a b r P.width t z^2 *
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2 *
        ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hbound⟩ := SourceLatticePacket.exists_weighted_physical_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr c hlen hX hZ hspectrum hselector
  let weight := treeProductPolynomial a b r P.width t
  let coeff := fun (s : Fin B) j (u : P.SlotItem hcard s j) => c j u.1.1 u.1.2
  let M := fun s : Fin B => (P.slotted hcard s).physicalTreeMaximal t (coeff s)
  let mass := fun s : Fin B => ∑ j, ∑ u : P.SlotItem hcard s j,
    ‖coeff s j u‖^2*P.length j*P.width
  have hslot (s : Fin B) : Integrable (fun z => weight z^2*M s z^2) (volume.prod volume) ∧
      (∫ z, weight z^2*M s z^2 ∂volume.prod volume)≤C*P.absoluteConstant^2*mass s := by
    apply hbound N κ (P.SlotItem hcard s) (P.slotted hcard s) t w a b r hw hr (coeff s)
    · intro j u; exact hlen j u.1.1 u.1.2
    · intro j u; simpa only [P.slotted_actualX hcard] using hX j u.1.1 u.1.2
    · intro j u
      change |(P.slotted hcard s).actualZ j u-b|≤P.width
      simpa only [P.slotted_actualZ hcard] using hZ j u.1.1 u.1.2
    · exact P.slotted_spectrum hcard t w cStar cEta CEta hspectrum s
    · intro j u
      simpa only [P.slotted_length hcard,P.slotted_rowSlope hcard s j u] using
        hselector j u.1.1 u.1.2
  have hpartial (n : ℕ) (z : ℝ×ℝ) :
      (∑ s : Fin B, (P.slotted hcard s).physicalTreePartial t (coeff s) n z)=
        P.physicalTreePartial t c n z := by
    simp only [SourceLatticePacket.physicalTreePartial,physicalTreePartial,packetPartialSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<n
    · simp only [ite_eq_left hj]
      ext k
      simp only [planarFixedSynthesis,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,
        P.slotted_physicalPacket hcard,coeff]
      simpa only [Fintype.sum_sigma] using P.sum_slotted hcard j
        (fun l u => c j l u k*P.physicalPacket t j l u k z)
    · simp only [ite_eq_right hj,Finset.sum_const_zero]
  have hmax (z : ℝ×ℝ) : P.physicalTreeMaximal t c z≤∑ s, M s z := by
    have heq : (fun n => P.physicalTreePartial t c n z)=
        (fun n => ∑ s : Fin B, (P.slotted hcard s).physicalTreePartial t (coeff s) n z) :=
      funext fun n => (hpartial n z).symm
    unfold physicalTreeMaximal
    rw [heq]
    exact interval_max_sum_le _ N
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hM0 (s : Fin B) (z : ℝ×ℝ) : 0≤M s z := intervalOscillation_nonneg _ _ _ _
  have hM2 (s : Fin B) : MemLp (fun z => weight z*M s z) 2 (volume.prod volume) := by
    have hm : AEStronglyMeasurable (fun z => weight z*M s z) (volume.prod volume) :=
      (hwc.mul ((P.slotted hcard s).physicalTreeMaximal_continuous t (coeff s))).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hm).2
    simpa only [mul_pow] using (hslot s).1
  have hsum2 := memLp_finsetSum Finset.univ (fun s _ => hM2 s)
  have hsumI := hsum2.integrable_norm_pow (by decide : 2≠0)
  have hcost := weighted_integral_sum_square (volume.prod volume)
    (fun s z => weight z*M s z) hM2 (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcost
  have hpoint (z : ℝ×ℝ) : weight z^2*P.physicalTreeMaximal t c z^2≤
      ‖∑ s, weight z*M s z‖^2 := by
    rw [←Finset.mul_sum,Real.norm_eq_abs,sq_abs,mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (intervalOscillation_nonneg _ _ _ _) (hmax z) 2) (sq_nonneg _)
  have hE : Integrable (fun z => weight z^2*P.physicalTreeMaximal t c z^2) (volume.prod volume) := by
    apply hsumI.mono'
      ((hwc.pow 2).mul ((P.physicalTreeMaximal_continuous t c).pow 2)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖weight z^2*P.physicalTreeMaximal t c z^2‖ ≤ ‖∑ s, weight z*M s z‖^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg (weight z))
      (sq_nonneg (P.physicalTreeMaximal t c z)))]
    exact hpoint z
  have hmass : (∑ s, mass s)=
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    dsimp only [mass,coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_slotted hcard j (fun l u => ‖c j l u‖^2*P.length j*P.width)
  refine ⟨hE,(integral_mono hE hsumI hpoint).trans (hcost.trans ?_)⟩
  simp only [Real.norm_eq_abs,mul_pow,sq_abs]
  calc
    _ ≤ (B:ℝ)*∑ s, C*P.absoluteConstant^2*mass s :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => (hslot s).2) (Nat.cast_nonneg B)
    _ = _ := by rw [←Finset.mul_sum,hmass]; ring

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
