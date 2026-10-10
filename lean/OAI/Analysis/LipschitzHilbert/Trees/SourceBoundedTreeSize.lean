import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeEnergy
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenCoefficientEnergy
import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction

namespace OAI

/-! Bounded test functions have uniformly bounded coefficient size on a
separated source tree. The proof uses the actual analyzing integrals,
polynomially weighted synthesis and an integrable reciprocal weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert

/-- Weighted synthesis duality needs only a bounded test function. -/
theorem analyzingCoefficient_bounded_energy_le
    {X I K : Type*} [MeasurableSpace X] [Fintype I] [Fintype K]
    (μ : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (weight : X → ℝ) (A V M : ℝ)
    (hA : 0≤A) (hV : 0≤V) (hM : 0≤M)
    (ha : ∀ i, 0<area i) (hw : ∀ x, 0<weight x)
    (hrec : MemLp (fun x => (weight x)⁻¹) 2 μ)
    (hinv : (∫ x, ((weight x)⁻¹)^2 ∂μ)≤V)
    (hg : ∀ x, ‖g x‖≤M)
    (hint : ∀ i k, Integrable (fun x => g x k * conj (wave i k x)) μ)
    (hsyn : ∀ c, MemLp (fun x => weight x • diagonalSynthesis wave c x) 2 μ)
    (hbound : ∀ c, (∫ x, ‖weight x • diagonalSynthesis wave c x‖^2 ∂μ) ≤
      A * ∑ i, area i * ‖c i‖^2) :
    (∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2) ≤ M^2*A*V := by
  let a := analyzingCoefficient μ area wave g
  let S := ∑ i, area i*‖a i‖^2
  let F := diagonalSynthesis wave a
  let H := fun x => weight x • F x
  have hS : 0≤S := Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (sq_nonneg _)
  have hH : MemLp H 2 μ := hsyn a
  have heq (x : X) : ‖H x‖*‖(weight x)⁻¹‖=‖F x‖ := by
    simp only [H,norm_smul,Real.norm_eq_abs,abs_of_pos (hw x),
      abs_of_pos (inv_pos.mpr (hw x))]
    field_simp [(hw x).ne']
  have hprod : Integrable (fun x => ‖H x‖*‖(weight x)⁻¹‖) μ :=
    hH.norm.integrable_mul hrec.norm
  have hFnorm : Integrable (fun x => ‖F x‖) μ := by
    simpa only [heq] using hprod
  have hp : (S : ℂ)=∫ x, inner ℂ (F x) (g x) ∂μ :=
    analyzingCoefficient_self_pairing μ area wave g (fun i => (ha i).ne') hint
  have hcs : S ≤ M*(Real.sqrt (∫ x, ‖H x‖^2 ∂μ)*
      Real.sqrt (∫ x, ((weight x)⁻¹)^2 ∂μ)) := by
    calc
      S = ‖∫ x, inner ℂ (F x) (g x) ∂μ‖ := by
        rw [←hp,Complex.norm_real,Real.norm_of_nonneg hS]
      _ ≤ ∫ x, ‖inner ℂ (F x) (g x)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, M*‖F x‖ ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hFnorm.const_mul M) (Filter.Eventually.of_forall fun x =>
            (norm_inner_le_norm (F x) (g x)).trans (by
              simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hg x) (norm_nonneg (F x))))
      _ = M*∫ x, ‖H x‖*‖(weight x)⁻¹‖ ∂μ := by rw [integral_const_mul]; simp only [heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        have hn (x : X) : ‖(weight x)⁻¹‖=(weight x)⁻¹ :=
          Real.norm_of_nonneg (inv_nonneg.mpr (hw x).le)
        simpa only [Real.rpow_two,←Real.sqrt_eq_rpow,hn] using
          integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
            (Filter.Eventually.of_forall fun x => norm_nonneg (H x))
            (Filter.Eventually.of_forall fun x => inv_nonneg.mpr (hw x).le)
            (by simpa using hH.norm) (by simpa using hrec)) hM
  have hE : 0≤∫ x, ‖H x‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hI : 0≤∫ x, ((weight x)⁻¹)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hsq := pow_le_pow_left₀ hS hcs 2
  rw [mul_pow,mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hI] at hsq
  have henergy : (∫ x, ‖H x‖^2 ∂μ)≤A*S := hbound a
  have hmul : M^2*((∫ x, ‖H x‖^2 ∂μ)*(∫ x, ((weight x)⁻¹)^2 ∂μ))≤M^2*(A*S*V) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
    exact mul_le_mul henergy hinv hI (mul_nonneg hA hS)
  change S≤M^2*A*V
  by_cases hz : S=0
  · rw [hz]; positivity
  · have hpos : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := S) _ hpos
    nlinarith [hsq,hmul]

/-- The reciprocal polynomial square is integrable with only the top
area as its scale. The slope shear has Jacobian one. -/
theorem treeProductPolynomial_reciprocal (a b r W t : ℝ) (hr : 0<r) (hW : 0<W) :
    MemLp (fun z => (treeProductPolynomial a b r W t z)⁻¹) 2 (volume.prod volume) ∧
    (∫ z, ((treeProductPolynomial a b r W t z)⁻¹)^2 ∂volume.prod volume) ≤
      4*Real.pi^2*r*W := by
  let E := fun z : ℝ×ℝ => lineEnvelope a (2*r) 1 z.1 *
    lineEnvelope b (2*W) 1 (z.2-t*z.1)
  have hwc : Continuous (treeProductPolynomial a b r W t) := by
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hrc : Continuous (fun z => (treeProductPolynomial a b r W t z)⁻¹) :=
    hwc.inv₀ (fun z => (treeProductPolynomial_pos a b r W t z).ne')
  have he (z : ℝ×ℝ) : E z=(treeProductPolynomial a b r W t z)⁻¹ := by
    simp only [E,treeProductPolynomial,polynomialWeight,lineEnvelope,pow_one,
      ←div_pow,mul_inv_rev,mul_comm]
  have hEi : Integrable E (volume.prod volume) := by
    have hi := (integrable_lineEnvelope_one a (2*r) (by positivity)).mul_prod
      (integrable_lineEnvelope_one b (2*W) (by positivity))
    have hm : AEStronglyMeasurable E (volume.prod volume) := by
      have heq : E=(fun z => (treeProductPolynomial a b r W t z)⁻¹) := funext he
      rw [heq]
      exact hrc.aestronglyMeasurable
    apply ((slopeShear_measurePreserving t).integrable_comp hm).1
    convert hi using 1
    ext z
    dsimp [E,slopeShear]
    congr 2; ring
  have hInt : (∫ z, E z ∂volume.prod volume)=4*Real.pi^2*r*W := by
    rw [←integral_slopeShear t E]
    have he (z : ℝ×ℝ) : E (slopeShear t z)=
        lineEnvelope a (2*r) 1 z.1*lineEnvelope b (2*W) 1 z.2 := by
      dsimp [E,slopeShear]; congr 2; ring
    simp_rw [he]
    rw [integral_prod_mul,integral_lineEnvelope_one a (2*r) (by positivity),
      integral_lineEnvelope_one b (2*W) (by positivity)]
    ring
  have hm : AEStronglyMeasurable (fun z => ((treeProductPolynomial a b r W t z)⁻¹)^2)
      (volume.prod volume) := by
    exact (hrc.pow 2).aestronglyMeasurable
  have hpoint (z : ℝ×ℝ) : ((treeProductPolynomial a b r W t z)⁻¹)^2≤E z := by
    have hx : 1≤polynomialWeight a (2*r) 1 z.1 := polynomialWeight_one_le _ _ _ _
    have hy : 1≤polynomialWeight b (2*W) 1 (z.2-t*z.1) := polynomialWeight_one_le _ _ _ _
    have hxy : 1≤treeProductPolynomial a b r W t z := by
      exact one_le_mul_of_one_le_of_one_le hx hy
    have hp : 0<(treeProductPolynomial a b r W t z)⁻¹ := inv_pos.mpr (treeProductPolynomial_pos _ _ _ _ _ _)
    have hi : (treeProductPolynomial a b r W t z)⁻¹≤1 := inv_le_one_of_one_le₀ hxy
    rw [he]
    nlinarith
  have hi : Integrable (fun z => ((treeProductPolynomial a b r W t z)⁻¹)^2)
      (volume.prod volume) := hEi.mono' hm (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((treeProductPolynomial a b r W t z)⁻¹))] using hpoint z)
  refine ⟨?_,(integral_mono hi hEi hpoint).trans_eq hInt⟩
  apply (memLp_two_iff_integrable_sq ?_).2 hi
  exact hrc.aestronglyMeasurable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

/-- A bounded test has bounded size on a separated physical source tree.
The constant is independent of the finite scale, packet and vector types. -/
theorem exists_physical_bounded_tree_size
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0<cEta)
    (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a b r : ℝ), 0<w → 0<r →
    ∀ (beta : P.PacketIndex → κ → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (M : ℝ),
      0≤M → (∀ q k, ‖beta q k‖≤1) → Measurable g → (∀ z, ‖g z‖≤M) →
      (∀ j (l : P.labels j) (_u : Item j l), P.length j≤r) →
      (∀ j l u, |P.actualX j l u-a|≤r) →
      (∀ j l u, |P.actualZ j l u-b|≤P.width) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j) (_u : Item j l), cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      (∑ q : P.PacketIndex, P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2) ≤
        (B:ℝ)*C*P.absoluteConstant^2*M^2*(r*P.width) := by
  obtain ⟨C,hC,henergy⟩ := exists_weighted_labeled_tree_energy
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C*(4*Real.pi^2),by positivity,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr beta g M hM hbeta hg hgM
    hlen hX hZ hspectrum hselector
  let weight := treeProductPolynomial a b r P.width t
  let wave := fun q : P.PacketIndex => fun k z =>
    beta q k * P.physicalPacket t q.1 q.2.1 q.2.2 k z
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let d := fun c : P.PacketIndex → EuclideanSpace ℂ κ =>
    fun j (l : P.labels j) (u : Item j l) =>
      WithLp.toLp 2 (fun k => c ⟨j,⟨l,u⟩⟩ k * beta ⟨j,⟨l,u⟩⟩ k)
  have hdiag (c : P.PacketIndex → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
      diagonalSynthesis wave c z=P.physicalLabeledSynthesis t (d c) z := by
    ext k
    simp only [diagonalSynthesis,physicalLabeledSynthesis,planarFixedSynthesis,wave,d,
      WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,Fintype.sum_sigma,mul_assoc]
  have hweighted (c : P.PacketIndex → EuclideanSpace ℂ κ) :
      Integrable (fun z => weight z^2*‖diagonalSynthesis wave c z‖^2) (volume.prod volume) ∧
      (∫ z, weight z^2*‖diagonalSynthesis wave c z‖^2 ∂volume.prod volume) ≤
        ((B:ℝ)*C*P.absoluteConstant^2)*∑ q, area q*‖c q‖^2 := by
    have h := henergy N κ Label Item P B hcard t w a b r hw hr (d c)
      hlen hX hZ hspectrum hselector
    simp_rw [←hdiag] at h
    refine ⟨h.1,h.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hn (j) (l : P.labels j) (u : Item j l) : ‖d c j l u‖≤‖c ⟨j,⟨l,u⟩⟩‖ := by
      simpa only [d,one_mul] using diagonal_packet_norm (c ⟨j,⟨l,u⟩⟩) (beta ⟨j,⟨l,u⟩⟩)
        (show (0:ℝ)≤1 by norm_num) (hbeta ⟨j,⟨l,u⟩⟩)
    simp only [Fintype.sum_sigma,area]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro u _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn j l u) 2
    convert mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (P.length_pos j).le P.width_pos.le) using 1 <;> ring
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hsyn (c : P.PacketIndex → EuclideanSpace ℂ κ) :
      MemLp (fun z => weight z • diagonalSynthesis wave c z) 2 (volume.prod volume) := by
    have hdm : AEStronglyMeasurable (diagonalSynthesis wave c) (volume.prod volume) := by
      have he : diagonalSynthesis wave c=P.physicalLabeledSynthesis t (d c) := funext (hdiag c)
      rw [he]
      exact (P.physicalLabeledSynthesis_memLp t _).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm (hwc.aestronglyMeasurable.smul hdm)).2
    simpa only [Pi.smul_apply',norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using (hweighted c).1
  have hint (q : P.PacketIndex) (k : κ) :
      Integrable (fun z => g z k*conj (wave q k z)) (volume.prod volume) := by
    have hgm : Measurable (fun z => g z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    have hwm : Measurable (wave q k) :=
      measurable_const.mul (P.physicalPacket t q.1 q.2.1 q.2.2 k).continuous.measurable
    have hwi : Integrable (wave q k) (volume.prod volume) :=
      (P.physicalPacket t q.1 q.2.1 q.2.2 k).integrable.const_mul _
    apply (hwi.norm.const_mul M).mono' (hgm.mul (continuous_star.measurable.comp hwm)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖g z k*conj (wave q k z)‖≤M*‖wave q k z‖
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (g z) k).trans (hgM z)) (norm_nonneg _)
  obtain ⟨hrec,hinv⟩ := treeProductPolynomial_reciprocal a b r P.width t hr P.width_pos
  have h := analyzingCoefficient_bounded_energy_le (volume.prod volume) area wave g weight
    ((B:ℝ)*C*P.absoluteConstant^2) (4*Real.pi^2*r*P.width) M (by positivity)
    (mul_nonneg (mul_nonneg (by positivity) hr.le) P.width_pos.le) hM
    (fun q => mul_pos (P.length_pos q.1) P.width_pos)
    (treeProductPolynomial_pos a b r P.width t) hrec hinv hgM hint hsyn
    (fun c => by
      simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using (hweighted c).2)
  change (∑ q, area q*‖analyzingCoefficient (volume.prod volume) area wave g q‖^2)≤_
  convert h using 1; ring

/-- Restriction is literal: packets outside the selected tree add no
hypotheses and the original physical analyzing integrals are retained. -/
theorem exists_selected_physical_bounded_tree_size
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0<cEta)
    (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a b r : ℝ), 0<w → 0<r →
    ∀ (beta : P.PacketIndex → κ → ℂ) (packets : Finset P.PacketIndex)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (M : ℝ),
      0≤M → (∀ q ∈ packets, ∀ k, ‖beta q k‖≤1) → Measurable g → (∀ z, ‖g z‖≤M) →
      (∀ q ∈ packets, P.length q.1≤r) →
      (∀ q ∈ packets, |P.actualX q.1 q.2.1 q.2.2-a|≤r) →
      (∀ q ∈ packets, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width) →
      (∀ q ∈ packets, ∀ k ξ η, planarAngularFourier
          (P.physicalPacket t q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope q.1 q.2.1)*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q ∈ packets, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1| ∧
        |P.rowSlope q.1 q.2.1|≤Cb*w/P.length q.1) →
      (∑ q ∈ packets, P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2) ≤
        (B:ℝ)*C*P.absoluteConstant^2*M^2*(r*P.width) := by
  obtain ⟨C,hC,hsize⟩ := exists_physical_bounded_tree_size
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr beta packets g M hM hbeta hg hgM
    hlen hX hZ hspectrum hselector
  let R := P.restrictPackets packets
  let betaR := fun q : R.PacketIndex => beta ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩
  have hmem (j) (l : R.labels j) (u : P.RestrictedPacketItem packets j l) :
      (⟨j,⟨l,u.val⟩⟩ : P.PacketIndex)∈packets :=
    (P.restrictedPacketEquiv packets ⟨j,⟨l,u⟩⟩).property
  have h := hsize N κ Label (P.RestrictedPacketItem packets) R B hcard t w a b r hw hr
    betaR g M hM (fun q k => hbeta _ (hmem q.1 q.2.1 q.2.2) k) hg hgM
    (fun j l u => hlen _ (hmem j l u))
    (fun j l u => hX _ (hmem j l u))
    (fun j l u => hZ _ (hmem j l u))
    (fun j l u k ξ η => hspectrum _ (hmem j l u) k ξ η)
    (fun j l u => hselector _ (hmem j l u))
  have hf (q : R.PacketIndex) : R.physicalFrozenCoefficient t betaR g q=
      P.physicalFrozenCoefficient t beta g ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩ := by
    ext k
    rfl
  simp_rw [hf] at h
  change (∑ q : (P.restrictPackets packets).PacketIndex,
    P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩‖^2)≤_
    at h
  rw [P.sum_restrictPackets packets (fun q =>
    P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2)] at h
  exact h

/-- The same size bound for the original source multiplier coefficient,
with the selector frozen at the tree direction. -/
theorem exists_frozen_multiplier_bounded_tree_size
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0<cEta)
    (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a z r : ℝ), 0<w → 0<r →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (packets : Finset P.PacketIndex)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (M : ℝ),
      0≤M → (∀ q ∈ packets, ∀ k, ‖b q.1 q.2.1 k t‖≤1) →
      Measurable g → (∀ x, ‖g x‖≤M) →
      (∀ q ∈ packets, P.length q.1≤r) →
      (∀ q ∈ packets, |P.actualX q.1 q.2.1 q.2.2-a|≤r) →
      (∀ q ∈ packets, |P.actualZ q.1 q.2.1 q.2.2-z|≤P.width) →
      (∀ q ∈ packets, ∀ k ξ η, planarAngularFourier
          (P.physicalPacket t q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope q.1 q.2.1)*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q ∈ packets, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1| ∧
        |P.rowSlope q.1 q.2.1|≤Cb*w/P.length q.1) →
      (∑ q ∈ packets, P.length q.1*P.width*
        ‖P.physicalMultiplierCoefficient t b (fun _ => t) g q.1 q.2.1 q.2.2‖^2) ≤
        (B:ℝ)*C*P.absoluteConstant^2*M^2*(r*P.width) := by
  obtain ⟨C,hC,hsize⟩ := exists_selected_physical_bounded_tree_size
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w a z r hw hr b packets g M hM hb hg hgM
    hlen hX hZ hspectrum hselector
  have h := hsize N κ Label Item P B hcard t w a z r hw hr
    (fun q k => b q.1 q.2.1 k t) packets g M hM hb hg hgM hlen hX hZ hspectrum hselector
  convert h using 1
  apply Finset.sum_congr rfl
  intro q _
  rw [P.physicalFrozenCoefficient_eq_multiplier]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
