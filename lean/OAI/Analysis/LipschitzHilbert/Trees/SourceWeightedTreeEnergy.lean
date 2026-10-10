import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeMultiscaleEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMultiscaleEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRawEnvelope
import OAI.Analysis.LipschitzHilbert.Packets.WeightedPacketEnergy

namespace OAI

/-! Polynomially weighted separated synthesis on an actual source top.
The product polynomial is used only as a stronger convenient weight;
its reciprocal has an integral proportional to the top area. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

private theorem schwartz_colored_energy {I : Type*} [Fintype I] {q : ℕ}
    (f : I → SchwartzMap ℝ ℂ) (color : I → Fin q)
    (hdisjoint : ∀ ξ i j, i ≠ j → color i=color j → 𝓕 (f i) ξ=0 ∨ 𝓕 (f j) ξ=0) :
    (∫ x, ‖∑ i, f i x‖^2) ≤ (q:ℝ)*∑ i, ∫ x, ‖f i x‖^2 := by
  classical
  let selected := fun (r : Fin q) (i : I) => if color i=r then f i else (0 : SchwartzMap ℝ ℂ)
  let G := fun r : Fin q => (∑ i, selected r i : SchwartzMap ℝ ℂ)
  have hg (r : Fin q) : (∫ x, ‖G r x‖^2) =
      ∑ i, if color i=r then (∫ x, ‖f i x‖^2) else 0 := by
    have hd (ξ : ℝ) (i j : I) (hij : i≠j) :
        𝓕 (selected r i) ξ=0 ∨ 𝓕 (selected r j) ξ=0 := by
      by_cases hi : color i=r
      · by_cases hj : color j=r
        · simpa only [selected,ite_eq_left hi,ite_eq_left hj] using hdisjoint ξ i j hij (hi.trans hj.symm)
        · right; simp [selected,hj]
      · left; simp [selected,hi]
    have h := schwartz_energy_fourier_disjoint (selected r) hd
    have hleft (x : ℝ) : G r x = ∑ i, selected r i x := by simp [G]
    simp_rw [hleft]
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : color i=r <;> simp [selected,hi]
  have hpart (x : ℝ) : (∑ r, G r x) = ∑ i, f i x := by
    simp only [G,sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (color i)]
    · simp [selected]
    · intro r _ hr; simp [selected,Ne.symm hr]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have h := weighted_integral_sum_square volume (fun r x => G r x)
    (fun r => (G r).memLp 2) (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [hpart,div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one] at h
  rw [show (∑ r, ∫ x, ‖G r x‖^2) = ∑ i, ∫ x, ‖f i x‖^2 by
    simp_rw [hg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp] at h
  exact h

private theorem schwartz_colored_vector_energy {I K : Type*} [Fintype I] [Fintype K] {q : ℕ}
    (f : I → K → SchwartzMap ℝ ℂ) (color : I → Fin q)
    (hdisjoint : ∀ k ξ i j, i≠j → color i=color j → 𝓕 (f i k) ξ=0 ∨ 𝓕 (f j k) ξ=0) :
    (∫ x, ‖WithLp.toLp 2 (fun k => ∑ i, f i k x)‖^2) ≤
      (q:ℝ)*∑ i, ∑ k, ∫ x, ‖f i k x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  have hi (k : K) : Integrable (fun x => ‖∑ i, f i k x‖^2) := by
    let F : SchwartzMap ℝ ℂ := ∑ i, f i k
    have he (x : ℝ) : F x = ∑ i, f i k x := by simp [F]
    simpa only [he] using (F.memLp 2).integrable_norm_pow (by decide : 2≠0)
  rw [integral_finsetSum _ (fun k _ => hi k)]
  calc
    _ ≤ ∑ k, (q:ℝ)*∑ i, ∫ x, ‖f i k x‖^2 :=
      Finset.sum_le_sum fun k _ => schwartz_colored_energy (fun i => f i k) color (hdisjoint k)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

/-- Polynomial multiplication preserves the separation used in the
finite colored synthesis estimate. -/
theorem polynomial_colored_packet_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)] {q : ℕ}
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (color : Fin N → Fin q) (lo hi : Fin N → ℝ)
    (hsep : ∀ i j, i≠j → color i=color j → hi i<lo j ∨ hi j<lo i)
    (hlow : ∀ j u k ξ, |ξ|<lo j → 𝓕 (f j u k) ξ=0)
    (hhigh : ∀ j u k ξ, hi j < |ξ| → 𝓕 (f j u k) ξ=0)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ×ℤ) (len : Fin N → ℝ)
    (a0 b0 a r W y C : ℝ) (hr : 0<r) (hW : 0<W)
    (hlen : ∀ j, 0<len j) (hlenr : ∀ j, ∀ _ : ι j, len j≤r)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j u, X j u=a0+len j*(site j u).1)
    (hZ : ∀ j u, Z j u=b0+W*(site j u).2)
    (hcenter : ∀ j u, |X j u-a|≤r)
    (hf : ∀ j u k x, ‖f j u k x‖≤C*
      (lineEnvelope (X j u) (len j) 3 x*lineEnvelope (Z j u) W 3 y)) :
    (∫ x, ‖WithLp.toLp 2 (fun k => ∑ j,
      polynomialLocalization a r 1 (packetSynthesis (fun u => c j u k) (fun u => f j u k)) x)‖^2) ≤
      (q:ℝ)*((4*Real.pi)^2*C^2*16*Real.pi)*
        ∑ j, len j*∑ u, ‖c j u‖^2*lineEnvelope (Z j u) W 3 y := by
  let F := fun j k => packetSynthesis (fun u => c j u k) (fun u => f j u k)
  have hl (j k ξ) (hξ : |ξ|<lo j) : 𝓕 (F j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ _ (fun u => hlow j u k ξ hξ)
  have hh (j k ξ) (hξ : hi j < |ξ|) : 𝓕 (F j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ _ (fun u => hhigh j u k ξ hξ)
  have hp := schwartz_colored_vector_energy
    (fun j k => polynomialLocalization a r 1 (F j k)) color (by
      intro k ξ i j hij hcolor
      rcases hsep i j hij hcolor with hs | hs
      · by_cases hj : |ξ|<lo j
        · right; exact polynomialLocalization_low a r 1 (F j k) (lo j) (hi j) (hl j k) (hh j k) ξ hj
        · left; exact polynomialLocalization_high a r 1 (F i k) (lo i) (hi i) (hl i k) (hh i k) ξ
            (hs.trans_le (le_of_not_gt hj))
      · by_cases hi' : |ξ|<lo i
        · left; exact polynomialLocalization_low a r 1 (F i k) (lo i) (hi i) (hl i k) (hh i k) ξ hi'
        · right; exact polynomialLocalization_high a r 1 (F j k) (lo j) (hi j) (hl j k) (hh j k) ξ
            (hs.trans_le (le_of_not_gt hi')))
  exact hp.trans (by
    have h := mul_le_mul_of_nonneg_left
      (weighted_packet_energy c f X Z site len a0 b0 a r W y C hr hW hlen hlenr hinj hX hZ hcenter hf)
      (Nat.cast_nonneg q)
    simpa only [mul_assoc] using h)


private theorem integral_le_of_slice_majorant (f : ℝ×ℝ → ℝ) (H : ℝ → ℝ)
    (hfm : AEStronglyMeasurable f (volume.prod volume)) (hf0 : ∀ z, 0≤f z)
    (hH : Integrable H) (hi : ∀ y, Integrable (fun x => f (x,y)))
    (hb : ∀ y, (∫ x, f (x,y))≤H y) :
    Integrable f (volume.prod volume) ∧ (∫ z, f z ∂volume.prod volume)≤∫ y, H y := by
  have hint : Integrable (fun y => ∫ x, f (x,y)) :=
    hH.mono' hfm.prod_swap.integral_prod_right' (Filter.Eventually.of_forall fun y => by
      have hn : 0 ≤ ∫ x, f (x,y) := integral_nonneg fun x => hf0 (x,y)
      simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hb y)
  have hnorm : Integrable (fun y => ∫ x, ‖f (x,y)‖) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 _)] using hint
  have hfi : Integrable f (volume.prod volume) :=
    (integrable_prod_iff' hfm).2 ⟨Filter.Eventually.of_forall hi,hnorm⟩
  refine ⟨hfi,?_⟩
  rw [integral_prod_symm _ hfi]
  exact integral_mono hint hH hb

/-- A convenient product polynomial on the physical top coordinates. -/
def treeProductPolynomial (a b r W t : ℝ) (z : ℝ×ℝ) : ℝ :=
  polynomialWeight a (2*r) 1 z.1 * polynomialWeight b (2*W) 1 (z.2-t*z.1)

theorem treeProductPolynomial_pos (a b r W t : ℝ) (z : ℝ×ℝ) :
    0 < treeProductPolynomial a b r W t z :=
  mul_pos (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

/-- The original source packets have polynomially weighted separated
energy on every containing top. Constants precede the finite families. -/
theorem exists_weighted_physical_tree_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0<cEta)
    (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
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
      let E := fun z => (treeProductPolynomial a b r P.width t z)^2 *
        ‖∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z‖^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume) ≤ C*P.absoluteConstant^2 *
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  let lower := (cEta*cb-cStar)/(2*Real.pi)
  let upper := (CEta*Cb+cStar)/(2*Real.pi)
  have hlower : 0<lower := div_pos (sub_pos.mpr hgap) (by positivity)
  obtain ⟨q,hq,hsep⟩ := exists_dyadic_annular_separation (upper := upper) hlower
  refine ⟨(q:ℝ)*(4*Real.pi)^2*256*Real.pi^2,by positivity,?_⟩
  intro N κ ι _ _ P t w a b r hw hr c hlen hX hZ hspectrum hselector
  let G := fun y x => (WithLp.toLp 2 (fun k => ∑ j,
    polynomialLocalization a (2*r) 1
      (packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)) x) : EuclideanSpace ℂ κ)
  let F := fun z => ∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z
  let E := fun z => (treeProductPolynomial a b r P.width t z)^2 * ‖F z‖^2
  let M := fun y => (q:ℝ)*(4*Real.pi)^2*P.absoluteConstant^2*256*Real.pi *
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
  have hG (y x : ℝ) : G y x = (polynomialWeight a (2*r) 1 x : ℂ) • F (x,y+t*x) := by
    ext k
    simp only [G,F,planarFixedSynthesis,WithLp.ofLp_sum,Finset.sum_apply,
      polynomialLocalization_apply,packetSynthesis_apply,PiLp.smul_apply,smul_eq_mul,
      Finset.mul_sum,hraw]
  have hGy (y) : MemLp (G y) 2 volume := by
    apply memLp_piLp_iff.mpr
    intro k
    change MemLp (fun x => ∑ j, polynomialLocalization a (2*r) 1
      (packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)) x) 2 volume
    exact memLp_finsetSum _ (fun j _ =>
      (polynomialLocalization a (2*r) 1
        (packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y))).memLp 2)
  have hEq (x y : ℝ) : E (x,y+t*x) =
      polynomialWeight b (2*P.width) 1 y ^2 * ‖G y x‖^2 := by
    rw [hG,norm_smul,Complex.norm_real,Real.norm_of_nonneg
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))]
    dsimp only [E,treeProductPolynomial]
    have hy : y+t*x-t*x=y := by ring
    rw [hy]
    ring
  have hline (y : ℝ) : (∫ x, ‖G y x‖^2) ≤
      (q:ℝ)*((4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi)*
        ∑ j, P.length j*∑ u, ‖c j u‖^2*
          lineEnvelope (P.width*(P.snappedSite j u).2) P.width 3 y := by
    refine polynomial_colored_packet_energy c (fun j u k => P.raw 0 j u k y)
      (fun j => ⟨j.val % q,Nat.mod_lt _ hq⟩)
      (fun j => (lower/P.topLength)*(2:ℝ)^j.val)
      (fun j => (upper/P.topLength)*(2:ℝ)^j.val) ?_ ?_ ?_
      (fun j u => P.length j*(P.snappedSite j u).1)
      (fun j u => P.width*(P.snappedSite j u).2) P.snappedSite P.length
      0 0 a (2*r) P.width y P.absoluteConstant (by positivity) P.width_pos P.length_pos
      ?_ P.snappedSite_injective (by intros; ring) (by intros; ring) hPx ?_
    · intro i j hij hmod
      have hm : i.val % q=j.val % q := congrArg Fin.val hmod
      rcases lt_or_gt_of_ne hij with hij | hji
      · left
        have hh := div_lt_div_of_pos_right (hsep i.val j.val hij hm) P.topLength_pos
        simpa only [div_mul_eq_mul_div] using hh
      · right
        have hh := div_lt_div_of_pos_right (hsep j.val i.val hji hm.symm) P.topLength_pos
        simpa only [div_mul_eq_mul_div] using hh
    · intro j u k ξ hξ
      exact (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).1 ξ hξ
    · intro j u k ξ hξ
      exact (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).2 ξ hξ
    · intro j u; linarith [hlen j u]
    · intro j u k x
      apply (P.raw_absolute_lattice_envelope 0 j u k y x).trans
      apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
      exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
        (lineEnvelope_antitone _ _ _ P.order_ge_three) (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hslice (y : ℝ) : Integrable (fun x => E (x,y+t*x)) := by
    simp_rw [hEq]
    exact (hGy y).integrable_norm_pow (by decide : 2≠0) |>.const_mul _
  have hbound (y : ℝ) : (∫ x, E (x,y+t*x))≤M y := by
    simp_rw [hEq]
    rw [integral_const_mul]
    apply (mul_le_mul_of_nonneg_left (hline y) (sq_nonneg _)).trans
    dsimp only [M]
    have he (j) (u : ι j) := polynomialWeight_sq_mul_envelope y
      (P.width*(P.snappedSite j u).2) b P.width (2*P.width) 1 1 P.width_pos
      (mul_pos (by norm_num) P.width_pos) (by linarith [P.width_pos]) (hPy j u)
    simp only [Nat.reduceAdd,Nat.reduceMul,pow_one] at he
    calc
      _ = ((q:ℝ)*(4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi) *
          ∑ j, P.length j*∑ u, ‖c j u‖^2*
            (polynomialWeight b (2*P.width) 1 y ^2*
              lineEnvelope (P.width*(P.snappedSite j u).2) P.width 3 y) := by
        simp only [Finset.mul_sum]; ring_nf
      _ ≤ ((q:ℝ)*(4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi) *
          ∑ j, P.length j*∑ u, ‖c j u‖^2*
            (16*lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (P.length_pos j).le
        exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (he j u) (sq_nonneg _)
      _ = _ := by simp only [Finset.mul_sum]; ring_nf
  have hM : Integrable M := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun u _ =>
      (integrable_lineEnvelope_one (P.width*(P.snappedSite j u).2) P.width P.width_pos).const_mul _
  have hF : MemLp F 2 (volume.prod volume) := P.physicalMultiscaleSynthesis_memLp t c
  have hpoly : Continuous (treeProductPolynomial a b r P.width t) := by
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hEm : AEStronglyMeasurable E (volume.prod volume) :=
    (hpoly.aestronglyMeasurable.pow 2).mul (hF.aestronglyMeasurable.norm.pow 2)
  obtain ⟨hEi,hEbound⟩ := integral_le_of_slice_majorant
    (fun z => E (slopeShear t z)) M
    (hEm.comp_measurePreserving (slopeShear_measurePreserving t))
    (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hM hslice hbound
  have hE : Integrable E (volume.prod volume) :=
    ((slopeShear_measurePreserving t).integrable_comp hEm).1 hEi
  refine ⟨hE,?_⟩
  rw [integral_slopeShear] at hEbound
  apply hEbound.trans_eq
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

end SourceLatticePacket

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

/-- Exact slot decomposition preserves the tree weight. The only label
loss is the stated bound on labels per scale. -/
theorem exists_weighted_labeled_tree_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0<cEta)
    (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
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
      let E := fun z => (treeProductPolynomial a b r P.width t z)^2 *
        ‖P.physicalLabeledSynthesis t c z‖^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume) ≤ (B:ℝ)*C*P.absoluteConstant^2 *
        ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,henergy⟩ := SourceLatticePacket.exists_weighted_physical_tree_energy
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr c hlen hX hZ hspectrum hselector
  let weight := treeProductPolynomial a b r P.width t
  let F := fun s : Fin B => fun z => ∑ j, planarFixedSynthesis
    (fun u : P.SlotItem hcard s j => c j u.1.1 u.1.2)
    ((P.slotted hcard s).physicalPacket t j) z
  let mass := fun s : Fin B => ∑ j, ∑ u : P.SlotItem hcard s j,
    ‖c j u.1.1 u.1.2‖^2*P.length j*P.width
  have hslot (s : Fin B) :
      Integrable (fun z => weight z^2*‖F s z‖^2) (volume.prod volume) ∧
      (∫ z, weight z^2*‖F s z‖^2 ∂volume.prod volume)≤C*P.absoluteConstant^2*mass s := by
    apply henergy N κ (P.SlotItem hcard s) (P.slotted hcard s) t w a b r hw hr
      (fun j u => c j u.1.1 u.1.2)
    · intro j u; exact hlen j u.1.1 u.1.2
    · intro j u
      simpa only [P.slotted_actualX hcard] using hX j u.1.1 u.1.2
    · intro j u
      change |(P.slotted hcard s).actualZ j u-b|≤P.width
      simpa only [P.slotted_actualZ hcard] using hZ j u.1.1 u.1.2
    · exact P.slotted_spectrum hcard t w cStar cEta CEta hspectrum s
    · intro j u
      simpa only [P.slotted_length hcard,P.slotted_rowSlope hcard s j u] using
        hselector j u.1.1 u.1.2
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hF (s : Fin B) : MemLp (fun z => weight z • F s z) 2 (volume.prod volume) := by
    apply (memLp_two_iff_integrable_sq_norm
      (hwc.aestronglyMeasurable.smul
        ((P.slotted hcard s).physicalMultiscaleSynthesis_memLp t _).aestronglyMeasurable)).2
    simpa only [Pi.smul_apply',norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using (hslot s).1
  have hsum (z : ℝ×ℝ) : (∑ s, weight z • F s z)=
      weight z • P.physicalLabeledSynthesis t c z := by
    rw [←Finset.smul_sum]
    exact congrArg (fun v : EuclideanSpace ℂ κ => weight z • v)
      (P.physicalLabeledSynthesis_eq_slots hcard t c z)
  have htotal : MemLp (fun z => weight z • P.physicalLabeledSynthesis t c z) 2
      (volume.prod volume) := by
    simpa only [hsum] using memLp_finsetSum Finset.univ (fun s _ => hF s)
  have hcost := weighted_integral_sum_square (volume.prod volume)
    (fun s z => weight z • F s z) hF (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,hsum,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hcost
  have hmass : (∑ s, mass s)=
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    dsimp only [mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_slotted hcard j (fun l u => ‖c j l u‖^2*P.length j*P.width)
  refine ⟨?_,hcost.trans ?_⟩
  · simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using
      htotal.integrable_norm_pow (by decide : 2≠0)
  · calc
      _ ≤ (B:ℝ)*∑ s, C*P.absoluteConstant^2*mass s :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => (hslot s).2) (Nat.cast_nonneg B)
      _ = _ := by rw [←Finset.mul_sum,hmass]; ring

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
