import OAI.Analysis.IntegralMeans.BoundaryEscape

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma compact_sublevels_iff_exhaustion.{u_1} {X : Type u_1} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ x : X, x ∉ K m → (n : ℝ) ≤ f x := by
  constructor
  · intro h n
    obtain ⟨m,hm⟩ := K.exists_superset_of_isCompact (h n)
    refine ⟨m,fun x hx => ?_⟩
    by_contra! hh
    exact hx (hm hh.le)
  · intro h r
    obtain ⟨n,hn⟩ := exists_nat_gt r
    obtain ⟨m,hm⟩ := h n
    apply (K.isCompact m).of_isClosed_subset (isClosed_le hf continuous_const)
    intro x hx
    by_contra hh
    exact (not_lt_of_ge ((hm x hh).trans hx)) hn

lemma measurableSet_compact_sublevels.{u_1, u_2} {P : Type u_1} {X : Type u_2}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    {f : P → X → ℝ} (hp : ∀ x, Continuous (fun p => f p x))
    (hx : ∀ p, Continuous (f p)) :
    MeasurableSet {p | ∀ r : ℝ, IsCompact {x | f p x ≤ r}} := by
  let K := CompactExhaustion.choice X
  have he : {p | ∀ r : ℝ, IsCompact {x | f p x ≤ r}} =
      ⋂ n : ℕ, ⋃ m : ℕ, ⋂ x : X, ⋂ (_ : x ∉ K m), {p | (n : ℝ) ≤ f p x} := by
    ext p
    simp only [mem_ofPred_eq,mem_iInter,mem_iUnion]
    exact compact_sublevels_iff_exhaustion K (hx p)
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro m
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (hp x)

lemma compact_sublevels_iff_positive.{u_1} {X : Type u_1} [TopologicalSpace X] [T2Space X]
    {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔ ∀ r : ℝ, 0 < r → IsCompact {x | f x ≤ r} := by
  refine ⟨fun h r _ => h r,fun h r => ?_⟩
  exact (h (max r 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))).of_isClosed_subset
    (isClosed_le hf continuous_const) (fun x hx => (show f x ≤ r from hx).trans (le_max_left _ _))

lemma compact_positive_superlevels_iff {F : ℂ → ℂ} (k : ℝ) (ξ : ℂ)
    (hc : ContinuousOn F halfPlane) :
    (∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ)) ↔
      ∀ r : ℝ, IsCompact {z : halfPlane | ‖F z-ξ‖/z.val.im^k ≤ r} := by
  have hy (z : halfPlane) : 0 < z.val.im^k := Real.rpow_pos_of_pos z.property k
  have hcont : Continuous (fun z : halfPlane => ‖F z-ξ‖/z.val.im^k) := by
    refine ((hc.domRestrict.sub continuous_const).norm).div ?_ (fun z => ne_of_gt (hy z))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))
  rw [compact_sublevels_iff_positive hcont]
  have he (r : ℝ) (hr : 0 < r) :
      Subtype.val '' {z : halfPlane | ‖F z-ξ‖/z.val.im^k ≤ r} =
        closedPositiveSuperlevel F k (1/r) ξ := by
    ext z
    simp only [mem_image,mem_ofPred_eq,closedPositiveSuperlevel]
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      rw [div_le_iff₀ (hy w)] at hw
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hw
    · rintro ⟨hz,hzv⟩
      refine ⟨⟨z,hz⟩,?_,rfl⟩
      rw [div_le_iff₀ (hy ⟨z,hz⟩)]
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hzv
  constructor
  · intro h r hr
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [he r hr]
    exact h (1/r) (by positivity)
  · intro h δ hδ
    have hh := (h (1/δ) (by positivity)).image continuous_subtype_val
    rw [he (1/δ) (by positivity)] at hh
    simpa only [one_div_one_div] using hh

lemma measurableSet_compact_positive_superlevels.{u_1} {P : Type u_1}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    {F : P → ℂ → ℂ} (hF : Continuous (fun p : P × halfPlane => F p.1 p.2)) (k : ℝ) :
    MeasurableSet {p : P × ℂ | ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (F p.1) k δ p.2)} := by
  let f : (P × ℂ) → halfPlane → ℝ := fun p z => ‖F p.1 z-p.2‖/z.val.im^k
  have hc (p : P × ℂ) : ContinuousOn (F p.1) halfPlane := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hF.comp (continuous_const.prodMk continuous_id)
  have he : {p : P × ℂ | ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (F p.1) k δ p.2)} =
      {p | ∀ r : ℝ, IsCompact {z : halfPlane | f p z ≤ r}} := by
    ext p
    exact compact_positive_superlevels_iff k p.2 (hc p)
  rw [he]
  apply measurableSet_compact_sublevels
  · intro z
    exact (((hF.comp (continuous_fst.prodMk continuous_const)).sub continuous_snd).norm).div_const _
  · intro p
    refine (((hc p).domRestrict.sub continuous_const).norm).div ?_
      (fun z => ne_of_gt (Real.rpow_pos_of_pos z.property k))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))

lemma measurableSet_regular_parameters.{u_1, u_2, u_3} {P : Type u_1} {X : Type u_2} {Y : Type u_3}
    [TopologicalSpace P] [SigmaCompactSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [T2Space P]
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology P] [SecondCountableTopology Y]
    {F : P → X → Y} {J : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hJ : Continuous (fun q : P × X => J q.1 q.2)) :
    MeasurableSet {q : P × Y | ∀ x, F q.1 x = q.2 → J q.1 x ≠ 0} := by
  let Z : Set (P × X) := {q | J q.1 q.2 = 0}
  let M : P × X → P × Y := fun q => (q.1,F q.1 q.2)
  have hZ : IsSigmaCompact Z := isSigmaCompact_univ.of_isClosed_subset
    (isClosed_eq hJ continuous_const) (subset_univ _)
  have hM : Continuous M := continuous_fst.prodMk hF
  have him : MeasurableSet (M '' Z) := by
    obtain ⟨K,hK,he⟩ := hZ.image hM
    rw [← he]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  have he : {q : P × Y | ∀ x, F q.1 x = q.2 → J q.1 x ≠ 0} = (M '' Z)ᶜ := by
    ext q
    constructor
    · intro h ⟨⟨p,x⟩,hx,hq⟩
      have hp : p = q.1 := congrArg Prod.fst hq
      have hf : F p x = q.2 := congrArg Prod.snd hq
      exact h x (hp ▸ hf) (hp ▸ hx)
    · intro h x hx hJx
      exact h ⟨(q.1,x),hJx,Prod.ext rfl hx⟩
  rw [he]
  exact him.compl

lemma ae_regular_values {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) :
    ∀ᵐ ξ ∂volume, ∀ z ∈ s, f z = ξ → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 := by
  let t : Set ℂ := {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap = 0}
  have hz : volume (f '' t) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z hz => (hf z hz.1).hasFDerivAt.hasFDerivWithinAt) (fun z hz => hz.2)
  filter_upwards [show ∀ᵐ ξ ∂volume, ξ ∉ f '' t from ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hz)] with ξ hξ z hzs hfz hdet
  exact hξ ⟨z,⟨hzs,hdet⟩,hfz⟩

lemma potential_superlevel_eq_closed {f : ℂ → ℂ} {k δ : ℝ} (hk : 0 ≤ k) (hδ : 0 < δ) (ξ : ℂ) :
    {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z} =
      closedPositiveSuperlevel f k δ ξ := by
  ext z
  by_cases hz : z ∈ halfPlane
  · simp only [mem_ofPred_eq,closedPositiveSuperlevel,show 0 < z.im from hz,hz,true_and]
    rw [potential_ge_iff_reciprocalPotential_le hk hδ hz,reciprocalPotential,
      div_le_iff₀ (Real.rpow_pos_of_pos hz k),inv_mul_eq_div]
  · simp only [mem_ofPred_eq,hz,false_and,closedPositiveSuperlevel]
    exact iff_false_intro (fun h => hz h.1) |>.symm

lemma measurableSet_class_goodPairs {k : ℝ} (hk : 0 ≤ k) :
    MeasurableSet {p : DiskClass × ℂ | GoodPair (classFun p.1) k p.2} := by
  have hcompact := measurableSet_compact_positive_superlevels continuous_classFun_eval k
  have hregular := measurableSet_regular_parameters (F := fun g (z : halfPlane) => criticalMap (classFun g) k z) (J := fun g (z : halfPlane) => normalizedJacobian (classFun g) k z) (continuous_class_criticalMap k)
    (continuous_class_normalizedJacobian k)
  have he : {p : DiskClass × ℂ | GoodPair (classFun p.1) k p.2} =
      {p : DiskClass × ℂ | ∀ δ : ℝ, 0 < δ →
        IsCompact (closedPositiveSuperlevel (classFun p.1) k δ p.2)} ∩
      {p : DiskClass × ℂ | ∀ z : halfPlane,
        criticalMap (classFun p.1) k z = p.2 → normalizedJacobian (classFun p.1) k z ≠ 0} := by
    ext p
    simp only [mem_inter_iff,mem_ofPred_eq,GoodPair]
    constructor
    · rintro ⟨hc,hr⟩
      exact ⟨fun δ hδ => (potential_superlevel_eq_closed hk hδ p.2) ▸ hc δ hδ,
        fun z => hr z z.property⟩
    · rintro ⟨hc,hr⟩
      exact ⟨fun δ hδ => (potential_superlevel_eq_closed hk hδ p.2).symm ▸ hc δ hδ,
        fun z hz => hr ⟨z,hz⟩⟩
  rw [he]
  exact hcompact.inter hregular

lemma class_ae_goodPairs (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞) :
    ∀ᵐ ξ : ℂ, GoodPair (classFun g) ((β+3)/4) ξ := by
  have hc := class_ae_compact_superlevels g hβ hfin
  have hr := ae_regular_values (s := halfPlane)
    (fun z hz => differentiableAt_criticalMap (classFun_schlicht g).1 hz ((β+3)/4))
  filter_upwards [hc,hr] with ξ hc hr
  refine ⟨fun δ hδ => ?_,fun z hz hG => ?_⟩
  · rw [potential_superlevel_eq_closed (by linarith : 0 ≤ (β+3)/4) hδ]
    exact hc δ hδ
  · exact div_ne_zero (hr z hz hG) (pow_ne_zero _ (norm_ne_zero_iff.mpr
      (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz)))

def pairingDomain (k : ℝ) : Set (DiskClass × halfPlane) :=
  {q | 0 < normalizedJacobian (classFun q.1) k q.2 ∧
    GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)}

lemma measurableSet_pairingDomain {k : ℝ} (hk : 0 ≤ k) : MeasurableSet (pairingDomain k) := by
  have hJ : Measurable (fun q : DiskClass × halfPlane => normalizedJacobian (classFun q.1) k q.2) :=
    (continuous_class_normalizedJacobian k).measurable
  have hG := (measurableSet_class_goodPairs hk).preimage (continuous_jointCriticalMap k).measurable
  change MeasurableSet {q : DiskClass × halfPlane | GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)} at hG
  exact (measurableSet_lt measurable_const hJ).inter hG

lemma criticalPair_eq_of_classRanks {k : ℝ} (hk : 0 < k) (q r : DiskClass × halfPlane)
    (hg : GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2))
    (he : jointCriticalMap k r = jointCriticalMap k q)
    (hJ : normalizedJacobian (classFun r.1) k r.2 < 0)
    (hr : classRankCount k (-1) r = classRankCount k 1 q) :
    criticalPair (classFun q.1) k q.2 = r.2 := by
  rcases q with ⟨g,z⟩
  rcases r with ⟨h,w⟩
  have hp : h = g := congrArg Prod.fst he
  subst h
  have hG : criticalMap (classFun g) k w = criticalMap (classFun g) k z := congrArg Prod.snd he
  have hgw : GoodPair (classFun g) k (criticalMap (classFun g) k w) := hG ▸ hg
  rw [classRankCount_eq_heightRank hk (-1) (g,w) hgw,
    classRankCount_eq_heightRank hk 1 (g,z) hg,signedFiber_neg_one,signedFiber_one,hG] at hr
  have heq : heightRank (criticalHeight (classFun g) k) (negativeFiber (classFun g) k (criticalMap (classFun g) k z)) w =
      heightRank (criticalHeight (classFun g) k) (positiveFiber (classFun g) k (criticalMap (classFun g) k z)) z := by
    exact_mod_cast hr
  exact rankPartner_eq (criticalHeight_rank_inj (classFun_schlicht g).1 hk hg).2 ⟨w.property,hG,hJ⟩ heq

lemma measurable_criticalPair {k : ℝ} (hk : 0 < k) :
    Measurable (fun q : pairingDomain k => criticalPair (classFun q.val.1) k q.val.2) := by
  let B := Classical.choice (exists_class_branches k)
  let y : pairingDomain k → DiskClass × ℂ := fun q => jointCriticalMap k q.val
  let b : ℕ → pairingDomain k → DiskClass × halfPlane := fun n q => B.branch n (y q)
  let M : ℕ → Set (pairingDomain k) := fun n => {q | y q ∈ jointCriticalMap k '' B.part n ∧
    normalizedJacobian (classFun (b n q).1) k (b n q).2 < 0 ∧
    classRankCount k (-1) (b n q) = classRankCount k 1 q.val}
  have hym : Measurable y := (continuous_jointCriticalMap k).measurable.comp measurable_subtype_coe
  have hbm (n) : Measurable (b n) := (B.measurable_branch n).comp hym
  apply measurable_branch_selection (b := fun n q => (b n q).2.val) (M := M)
  · intro n
    exact measurable_subtype_coe.comp ((hbm n).snd)
  · intro n
    exact ((B.measurable_image n).preimage hym).inter
      ((measurableSet_lt ((continuous_class_normalizedJacobian k).measurable.comp (hbm n)) measurable_const).inter
        (measurableSet_eq_fun ((measurable_classRankCount k (-1)).comp (hbm n))
          ((measurable_classRankCount k 1).comp measurable_subtype_coe)))
  · intro q
    obtain ⟨w,hw,_,hr⟩ := exists_critical_equalRank (classFun_schlicht q.val.1).1 hk q.property.2
      (show q.val.2.val ∈ positiveFiber (classFun q.val.1) k (criticalMap (classFun q.val.1) k q.val.2) from
        ⟨q.val.2.property,rfl,q.property.1⟩)
    let r : DiskClass × halfPlane := (q.val.1,⟨w,hw.1⟩)
    have hG : jointCriticalMap k r = y q := Prod.ext rfl hw.2.1
    have hns : r ∈ nonsingularClass k := ne_of_lt hw.2.2
    obtain ⟨n,hn⟩ := mem_iUnion.mp (B.cover.symm ▸ hns)
    have hb : b n q = r := by
      dsimp [b]
      rw [← hG]
      exact B.left_inv n r hn
    refine ⟨n,⟨⟨r,hn,hG⟩,?_,?_⟩⟩
    · simpa only [hb] using hw.2.2
    · rw [hb,classRankCount_eq_heightRank hk (-1) r (by simpa only [r,hw.2.1] using q.property.2),
        classRankCount_eq_heightRank hk 1 q.val q.property.2,signedFiber_neg_one,signedFiber_one]
      simpa only [r,hw.2.1] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hr
  · intro n q hq
    exact criticalPair_eq_of_classRanks hk q.val (b n q) q.property.2
      (B.right_inv n (y q) hq.1).2 hq.2.1 hq.2.2

end Brennan

end

end OAI
