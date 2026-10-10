import OAI.Analysis.IntegralMeans.RankPairing

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

lemma joint_locally_injective.{u_1} {P : Type u_1} [TopologicalSpace P]
    {F : P → ℂ → ℂ} {DF : P → ℂ → ℂ →L[ℝ] ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hder : ∀ p z, z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc : ContinuousOn (fun q : P × ℂ => DF q.1 q.2) (univ ×ˢ s))
    {p : P} {z : ℂ} (hz : z ∈ s) (he : LinearMap.det (DF p z).toLinearMap ≠ 0) :
    ∃ U : Set (P × ℂ), IsOpen U ∧ (p,z) ∈ U ∧
      InjOn (fun q : P × ℂ => (q.1,F q.1 q.2)) U := by
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr he)).toContinuousLinearEquiv
  have heq : (e : ℂ →L[ℝ] ℂ) = DF p z := by
    ext v
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr he) v
  let c : ℝ≥0 := ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
  have hn : 0 < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊ := by exact_mod_cast e.symm.norm_pos
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hclt : c < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    dsimp [c]
    exact half_lt_self (inv_pos.mpr hn)
  have hcAt : ContinuousAt (fun q : P × ℂ => DF q.1 q.2) (p,z) := hc.continuousAt ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ p,hz⟩)
  have hnb : {q : P × ℂ | q.2 ∈ s ∧ ‖DF q.1 q.2-(e : ℂ →L[ℝ] ℂ)‖₊ < c} ∈ 𝓝 (p,z) := by
    apply Filter.inter_mem
    · exact continuous_snd.continuousAt.preimage_mem_nhds (hs.mem_nhds hz)
    · exact ((hcAt.sub continuousAt_const).nnnorm).eventually
        (gt_mem_nhds (by simpa only [Pi.sub_apply,heq,sub_self,nnnorm_zero] using hcpos))
  obtain ⟨u,hu,v,hv,huv⟩ := mem_nhds_prod_iff.mp hnb
  obtain ⟨u',hu'u,hu'o,hpu⟩ := mem_nhds_iff.mp hu
  obtain ⟨r,hr,hvr⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨u' ×ˢ Metric.ball z r,hu'o.prod Metric.isOpen_ball,⟨hpu,Metric.mem_ball_self hr⟩,?_⟩
  rintro ⟨p1,z1⟩ h1 ⟨p2,z2⟩ h2 hh
  have hp : p1 = p2 := congrArg Prod.fst hh
  subst p2
  have hbound (w : ℂ) (hw : w ∈ Metric.ball z r) :
      w ∈ s ∧ ‖DF p1 w-(e : ℂ →L[ℝ] ℂ)‖₊ < c :=
    huv (show (p1,w) ∈ u ×ˢ v from ⟨hu'u h1.1,hvr hw⟩)
  have hLip : LipschitzOnWith c (fun w => F p1 w-e w) (Metric.ball z r) := by
    apply (convex_ball z r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun w hw => ((hder p1 w (hbound w hw).1).sub e.hasFDerivAt).hasFDerivWithinAt)
    exact fun w hw => (hbound w hw).2.le
  have hInj := hLip.approximatesLinearOn.injOn (Or.inr hclt)
  exact Prod.ext rfl (hInj h1.2 h2.2 (congrArg Prod.snd hh))

lemma countable_joint_injective_partition.{u_1} {P : Type u_1} [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]
    {F : P → ℂ → ℂ} {DF : P → ℂ → ℂ →L[ℝ] ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hder : ∀ p z, z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc : ContinuousOn (fun q : P × ℂ => DF q.1 q.2) (univ ×ˢ s)) :
    ∃ p : ℕ → Set (P × ℂ), (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0} ∧
      ∀ n, InjOn (fun q : P × ℂ => (q.1,F q.1 q.2)) (p n) := by
  classical
  let t : Set (P × ℂ) := {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0}
  have htopen : IsOpen t := by
    have h : IsOpen ((univ ×ˢ s) ∩ (fun q : P × ℂ => DF q.1 q.2) ⁻¹' {d | d.det ≠ 0}) :=
      hc.isOpen_inter_preimage (isOpen_univ.prod hs)
        (isClosed_eq ContinuousLinearMap.continuous_det continuous_const).isOpen_compl
    convert h using 1
    ext q
    simp [t]
  have hlocal (q : t) : ∃ U : Set (P × ℂ), IsOpen U ∧ q.val ∈ U ∧
      InjOn (fun q : P × ℂ => (q.1,F q.1 q.2)) U :=
    joint_locally_injective hs hder hc q.property.1 q.property.2
  choose U hUo hUq hUi using hlocal
  by_cases he : t = ∅
  · refine ⟨fun _ => ∅,by simp,by simp [Pairwise],?_,by simp⟩
    simpa using he.symm
  · have : Nonempty t := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,hj⟩ := (show IsLindelof t from HereditarilyLindelofSpace.isLindelof t).indexed_countable_subcover
      U hUo (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hUq ⟨q,hq⟩⟩)
    let q : ℕ → Set (P × ℂ) := fun n => t ∩ U (j n)
    refine ⟨disjointed q,?_,disjoint_disjointed q,?_,?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => htopen.measurableSet.inter (hUo (j n)).measurableSet) n
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion,mem_inter_iff,q]
      exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => by obtain ⟨n,hn⟩ := mem_iUnion.mp (hj hz); exact ⟨n,hz,hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)

lemma exists_borel_partial_inverse.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hs : MeasurableSet s) (hf : ContinuousOn f s) (hi : InjOn f s) :
    ∃ b : Y → X, Measurable b ∧ MeasurableSet (f '' s) ∧
      (∀ y ∈ f '' s, b y ∈ s ∧ f (b y) = y) ∧ ∀ x ∈ s, b (f x) = x := by
  classical
  have hm := hf.measurableEmbedding hs hi
  by_cases hne : s.Nonempty
  · let : Nonempty s := Set.nonempty_coe_sort.mpr hne
    let b : Y → X := fun y => (hm.invFun y).val
    refine ⟨b,measurable_subtype_coe.comp hm.measurable_invFun,?_,?_,?_⟩
    · simpa only [Set.range_domRestrict] using hm.measurableSet_range
    · rintro y ⟨x,hx,rfl⟩
      have hb : b (f x) = x := congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
      exact ⟨hb.symm ▸ hx,congrArg f hb⟩
    · intro x hx
      exact congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => Classical.arbitrary X,measurable_const,?_,?_,?_⟩ <;> simp [he]

lemma fiber_count_eq_tsum_branches.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSingletonClass X]
    {f : X → Y} {s : Set X} {p : ℕ → Set X} {b : ℕ → Y → X}
    (hp : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s)
    (hi : ∀ n, InjOn f (p n))
    (hb : ∀ n y, y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv : ∀ n x, x ∈ p n → b n (f x) = x)
    (R : X → Prop) (y : Y) :
    Measure.count {x | x ∈ s ∧ f x = y ∧ R x} =
      ∑' n, if y ∈ f '' p n ∧ R (b n y) then (1 : ℝ≥0∞) else 0 := by
  classical
  have he : {x | x ∈ s ∧ f x = y ∧ R x} = ⋃ n, {x | x ∈ p n ∧ f x = y ∧ R x} := by
    rw [← hu]
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  have hsub (n) : ({x | x ∈ p n ∧ f x = y ∧ R x} : Set X).Subsingleton := by
    intro x hx z hz
    exact hi n hx.1 hz.1 (hx.2.1.trans hz.2.1.symm)
  rw [he,measure_iUnion]
  · apply tsum_congr
    intro n
    by_cases hy : y ∈ f '' p n ∧ R (b n y)
    · rw [ite_eq_left hy]
      have hx : {x | x ∈ p n ∧ f x = y ∧ R x} = {b n y} := by
        apply Set.Subsingleton.eq_singleton_of_mem (hsub n)
        exact ⟨(hb n y hy.1).1,(hb n y hy.1).2,hy.2⟩
      rw [hx,Measure.count_singleton]
    · rw [ite_eq_right hy]
      have hx : {x | x ∈ p n ∧ f x = y ∧ R x} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hy
        refine ⟨⟨x,hx.1,hx.2.1⟩,?_⟩
        rw [← hx.2.1,hinv n x hx.1]
        exact hx.2.2
      rw [hx,measure_empty]
  · exact pairwise_disjoint_mono hp (fun n => fun x hx => hx.1)
  · intro n
    exact (hsub n).countable.measurableSet

lemma measurable_fiber_count_branches.{u_1, u_2, u_3} {X : Type u_1} {Y : Type u_2} {Q : Type u_3}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q]
    {f : X → Y} {s : Set X} {p : ℕ → Set X} {b : ℕ → Y → X}
    (hp : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s)
    (hi : ∀ n, InjOn f (p n)) (hbm : ∀ n, Measurable (b n))
    (hdm : ∀ n, MeasurableSet (f '' p n))
    (hb : ∀ n y, y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv : ∀ n x, x ∈ p n → b n (f x) = x)
    {R : Q → X → Prop} (hR : MeasurableSet {q : Q × X | R q.1 q.2})
    {y : Q → Y} (hy : Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) := by
  classical
  have he : (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) =
      fun q => ∑' n, if y q ∈ f '' p n ∧ R q (b n (y q)) then (1 : ℝ≥0∞) else 0 := by
    funext q
    exact fiber_count_eq_tsum_branches hp hu hi hb hinv (R q) (y q)
  rw [he]
  apply Measurable.tsum
  intro n
  apply Measurable.ite
  · exact (hdm n |>.preimage hy).inter
      (hR.preimage (measurable_id.prodMk ((hbm n).comp hy)))
  · exact measurable_const
  · exact measurable_const

lemma measurable_branch_selection.{u_1, u_2} {Q : Type u_1} {X : Type u_2} [MeasurableSpace Q] [MeasurableSpace X]
    {b : ℕ → Q → X} {M : ℕ → Set Q} {f : Q → X}
    (hb : ∀ n, Measurable (b n)) (hM : ∀ n, MeasurableSet (M n))
    (he : ∀ q, ∃ n, q ∈ M n) (hf : ∀ n q, q ∈ M n → f q = b n q) : Measurable f := by
  intro T hT
  have hset : f ⁻¹' T = ⋃ n, M n ∩ (b n) ⁻¹' T := by
    ext q
    constructor
    · intro hq
      obtain ⟨n,hn⟩ := he q
      exact mem_iUnion.mpr ⟨n,hn,by simpa only [mem_preimage,← hf n q hn] using hq⟩
    · intro hq
      obtain ⟨n,hn,ht⟩ := mem_iUnion.mp hq
      simpa only [mem_preimage,hf n q hn] using ht
  rw [hset]
  exact MeasurableSet.iUnion (fun n => (hM n).inter (hT.preimage (hb n)))

structure BorelBranches.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : Set X) where
  part : ℕ → Set X
  branch : ℕ → Y → X
  measurable_part : ∀ n, MeasurableSet (part n)
  disjoint : Pairwise (Disjoint on part)
  cover : (⋃ n, part n) = s
  injective : ∀ n, InjOn f (part n)
  measurable_branch : ∀ n, Measurable (branch n)
  measurable_image : ∀ n, MeasurableSet (f '' part n)
  right_inv : ∀ n y, y ∈ f '' part n → branch n y ∈ part n ∧ f (branch n y) = y
  left_inv : ∀ n x, x ∈ part n → branch n (f x) = x

lemma exists_borelBranches.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hf : ContinuousOn f s)
    (hp : ∃ p : ℕ → Set X, (∀ n, MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n)) : Nonempty (BorelBranches f s) := by
  obtain ⟨p,hpm,hpd,hpc,hpi⟩ := hp
  have hb (n) := exists_borel_partial_inverse (hpm n)
    (hf.mono (show p n ⊆ s from hpc ▸ subset_iUnion p n)) (hpi n)
  choose b hbm him hbr hbl using hb
  exact ⟨⟨p,b,hpm,hpd,hpc,hpi,hbm,him,hbr,hbl⟩⟩

lemma BorelBranches.measurable_count.{u_1, u_2, u_3} {X : Type u_1} {Y : Type u_2} {Q : Type u_3}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q]
    {f : X → Y} {s : Set X} (B : BorelBranches f s)
    {R : Q → X → Prop} (hR : MeasurableSet {q : Q × X | R q.1 q.2})
    {y : Q → Y} (hy : Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) :=
  measurable_fiber_count_branches B.disjoint B.cover B.injective B.measurable_branch
    B.measurable_image B.right_inv B.left_inv hR hy

lemma count_product_fiber.{u_1, u_2, u_3} {P : Type u_1} {X : Type u_2} {Y : Type u_3} [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace X] [MeasurableSingletonClass X] (F : P → X → Y)
    (R : P × X → Prop) (p : P) (y : Y) :
    Measure.count {q : P × X | (q.1,F q.1 q.2) = (p,y) ∧ R q} =
      Measure.count {x | F p x = y ∧ R (p,x)} := by
  have he : {q : P × X | (q.1,F q.1 q.2) = (p,y) ∧ R q} =
      (fun x => (p,x)) '' {x | F p x = y ∧ R (p,x)} := by
    ext q
    constructor
    · rintro ⟨hq,hR⟩
      obtain rfl : q.1 = p := congrArg Prod.fst hq
      exact ⟨q.2,⟨congrArg Prod.snd hq,hR⟩,rfl⟩
    · rintro ⟨x,⟨hx,hR⟩,rfl⟩
      exact ⟨Prod.ext rfl hx,hR⟩
  rw [he]
  exact Measure.count_injective_image (fun _ _ h => congrArg Prod.snd h) _

lemma count_subtype_set.{u_1} {X : Type u_1} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Set X) (R : X → Prop) :
    Measure.count {x : s | R x} = Measure.count {x : X | x ∈ s ∧ R x} := by
  rw [← Measure.count_injective_image (f := (Subtype.val : s → X)) Subtype.val_injective]
  congr 1
  ext x
  simp only [mem_image,mem_ofPred_eq,Subtype.exists,exists_prop]
  aesop

instance : PolishSpace DiskClass := by
  let := TopologicalSpace.metrizableSpaceMetric DiskClass
  infer_instance

instance : PolishSpace halfPlane := isOpen_halfPlane.polishSpace

instance : Nonempty halfPlane := ⟨⟨Complex.I,by simp [halfPlane]⟩⟩

def identityHalf (z : ℂ) : ℂ := z-Complex.I

lemma identityHalf_schlicht : HalfPlaneSchlicht identityHalf := by
  refine ⟨⟨(differentiable_id.sub_const Complex.I).differentiableOn,?_⟩,by simp [identityHalf],?_⟩
  · exact (sub_left_injective).injOn
  · exact (hasDerivAt_id Complex.I |>.sub_const Complex.I).deriv

def identityClass : DiskClass := classOfHalf identityHalf identityHalf_schlicht

instance : Nonempty DiskClass := ⟨identityClass⟩

def jointCriticalMap (k : ℝ) (q : DiskClass × halfPlane) : DiskClass × ℂ :=
  (q.1,criticalMap (classFun q.1) k q.2)

def nonsingularClass (k : ℝ) : Set (DiskClass × halfPlane) :=
  {q | normalizedJacobian (classFun q.1) k q.2 ≠ 0}

lemma continuous_jointCriticalMap (k : ℝ) : Continuous (jointCriticalMap k) :=
  continuous_fst.prodMk (continuous_class_criticalMap k)

lemma exists_class_branches (k : ℝ) : Nonempty (BorelBranches (jointCriticalMap k) (nonsingularClass k)) := by
  apply exists_borelBranches (continuous_jointCriticalMap k).continuousOn
  obtain ⟨p,hpm,hpd,hpc,hpi⟩ := countable_joint_injective_partition isOpen_halfPlane
    (fun g z hz => (differentiableAt_criticalMap (classFun_schlicht g).1 hz k).hasFDerivAt)
    (continuousOn_prod_of_continuous_subtype (F := fun g z => fderiv ℝ (criticalMap (classFun g) k) z) (continuous_class_fderiv_criticalMap k))
  let e : DiskClass × halfPlane → DiskClass × ℂ := fun q => (q.1,q.2)
  have hem : Measurable e := measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  let u : ℕ → Set (DiskClass × halfPlane) := fun n => e ⁻¹' p n
  refine ⟨u,fun n => (hpm n).preimage hem,?_,?_,?_⟩
  · intro n m hnm
    exact (hpd hnm).preimage e
  · ext q
    have hc : (∃ n, e q ∈ p n) ↔ (e q).2 ∈ halfPlane ∧
        LinearMap.det (fderiv ℝ (criticalMap (classFun q.1) k) q.2).toLinearMap ≠ 0 := by
      rw [← mem_iUnion,hpc]
      rfl
    simp only [mem_iUnion,mem_preimage,u]
    rw [hc]
    simp only [e,q.2.property,true_and,nonsingularClass,mem_ofPred_eq,normalizedJacobian]
    exact ((div_ne_zero_iff).trans (and_iff_left
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane
        (classFun_schlicht q.1).1 q.2.property))))).symm
  · intro n q hq r hr he
    have hz : e q = e r := hpi n hq hr he
    have hfst : q.1 = r.1 := congrArg (fun x : DiskClass × ℂ => x.1) hz
    have hsnd : q.2.val = r.2.val := congrArg (fun x : DiskClass × ℂ => x.2) hz
    exact Prod.ext hfst (Subtype.ext hsnd)

def classPrecedes (k : ℝ) (q r : DiskClass × halfPlane) : Prop :=
  criticalHeight (classFun r.1) k r.2 < criticalHeight (classFun q.1) k q.2 ∨
  criticalHeight (classFun q.1) k q.2 = criticalHeight (classFun r.1) k r.2 ∧
    (q.2.val.re < r.2.val.re ∨ q.2.val.re = r.2.val.re ∧ q.2.val.im < r.2.val.im)

lemma measurableSet_classPrecedes (k : ℝ) :
    MeasurableSet {p : (DiskClass × halfPlane) × (DiskClass × halfPlane) | classPrecedes k p.1 p.2} := by
  have hH := (continuous_class_criticalHeight k).measurable
  have hr : Measurable (fun q : DiskClass × halfPlane => q.2.val.re) :=
    Complex.continuous_re.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hi : Measurable (fun q : DiskClass × halfPlane => q.2.val.im) :=
    Complex.continuous_im.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  exact (measurableSet_lt (hH.comp measurable_snd) (hH.comp measurable_fst)).union
    ((measurableSet_eq_fun (hH.comp measurable_fst) (hH.comp measurable_snd)).inter
      ((measurableSet_lt (hr.comp measurable_fst) (hr.comp measurable_snd)).union
        ((measurableSet_eq_fun (hr.comp measurable_fst) (hr.comp measurable_snd)).inter
          (measurableSet_lt (hi.comp measurable_fst) (hi.comp measurable_snd)))))

def classRankCount (k σ : ℝ) (q : DiskClass × halfPlane) : ℝ≥0∞ :=
  Measure.count {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧
    0 < σ * normalizedJacobian (classFun r.1) k r.2 ∧ classPrecedes k r q}

lemma measurable_classRankCount (k σ : ℝ) : Measurable (classRankCount k σ) := by
  let B := Classical.choice (exists_class_branches k)
  apply B.measurable_count _ (continuous_jointCriticalMap k).measurable
  exact (measurableSet_lt measurable_const
    (measurable_const.mul ((continuous_class_normalizedJacobian k).measurable.comp measurable_snd))).inter
    ((measurableSet_classPrecedes k).preimage measurable_swap)

def signedFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) (σ : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ 0 < σ * normalizedJacobian f k z}

lemma signedFiber_one (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) :
    signedFiber f k ξ 1 = positiveFiber f k ξ := by ext z; simp [signedFiber,positiveFiber]

lemma signedFiber_neg_one (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) :
    signedFiber f k ξ (-1) = negativeFiber f k ξ := by ext z; simp [signedFiber,negativeFiber]

lemma classRankCount_eq_count (k σ : ℝ) (q : DiskClass × halfPlane) :
    classRankCount k σ q = Measure.count {w | w ∈ signedFiber (classFun q.1) k
      (criticalMap (classFun q.1) k q.2) σ ∧ heightPrecedes (criticalHeight (classFun q.1) k) w q.2} := by
  let R : DiskClass × halfPlane → Prop := fun r =>
    0 < σ * normalizedJacobian (classFun r.1) k r.2 ∧ classPrecedes k r q
  have he : {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧ R r} =
      {r : DiskClass × halfPlane | jointCriticalMap k r = jointCriticalMap k q ∧ R r} := by
    ext r
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_,h⟩
      intro hz
      have hp := h.2.1
      rw [hz,mul_zero] at hp
      exact lt_irrefl 0 hp
  change Measure.count {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧ R r} = _
  rw [he]
  simp only [jointCriticalMap]
  rw [count_product_fiber (fun g (z : halfPlane) => criticalMap (classFun g) k z) R]
  change Measure.count {w : halfPlane | criticalMap (classFun q.1) k w = criticalMap (classFun q.1) k q.2 ∧
    0 < σ * normalizedJacobian (classFun q.1) k w ∧ heightPrecedes (criticalHeight (classFun q.1) k) w q.2} = _
  rw [count_subtype_set halfPlane (fun w : ℂ => criticalMap (classFun q.1) k w = criticalMap (classFun q.1) k q.2 ∧
    0 < σ * normalizedJacobian (classFun q.1) k w ∧ heightPrecedes (criticalHeight (classFun q.1) k) w q.2)]
  congr 1
  ext w
  simp only [mem_ofPred_eq,signedFiber]
  tauto

lemma classRankCount_eq_heightRank {k : ℝ} (hk : 0 < k) (σ : ℝ) (q : DiskClass × halfPlane)
    (hg : GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)) :
    classRankCount k σ q =
      (heightRank (criticalHeight (classFun q.1) k)
        (signedFiber (classFun q.1) k (criticalMap (classFun q.1) k q.2) σ) q.2 : ℝ≥0∞) := by
  rw [classRankCount_eq_count,heightRank_eq_ncard]
  have hpos := criticalHeight_pos (classFun_schlicht q.1).1 hk q.2.property
  have hc := critical_count (classFun_schlicht q.1).1 hk hg hpos
  have hf : {w | w ∈ signedFiber (classFun q.1) k (criticalMap (classFun q.1) k q.2) σ ∧
      heightPrecedes (criticalHeight (classFun q.1) k) w q.2}.Finite := by
    apply hc.1.subset
    intro w hw
    refine ⟨hw.1.1,hw.1.2.1,?_⟩
    rw [potential_critical_height (classFun_schlicht q.1).1 hk hw.1.1 hw.1.2.1]
    apply ENNReal.ofReal_le_ofReal
    exact heightOrder_height_le ((heightOrder_lt_iff _ _ _).mpr hw.2)
  rw [Measure.count_apply_finite _ hf,← Set.ncard_eq_toFinset_card _ hf]

lemma heightRank_transport_on {H H' : ℂ → ℝ} {S S' : Set ℂ} (e : ℂ ≃ ℂ)
    (hS : ∀ w, w ∈ S' ↔ e w ∈ S) (z : ℂ)
    (hord : ∀ w ∈ S', heightPrecedes H' w z ↔ heightPrecedes H (e w) (e z)) :
    heightRank H' S' z = heightRank H S (e z) := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  apply Set.ncard_congr (fun w _ => e w)
  · intro w hw
    exact ⟨(hS w).mp hw.1,(hord w hw.1).mp hw.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro w hw
    have hm : e.symm w ∈ S' := (hS _).mpr (by simpa using hw.1)
    exact ⟨e.symm w,⟨hm,(hord _ hm).mpr (by simpa using hw.2)⟩,e.apply_symm_apply w⟩

lemma heightPrecedes_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z w : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    heightPrecedes (criticalHeight (reroot f t) k) z w ↔
      heightPrecedes (criticalHeight f k) (affine t z) (affine t w) := by
  have hc := heightScaleInverse_pos hf k ht
  have hre (v : ℂ) : (affine t v).re = t.re+t.im*v.re := by simp [affine]
  have him (v : ℂ) : (affine t v).im = t.im*v.im := by simp [affine]
  simp only [heightPrecedes,criticalHeight_reroot hf k ht hz,criticalHeight_reroot hf k ht hw,
    div_lt_div_iff_of_pos_right hc,div_left_inj' (ne_of_gt hc),hre,him,
    add_lt_add_iff_left,add_right_inj,mul_lt_mul_iff_right₀ (show 0 < t.im from ht),mul_right_inj' (ne_of_gt (show 0 < t.im from ht))]

lemma signedFiber_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) (σ : ℝ) (w : ℂ) :
    w ∈ signedFiber (reroot f t) k (rerootTarget f t ξ) σ ↔
      affine t w ∈ signedFiber f k ξ σ := by
  simp only [signedFiber,mem_ofPred_eq,affine_mem_iff ht]
  apply and_congr_right
  intro hw
  rw [criticalMap_reroot_fiber hf k ht hw,normalizedJacobian_reroot hf ht hw k (ne_of_gt hk)]

lemma heightRank_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) (σ : ℝ) :
    heightRank (criticalHeight (reroot f t) k) (signedFiber (reroot f t) k (rerootTarget f t ξ) σ) z =
      heightRank (criticalHeight f k) (signedFiber f k ξ σ) (affine t z) := by
  apply heightRank_transport_on (affineHome t ht).toEquiv
    (signedFiber_reroot hf hk ht ξ σ) z
  intro w hw
  exact heightPrecedes_reroot hf k ht hw.1 hz

lemma criticalPair_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane)
    (hJ : 0 < normalizedJacobian f k (affine t z))
    (hg : GoodPair f k (criticalMap f k (affine t z))) :
    affine t (criticalPair (reroot f t) k z) = criticalPair f k (affine t z) := by
  let f' := reroot f t
  have hf' : UnivalentOn f' halfPlane := (reroot_normalized hf ht).1
  have hG : criticalMap f' k z = rerootTarget f t (criticalMap f k (affine t z)) :=
    criticalMap_reroot hf ht hz k
  have hg' : GoodPair f' k (criticalMap f' k z) := by
    rw [hG]
    exact (goodPair_reroot hf hk ht _).mpr hg
  have hJ' : 0 < normalizedJacobian f' k z := by
    rw [normalizedJacobian_reroot hf ht hz k (ne_of_gt hk)]
    exact hJ
  have hs := criticalPair_spec hf' hk hz hJ' hg'
  have hr := rankPartner_spec (show ∃ w ∈ negativeFiber f' k (criticalMap f' k z),
      heightRank (criticalHeight f' k) (negativeFiber f' k (criticalMap f' k z)) w =
        heightRank (criticalHeight f' k) (positiveFiber f' k (criticalMap f' k z)) z from by
    obtain ⟨w,hw,_,he⟩ := exists_critical_equalRank hf' hk hg' ⟨hz,rfl,hJ'⟩
    exact ⟨w,hw,he⟩)
  have hr' : heightRank (criticalHeight f k)
      (negativeFiber f k (criticalMap f k (affine t z))) (affine t (criticalPair f' k z)) =
      heightRank (criticalHeight f k) (positiveFiber f k (criticalMap f k (affine t z))) (affine t z) := by
    have h := hr.2
    change heightRank (criticalHeight f' k) (negativeFiber f' k (criticalMap f' k z)) (criticalPair f' k z) = _ at h
    rw [← signedFiber_neg_one,← signedFiber_one,hG,
      heightRank_reroot hf hk ht hs.1 _ (-1),heightRank_reroot hf hk ht hz _ 1,
      signedFiber_neg_one,signedFiber_one] at h
    exact h
  have hm : affine t (criticalPair f' k z) ∈ negativeFiber f k (criticalMap f k (affine t z)) := by
    rw [← signedFiber_neg_one,← signedFiber_reroot hf hk ht _ (-1),← hG,signedFiber_neg_one]
    exact ⟨hs.1,hs.2.1,hs.2.2.1⟩
  exact (rankPartner_eq (criticalHeight_rank_inj hf hk hg).2 hm hr').symm

lemma heightRank_congr_on {H H' : ℂ → ℝ} {S : Set ℂ} (hS : S ⊆ halfPlane)
    (he : EqOn H H' halfPlane) {z : ℂ} (hz : z ∈ halfPlane) :
    heightRank H S z = heightRank H' S z := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  congr 1
  ext w
  apply and_congr_right
  intro hw
  simp only [heightPrecedes,he hz,he (hS hw)]

lemma signedFiber_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) (ξ : ℂ) (σ : ℝ) :
    signedFiber f k ξ σ = signedFiber g k ξ σ := by
  ext z
  simp only [signedFiber,mem_ofPred_eq]
  apply and_congr_right
  intro hz
  rw [criticalMap_congr he k hz,normalizedJacobian_congr he k hz]

lemma criticalPair_congr {f g : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (hg : UnivalentOn g halfPlane)
    (he : EqOn f g halfPlane) {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : z ∈ halfPlane)
    (hJ : 0 < normalizedJacobian f k z) (hgood : GoodPair f k (criticalMap f k z)) :
    criticalPair f k z = criticalPair g k z := by
  have hG := criticalMap_congr he k hz
  have hgood' : GoodPair g k (criticalMap g k z) := by
    rw [← hG]
    exact (goodPair_congr he k _).mp hgood
  have hs := criticalPair_spec hf hk hz hJ hgood
  have hr := rankPartner_spec (show ∃ w ∈ negativeFiber f k (criticalMap f k z),
      heightRank (criticalHeight f k) (negativeFiber f k (criticalMap f k z)) w =
        heightRank (criticalHeight f k) (positiveFiber f k (criticalMap f k z)) z from by
    obtain ⟨w,hw,_,hr⟩ := exists_critical_equalRank hf hk hgood ⟨hz,rfl,hJ⟩
    exact ⟨w,hw,hr⟩)
  have hneg : negativeFiber f k (criticalMap f k z) = negativeFiber g k (criticalMap g k z) := by
    rw [← signedFiber_neg_one,← signedFiber_neg_one,signedFiber_congr he,hG]
  have hpos : positiveFiber f k (criticalMap f k z) = positiveFiber g k (criticalMap g k z) := by
    rw [← signedFiber_one,← signedFiber_one,signedFiber_congr he,hG]
  have hr' := hr.2
  change heightRank (criticalHeight f k) (negativeFiber f k (criticalMap f k z)) (criticalPair f k z) = _ at hr'
  rw [heightRank_congr_on (fun w hw => hw.1) (criticalHeight_congr he k) hs.1,
    heightRank_congr_on (fun w hw => hw.1) (criticalHeight_congr he k) hz,hneg,hpos] at hr'
  exact (rankPartner_eq (criticalHeight_rank_inj hg hk hgood').2 (hneg ▸ hr.1) hr').symm

def halfOne : halfPlane := ⟨Complex.I,by simp [halfPlane]⟩

lemma class_normalizedJacobian_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k)
    (t w : halfPlane) :
    normalizedJacobian (classFun (rerootClass g t)) k w =
      normalizedJacobian (classFun g) k (affine t w) := by
  rw [normalizedJacobian_congr (classFun_rerootClass g t) k w.property,
    normalizedJacobian_reroot (classFun_schlicht g).1 t.property w.property k (ne_of_gt hk)]

lemma class_goodPair_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (t w : halfPlane) :
    GoodPair (classFun (rerootClass g t)) k
        (criticalMap (classFun (rerootClass g t)) k w) ↔
      GoodPair (classFun g) k (criticalMap (classFun g) k (affine t w)) := by
  rw [criticalMap_congr (classFun_rerootClass g t) k w.property,
    goodPair_congr (classFun_rerootClass g t) k,
    criticalMap_reroot (classFun_schlicht g).1 t.property w.property k]
  exact goodPair_reroot (classFun_schlicht g).1 hk t.property _

lemma class_criticalPair_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (t w : halfPlane)
    (hj : 0 < normalizedJacobian (classFun g) k (affine t w))
    (hg : GoodPair (classFun g) k (criticalMap (classFun g) k (affine t w))) :
    affine t (criticalPair (classFun (rerootClass g t)) k w) =
      criticalPair (classFun g) k (affine t w) := by
  have hj' : 0 < normalizedJacobian (classFun (rerootClass g t)) k w := by
    rw [class_normalizedJacobian_reroot g hk t w]; exact hj
  have hg' := (class_goodPair_reroot g hk t w).mpr hg
  rw [criticalPair_congr (classFun_schlicht (rerootClass g t)).1
      (reroot_normalized (classFun_schlicht g).1 t.property).1
      (classFun_rerootClass g t) hk w.property hj' hg']
  exact criticalPair_reroot (classFun_schlicht g).1 hk t.property w.property hj hg

lemma class_normalizedJacobian_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    normalizedJacobian (classFun (rerootClass g z)) k Complex.I =
      normalizedJacobian (classFun g) k z := by
  simpa only [halfOne,affine_I] using class_normalizedJacobian_reroot g hk z halfOne

lemma class_goodPair_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    GoodPair (classFun (rerootClass g z)) k
        (criticalMap (classFun (rerootClass g z)) k Complex.I) ↔
      GoodPair (classFun g) k (criticalMap (classFun g) k z) := by
  simpa only [halfOne,affine_I] using class_goodPair_reroot g hk z halfOne

end Brennan

end

end OAI
