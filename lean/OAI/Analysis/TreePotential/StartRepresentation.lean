import OAI.Analysis.TreePotential.StartMass

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

/-- The literal output coefficient of a countable segment array. Equivalently
this is the double sum over t≼v with t≼s≼v; Segment carries exactly that pair. -/
def representationOutput (a : Segment → ℝ) (v : Node) : ℝ :=
  ∑' S : Segment,if v ∈ S.nodes then a S else 0

lemma representationOutput_summable (a : Segment → ℝ) (ha : representationCost a≠∞) (v : Node) :
    Summable (fun S : Segment => if v ∈ S.nodes then a S else 0) := by
  have hh := (representation_series_bound a ha (Finsupp.single v 1)).1
  have he (S : Segment) : S.eval (Finsupp.single v (1:ℝ))=if v ∈ S.nodes then 1 else 0 := by
    change (∑ w ∈ S.nodes,Finsupp.single v (1:ℝ) w)=_
    simp [Finsupp.single_apply]
  simpa only [he,mul_ite,mul_one,mul_zero] using hh

def finiteRepresentationFunctional (a : Segment → ℝ) (ha : representationCost a≠∞) :
    TestVector atomTests →L[ℝ] ℝ :=
  ((representationPairing a ha).comp (testVectorEquiv atomTests).toLinearMap).mkContinuous
    (representationCost a).toReal (fun g => (representation_series_bound a ha ((testVectorEquiv atomTests) g)).2)

lemma finiteRepresentationFunctional_norm (a : Segment → ℝ) (ha : representationCost a≠∞) :
    ‖finiteRepresentationFunctional a ha‖ ≤ (representationCost a).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro g
  exact (representation_series_bound a ha ((testVectorEquiv atomTests) g)).2

def representationFunctional (a : Segment → ℝ) (ha : representationCost a≠∞) : Dual :=
  (finiteRepresentationFunctional a ha).extend UniformSpace.Completion.toComplL

lemma representationFunctional_lift (a : Segment → ℝ) (ha : representationCost a≠∞) (g : Node →₀ ℝ) :
    representationFunctional a ha (finiteLift atomTests g)=∑' S : Segment,a S*S.eval g := by
  exact (finiteRepresentationFunctional a ha).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing ((testVectorEquiv atomTests).symm g)

lemma representationFunctional_norm (a : Segment → ℝ) (ha : representationCost a≠∞) :
    ‖representationFunctional a ha‖ ≤ (representationCost a).toReal := by
  have h := (finiteRepresentationFunctional a ha).opNorm_extend_le (N:=1)
    (e:=UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe (fun x => by simp)
  have h' : ‖representationFunctional a ha‖ ≤ ‖finiteRepresentationFunctional a ha‖ := by
    simpa only [NNReal.coe_one,one_mul,representationFunctional] using h
  exact h'.trans (finiteRepresentationFunctional_norm a ha)

/-- Every finite-cost literal representation defines an element of the full incomparable dual through the core/full-dual equivalence. -/

def representedCore (a : Segment → ℝ) (ha : representationCost a≠∞) : DualCore :=
  coreDualEquiv.symm (representationFunctional a ha)

lemma representedCore_norm (a : Segment → ℝ) (ha : representationCost a≠∞) :
    ‖representedCore a ha‖ ≤ (representationCost a).toReal := by
  unfold representedCore
  rw [LinearIsometryEquiv.norm_map]
  exact representationFunctional_norm a ha

lemma representedCore_coordinate (a : Segment → ℝ) (ha : representationCost a≠∞) (v : Node) :
    coordinateFunctional unitTests v (representedCore a ha)=representationOutput a v := by
  rw [← coreToDual_coordinate_apply]
  have he : coreToDual (representedCore a ha)=representationFunctional a ha := coreDualEquiv.apply_symm_apply _
  rw [he]
  change representationFunctional a ha (finiteLift atomTests (Finsupp.single v 1))=_
  rw [representationFunctional_lift]
  apply tsum_congr
  intro S
  have hs : S.eval (Finsupp.single v (1:ℝ))=if v ∈ S.nodes then 1 else 0 := by
    change (∑ w ∈ S.nodes,Finsupp.single v (1:ℝ) w)=_
    simp [Finsupp.single_apply]
  rw [hs]
  split_ifs <;> simp

lemma dual_coordinates_total (φ : Dual) (hφ : ∀ v,φ (coordinateVector atomTests v)=0) : φ=0 := by
  have hfinite (z : Node →₀ ℝ) : φ (finiteLift atomTests z)=0 := by
    have he : (∑ v ∈ z.support,z v • Finsupp.single v (1:ℝ))=z := by
      simpa only [Finsupp.sum,Finsupp.smul_single,smul_eq_mul,mul_one] using z.sum_single
    rw [← he]
    simp only [map_sum,map_smul,smul_eq_mul]
    have hz (v : Node) : φ (finiteLift atomTests (Finsupp.single v 1))=0 := hφ v
    simp only [hz,mul_zero,Finset.sum_const_zero]
  apply ContinuousLinearMap.ext
  intro x
  change φ x=0
  refine UniformSpace.Completion.induction_on x (isClosed_eq φ.continuous continuous_const) ?_
  intro z
  exact hfinite ((testVectorEquiv atomTests) z)

lemma core_coordinates_total (x : DualCore) (hx : ∀ v,coordinateFunctional unitTests v x=0) : x=0 := by
  apply coreToDualIsometry.injective
  rw [map_zero]
  apply dual_coordinates_total
  intro v
  change coreToDual x (coordinateVector atomTests v)=0
  rw [coreToDual_coordinate_apply,hx]

lemma representedCore_add (a b : Segment → ℝ) (ha : representationCost a≠∞) (hb : representationCost b≠∞)
    (hab : representationCost (a+b)≠∞) :
    representedCore (a+b) hab=representedCore a ha+representedCore b hb := by
  apply sub_eq_zero.mp
  apply core_coordinates_total
  intro v
  simp only [map_sub,map_add,representedCore_coordinate]
  have h := (representationOutput_summable a ha v).tsum_add (representationOutput_summable b hb v)
  change representationOutput (a+b) v-(representationOutput a v+representationOutput b v)=0
  apply sub_eq_zero.mpr
  unfold representationOutput
  rw [← h]
  apply tsum_congr
  intro S
  split_ifs <;> simp

lemma representedCore_smul (c : ℝ) (a : Segment → ℝ) (ha : representationCost a≠∞)
    (hca : representationCost (c • a)≠∞) :
    representedCore (c • a) hca=c • representedCore a ha := by
  apply sub_eq_zero.mp
  apply core_coordinates_total
  intro v
  simp only [map_sub,map_smul,representedCore_coordinate,smul_eq_mul]
  change representationOutput (c • a) v-c*representationOutput a v=0
  apply sub_eq_zero.mpr
  unfold representationOutput
  rw [← tsum_mul_left]
  apply tsum_congr
  intro S
  split_ifs <;> simp

lemma Atom.representedCore (A : Atom) (hA : representationCost A.representation≠∞) :
    representedCore A.representation hA=A.inCore := by
  apply sub_eq_zero.mp
  apply core_coordinates_total
  intro v
  rw [map_sub,representedCore_coordinate]
  change representationOutput A.representation v-
    coordinateFunctional unitTests v ((testVectorEquiv unitTests).symm A.vector : TestVector unitTests)=0
  rw [coordinateFunctional_coe,LinearEquiv.apply_symm_apply]
  have he : representationOutput A.representation v=A.vector v := by
    unfold representationOutput
    rw [tsum_eq_sum (s:=A.family)]
    · simp only [Atom.vector,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,segmentVector_apply]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Atom.representation_apply,ite_eq_left hS]
      split_ifs <;> simp
    · intro S hS
      simp [Atom.representation_apply,hS]
  exact sub_eq_zero.mpr he

lemma representationCost_entry (a : Segment → ℝ) (S : Segment) :
    ENNReal.ofReal |a S| ≤ representationCost a := by
  apply le_trans (b:=startArray (fun T => ENNReal.ofReal |a T|) S.start.1 S.start.2.val)
  · unfold startArray
    simpa only [and_self,ite_true] using
      (ENNReal.le_tsum (f := fun segment => if S.start.1=segment.start.1 ∧ S.start.2.val=segment.start.2.val then ENNReal.ofReal |a segment| else 0) S : (if S.start.1=S.start.1 ∧ S.start.2.val=S.start.2.val then ENNReal.ofReal |a S| else 0)≤_)
  · exact forestCost_node_le _ _ _ S.start.2.property

/-- The domain consists of all literal arrays of finite upward start cost. -/
def CostDomain : Submodule ℝ (Segment → ℝ) where
  carrier := {a | representationCost a≠∞}
  zero_mem' := by simp
  add_mem' ha hb := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ha,hb⟩) (representationCost_add _ _)
  smul_mem' c a ha := by
    change representationCost (c • a)≠∞
    rw [representationCost_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha

def representationMap : CostDomain →ₗ[ℝ] DualCore where
  toFun a := representedCore a.val a.property
  map_add' a b := representedCore_add _ _ a.property b.property _
  map_smul' c a := representedCore_smul c _ a.property _

lemma representationCost_finset_sum {I : Type*} (E : Finset I) (a : I → Segment → ℝ) :
    representationCost (∑ i ∈ E,a i)≤∑ i ∈ E,representationCost (a i) := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert i E hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (representationCost_add _ _).trans (add_le_add le_rfl ih)

lemma atom_mixture_cost {I : Type*} [Fintype I] (p : I → ℝ) (A : I → Atom)
    (hp : ∀ i,0≤ p i) (hp1 : ∑ i,p i=1) :
    representationCost (∑ i,p i • (A i).representation)≤1 := by
  apply (representationCost_finset_sum Finset.univ _).trans
  calc
    _ ≤ ∑ i,ENNReal.ofReal (p i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [representationCost_smul,abs_of_nonneg (hp i)]
      exact mul_le_of_le_one_right zero_le (Atom.representation_cost (A i))
    _ = 1 := by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i),hp1]; norm_num

lemma atom_mixture_output {I : Type*} [Fintype I] (p : I → ℝ) (A : I → Atom)
    (ha : representationCost (∑ i,p i • (A i).representation)≠∞) :
    representedCore (∑ i,p i • (A i).representation) ha=∑ i,p i • (A i).inCore := by
  let a : I → CostDomain := fun i => ⟨(A i).representation,
    ne_top_of_le_ne_top ENNReal.one_ne_top (Atom.representation_cost (A i))⟩
  have he : (∑ i,p i • (A i).representation)=((∑ i,p i • a i : CostDomain) : Segment → ℝ) := by simp [a]
  change representationMap ⟨_,ha⟩=_
  have he' : (⟨_,ha⟩ : CostDomain)=∑ i,p i • a i := Subtype.ext he
  rw [he',map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  exact Atom.representedCore (A i) _

lemma exists_representation_approx (x : DualCore) {e : ℝ} (he : 0< e) :
    ∃ (a : Segment → ℝ) (ha : representationCost a≠∞),
      representationCost a≤ ENNReal.ofReal ‖x‖ ∧ ‖representedCore a ha-x‖≤ e := by
  by_cases hx : x=0
  · subst x
    refine ⟨0,by simp,by simp,?_⟩
    have h0 : representedCore 0 (by simp)=0 := representationMap.map_zero
    simpa only [h0,sub_zero,norm_zero] using he.le
  · have hn : 0<‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖≤1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
      simp [ne_of_gt hn]
    obtain ⟨I,hI,hne,p,A,hp,hp1,happrox⟩ := exists_atom_distribution (‖x‖⁻¹ • x) hu (div_pos he hn)
    let := hI
    let a := ∑ i,p i • (A i).representation
    have ha1 : representationCost a≤1 := atom_mixture_cost p A hp hp1
    have ha : representationCost a≠∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
    have hna : representationCost (‖x‖ • a)≤ ENNReal.ofReal ‖x‖ := by
      rw [representationCost_smul,abs_of_nonneg (norm_nonneg _)]
      exact mul_le_of_le_one_right zero_le ha1
    have hnat : representationCost (‖x‖ • a)≠∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hna
    refine ⟨‖x‖ • a,hnat,hna,?_⟩
    rw [representedCore_smul _ _ ha,atom_mixture_output p A]
    have heq : ‖x‖ • (∑ i,p i • (A i).inCore)-x=
        ‖x‖ • ((∑ i,p i • (A i).inCore)-‖x‖⁻¹ • x) := by
      rw [smul_sub,smul_smul,mul_inv_cancel₀ (ne_of_gt hn),one_smul]
    rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left happrox (norm_nonneg x)).trans_eq (mul_div_cancel₀ _ (ne_of_gt hn))

lemma representationCost_tsum {I : Type*} (a : I → Segment → ℝ)
    (hcost : (∑' i,representationCost (a i))≠∞) :
    representationCost (fun S => ∑' i,a i S)≤∑' i,representationCost (a i) := by
  have hentry (S : Segment) : Summable (fun i => a i S) :=
    (real_series_bound _ hcost (ENNReal.tsum_le_tsum (fun i => representationCost_entry (a i) S))).1
  have hentryabs (S : Segment) :
      ENNReal.ofReal |∑' i,a i S| ≤ ∑' i,ENNReal.ofReal |a i S| := by
    have hnorm : Summable (fun i => |a i S|) := by simpa only [Real.norm_eq_abs] using (hentry S).norm
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) hnorm]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hentry S).norm)
  calc
    _ ≤ forestCost (startArray (fun S => ∑' i,ENNReal.ofReal |a i S|)) := by
      exact forestCost_mono (startArray_mono hentryabs)
    _ ≤ ∑' i,representationCost (a i) := by
      rw [startArray_tsum]
      exact forestCost_tsum _

lemma representationOutput_energy (a : Segment → ℝ) (v : Node) :
    (∑' S : Segment,ENNReal.ofReal |if v ∈ S.nodes then a S else 0|)≤ representationCost a := by
  have hh := representation_finite_energy a (Finsupp.single v 1)
  have he (S : Segment) : S.eval (Finsupp.single v (1:ℝ))=if v ∈ S.nodes then 1 else 0 := by
    change (∑ w ∈ S.nodes,Finsupp.single v (1:ℝ) w)=_
    simp [Finsupp.single_apply]
  have hn : testNorm atomTests (Finsupp.single v 1)=1 := norm_test_single atomTests v
  simpa only [he,mul_ite,mul_one,mul_zero,hn,ENNReal.ofReal_one] using hh

lemma representedCore_summable {I : Type*} (a : I → Segment → ℝ)
    (hcost : (∑' i,representationCost (a i))≠∞) :
    Summable (fun i => representedCore (a i) (ENNReal.ne_top_of_tsum_ne_top hcost i)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _)
    (fun i => representedCore_norm (a i) _)
  exact ENNReal.summable_toReal hcost

/-- Absolute joint-coordinate summability, before exchanging two series. -/
lemma representationOutput_joint_summable {I : Type*} (a : I → Segment → ℝ)
    (hcost : (∑' i,representationCost (a i))≠∞) (v : Node) :
    Summable (fun q : I × Segment => if v ∈ q.2.nodes then a q.1 q.2 else 0) := by
  apply (real_series_bound _ hcost _).1
  rw [ENNReal.tsum_prod (f:=fun i S => ENNReal.ofReal |if v ∈ S.nodes then a i S else 0|)]
  exact ENNReal.tsum_le_tsum (fun i => representationOutput_energy (a i) v)

lemma real_tsum_ite_comm {I J : Type*} (a : I → J → ℝ) (p : J → Prop) [DecidablePred p]
    (h : Summable (fun q : I × J => if p q.2 then a q.1 q.2 else 0)) :
    (∑' j,if p j then ∑' i,a i j else 0)=∑' i,∑' j,if p j then a i j else 0 := by
  have he (j : J) : (if p j then ∑' i,a i j else 0)=∑' i,if p j then a i j else 0 := by
    by_cases hp : p j
    · simp only [hp,ite_true]
    · simp only [hp,ite_false,tsum_zero]
  exact (tsum_congr he).trans (Summable.tsum_comm (f:=fun i j => if p j then a i j else 0) h)

/-- Combining identical segments preserves every output coordinate. -/
lemma representationOutput_tsum {I : Type*} (a : I → Segment → ℝ)
    (hcost : (∑' i,representationCost (a i))≠∞) (v : Node) :
    representationOutput (fun S => ∑' i,a i S) v=∑' i,representationOutput (a i) v := by
  exact real_tsum_ite_comm a (fun S => v ∈ S.nodes) (representationOutput_joint_summable a hcost v)

/-- Countable finite-cost representations commute with summation. -/
lemma representedCore_tsum {I : Type*} (a : I → Segment → ℝ)
    (hcost : (∑' i,representationCost (a i))≠∞)
    (ha : representationCost (fun S => ∑' i,a i S)≠∞) :
    representedCore (fun S => ∑' i,a i S) ha=
      ∑' i,representedCore (a i) (ENNReal.ne_top_of_tsum_ne_top hcost i) := by
  have hs := representedCore_summable a hcost
  apply sub_eq_zero.mp
  apply core_coordinates_total
  intro v
  rw [map_sub,representedCore_coordinate,(coordinateFunctional unitTests v).map_tsum hs]
  simp only [representedCore_coordinate]
  exact sub_eq_zero.mpr (representationOutput_tsum a hcost v)

end BoundedTreePotentials.Segments

end

end OAI
