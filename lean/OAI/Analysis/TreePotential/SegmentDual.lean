import OAI.Analysis.TreePotential.SegmentComponents

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

/-- The finite ancestral closure, not a same-level truncation. -/
def prefixClosure (E : Finset Node) : Finset Node := E.biUnion ancestors

lemma subset_prefixClosure (E : Finset Node) : E ⊆ prefixClosure E := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨v,hv,(mem_ancestors v v).mpr (prefix_refl v)⟩

lemma initial_prefixClosure (E : Finset Node) : Initial (prefixClosure E : Set Node) := by
  intro s t hs hts
  obtain ⟨v,hv,hsv⟩ := Finset.mem_biUnion.mp hs
  exact Finset.mem_biUnion.mpr ⟨v,hv,(mem_ancestors v t).mpr (hts.trans ((mem_ancestors v s).mp hsv))⟩

def finitelyRestrict (E : Finset Node) (g : Node → ℝ) : Node →₀ ℝ :=
  Finsupp.onFinset E ((E : Set Node).indicator g) (by
    intro v hv
    by_contra hn
    exact hv (Set.indicator_of_notMem hn g))

@[simp] lemma finitelyRestrict_apply (E : Finset Node) (g : Node → ℝ) (v : Node) :
    finitelyRestrict E g v = if v ∈ E then g v else 0 := by
  simp only [finitelyRestrict,Finsupp.onFinset_apply,Set.indicator_apply,Finset.mem_coe]

lemma pairing_finitelyRestrict (E : Finset Node) (g : Node → ℝ) (z : Node →₀ ℝ)
    (hz : z.support ⊆ E) : finitePairing (finitelyRestrict E g) z=finitePairing g z := by
  simp only [finitePairing_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [finitelyRestrict_apply,ite_eq_left (hz hv)]

lemma finitePairing_coeff_smul (c : ℝ) (g : Node → ℝ) (z : Node →₀ ℝ) :
    finitePairing (c • g) z=c*finitePairing g z := by
  simp only [finitePairing_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma polar_pairing_bound (z g : Node →₀ ℝ) :
    |finitePairing g z| ≤ testNorm unitTests z*testNorm atomTests g := by
  let R := testNorm atomTests g
  have hR := testNorm_nonneg atomTests g
  by_cases hz : R=0
  · have hg : g=0 := (testNorm_eq_zero atomTests g).mp hz
    subst g
    simp [finitePairing, testNorm_zero]
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    have hu : IsUnitTest (R⁻¹ • (g : Node → ℝ)) := by
      have hh : testNorm atomTests (R⁻¹ • g) ≤ 1 := by
        calc
          _ ≤ ‖R⁻¹‖*testNorm atomTests g := testNorm_smul_le atomTests _ _
          _ = 1 := by rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]; exact inv_mul_cancel₀ hz
      exact (predual_unit_iff (R⁻¹ • g)).mp hh
    have hh := finitePairing_le_testNorm unitTests ⟨_,hu⟩ z
    rw [finitePairing_coeff_smul,abs_mul,abs_of_pos (inv_pos.mpr hp)] at hh
    have he := mul_le_mul_of_nonneg_left hh hp.le
    rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul] at he
    simpa only [R,mul_comm] using he

/-- On finite arrays this is exactly the coefficient functional in the full dual. -/

def finiteDual : (Node →₀ ℝ) →ₗ[ℝ] Dual :=
  Finsupp.linearCombination ℝ (coordinateFunctional atomTests)

lemma finiteDual_apply (z : Node →₀ ℝ) (x : Predual) :
    finiteDual z x=∑ v ∈ z.support,z v*coordinateFunctional atomTests v x := by
  simp [finiteDual,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul]

lemma finiteDual_lift (z g : Node →₀ ℝ) :
    finiteDual z (finiteLift atomTests g)=finitePairing g z := by
  rw [finiteDual_apply,finitePairing_apply]
  apply Finset.sum_congr rfl
  intro v hv
  change z v * coordinateFunctional atomTests v
    (((testVectorEquiv atomTests).symm g : TestVector atomTests) : Predual)=_
  rw [coordinateFunctional_coe,LinearEquiv.apply_symm_apply]

lemma finiteDual_norm_le (z : Node →₀ ℝ) : ‖finiteDual z‖ ≤ testNorm unitTests z := by
  apply (finiteDual z).opNorm_le_bound (testNorm_nonneg unitTests z)
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_le ((finiteDual z).continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro w
  let g := testVectorEquiv atomTests w
  change |finiteDual z (finiteLift atomTests g)| ≤ testNorm unitTests z*‖finiteLift atomTests g‖
  rw [finiteDual_lift,finiteLift_norm]
  exact polar_pairing_bound z g

lemma finiteDual_norm (z : Node →₀ ℝ) : ‖finiteDual z‖=testNorm unitTests z := by
  apply le_antisymm (finiteDual_norm_le z)
  apply ciSup_le
  intro g
  let E := prefixClosure z.support
  let w := finitelyRestrict E g.val
  have hw : testNorm atomTests w ≤ 1 := (predual_unit_iff w).mpr
    (unit_head (initial_prefixClosure z.support) g.property)
  have he : finitePairing g.val z=finiteDual z (finiteLift atomTests w) := by
    rw [finiteDual_lift,pairing_finitelyRestrict E g.val z (subset_prefixClosure z.support)]
  rw [he]
  calc
    _ ≤ ‖finiteDual z‖*‖finiteLift atomTests w‖ := (finiteDual z).le_opNorm _
    _ ≤ ‖finiteDual z‖ := by rw [finiteLift_norm]; exact mul_le_of_le_one_right (norm_nonneg _) hw

def finiteDualIsometry : TestVector unitTests →ₗᵢ[ℝ] Dual where
  toLinearMap := finiteDual.comp (testVectorEquiv unitTests).toLinearMap
  norm_map' := fun z => finiteDual_norm ((testVectorEquiv unitTests) z)

def coreToDual : DualCore →L[ℝ] Dual :=
  finiteDualIsometry.toContinuousLinearMap.extend UniformSpace.Completion.toComplL

lemma coreToDual_coe (z : TestVector unitTests) :
    coreToDual z=finiteDual ((testVectorEquiv unitTests) z) :=
  finiteDualIsometry.toContinuousLinearMap.extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing z

lemma coreToDual_lift (z : Node →₀ ℝ) : coreToDual (coreLift z)=finiteDual z :=
  coreToDual_coe ((testVectorEquiv unitTests).symm z)

lemma coreToDual_norm (x : DualCore) : ‖coreToDual x‖=‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq coreToDual.continuous.norm continuous_norm) ?_
  intro z
  rw [coreToDual_coe,UniformSpace.Completion.norm_coe]
  exact finiteDual_norm ((testVectorEquiv unitTests) z)

def coreToDualIsometry : DualCore →ₗᵢ[ℝ] Dual where
  toLinearMap := coreToDual.toLinearMap
  norm_map' := coreToDual_norm

lemma coordinateFunctional_total (x : Predual)
    (hx : ∀ v, coordinateFunctional atomTests v x=0) : x=0 := by
  -- Finite atomic profiles are norming, so their coordinate span is total.
  have hc : ∀ f : atomTests, completedTestFunctional atomTests f x=0 := by
    rintro ⟨f,A,hA⟩
    subst f
    have he : completedTestFunctional atomTests ⟨A.profile,⟨A,rfl⟩⟩ = finiteDual A.vector := by
      apply ContinuousLinearMap.ext
      intro y
      refine UniformSpace.Completion.induction_on y
        (isClosed_eq (completedTestFunctional atomTests ⟨A.profile,⟨A,rfl⟩⟩).continuous
          (finiteDual A.vector).continuous) ?_
      intro w
      rw [completedTestFunctional_coe]
      change finitePairing A.profile ((testVectorEquiv atomTests) w)=
        finiteDual A.vector (finiteLift atomTests ((testVectorEquiv atomTests) w))
      rw [finiteDual_lift,Atom.finitePairing_vector,finitePairing_profile]
    rw [he,finiteDual_apply]
    exact Finset.sum_eq_zero (fun v hv => by rw [hx v,mul_zero])
  apply norm_eq_zero.mp
  rw [completed_tests_norming]
  simp only [hc,ciSup_const]

lemma coreToDual_surjective : Function.Surjective coreToDual := by
  have hclosed : IsClosed (Set.range coreToDual) :=
    coreToDualIsometry.isometry.antilipschitzWith.isClosed_range coreToDual.uniformContinuous
  intro x
  by_contra hx
  have hn : x ∉ (coreToDual.range : Set Dual) := hx
  obtain ⟨Ψ,R,hR,hxR⟩ := geometric_hahn_banach_closed_point coreToDual.range.convex hclosed hn
  obtain ⟨g,hg⟩ := predual_reflexive Ψ
  have hzero : ∀ z : DualCore, Ψ (coreToDual z)=0 := by
    intro z
    have hbound : ∀ a : ℝ, a*Ψ (coreToDual z) < R := by
      intro a
      have hh := hR (coreToDual (a • z)) ⟨a • z,rfl⟩
      change Ψ (coreToDual (a • z)) < R at hh
      simpa only [map_smul,smul_eq_mul] using hh
    by_contra hz
    have hh := hbound (R/Ψ (coreToDual z))
    rw [div_mul_cancel₀ _ hz] at hh
    exact lt_irrefl R hh
  have hcoords : ∀ v, coordinateFunctional atomTests v g=0 := by
    intro v
    have he := DFunLike.congr_fun hg (finiteDual (Finsupp.single v 1))
    change finiteDual (Finsupp.single v 1) g=Ψ (finiteDual (Finsupp.single v 1)) at he
    rw [← coreToDual_lift,hzero,coreToDual_lift] at he
    simpa [finiteDual,Finsupp.linearCombination_single] using he
  have hg0 := coordinateFunctional_total g hcoords
  subst g
  have hΨ : Ψ=0 := by simpa only [map_zero] using hg.symm
  have hpos := hR 0 ⟨0,map_zero _⟩
  rw [hΨ] at hpos hxR
  simp only [zero_apply] at hpos hxR
  linarith

/-- The segment estimate extends to the completed dual. -/

def coreDualEquiv : DualCore ≃ₗᵢ[ℝ] Dual :=
  LinearIsometryEquiv.ofSurjective coreToDualIsometry coreToDual_surjective

end BoundedTreePotentials.Segments

namespace BoundedTreePotentials

/-- Surjectivity of the canonical bidual map passes to the continuous dual. -/
theorem dual_reflexive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : IsReflexive E) : IsReflexive (StrongDual ℝ E) := by
  intro Φ
  let φ := Φ.comp (NormedSpace.inclusionInDoubleDual ℝ E)
  refine ⟨φ,?_⟩
  ext Ψ
  obtain ⟨x,rfl⟩ := hE Ψ
  rfl

end BoundedTreePotentials

namespace BoundedTreePotentials.Segments

theorem incomparable_reflexive : IsReflexive Dual := dual_reflexive predual_reflexive

theorem core_reflexive : IsReflexive DualCore :=
  reflexive_equiv coreDualEquiv.toContinuousLinearEquiv incomparable_reflexive

/-- Coordinate truncation on the full dual, defined by the biorthogonal basis
independently of the core isometry. -/

def dualHead (E : Finset Node) : Dual →L[ℝ] Dual :=
  ∑ v ∈ E, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector atomTests v)).smulRight
    (coordinateFunctional atomTests v)

def dualTail (E : Finset Node) : Dual →L[ℝ] Dual := ContinuousLinearMap.id ℝ Dual-dualHead E

lemma dualHead_apply (E : Finset Node) (x : Dual) :
    dualHead E x=∑ v ∈ E,x (coordinateVector atomTests v) • coordinateFunctional atomTests v := by
  simp [dualHead]

lemma coreToDual_coordinate (v : Node) :
    coreToDual (coordinateVector unitTests v)=coordinateFunctional atomTests v := by
  change coreToDual (coreLift (Finsupp.single v 1))=_
  rw [coreToDual_lift]
  simp [finiteDual,Finsupp.linearCombination_single]

lemma coreToDual_coordinate_apply (x : DualCore) (v : Node) :
    coreToDual x (coordinateVector atomTests v)=coordinateFunctional unitTests v x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (by fun_prop) (coordinateFunctional unitTests v).continuous) ?_
  intro z
  rw [coreToDual_coe,coordinateFunctional_coe]
  change finiteDual ((testVectorEquiv unitTests) z) (finiteLift atomTests (Finsupp.single v 1))=_
  rw [finiteDual_lift]
  have hf : (↑(Finsupp.single v (1:ℝ)) : Node → ℝ) = (fun j => if j=v then 1 else 0) := by
    funext j
    simp only [Finsupp.single_apply,eq_comm]
  rw [hf]
  exact finitePairing_single_test ((testVectorEquiv unitTests) z) v

lemma coreToDual_head (E : Finset Node) (x : DualCore) :
    coreToDual (completedHead unitTests E x)=dualHead E (coreToDual x) := by
  simp only [completedHead_apply,map_sum,map_smul,coreToDual_coordinate,dualHead_apply,
    coreToDual_coordinate_apply]

lemma coreToDual_tail (E : Finset Node) (x : DualCore) :
    coreToDual (completedTail unitTests E x)=dualTail E (coreToDual x) := by
  simp only [completedTail_apply,map_sub,coreToDual_head,dualTail,sub_apply,
    ContinuousLinearMap.id_apply]

/-- Full-dual version of the incomparable-segment estimate, with the exact
constant and the literal coordinate head. -/
theorem incomparable_tail {E : Finset Node} (hE : Initial (E : Set Node))
    (x y : Dual) (hx : dualHead E x=x) (hp : ‖x+y‖ ≤ 1) (hm : ‖x-y‖ ≤ 1) :
    ‖dualTail E y‖ ≤ (Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-‖x‖) := by
  obtain ⟨u,rfl⟩ := coreToDual_surjective x
  obtain ⟨v,rfl⟩ := coreToDual_surjective y
  have hu : completedHead unitTests E u=u := coreToDualIsometry.injective
    ((coreToDual_head E u).trans hx)
  rw [← map_add,coreToDual_norm] at hp
  rw [← map_sub,coreToDual_norm] at hm
  rw [← coreToDual_tail,coreToDual_norm,coreToDual_norm]
  exact incomparable_tail_core hE u v hu hp hm

end BoundedTreePotentials.Segments

namespace BoundedTreePotentials
section FiniteHeadsFurther
variable {I : Type*} (K : TestFamily I) (E : Finset I)

lemma completedHead_idem (x : TestCompletion K) :
    completedHead K E (completedHead K E x)=completedHead K E x := by
  nth_rw 1 [completedHead_apply]
  simp only [coordinate_completedHead]
  rw [completedHead_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left hi]

lemma completedHead_ker : (completedHead K E).ker=coordinateTail K E := by
  ext x
  change completedHead K E x=0 ↔ _
  rw [mem_coordinateTail]
  constructor
  · intro hx i hi
    have he := congrArg (coordinateFunctional K i) hx
    simpa only [coordinate_completedHead,ite_eq_left hi,map_zero] using he
  · intro hx
    rw [completedHead_apply]
    exact Finset.sum_eq_zero (fun i hi => by rw [hx i hi,zero_smul])

instance completedHead_finiteRank : Module.Finite ℝ (completedHead K E).range := by
  have h : Module.Finite ℝ (TestCompletion K ⧸ (completedHead K E).ker) := by
    rw [completedHead_ker]
    infer_instance
  let := h
  exact Module.Finite.equiv (completedHead K E).toLinearMap.quotKerEquivRange

lemma completedTail_idem (x : TestCompletion K) :
    completedTail K E (completedTail K E x)=completedTail K E x := by
  simp only [completedTail_apply,map_sub,completedHead_idem,sub_self,sub_zero]

lemma completedHead_tail (x : TestCompletion K) : completedHead K E (completedTail K E x)=0 := by
  simp only [completedTail_apply,map_sub,completedHead_idem,sub_self]

end FiniteHeadsFurther
end BoundedTreePotentials

end

end OAI
