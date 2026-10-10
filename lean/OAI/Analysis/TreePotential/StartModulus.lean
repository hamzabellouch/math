import OAI.Analysis.TreePotential.StartQuotient

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical



namespace BoundedTreePotentials.Segments

def startHead (E : Finset Node) : StartSpace →L[ℝ] StartSpace :=
  startCoreIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((completedHead unitTests E).comp startCoreIsometry.toContinuousLinearEquiv.toContinuousLinearMap)

def startTail (E : Finset Node) : StartSpace →L[ℝ] StartSpace := ContinuousLinearMap.id ℝ StartSpace-startHead E

lemma startCore_head (E : Finset Node) (x : StartSpace) :
    startCoreEquiv (startHead E x)=completedHead unitTests E (startCoreEquiv x) := by
  exact startCoreEquiv.apply_symm_apply _

lemma startCore_tail (E : Finset Node) (x : StartSpace) :
    startCoreEquiv (startTail E x)=completedTail unitTests E (startCoreEquiv x) := by
  change startCoreEquiv (x-startHead E x)=_
  rw [map_sub,startCore_head,completedTail_apply]

lemma startHead_coordinate (E : Finset Node) (x : StartSpace) (v : Node) :
    (startHead E x).val v=if v ∈ E then x.val v else 0 := by
  rw [← startCore_coordinate,startCore_head,completedHead_apply]
  simp only [map_sum,map_smul,smul_eq_mul,coordinateFunctional_vector,mul_ite,mul_one,mul_zero]
  simp [startCore_coordinate]

lemma startHead_norm {E : Finset Node} (hE : Initial (E : Set Node)) (x : StartSpace) :
    ‖startHead E x‖≤‖x‖ := by
  change ‖startCoreEquiv (startHead E x)‖≤‖startCoreEquiv x‖
  rw [startCore_head]
  exact core_head_norm E hE _

lemma startTail_norm {E : Finset Node} (hE : Initial (E : Set Node)) (x : StartSpace) :
    ‖startTail E x‖≤2*‖x‖ := by
  change ‖startCoreEquiv (startTail E x)‖≤2*‖startCoreEquiv x‖
  rw [startCore_tail]
  exact (core_tail_norm E hE _).trans (by nlinarith [norm_nonneg (startCoreEquiv x)])

lemma start_coordinate_bound (x : StartSpace) (v : Node) : |x.val v|≤‖x‖ := by
  rw [← startCore_coordinate]
  exact completedTestFunctional_abs_le unitTests ⟨_,unitTests.singleton_mem v⟩ (startCoreEquiv x)

lemma sqrt_segment_constant_le_eight : Real.sqrt 2+Real.sqrt 6≤8 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h6 := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have hh2 : Real.sqrt (2:ℝ)≤2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hh6 : Real.sqrt (6:ℝ)≤3 := by nlinarith [Real.sqrt_nonneg (6:ℝ)]
  linarith

/-- The segment-start squared tail bound with constant 64 and both literal coordinate support hypotheses, using equality of representation norms. -/


theorem segment_start_tail {E : Finset Node} (hE : Initial (E : Set Node))
    (p y : StartSpace) (hp : ∀ v,v ∉ E → p.val v=0) (hy : ∀ v ∈ E,y.val v=0) :
    ‖p‖^2+‖y‖^2/64≤(max ‖p+y‖ ‖p-y‖)^2 := by
  have hphead : startHead E p=p := by
    apply Subtype.ext
    funext v
    rw [startHead_coordinate]
    by_cases hv : v ∈ E
    · simp [hv]
    · simp [hv,hp v hv]
  have hyhead : startHead E y=0 := by
    apply Subtype.ext
    funext v
    change (startHead E y).val v=0
    rw [startHead_coordinate]
    by_cases hv : v ∈ E
    · simp [hv,hy v hv]
    · simp [hv]
  let P := startCoreEquiv p
  let Y := startCoreEquiv y
  let R := max ‖p+y‖ ‖p-y‖
  have hP : completedHead unitTests E P=P := by
    rw [← startCore_head,hphead]
  have hY : completedTail unitTests E Y=Y := by
    rw [completedTail_apply,← startCore_head,hyhead,map_zero,sub_zero]
  have hplus : ‖P+Y‖≤ R := by
    change ‖startCoreEquiv p+startCoreEquiv y‖≤_
    rw [← map_add]
    exact le_max_left _ _
  have hminus : ‖P-Y‖≤ R := by
    change ‖startCoreEquiv p-startCoreEquiv y‖≤_
    rw [← map_sub]
    exact le_max_right _ _
  have hg := incomparable_squared_core hE P Y hP hplus hminus
  rw [hY] at hg
  have hpn : ‖P‖≤ R := by linarith [norm_center_le_avg P Y]
  have hRn : 0≤ R := (norm_nonneg P).trans hpn
  have hpos : 0≤ R*(R-‖P‖) := mul_nonneg hRn (sub_nonneg.mpr hpn)
  have hK : (Real.sqrt 2+Real.sqrt 6)^2≤64 := by
    nlinarith [sqrt_segment_constant_le_eight,Real.sqrt_nonneg (2:ℝ),Real.sqrt_nonneg (6:ℝ)]
  have hh := mul_le_mul_of_nonneg_right hK hpos
  have hcross : R*(R-‖P‖)≤ R^2-‖P‖^2 := by
    nlinarith [mul_nonneg (norm_nonneg P) (sub_nonneg.mpr hpn)]
  change ‖P‖^2+‖Y‖^2/64≤ R^2
  nlinarith

end BoundedTreePotentials.Segments

namespace BoundedTreePotentials

lemma maximumModulus_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t b : ℝ}
    (h : ∀ x : E, ‖x‖=1 → ∀ ε : ℝ, 0<ε → ∃ F : ClosedFiniteCodim E,
      ∀ y : E, y ∈ F.space → 1 ≤ ‖y‖ → b-ε ≤ max ‖x+t • y‖ ‖x-t • y‖-1) :
    (b : EReal) ≤ maximumModulus E t := by
  apply le_iInf
  intro x
  apply ereal_le_of_forall_pos_sub_le
  intro ε hε
  obtain ⟨F,hF⟩ := h x.val x.property ε hε
  apply le_iSup_of_le F
  apply le_iInf
  intro y
  exact EReal.coe_le_coe_iff.mpr (hF y.val y.property.1 y.property.2)

lemma maximum_center_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x p y : E) (t : ℝ) :
    max ‖p+t • y‖ ‖p-t • y‖ ≤ max ‖x+t • y‖ ‖x-t • y‖+‖x-p‖ := by
  have h1 := norm_sub_norm_le (p+t • y) (x+t • y)
  have h2 := norm_sub_norm_le (p-t • y) (x-t • y)
  have he1 : (p+t • y)-(x+t • y)=p-x := by abel
  have he2 : (p-t • y)-(x-t • y)=p-x := by abel
  rw [he1,norm_sub_rev p x] at h1
  rw [he2,norm_sub_rev p x] at h2
  apply max_le <;> linarith [le_max_left ‖x+t • y‖ ‖x-t • y‖,
    le_max_right ‖x+t • y‖ ‖x-t • y‖]

end BoundedTreePotentials

namespace BoundedTreePotentials.Segments
open scoped Classical

abbrev startCoordinate (v : Node) : StartSpace →L[ℝ] ℝ :=
  (coordinateFunctional unitTests v).comp startCoreIsometry.toContinuousLinearEquiv.toContinuousLinearMap

lemma startCoordinate_apply (v : Node) (x : StartSpace) : startCoordinate v x=x.val v :=
  startCore_coordinate x v

def startFiniteCoordinates (E : Finset Node) : StartSpace →L[ℝ] (E → ℝ) :=
  ContinuousLinearMap.pi (fun v => startCoordinate v.val)

def startCoordinateTail (E : Finset Node) : ClosedFiniteCodim StartSpace :=
  ⟨(startFiniteCoordinates E).ker,(startFiniteCoordinates E).isClosed_ker,
    Module.Finite.equiv (startFiniteCoordinates E).toLinearMap.quotKerEquivRange.symm⟩

lemma mem_startCoordinateTail (E : Finset Node) (x : StartSpace) :
    x ∈ (startCoordinateTail E).space ↔ ∀ v ∈ E,x.val v=0 := by
  change startFiniteCoordinates E x=0 ↔ _
  simp only [startFiniteCoordinates,ContinuousLinearMap.pi_apply,startCoordinate_apply,
    funext_iff,Pi.zero_apply,Subtype.forall]

lemma start_head_approx (x : StartSpace) {ε : ℝ} (hε : 0<ε) :
    ∃ E : Finset Node, Initial (E : Set Node) ∧ ‖x-startHead E x‖<ε := by
  obtain ⟨E,hE,hεE⟩ := core_head_approx (startCoreEquiv x) hε
  refine ⟨E,hE,?_⟩
  change ‖startCoreEquiv (x-startHead E x)‖<ε
  rw [map_sub,startCore_head]
  exact hεE

/-- The finite-codimensional conclusion for the maximum (not averaged)
modulus, at every positive radius. -/
theorem start_completed_tail_bound (x : StartSpace) (hx : ‖x‖=1)
    {t ε : ℝ} (ht : 0< t) (hε : 0<ε) :
    ∃ F : ClosedFiniteCodim StartSpace, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/64)-1-ε ≤ max ‖x+t • y‖ ‖x-t • y‖-1 := by
  obtain ⟨E,hE,happrox⟩ := start_head_approx x (show 0<ε/2 by positivity)
  let p := startHead E x
  refine ⟨startCoordinateTail E,?_⟩
  intro y hy hyn
  have hys := (mem_startCoordinateTail E y).mp hy
  have hp : ∀ v,v ∉ E → p.val v=0 := by
    intro v hv
    simp [p,startHead_coordinate,hv]
  have hty : ∀ v ∈ E,(t • y).val v=0 := by
    intro v hv
    change t*y.val v=0
    rw [hys v hv,mul_zero]
  have he := segment_start_tail hE p (t • y) hp hty
  rw [norm_smul,Real.norm_of_nonneg ht.le] at he
  have hmax : 0 ≤ max ‖p+t • y‖ ‖p-t • y‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hsq : Real.sqrt (‖p‖^2+(t*‖y‖)^2/64) ≤ max ‖p+t • y‖ ‖p-t • y‖ := by
    apply (Real.sqrt_le_left hmax).mpr
    exact he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/64 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/64) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/64) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := maximum_center_perturbation x p y t
  change ‖x-p‖<ε/2 at happrox
  linarith

theorem start_maximum_modulus {t : ℝ} (ht : 0< t) :
    ((Real.sqrt (1+t^2/64)-1 : ℝ) : EReal) ≤ maximumModulus StartSpace t := by
  apply maximumModulus_lower_bound
  intro x hx ε hε
  exact start_completed_tail_bound x hx ht hε

def startBoundedPath (h : ℕ) (s : Tree h) : StartSpace := startCoreIsometry.symm (boundedPath h s)
def startCoordinateVector (v : Node) : StartSpace := startCoreIsometry.symm (coordinateVector unitTests v)

lemma startBoundedPath_norm (h : ℕ) (s : Tree h) : ‖startBoundedPath h s‖=1 := by
  rw [startBoundedPath,startCoreIsometry.symm.norm_map,boundedPath_norm]

lemma startCoordinateVector_apply (v w : Node) :
    (startCoordinateVector v).val w=if w=v then 1 else 0 := by
  rw [← startCore_coordinate]
  change coordinateFunctional unitTests w (startCoreIsometry (startCoreIsometry.symm _))=_
  rw [startCoreIsometry.apply_symm_apply,coordinateFunctional_vector]

lemma startCoordinateVector_norm (v : Node) : ‖startCoordinateVector v‖=1 := by
  rw [startCoordinateVector,startCoreIsometry.symm.norm_map,norm_coordinateVector]

lemma startBoundedPath_increment {h : ℕ} (s : Tree h) (hs : s.val.length< h) (j : ℕ) :
    startBoundedPath h (child s hs j)-startBoundedPath h s=
      startCoordinateVector (treeNode h (child s hs j)) := by
  unfold startBoundedPath startCoordinateVector
  rw [← map_sub,boundedPath_increment]

lemma start_children_weaklyNull {h : ℕ} (s : Tree h) (hs : s.val.length< h) :
    WeaklyNull (fun j => startCoordinateVector (treeNode h (child s hs j))) := by
  intro f
  exact core_children_weaklyNull s hs (f.comp startCoreIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem start_renorming_obstruction {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : StartSpace ≃L[ℝ] Y) {α β : ℝ} (hα : 0<α) (hαβ : α ≤ β)
    (he : ∀ x,α*‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β*‖x‖) :
    oneSidedModulus Y (α/(2*β))=0 := by
  apply incomparable_core_renorming_obstruction (startCoreIsometry.symm.toContinuousLinearEquiv.trans e) hα hαβ
  intro x
  simpa only [ContinuousLinearEquiv.trans_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    startCoreIsometry.symm.norm_map] using he (startCoreIsometry.symm x)

theorem start_no_equivalent_AUC {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : StartSpace ≃L[ℝ] Y) : ¬IsAUC Y := by
  obtain ⟨α,β,hα,hαβ,he⟩ := continuousEquiv_bounds e
  have hβ : 0<β := hα.trans_le hαβ
  intro hauc
  have hh := hauc (α/(2*β)) (by positivity)
  rw [start_renorming_obstruction e hα hαβ he] at hh
  exact lt_irrefl _ hh

end BoundedTreePotentials.Segments


end

end OAI
