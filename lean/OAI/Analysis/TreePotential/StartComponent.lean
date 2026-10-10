import OAI.Analysis.TreePotential.StartModulus

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
section DualTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dualTransport (e : E ≃L[ℝ] F) : StrongDual ℝ E ≃L[ℝ] StrongDual ℝ F :=
  e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

lemma dualTransport_apply (e : E ≃L[ℝ] F) (f : StrongDual ℝ E) (x : F) :
    dualTransport e f x=f (e.symm x) := rfl

lemma dualTransport_bound (e : E ≃L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : F,‖e.symm x‖ ≤ C*‖x‖) (f : StrongDual ℝ E) :
    ‖dualTransport e f‖ ≤ C*‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg f))
  intro x
  change ‖f (e.symm x)‖ ≤ _
  calc
    _  ≤  ‖f‖*‖e.symm x‖ := f.le_opNorm _
    _  ≤  ‖f‖*(C*‖x‖) := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg f)
    _ = _ := by ring

lemma dualTransportIsometry_norm (e : E ≃ₗᵢ[ℝ] F) (f : StrongDual ℝ E) :
    ‖dualTransport e.toContinuousLinearEquiv f‖=‖f‖ := by
  have h1 := dualTransport_bound e.toContinuousLinearEquiv zero_le_one
    (fun x => by change ‖e.symm x‖ ≤ 1*‖x‖; rw [e.symm.norm_map,one_mul]) f
  have h2 := dualTransport_bound e.symm.toContinuousLinearEquiv zero_le_one
    (fun x => by change ‖e x‖ ≤ 1*‖x‖; rw [e.norm_map,one_mul])
    (dualTransport e.toContinuousLinearEquiv f)
  have he : dualTransport e.symm.toContinuousLinearEquiv (dualTransport e.toContinuousLinearEquiv f)=f := by
    ext x
    change f (e.symm (e x))=f x
    rw [e.symm_apply_apply]
  rw [he,one_mul] at h2
  rw [one_mul] at h1
  exact le_antisymm h1 h2

def dualTransportIsometry (e : E ≃ₗᵢ[ℝ] F) : StrongDual ℝ E ≃ₗᵢ[ℝ] StrongDual ℝ F :=
  { (dualTransport e.toContinuousLinearEquiv).toLinearEquiv with norm_map' := dualTransportIsometry_norm e }

end DualTransport

lemma l2DualEquiv_symm_apply {I : Type*} [DecidableEq I] (E : I → Type*)
    [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)]
    (φ : StrongDual ℝ (HilbertSum E)) : (l2DualEquiv E).symm φ=dualPieces E φ := by
  apply (l2DualEquiv E).injective
  rw [(l2DualEquiv E).apply_symm_apply]
  exact (l2Dual_dualPieces E φ).symm

lemma completedHilbertMap_upper {I : Type*} (K : TestFamily I) (C : ℝ)
    (hlower : ∀ g, ‖finiteHilbert g‖ ≤ C*testNorm K g) (x : TestCompletion K) :
    ‖completedHilbertMap K C hlower x‖ ≤ C*‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le ((completedHilbertMap K C hlower).continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro g
  rw [completedHilbertMap_coe,UniformSpace.Completion.norm_coe]
  exact hlower ((testVectorEquiv K) g)
end BoundedTreePotentials

namespace BoundedTreePotentials.Segments
open scoped Classical

abbrev StartBlock (n : ℕ) := StrongDual ℝ (PredualBlock n)

def startPiecesEquiv : StartSpace ≃ₗᵢ[ℝ] HilbertSum StartBlock :=
  startCoreIsometry.trans (coreDualEquiv.trans
    ((dualTransportIsometry predualComponentEquiv).trans (l2DualEquiv PredualBlock).symm))

lemma predualComponentEquiv_finite (n : ℕ) (g : BlockNode n →₀ ℝ) :
    predualComponentEquiv (finiteLift atomTests (Finsupp.embDomain (componentEmbedding n) g))=
      lp.single 2 n (finiteLift (blockTests n) g) := by
  change completedComponents (finiteLift atomTests (Finsupp.embDomain (componentEmbedding n) g))=_
  rw [completedComponents_lift,finiteComponents_emb]

lemma predualComponentEquiv_coordinate (n : ℕ) (v : BlockNode n) :
    predualComponentEquiv (coordinateVector atomTests (componentEmbedding n v))=
      lp.single 2 n (coordinateVector (blockTests n) v) := by
  have hh := predualComponentEquiv_finite n (Finsupp.single v 1)
  rw [Finsupp.embDomain_single] at hh
  convert hh using 1 <;> rfl

def startBlockCoordinate (n : ℕ) (x : StartBlock n) (v : BlockNode n) : ℝ :=
  x (coordinateVector (blockTests n) v)

lemma startPiecesEquiv_apply (x : StartSpace) :
    startPiecesEquiv x=dualPieces PredualBlock
      (dualTransport predualComponentEquiv.toContinuousLinearEquiv (coreToDual (startCoreEquiv x))) :=
  l2DualEquiv_symm_apply PredualBlock _

lemma startPieces_coordinate (x : StartSpace) (n : ℕ) (v : BlockNode n) :
    startBlockCoordinate n (startPiecesEquiv x n) v=x.val (componentEmbedding n v) := by
  have hh := congrArg (fun z : HilbertSum StartBlock => startBlockCoordinate n (z n) v)
    (startPiecesEquiv_apply x)
  apply hh.trans
  change coreToDual (startCoreEquiv x)
    (predualComponentEquiv.symm (lp.single 2 n (coordinateVector (blockTests n) v)))=_
  rw [← predualComponentEquiv_coordinate,predualComponentEquiv.symm_apply_apply]
  rw [coreToDual_coordinate_apply,startCore_coordinate]

def startBlockInclusion (n : ℕ) : StartBlock n →L[ℝ] StartSpace :=
  startPiecesEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℝ StartBlock 2 n)

lemma startPieces_inclusion (n : ℕ) (x : StartBlock n) :
    startPiecesEquiv (startBlockInclusion n x)=lp.single 2 n x := by
  exact startPiecesEquiv.apply_symm_apply _

lemma startBlockInclusion_norm (n : ℕ) (x : StartBlock n) : ‖startBlockInclusion n x‖=‖x‖ := by
  change ‖startPiecesEquiv.symm (lp.single 2 n x)‖=‖x‖
  rw [startPiecesEquiv.symm.norm_map,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]

lemma startBlockInclusion_coordinate (n : ℕ) (x : StartBlock n) (v : BlockNode n) :
    (startBlockInclusion n x).val (componentEmbedding n v)=startBlockCoordinate n x v := by
  rw [← startPieces_coordinate,startPieces_inclusion,lp.single_apply_self]

lemma startBlockInclusion_outside (n : ℕ) (x : StartBlock n) (v : Node) (hv : v.1 ≠ n) :
    (startBlockInclusion n x).val v=0 := by
  obtain ⟨k,v⟩ := v
  change (startBlockInclusion n x).val (componentEmbedding k v)=0
  rw [← startPieces_coordinate,startPieces_inclusion,lp.single_apply_ne 2 n x hv]
  rfl

lemma startBlock_reflexive (n : ℕ) : IsReflexive (StartBlock n) := dual_reflexive (predualBlock_reflexive n)

theorem start_outer_reflexive : IsReflexive (HilbertSum StartBlock) :=
  hilbertSum_reflexive StartBlock startBlock_reflexive

def startBlockHilbertEquiv (n : ℕ) : StartBlock n ≃L[ℝ] CoordinateHilbert (BlockNode n) :=
  (dualTransport (predualBlockHilbertEquiv n)).trans
    (InnerProductSpace.toDual ℝ (CoordinateHilbert (BlockNode n))).symm.toContinuousLinearEquiv

lemma predualBlockHilbertEquiv_coordinate (n : ℕ) (v : BlockNode n) :
    predualBlockHilbertEquiv n (coordinateVector (blockTests n) v)=lp.single 2 v (1:ℝ) := by
  change completedHilbertMap _ _ _ (((testVectorEquiv (blockTests n)).symm
    (Finsupp.single v 1) : TestVector (blockTests n)) : PredualBlock n)=_
  rw [completedHilbertMap_coe]
  simp only [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext w
  change Finsupp.single v (1:ℝ) w=(lp.single (E := fun _ : BlockNode n => ℝ) 2 v (1:ℝ)) w
  rw [lp.single_apply]
  simp [Finsupp.single_apply,Pi.single_apply,eq_comm]

lemma startBlockHilbertEquiv_coordinate (n : ℕ) (x : StartBlock n) (v : BlockNode n) :
    startBlockHilbertEquiv n x v=startBlockCoordinate n x v := by
  have hh := @InnerProductSpace.toDual_symm_apply ℝ (CoordinateHilbert (BlockNode n)) _ _ _ _
    (lp.single 2 v (1:ℝ)) (dualTransport (predualBlockHilbertEquiv n) x)
  rw [lp.inner_single_right] at hh
  simp only [RCLike.inner_apply,RCLike.conj_to_real,one_mul] at hh
  change (startBlockHilbertEquiv n x) v=x ((predualBlockHilbertEquiv n).symm (lp.single 2 v 1)) at hh
  rw [← predualBlockHilbertEquiv_coordinate,(predualBlockHilbertEquiv n).symm_apply_apply] at hh
  exact hh

lemma predualBlockHilbert_bounds (n : ℕ) (x : PredualBlock n) :
    ‖predualBlockHilbertEquiv n x‖ ≤ Real.sqrt (n+2)*‖x‖ ∧
      ‖x‖ ≤ Real.sqrt (n+2)*‖predualBlockHilbertEquiv n x‖ := by
  constructor
  · exact completedHilbertMap_upper (blockTests n) (Real.sqrt (n+2))
      (fun g => (block_hilbert_comparisons n g).1) x
  · exact completedHilbertMap_lower (blockTests n) (Real.sqrt (n+2))
      (fun g => (block_hilbert_comparisons n g).1)
      (fun g => (block_hilbert_comparisons n g).2) x

lemma startBlockHilbert_bounds (n : ℕ) (x : StartBlock n) :
    ‖startBlockHilbertEquiv n x‖ ≤ Real.sqrt (n+2)*‖x‖ ∧
      ‖x‖ ≤ Real.sqrt (n+2)*‖startBlockHilbertEquiv n x‖ := by
  have hb : ∀ y,‖(predualBlockHilbertEquiv n).symm y‖ ≤ Real.sqrt (n+2)*‖y‖ := by
    intro y
    simpa only [(predualBlockHilbertEquiv n).apply_symm_apply] using
      (predualBlockHilbert_bounds n ((predualBlockHilbertEquiv n).symm y)).2
  have h1 := dualTransport_bound (predualBlockHilbertEquiv n) (Real.sqrt_nonneg _) hb x
  have hnorm : ‖startBlockHilbertEquiv n x‖=‖dualTransport (predualBlockHilbertEquiv n) x‖ :=
    (InnerProductSpace.toDual ℝ (CoordinateHilbert (BlockNode n))).symm.norm_map _
  have h2 := dualTransport_bound (predualBlockHilbertEquiv n).symm (Real.sqrt_nonneg _)
    (fun y => (predualBlockHilbert_bounds n y).1) (dualTransport (predualBlockHilbertEquiv n) x)
  have he : dualTransport (predualBlockHilbertEquiv n).symm (dualTransport (predualBlockHilbertEquiv n) x)=x := by
    ext y
    change x ((predualBlockHilbertEquiv n).symm (predualBlockHilbertEquiv n y))=x y
    rw [(predualBlockHilbertEquiv n).symm_apply_apply]
  rw [he] at h2
  rw [hnorm]
  exact ⟨h1,h2⟩

/-- Finite-height comparisons on the actual component, whose coordinate norm equals the literal component infimum. -/

theorem startBlock_norm_comparisons (n : ℕ) (x : StartBlock n) :
    ‖startBlockHilbertEquiv n x‖/(n+2) ≤ ‖x‖ ∧
      ‖x‖ ≤ Real.sqrt (n+2)*‖startBlockHilbertEquiv n x‖ := by
  have hn : (0:ℝ)< n+2 := by positivity
  have hs : Real.sqrt (n+2) ≤ (n+2:ℝ) := by
    have hh := Real.sq_sqrt hn.le
    have hn1 : (1:ℝ) ≤ n+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [Real.sqrt_nonneg (n+2:ℝ)]
  constructor
  · apply (div_le_iff₀ hn).mpr
    calc
      _  ≤  Real.sqrt (n+2)*‖x‖ := (startBlockHilbert_bounds n x).1
      _  ≤  (n+2)*‖x‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg x)
      _ = _ := by ring
  · exact (startBlockHilbert_bounds n x).2

/-- Arrays on one labelled component, extended by zero to all other segments.
This is exactly an array indexed by t≼v in that component. -/
def IsComponentArray (n : ℕ) (a : Segment → ℝ) : Prop := ∀ S,S.start.1 ≠ n → a S=0

def componentArray (n : ℕ) (a : Segment → ℝ) (S : Segment) : ℝ :=
  if S.start.1=n then a S else 0

lemma componentArray_supported (n : ℕ) (a : Segment → ℝ) : IsComponentArray n (componentArray n a) := by
  intro S hS
  simp only [componentArray,ite_eq_right hS]

lemma componentArray_eq_self (n : ℕ) (a : Segment → ℝ) (ha : IsComponentArray n a) :
    componentArray n a=a := by
  ext S
  by_cases hS : S.start.1=n
  · simp [componentArray,hS]
  · simp [componentArray,hS,ha S hS]

lemma componentArray_start (n k : ℕ) (a : Segment → ℝ) (s : List ℕ) :
    startArray (fun S => ENNReal.ofReal |componentArray n a S|) k s=
      if k=n then startArray (fun S => ENNReal.ofReal |a S|) k s else 0 := by
  by_cases hk : k=n
  · subst k
    rw [ite_eq_left rfl]
    apply tsum_congr
    intro S
    by_cases hh : n=S.start.1 ∧ s=S.start.2.val
    · simp only [ite_eq_left hh,componentArray,ite_eq_left hh.1.symm]
    · simp only [ite_eq_right hh]
  · rw [ite_eq_right hk]
    apply ENNReal.tsum_eq_zero.mpr
    intro S
    by_cases hh : k=S.start.1 ∧ s=S.start.2.val
    · have hS : S.start.1 ≠ n := by simpa only [← hh.1] using hk
      simp only [ite_eq_left hh,componentArray,ite_eq_right hS,abs_zero,ENNReal.ofReal_zero]
    · simp only [ite_eq_right hh]

lemma eTwo_single {I : Type*} [DecidableEq I] (i : I) (a : ℝ≥0∞) :
    eTwo (fun j => if j=i then a else 0)=a := by
  unfold eTwo
  rw [tsum_eq_single i (fun j hj => by simp [hj])]
  simp only []
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

/-- Literal cost M_{n+1} of the start masses on the component of height n+1. -/
def componentRepresentationCost (n : ℕ) (a : Segment → ℝ) : ℝ≥0∞ :=
  startCost (n+1) (startArray (fun S => ENNReal.ofReal |a S|) n)

lemma representationCost_componentArray (n : ℕ) (a : Segment → ℝ) :
    representationCost (componentArray n a)=componentRepresentationCost n a := by
  unfold representationCost forestCost
  have he : (fun k => startCost (k+1) (startArray (fun S => ENNReal.ofReal |componentArray n a S|) k))=
      fun k => if k=n then componentRepresentationCost n a else 0 := by
    funext k
    by_cases hk : k=n
    · subst k
      have hh : startArray (fun S => ENNReal.ofReal |componentArray n a S|) n=
          startArray (fun S => ENNReal.ofReal |a S|) n := by
        funext s
        rw [componentArray_start,ite_eq_left rfl]
      rw [hh,ite_eq_left rfl]
      rfl
    · have hh : startArray (fun S => ENNReal.ofReal |componentArray n a S|) k=0 := by
        funext s
        rw [componentArray_start,ite_eq_right hk]
        rfl
      rw [hh,startCost_zero,ite_eq_right hk]
  rw [he]
  exact eTwo_single n _

lemma representationCost_component_le (n : ℕ) (a : Segment → ℝ) :
    representationCost (componentArray n a) ≤ representationCost a := by
  apply forestCost_mono
  apply startArray_mono
  intro S
  by_cases hS : S.start.1=n
  · simp only [componentArray,ite_eq_left hS,le_refl]
  · simp only [componentArray,ite_eq_right hS,abs_zero,ENNReal.ofReal_zero,zero_le]

lemma componentCost_eq_forest (n : ℕ) (a : Segment → ℝ) (ha : IsComponentArray n a) :
    componentRepresentationCost n a=representationCost a := by
  rw [← representationCost_componentArray,componentArray_eq_self n a ha]

lemma representationOutput_component (n : ℕ) (a : Segment → ℝ) (v : Node) :
    representationOutput (componentArray n a) v=if v.1=n then representationOutput a v else 0 := by
  by_cases hv : v.1=n
  · rw [ite_eq_left hv]
    apply tsum_congr
    intro S
    by_cases hS : v ∈ S.nodes
    · have hh : S.start.1=n := ((S.mem_nodes v).mp hS).1.1.trans hv
      simp [hS,componentArray,hh]
    · simp [hS]
  · rw [ite_eq_right hv]
    have he : (fun S : Segment => if v ∈ S.nodes then componentArray n a S else 0)=0 := by
      funext S
      by_cases hS : v ∈ S.nodes
      · have hh : S.start.1 ≠ n := by simpa only [((S.mem_nodes v).mp hS).1.1] using hv
        simp only [ite_eq_left hS,componentArray,ite_eq_right hh,Pi.zero_apply]
      · simp only [ite_eq_right hS,Pi.zero_apply]
    change (∑' S : Segment,if v ∈ S.nodes then componentArray n a S else 0)=0
    rw [he]
    exact tsum_zero

lemma representationOutput_outside (n : ℕ) (a : Segment → ℝ) (ha : IsComponentArray n a)
    (v : Node) (hv : v.1 ≠ n) : representationOutput a v=0 := by
  rw [← componentArray_eq_self n a ha,representationOutput_component,ite_eq_right hv]

def representedStart (a : Segment → ℝ) (ha : representationCost a ≠ ∞) : StartSpace :=
  startCoreIsometry.symm (representedCore a ha)

lemma representedStart_coordinate (a : Segment → ℝ) (ha : representationCost a ≠ ∞) (v : Node) :
    (representedStart a ha).val v=representationOutput a v := by
  rw [← startCore_coordinate]
  change coordinateFunctional unitTests v (startCoreIsometry (startCoreIsometry.symm _))=_
  rw [startCoreIsometry.apply_symm_apply,representedCore_coordinate]

lemma representedStart_norm (a : Segment → ℝ) (ha : representationCost a ≠ ∞) :
    ‖representedStart a ha‖ ≤ (representationCost a).toReal := by
  rw [representedStart,startCoreIsometry.symm.norm_map]
  exact representedCore_norm a ha

lemma supported_representation_eq_block (n : ℕ) (x : StartBlock n) (a : Segment → ℝ)
    (hc : IsComponentArray n a) (ha : representationCost a ≠ ∞)
    (hx : ∀ v : BlockNode n,representationOutput a (componentEmbedding n v)=startBlockCoordinate n x v) :
    representedStart a ha=startBlockInclusion n x := by
  apply Subtype.ext
  funext v
  rw [representedStart_coordinate]
  obtain ⟨k,v⟩ := v
  by_cases hk : k=n
  · subst k
    change representationOutput a (componentEmbedding n v)=
      (startBlockInclusion n x).val (componentEmbedding n v)
    rw [hx,startBlockInclusion_coordinate]
  · rw [representationOutput_outside n a hc _ hk,startBlockInclusion_outside n x _ hk]

/-- The infimum over precisely all countable segment representations on the
specified component. The original recursive M_{n+1}, not a replacement, is
used in the set of costs. -/
def literalBlockStartNorm (n : ℕ) (z : BlockNode n → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ a : Segment → ℝ,IsComponentArray n a ∧ componentRepresentationCost n a ≠ ∞ ∧
    (∀ v : BlockNode n,representationOutput a (componentEmbedding n v)=z v) ∧
    (componentRepresentationCost n a).toReal=c}

lemma exists_component_representation (n : ℕ) (x : StartBlock n) {ε : ℝ} (hε : 0<ε) :
    ∃ a : Segment → ℝ,IsComponentArray n a ∧ componentRepresentationCost n a ≠ ∞ ∧
      (∀ v : BlockNode n,representationOutput a (componentEmbedding n v)=startBlockCoordinate n x v) ∧
      (componentRepresentationCost n a).toReal<‖x‖+ε := by
  obtain ⟨a,ha,hout,hcost⟩ := exists_representation_near_norm
    (startCoreEquiv (startBlockInclusion n x)) hε
  let b := componentArray n a
  have hbc : representationCost b ≤ representationCost a := representationCost_component_le n a
  have hbfin : representationCost b ≠ ∞ := ne_top_of_le_ne_top ha hbc
  have hb : IsComponentArray n b := componentArray_supported n a
  refine ⟨b,hb,?_,?_,?_⟩
  · rw [componentCost_eq_forest n b hb]
    exact hbfin
  · intro v
    rw [representationOutput_component,ite_eq_left (show (componentEmbedding n v).1=n from rfl),← representedCore_coordinate a ha,hout,
      startCore_coordinate,startBlockInclusion_coordinate]
  · rw [componentCost_eq_forest n b hb]
    have hh := ENNReal.toReal_mono ha hbc
    have hxnorm : ‖startCoreEquiv (startBlockInclusion n x)‖=‖x‖ := startBlockInclusion_norm n x
    rw [hxnorm] at hcost
    exact hh.trans_lt hcost

theorem startBlock_norm_eq_infimum (n : ℕ) (x : StartBlock n) :
    ‖x‖=literalBlockStartNorm n (startBlockCoordinate n x) := by
  let C : Set ℝ := {c | ∃ a : Segment → ℝ,IsComponentArray n a ∧ componentRepresentationCost n a ≠ ∞ ∧
    (∀ v : BlockNode n,representationOutput a (componentEmbedding n v)=startBlockCoordinate n x v) ∧
    (componentRepresentationCost n a).toReal=c}
  have hne : C.Nonempty := by
    obtain ⟨a,hc,ha,hx,hcost⟩ := exists_component_representation n x (by norm_num : (0:ℝ)<1)
    exact ⟨_,a,hc,ha,hx,rfl⟩
  have hbdd : BddBelow C := ⟨0,by rintro c ⟨a,hc,ha,hx,rfl⟩; exact ENNReal.toReal_nonneg⟩
  change ‖x‖=sInf C
  apply le_antisymm
  · apply le_csInf hne
    rintro c ⟨a,hc,ha,hx,rfl⟩
    rw [componentCost_eq_forest n a hc] at ha ⊢
    have he := supported_representation_eq_block n x a hc ha hx
    rw [← startBlockInclusion_norm n x,← he]
    exact representedStart_norm a ha
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a,hc,ha,hx,hcost⟩ := exists_component_representation n x hε
    exact (csInf_le hbdd ⟨a,hc,ha,hx,rfl⟩).trans hcost.le

/-- A finite-height component is the full Hilbert coordinate set with the literal infimal norm. -/

theorem hilbert_coordinates_literal_norm (n : ℕ) (z : CoordinateHilbert (BlockNode n)) :
    ‖(startBlockHilbertEquiv n).symm z‖=literalBlockStartNorm n z := by
  rw [startBlock_norm_eq_infimum]
  congr 1
  ext v
  rw [← startBlockHilbertEquiv_coordinate,(startBlockHilbertEquiv n).apply_symm_apply]

/-- Finite-height norm comparisons, with height n+1 and the root present. -/
theorem literalBlockStartNorm_comparisons (n : ℕ) (z : CoordinateHilbert (BlockNode n)) :
    ‖z‖/(n+2) ≤ literalBlockStartNorm n z ∧ literalBlockStartNorm n z ≤ Real.sqrt (n+2)*‖z‖ := by
  have hh := startBlock_norm_comparisons n ((startBlockHilbertEquiv n).symm z)
  rwa [(startBlockHilbertEquiv n).apply_symm_apply,hilbert_coordinates_literal_norm] at hh

end BoundedTreePotentials.Segments

end

end OAI
