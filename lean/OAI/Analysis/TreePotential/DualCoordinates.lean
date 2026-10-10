import OAI.Analysis.TreePotential.StartComponent

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
namespace ForestCoordinates
open scoped Classical
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]

/-- Countability is used on node coordinates, not just on the block index.
This also applies to each of the equivalent finite-height dual norms. -/
theorem hilbertSumTree_separable (e : ∀ n, E n ≃L[ℝ] TreeHilbert (n+1)) :
    TopologicalSpace.SeparableSpace (HilbertSum E) := by
  let v : ForestNode → HilbertSum E := fun s => lp.single 2 s.1 ((e s.1).symm (lp.single 2 s.2 (1:ℝ)))
  let S := Submodule.span ℝ (Set.range v)
  have hs (n : ℕ) (s : Tree (n+1)) (a : ℝ) :
      lp.single 2 n ((e n).symm (lp.single 2 s a)) ∈ S := by
    have hh : v ⟨n,s⟩ ∈ S := Submodule.subset_span ⟨⟨n,s⟩,rfl⟩
    have he : lp.single 2 n ((e n).symm (lp.single 2 s a)) = a • v ⟨n,s⟩ := by
      simp only [v,← lp.single_smul,← map_smul,smul_eq_mul,mul_one]
    rw [he]
    exact S.smul_mem a hh
  have hd : Dense (S : Set (HilbertSum E)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    intro x hx
    let U := S.topologicalClosure
    have hU : IsClosed (U : Set (HilbertSum E)) := S.isClosed_topologicalClosure
    have heach : ∀ n,lp.single 2 n (x n) ∈ U := by
      intro n
      let L : TreeHilbert (n+1) →L[ℝ] HilbertSum E :=
        (lp.singleContinuousLinearMap ℝ E 2 n).comp (e n).symm.toContinuousLinearMap
      have hh := L.hasSum (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (e n (x n)))
      have hh' : HasSum (fun s : Tree (n+1) => lp.single 2 n ((e n).symm (lp.single 2 s (e n (x n) s))))
          (lp.single 2 n (x n)) := by
        simpa only [L,ContinuousLinearMap.comp_apply,lp.singleContinuousLinearMap_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply] using hh
      apply hU.mem_of_tendsto hh'
      exact Filter.Eventually.of_forall (fun A => U.sum_mem fun s hA => S.le_topologicalClosure (hs n s _))
    apply hU.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x)
    exact Filter.Eventually.of_forall (fun A => U.sum_mem fun n hn => heach n)
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hsep := ((Set.countable_range v).isSeparable.span (R := ℝ)).closure
  change TopologicalSpace.IsSeparable (closure (S : Set (HilbertSum E))) at hsep
  rwa [hd.closure_eq] at hsep

end ForestCoordinates

/-- Hilbert coefficients of every finite-height linear-cost dual functional,
with its genuine continuous topology. Its norm is p_n, not the Hilbert norm. -/
def blockDualHilbertEquiv (n : ℕ) : StrongDual ℝ (LinearBlock n) ≃L[ℝ] TreeHilbert n :=
  (dualTransport (linearBlockHilbertEquiv n)).trans
    (InnerProductSpace.toDual ℝ (TreeHilbert n)).symm.toContinuousLinearEquiv

lemma blockDualHilbertEquiv_symm (n : ℕ) (f : TreeHilbert n) :
    (blockDualHilbertEquiv n).symm f=blockFunctional n f := by
  ext x
  change ((InnerProductSpace.toDual ℝ (TreeHilbert n)) f) (linearBlockHilbertEquiv n x)=_
  rfl

lemma blockDualHilbertEquiv_functional (n : ℕ) (φ : StrongDual ℝ (LinearBlock n)) :
    blockFunctional n (blockDualHilbertEquiv n φ)=φ := by
  rw [← blockDualHilbertEquiv_symm,(blockDualHilbertEquiv n).symm_apply_apply]

lemma blockDualHilbertEquiv_norm (n : ℕ) (φ : StrongDual ℝ (LinearBlock n)) :
    linearPolar n (blockDualHilbertEquiv n φ)=‖φ‖ := by
  rw [← blockFunctional_norm,blockDualHilbertEquiv_functional]

abbrev LinearDualPieces := HilbertSum (fun n : ℕ => StrongDual ℝ (LinearBlock (n+1)))

def linearDualCoefficients (φ : StrongDual ℝ LinearOuter) (n : ℕ) : TreeHilbert (n+1) :=
  blockDualHilbertEquiv (n+1) (dualPieces (fun n => LinearBlock (n+1)) φ n)

/-- The full linear-cost dual and its exact Hilbert pairing. -/
theorem linearOuterDual_pairing (φ : StrongDual ℝ LinearOuter) (x : LinearOuter) :
    φ x=∑' n,inner ℝ (linearDualCoefficients φ n) (linearBlockEquiv (n+1) (x n)) := by
  conv_lhs => rw [← l2Dual_dualPieces (fun n => LinearBlock (n+1)) φ]
  rw [l2Dual_apply]
  apply tsum_congr
  intro n
  rw [← blockFunctional_apply]
  exact (DFunLike.congr_fun (blockDualHilbertEquiv_functional (n+1) _) (x n)).symm

lemma dualPieces_norm_eq {I : Type*} [DecidableEq I] (E : I → Type*)
    [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)]
    (φ : StrongDual ℝ (HilbertSum E)) : ‖dualPieces E φ‖=‖φ‖ := by
  rw [← l2Dual_norm,l2Dual_dualPieces]

/-- The sum of p_n-squares, with no equivalence constants substituted. -/
theorem linearOuterDual_norm_sq (φ : StrongDual ℝ LinearOuter) :
    ‖φ‖^2=∑' n,(linearPolar (n+1) (linearDualCoefficients φ n))^2 := by
  have hh := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (dualPieces (fun n => LinearBlock (n+1)) φ)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,dualPieces_norm_eq] at hh
  rw [hh]
  apply tsum_congr
  intro n
  rw [linearDualCoefficients,blockDualHilbertEquiv_norm]

/-- Conversely every square-p_n-summable Hilbert coefficient family is a dual
functional. Thus the displayed coefficient description is onto. -/
theorem linearOuterDual_all_coefficients (f : (n : ℕ) → TreeHilbert (n+1))
    (hf : Summable (fun n => (linearPolar (n+1) (f n))^2)) :
    ∃ φ : StrongDual ℝ LinearOuter,linearDualCoefficients φ=f := by
  have hmem : Memℓp (fun n => blockFunctional (n+1) (f n)) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,blockFunctional_norm] using hf
  let F : LinearDualPieces := ⟨fun n => blockFunctional (n+1) (f n),hmem⟩
  refine ⟨l2Dual (fun n => LinearBlock (n+1)) F,?_⟩
  funext n
  unfold linearDualCoefficients
  rw [dualPieces_l2Dual]
  change blockDualHilbertEquiv (n+1) (blockFunctional (n+1) (f n))=f n
  rw [← blockDualHilbertEquiv_symm,(blockDualHilbertEquiv (n+1)).apply_symm_apply]

/-- Norm separability of the full continuous linear-cost dual. -/
theorem linearOuter_separable_dual : TopologicalSpace.SeparableSpace (StrongDual ℝ LinearOuter) := by
  let : TopologicalSpace.SeparableSpace LinearDualPieces :=
    ForestCoordinates.hilbertSumTree_separable (fun n => blockDualHilbertEquiv (n+1))
  exact (l2DualEquiv (fun n => LinearBlock (n+1))).surjective.denseRange.separableSpace
    (l2DualEquiv (fun n => LinearBlock (n+1))).continuous

end BoundedTreePotentials

namespace BoundedTreePotentials.Segments
open scoped Classical

/-- All component coordinates of a literal finite-cost forest vector belong
to the full finite-height Hilbert coordinate set. -/
theorem start_component_coordinates_mem (x : StartSpace) (n : ℕ) :
    Memℓp (fun v : BlockNode n => x.val (componentEmbedding n v)) 2 := by
  have he : (fun v : BlockNode n => x.val (componentEmbedding n v))=
      (fun v => startBlockHilbertEquiv n (startPiecesEquiv x n) v) := by
    funext v
    rw [startBlockHilbertEquiv_coordinate,startPieces_coordinate]
  rw [he]
  exact (startBlockHilbertEquiv n (startPiecesEquiv x n)).property

/-- Equality of the literal forest infimum with the outer Hilbert norm of
the literal finite-height infima, not merely equivalence of these norms. -/
theorem start_outer_norm_sq (x : StartSpace) :
    ‖x‖^2=∑' n,(literalBlockStartNorm n (fun v => x.val (componentEmbedding n v)))^2 := by
  have hh := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (startPiecesEquiv x)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,startPiecesEquiv.norm_map] at hh
  rw [hh]
  apply tsum_congr
  intro n
  rw [startBlock_norm_eq_infimum]
  congr 2
  funext v
  exact startPieces_coordinate x n v

/-- The range of countable finite-cost segment representations is exactly the outer ℓ₂ sum
of Hilbert coordinate sets equipped with their literal infimal component norms. -/



theorem start_coordinate_characterization (z : Node → ℝ) :
    (∃ x : StartSpace,x.val=z) ↔
      (∀ n,Memℓp (fun v : BlockNode n => z (componentEmbedding n v)) 2) ∧
      Summable (fun n => (literalBlockStartNorm n (fun v => z (componentEmbedding n v)))^2) := by
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨start_component_coordinates_mem x,?_⟩
    have hh := (lp.hasSum_norm (p := 2) (by norm_num) (startPiecesEquiv x)).summable
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
    have he : (fun n => ‖startPiecesEquiv x n‖^2)=
        (fun n => (literalBlockStartNorm n (fun v => x.val (componentEmbedding n v)))^2) := by
      funext n
      rw [startBlock_norm_eq_infimum]
      congr 2
      funext v
      exact startPieces_coordinate x n v
    rwa [he] at hh
  · rintro ⟨hz,hs⟩
    let b : (n : ℕ) → StartBlock n := fun n =>
      (startBlockHilbertEquiv n).symm ⟨fun v => z (componentEmbedding n v),hz n⟩
    have hb : ∀ n,‖b n‖=literalBlockStartNorm n (fun v => z (componentEmbedding n v)) := by
      intro n
      exact hilbert_coordinates_literal_norm n _
    have hmem : Memℓp b 2 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hb] using hs
    let B : HilbertSum StartBlock := ⟨b,hmem⟩
    refine ⟨startPiecesEquiv.symm B,?_⟩
    funext v
    obtain ⟨n,v⟩ := v
    change (startPiecesEquiv.symm B).val (componentEmbedding n v)=z (componentEmbedding n v)
    rw [← startPieces_coordinate,startPiecesEquiv.apply_symm_apply]
    change startBlockCoordinate n (b n) v=_
    rw [← startBlockHilbertEquiv_coordinate]
    exact congrFun (congrArg Subtype.val ((startBlockHilbertEquiv n).apply_symm_apply
      (⟨fun v => z (componentEmbedding n v),hz n⟩ : CoordinateHilbert (BlockNode n)))) v

/-- Density refers to finite node support, not merely to finite block support. -/
theorem start_finite_support_dense : Dense {x : StartSpace | (Function.support x.val).Finite} := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨E,hE,he⟩ := start_head_approx x hε
  refine ⟨startHead E x,?_,?_⟩
  · apply E.finite_toSet.subset
    intro v hv
    by_contra hnot
    have hvE : v ∉ E := hnot
    exact hv (by rw [startHead_coordinate,ite_eq_right hvE])
  · simpa only [dist_eq_norm] using he

end BoundedTreePotentials.Segments

end

end OAI
