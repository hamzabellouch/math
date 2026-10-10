import Mathlib
import OAI.Probability.UnimodularPercolation.Deformation.Corridors

namespace OAI

/-! Cluster Products for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallDeformationOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem exists_deformedOperator_small_change (G : BondGraph V E)
    (hG : Function.Injective G) (hloc : LocallyFinite G) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (hAT : ∀ x y, matrixCoeff A x y = (twoPoint G p x y : ℂ))
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V,
      (∀ x y, matrixCoeff B x y = (deformedKernel G (walkKernel G hloc a) p k t Set.univ x y : ℂ)) ∧
      ‖B‖ ≤ ‖A‖ ∧ ‖A-B‖ ≤ 2*t*‖P‖^k*‖A‖^2 ∧ ‖A‖-2*t*‖P‖^k*‖A‖^2 ≤ ‖B‖ := by
  let K := deformedKernel G (walkKernel G hloc a) p k t Set.univ
  have hKn (x y : V) : 0 ≤ K x y := deformedKernel_nonneg G _ p k t _ x y
  have hb (x y : V) := deformedKernel_change_bound G hG hloc p hp hp₁ a P hpos hPs hP A hA hAs hAT k t ht x y
  obtain ⟨B,hBn,hBK⟩ := exists_operator_of_matrix_domination (twoPoint G p) K (twoPoint_nonneg G p)
    (fun x y => by rw [abs_of_nonneg (hKn x y)]; exact sub_nonneg.mp (hb x y).1) A hAT
  have hBK' (x y : V) : matrixCoeff B x y = (K x y : ℂ) := hBK x y
  let C := A*(P^k*A)
  have hCn : PositiveRealMatrix C := hA.mul ((hpos.pow k).mul hA)
  have hscale (x y : V) : matrixCoeff (((2*t:ℝ):ℂ) • C) x y =
      (2*t*(matrixCoeff C x y).re : ℝ) := by
    change ((2*t:ℝ):ℂ)*matrixCoeff C x y = _
    rw [hCn.real]
    simp only [Complex.ofReal_re,Complex.ofReal_mul]
  obtain ⟨D,hDn,hDK⟩ := exists_operator_of_matrix_domination
    (fun x y => 2*t*(matrixCoeff C x y).re) (fun x y => twoPoint G p x y - K x y)
    (fun x y => mul_nonneg (mul_nonneg (by norm_num) ht) (hCn x y).2)
    (fun x y => by rw [abs_of_nonneg (hb x y).1]; exact (hb x y).2)
    (((2*t:ℝ):ℂ) • C) hscale
  have he : D = A-B := kernel_extension_unique hDK (by
    intro x y
    change matrixCoeff A x y - matrixCoeff B x y = _
    rw [hAT,hBK',Complex.ofReal_sub])
  rw [he] at hDn
  have hCnorm : ‖C‖ ≤ ‖A‖*‖P‖^k*‖A‖ := by
    calc
      _ ≤ ‖A‖*‖P^k*A‖ := norm_mul_le _ _
      _ ≤ ‖A‖*(‖P^k‖*‖A‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖A‖*(‖P‖^k*‖A‖) := by
        gcongr
        cases k with
        | zero =>
          simp only [pow_zero]
          have he : (1 : Hilbert V →L[ℂ] Hilbert V) = ContinuousLinearMap.id ℂ (Hilbert V) := by ext f; rfl
          rw [he]
          exact ContinuousLinearMap.norm_id_le
        | succ j => exact norm_pow_le' P (Nat.succ_pos j)
      _ = _ := by ring
  have hd : ‖A-B‖ ≤ 2*t*‖P‖^k*‖A‖^2 := by
    calc
      _ ≤ ‖((2*t:ℝ):ℂ) • C‖ := hDn
      _ = 2*t*‖C‖ := by rw [norm_smul,Complex.norm_of_nonneg (mul_nonneg (by norm_num) ht)]
      _ ≤ 2*t*(‖A‖*‖P‖^k*‖A‖) := mul_le_mul_of_nonneg_left hCnorm (mul_nonneg (by norm_num) ht)
      _ = _ := by ring
  refine ⟨B,hBK,hBn,hd,?_⟩
  have hh : ‖A‖ ≤ ‖A-B‖+‖B‖ := by simpa only [sub_add_cancel] using norm_add_le (A-B) B
  linarith

end SmallDeformationOperators
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
def closedBondNeighborhood (G : BondGraph V E) (A : Set V) : Set V :=
  {z | z ∈ A ∨ ∃ e, z ∈ G e ∧ ∃ a ∈ G e, a ∈ A}

def SimpleVisit (G : BondGraph V E) (S : Set E) (A : Set V) (x y : V) : Prop :=
  ∃ q : (openSimpleGraph G S).Walk x y, q.IsPath ∧ ∃ z ∈ q.support, z ∈ A

theorem SimpleVisit.mono (G : BondGraph V E) {S T : Set E} {A B : Set V}
    (hST : S ⊆ T) (hAB : A ⊆ B) {x y : V} (h : SimpleVisit G S A x y) :
    SimpleVisit G T B x y := by
  obtain ⟨q,hq,z,hz,ha⟩ := h
  have hg : openSimpleGraph G S ≤ openSimpleGraph G T := by
    rintro a b ⟨hne,e,he,hGe⟩
    exact ⟨hne,e,hST he,hGe⟩
  exact ⟨q.mapLe hg,hq.mapLe hg,z,by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz,hAB ha⟩

theorem walk_conn_restrict_vertices (G : BondGraph V E) (S : Set E) {x y : V}
    (q : (openSimpleGraph G S).Walk x y) (D : Set V)
    (hD : ∀ z ∈ q.support, z ∈ D) : Conn G (S ∩ internalEdges G D) x y := by
  obtain ⟨l,hl,hm,ho⟩ := walk_lift_bonds G S q
  apply hl.conn
  intro e he
  refine ⟨ho e he,?_⟩
  intro z hz
  exact hD z (SimpleGraph.Walk.mem_support_of_mem_edges (hm ▸ List.mem_map_of_mem he) hz)

theorem conn_restrict_of_no_simpleVisit (G : BondGraph V E) (S : Set E)
    (A : Set V) (x y : V) (hc : Conn G S x y) (hn : ¬SimpleVisit G S A x y) :
    Conn G (S ∩ internalEdges G Aᶜ) x y := by
  obtain ⟨q⟩ := (conn_iff_reachable G S x y).mp hc
  exact walk_conn_restrict_vertices G S q.bypass Aᶜ
    (fun z hz ha => hn ⟨q.bypass,q.bypass_isPath,z,hz,ha⟩)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_support_subset_walk (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (x y : V) (hc : w.counted D ω x y)
    (q : (openSimpleGraph G (ω ∩ internalEdges G D)).Walk x y) :
    ∀ z ∈ w.path.support, z ∈ q.support := by
  intro z hz
  have hl : 0 < w.path.length := by have := hc.1; omega
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp hz
  obtain ⟨e,he,hGe⟩ := w.edge_has_label s hs
  exact SimpleGraph.Walk.mem_support_of_mem_edges
    (pivotal_image_mem_edges G _ q e (hc.2.2.2.1 e he).2) (hGe.symm ▸ hzs)

end RawCorridor

 

theorem simplePath_disjoint_at (G : BondGraph V E) (S : Set E) {x y z : V}
    (q : (openSimpleGraph G S).Walk x y) (hq : q.IsPath) (hz : z ∈ q.support) :
    S ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G S (q.takeUntil z hz)
  obtain ⟨b,hb,heb,hob⟩ := walk_lift_bonds G S (q.dropUntil z hz)
  refine ⟨a.toFinset,b.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he; exact hoa e (List.mem_toFinset.mp he)
  · intro e he; exact hob e (List.mem_toFinset.mp he)
  · apply Finset.disjoint_left.mpr
    intro e hae hbe
    exact List.disjoint_left.mp (hq.isTrail.disjoint_edges_takeUntil_dropUntil hz)
      (hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp hae))
      (heb ▸ List.mem_map_of_mem (List.mem_toFinset.mp hbe))
  · exact ha.conn (fun e he => List.mem_toFinset.mpr he)
  · exact hb.conn (fun e he => List.mem_toFinset.mpr he)

end DeletionGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionCounted
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_delete_of_no_visit (G : BondGraph V E) (ω : Set E) (D A : Set V)
    (x y : V) (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y)
    (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (D \ A)) x y := by
  have hno : ¬SimpleVisit G S A x y := fun h => hn (h.mono G hS (fun _ => Or.inl))
  have h := conn_restrict_of_no_simpleVisit G S A x y hc hno
  apply conn_mono G ?_ h
  rintro e ⟨he,ha⟩
  exact ⟨he,fun z hz => ⟨(hS he).2 z hz,ha z hz⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_before_deletion_of_no_visit (w : RawCorridor G k)
    (D A : Set V) (ω : Set E) (x y : V)
    (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y)
    (hc : w.counted (D \ A) ω x y) : w.counted D ω x y := by
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  apply (w.counted_iff D ω x y).mpr
  refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
  · intro e he
    refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
    intro hbad
    have hd := conn_delete_of_no_visit G ω D A x y hn
      ((ω ∩ internalEdges G D) \ {e}) Set.sdiff_subset hbad
    apply (hc.2.2.2.1 e he).2
    apply conn_mono G ?_ hd
    rintro f ⟨⟨⟨hfω,hfD⟩,hfne⟩,hfnew⟩
    exact ⟨⟨hfω,hfnew⟩,hfne⟩
  · apply Set.disjoint_left.mpr
    intro e he ho
    have henew : e ∉ internalEdges G (D \ A) := fun he' =>
      Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,he'⟩
    obtain ⟨a,ha,hna⟩ : ∃ a ∈ G e, a ∉ D \ A := by
      change ¬(∀ a ∈ G e, a ∈ D \ A) at henew
      push Not at henew
      exact henew
    have haA : a ∈ A := by
      by_contra ha'
      exact hna ⟨ho.2 a ha,ha'⟩
    obtain ⟨z,hzi,hze⟩ := he.1
    obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
    have hz : z ∈ q.bypass.support := w.counted_support_subset_walk (D \ A) ω x y hc q.bypass z
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)
    have hv : SimpleVisit G (ω ∩ internalEdges G (D \ A)) (closedBondNeighborhood G A) x y :=
      ⟨q.bypass,q.bypass_isPath,z,hz,Or.inr ⟨e,hze,a,ha,haA⟩⟩
    exact hn (hv.mono G hs (Set.Subset.refl _))

end RawCorridor
end DeletionCounted
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionWeightedLoss
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem deformedConnection_no_visit (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (ω : Set E) (x y : V)
    (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y) :
    deformedConnection G P p k t D ω x y ≤ deformedConnection G P p k t (D \ A) ω x y := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2
    have hx : x ∉ A := fun ha => hn ⟨q.bypass,q.bypass_isPath,x,q.bypass.start_mem_support,Or.inl ha⟩
    have hy : y ∉ A := fun ha => hn ⟨q.bypass,q.bypass_isPath,y,q.bypass.end_mem_support,Or.inl ha⟩
    have hc' : x ∈ D \ A ∧ y ∈ D \ A ∧ Conn G (ω ∩ internalEdges G (D \ A)) x y := by
      refine ⟨⟨hc.1,hx⟩,⟨hc.2.1,hy⟩,?_⟩
      apply conn_mono G ?_ (conn_delete_of_no_visit G ω D A x y hn _ (Set.Subset.refl _) hc.2.2)
      rintro e ⟨⟨heω,heD⟩,henew⟩
      exact ⟨heω,henew⟩
    simp only [deformedConnection,hc,hc']
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left ?_ (neg_nonpos.mpr ht)
    apply (corridorPenalty_summable G hloc P p k (D \ A) ω x y).tsum_le_tsum ?_
      (corridorPenalty_summable G hloc P p k D ω x y)
    intro w
    by_cases hw : w.counted (D \ A) ω x y
    · have hw' := w.counted_before_deletion_of_no_visit D A ω x y hn hw
      simp only [corridorPenaltyTerm,hw,hw',ite_true,le_refl]
    · simpa only [corridorPenaltyTerm,hw,ite_false] using corridorPenaltyTerm_nonneg G P hP p D ω x y w
  · simpa only [deformedConnection,hc,ite_false] using deformedConnection_nonneg G P p k t (D \ A) ω x y

 

theorem deformedConnection_deletion_pointwise (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ≤
      if ∃ z ∈ closedBondNeighborhood G A,
        ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} then 1 else 0 := by
  split_ifs with h
  · linarith [deformedConnection_le_one G P hP p k t ht D ω x y,
      deformedConnection_nonneg G P p k t (D \ A) ω x y]
  · apply sub_nonpos.mpr
    apply deformedConnection_no_visit G hloc P hP p k t ht D A ω x y
    rintro ⟨q,hq,z,hz,hza⟩
    apply h
    exact ⟨z,hza,disjointOccurrence_upper _ _ Set.inter_subset_left (simplePath_disjoint_at G _ q hq hz)⟩

end DeletionWeightedLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeletionKernelBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem deformedKernel_deletion_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (x y : V)
    (hs : Summable (fun z : closedBondNeighborhood G A => twoPoint G p x z * twoPoint G p z y)) :
    deformedKernel G P p k t D x y - deformedKernel G P p k t (D \ A) x y ≤
      ∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y := by
  let B := fun z : closedBondNeighborhood G A =>
    DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y}
  let U := ⋃ z, B z
  have hBm (z : closedBondNeighborhood G A) : MeasurableSet (B z) :=
    measurableSet_finiteWitness _ (disjointOccurrence_upper _ _) (finiteWitness_disjointOccurrence _ _)
  have hUm : MeasurableSet U := MeasurableSet.iUnion hBm
  have hBn (z : closedBondNeighborhood G A) : 0 ≤ twoPoint G p x z * twoPoint G p z y :=
    mul_nonneg (twoPoint_nonneg G p x z) (twoPoint_nonneg G p z y)
  have hBK (z : closedBondNeighborhood G A) : law p (B z) ≤ ENNReal.ofReal (twoPoint G p x z * twoPoint G p z y) := by
    rw [←ENNReal.ofReal_toReal (measure_ne_top (law p) (B z))]
    exact ENNReal.ofReal_le_ofReal (bk p _ _ (fun _ _ h hc => conn_mono G h hc)
      (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x z) (finiteWitness_conn G z y))
  have hU : (law p).real U ≤ ∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y := by
    have hh : law p U ≤ ENNReal.ofReal (∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y) := by
      calc
        _ ≤ ∑' z, law p (B z) := measure_iUnion_le B
        _ ≤ ∑' z : closedBondNeighborhood G A, ENNReal.ofReal (twoPoint G p x z * twoPoint G p z y) := ENNReal.tsum_le_tsum hBK
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg hBn hs).symm
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (tsum_nonneg hBn))
  have hUi : Integrable (U.indicator (fun _ : Set E => (1:ℝ))) (law p) := (integrable_const _).indicator hUm
  have hpoint (ω : Set E) : deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ≤
      U.indicator (fun _ : Set E => (1:ℝ)) ω := by
    have he : ω ∈ U ↔ ∃ z ∈ closedBondNeighborhood G A, ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
      simp [U,B]
    simpa only [Set.indicator_apply,he] using deformedConnection_deletion_pointwise G hloc P hP p k t ht D A ω x y
  have hi := integrable_deformedConnection G P hP p k t ht D x y
  have hi' := integrable_deformedConnection G P hP p k t ht (D \ A) x y
  calc
    _ = ∫ ω, deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ∂law p := (integral_sub hi hi').symm
    _ ≤ ∫ ω, U.indicator (fun _ : Set E => (1:ℝ)) ω ∂law p := integral_mono (hi.sub hi') hUi hpoint
    _ = (law p).real U := integral_indicator_one hUm
    _ ≤ _ := hU

end DeletionKernelBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedSusceptibility (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) : ℝ :=
  ∑' y, deformedKernel G P p k t D x y

theorem deformedKernel_le_twoPoint [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    deformedKernel G P p k t D x y ≤ twoPoint G p x y := by
  rw [←deformedKernel_zero G P p k x y]
  apply integral_mono (integrable_deformedConnection G P hP p k t ht D x y)
    (integrable_deformedConnection G P hP p k 0 (le_refl _) Set.univ x y)
  intro ω
  exact (deformedConnection_mono G hloc P hP p k t ht (Set.subset_univ D)
    (Set.Subset.refl _) x y).trans (sub_nonneg.mp (deformedConnection_change G P hP p k t ht Set.univ ω x y).1)

theorem summable_deformedKernel [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    Summable (deformedKernel G P p k t D x) :=
  Summable.of_nonneg_of_le (deformedKernel_nonneg G P p k t D x)
    (deformedKernel_le_twoPoint G hloc P hP p k t ht D x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)

theorem deformedSusceptibility_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D x ≤ susceptibility G p x :=
  (summable_deformedKernel G hloc hqt P hP p hp k t ht D x).tsum_le_tsum
    (deformedKernel_le_twoPoint G hloc P hP p k t ht D x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)

end DeformedSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionSusceptibilityEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_twoPoint_restricted_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
    Summable (fun zy : N×V => twoPoint G p x zy.1 * twoPoint G p zy.1 zy.2) := by
  apply (summable_twoPoint_pair G hloc hqt p hp x).comp_injective (i := fun zy : N×V => (zy.1.val,zy.2))
  intro a b hab
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hab)) (congrArg (fun z : V×V => z.2) hab)

theorem twoPoint_double_restricted_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
    (∑' y : V, ∑' z : N, twoPoint G p x z * twoPoint G p z y) ≤
      maxSusceptibility G p * (∑' z : N, twoPoint G p x z) := by
  have hpairs := summable_twoPoint_restricted_pair G hloc hqt p hp x N
  have hcomm : (∑' y : V, ∑' z : N, twoPoint G p x z * twoPoint G p z y) =
      ∑' z : N, twoPoint G p x z * susceptibility G p z := by
    calc
      _ = ∑' z : N, ∑' y : V, twoPoint G p x z * twoPoint G p z y := hpairs.tsum_comm
      _ = _ := by simp only [tsum_mul_left, susceptibility]
  have hprod : Summable (fun z : N => twoPoint G p x z * susceptibility G p z) := by
    simpa only [tsum_mul_left, susceptibility] using hpairs.prod
  rw [hcomm]
  calc
    _ ≤ ∑' z : N, twoPoint G p x z * maxSusceptibility G p :=
      hprod.tsum_le_tsum
        (fun z => mul_le_mul_of_nonneg_left (susceptibility_le_max G hloc hqt p hp z) (twoPoint_nonneg G p x z))
        ((summable_twoPoint_subcritical G hloc hqt p hp x).subtype N |>.mul_right _)
    _ = _ := by rw [tsum_mul_right,mul_comm]

 

theorem deformedSusceptibility_deletion (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D A : Set V) (x : V) :
    deformedSusceptibility G P p k t D x -
      maxSusceptibility G p * (∑' z : closedBondNeighborhood G A, twoPoint G p x z) ≤
      deformedSusceptibility G P p k t (D \ A) x := by
  let N := closedBondNeighborhood G A
  have hpairs := summable_twoPoint_restricted_pair G hloc hqt p hp x N
  have hdiag (y : V) := hpairs.prod_symm.prod_factor y
  have hi := summable_deformedKernel G hloc hqt P hP p hp k t ht D x
  have hi' := summable_deformedKernel G hloc hqt P hP p hp k t ht (D \ A) x
  have hb := (hi.sub hi').tsum_le_tsum
    (fun y => deformedKernel_deletion_bound G hloc P hP p k t ht D A x y (hdiag y)) hpairs.prod_symm.prod
  rw [hi.tsum_sub hi'] at hb
  change deformedSusceptibility G P p k t D x - deformedSusceptibility G P p k t (D \ A) x ≤ _ at hb
  have herr := twoPoint_double_restricted_bound G hloc hqt p hp x N
  linarith

end DeletionSusceptibilityEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorCorridorGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_of_open_incident (G : BondGraph V E) (ω : Set E) (e : E)
    (he : e ∈ ω) (a b : V) (ha : a ∈ G e) (hb : b ∈ G e) : Conn G ω a b := by
  obtain ⟨c,d,hcd⟩ : ∃ c d, G e = s(c,d) := by
    obtain ⟨⟨c,d⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨c,d,hh.symm⟩
  rw [hcd,Sym2.mem_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact conn_refl G ω _
  · exact .single ⟨e,he,hcd⟩
  · exact conn_symm G ω (.single ⟨e,he,hcd⟩)
  · exact conn_refl G ω _

 

theorem conn_restrict_away_from_cluster (G : BondGraph V E) (ω S : Set E)
    (hS : S ⊆ ω) (u x y : V) (hx : x ∉ cluster G ω u) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (cluster G ω u)ᶜ) x y := by
  apply conn_restrict_of_no_simpleVisit G S (cluster G ω u) x y hc
  rintro ⟨q,_,z,hz,hzu⟩
  have hxz : Conn G ω x z := conn_mono G hS
    ((conn_iff_reachable G S x z).mpr ⟨q.takeUntil z hz⟩)
  exact hx (hzu.trans (conn_symm G ω hxz))

theorem conn_delete_cluster (G : BondGraph V E) (D : Set V) (ω : Set E)
    (u x y : V) (hx : x ∉ cluster G (ω ∩ internalEdges G D) u)
    (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (D \ cluster G (ω ∩ internalEdges G D) u)) x y := by
  apply conn_mono G ?_ (conn_restrict_away_from_cluster G _ S hS u x y hx hc)
  rintro e ⟨he,heA⟩
  exact ⟨he,fun z hz => ⟨(hS he).2 z hz,heA z hz⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_delete_other_cluster (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (u x y : V) (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    w.counted (D \ cluster G (ω ∩ internalEdges G D) u) ω x y ↔ w.counted D ω x y := by
  let A := cluster G (ω ∩ internalEdges G D) u
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  constructor
  · intro hc
    apply (w.counted_iff D ω x y).mpr
    refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
    · intro e he
      refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
      intro hbad
      have hd := conn_delete_cluster G D ω u x y hx
        ((ω ∩ internalEdges G D) \ {e}) Set.sdiff_subset hbad
      apply (hc.2.2.2.1 e he).2
      apply conn_mono G ?_ hd
      rintro f ⟨⟨⟨hfω,hfD⟩,hfne⟩,hfnew⟩
      exact ⟨⟨hfω,hfnew⟩,hfne⟩
    · apply Set.disjoint_left.mpr
      intro e he ho
      obtain ⟨z,hzi,hze⟩ := he.1
      obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
      have hz : z ∈ q.support := w.counted_support_subset_walk (D \ A) ω x y hc q z
        (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)
      have hxz : Conn G (ω ∩ internalEdges G D) x z := conn_mono G hs
        ((conn_iff_reachable G _ x z).mpr ⟨q.takeUntil z hz⟩)
      have heA : e ∈ internalEdges G (D \ A) := by
        intro a ha
        refine ⟨ho.2 a ha,?_⟩
        intro hau
        have hza := conn_of_open_incident G _ e ho z a hze ha
        exact hx (hau.trans (conn_symm G _ (hxz.trans hza)))
      exact Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,heA⟩
  · intro hc
    have hnew := conn_delete_cluster G D ω u x y hx _ (Set.Subset.refl _) hc.2.2.1
    have hc' : Conn G (ω ∩ internalEdges G (D \ A)) x y := by
      apply conn_mono G ?_ hnew
      rintro e ⟨⟨heω,_⟩,heA⟩
      exact ⟨heω,heA⟩
    exact (w.counted_iff _ ω x y).mpr ⟨hc.1,
      corridorCounted_restrict G _ _ Set.sdiff_subset (Set.Subset.refl _) x y hc' hc.2.2⟩

end RawCorridor
end ExteriorCorridorGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_delete_other_cluster (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (u x y : V)
    (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    corridorPenalty G P p k (D \ cluster G (ω ∩ internalEdges G D) u) ω x y =
      corridorPenalty G P p k D ω x y := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_delete_other_cluster D ω u x y hx]

 

theorem deformedConnection_delete_other_cluster (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (u x y : V)
    (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    deformedConnection G P p k t (D \ cluster G (ω ∩ internalEdges G D) u) ω x y =
      deformedConnection G P p k t D ω x y := by
  let A := cluster G (ω ∩ internalEdges G D) u
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  have hg : (x ∈ D \ A ∧ y ∈ D \ A ∧ Conn G (ω ∩ internalEdges G (D \ A)) x y) ↔
      (x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y) := by
    constructor
    · exact fun h => ⟨h.1.1,h.2.1.1,conn_mono G hs h.2.2⟩
    · rintro ⟨hxD,hyD,hc⟩
      have hy : y ∉ A := fun hy => hx (hy.trans (conn_symm G _ hc))
      refine ⟨⟨hxD,hx⟩,⟨hyD,hy⟩,?_⟩
      apply conn_mono G ?_ (conn_delete_cluster G D ω u x y hx _ (Set.Subset.refl _) hc)
      rintro e ⟨⟨heω,_⟩,heA⟩
      exact ⟨heω,heA⟩
  dsimp only [A] at hg
  simp only [deformedConnection,hg,corridorPenalty_delete_other_cluster G P p k D ω u x y hx]

noncomputable def deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) : ℝ :=
  ∑' y, deformedConnection G P p k t D ω x y

theorem deformedClusterMass_delete_other_cluster (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (u x : V)
    (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    deformedClusterMass G P p k t (D \ cluster G (ω ∩ internalEdges G D) u) ω x =
      deformedClusterMass G P p k t D ω x := by
  exact tsum_congr (fun y => deformedConnection_delete_other_cluster G P p k t D ω u x y hx)

theorem deformedConnection_le_conn (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) : deformedConnection G P p k t D ω x y ≤
      if Conn G ω x y then 1 else 0 := by
  by_cases hc : Conn G ω x y
  · simpa only [hc,ite_true] using deformedConnection_le_one G P hP p k t ht D ω x y
  · have hn : ¬Conn G (ω ∩ internalEdges G D) x y := fun h => hc (conn_mono G Set.inter_subset_left h)
    simp only [deformedConnection,hn,hc,and_false,ite_false,le_refl]

theorem measurable_deformedClusterMass [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    Measurable (fun ω => deformedClusterMass G P p k t D ω x) :=
  Measurable.tsum (fun y => measurable_deformedConnection G P p k t D x y)

end ExteriorWeightedConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedMassIntegrals
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_finite_support (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) :
    (deformedConnection G P p k t D ω x).HasFiniteSupport := by
  apply hf.subset
  intro y hy
  by_contra hn
  have hnc : ¬Conn G (ω ∩ internalEdges G D) x y := fun h => hn (conn_mono G Set.inter_subset_left h)
  exact hy (by simp only [deformedConnection,hnc,and_false,ite_false])

theorem deformedClusterMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) :
    0 ≤ deformedClusterMass G P p k t D ω x :=
  tsum_nonneg (deformedConnection_nonneg G P p k t D ω x)

theorem deformedClusterMass_le_ncard (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    deformedClusterMass G P p k t D ω x ≤ ((cluster G ω x).ncard:ℝ) := by
  unfold deformedClusterMass
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    have hn : ¬Conn G ω x y := fun hc => hy (hf.mem_toFinset.mpr hc)
    have hn' : ¬Conn G (ω ∩ internalEdges G D) x y := fun hc => hn (conn_mono G Set.inter_subset_left hc)
    simp only [deformedConnection,hn',and_false,ite_false])]
  calc
    _ ≤ ∑ _y ∈ hf.toFinset, (1:ℝ) := Finset.sum_le_sum (fun y _ => deformedConnection_le_one G P hP p k t ht D ω x y)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

theorem integrable_deformedClusterMass [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    Integrable (fun ω => deformedClusterMass G P p k t D ω x) (law p) := by
  apply Integrable.mono' (susceptibility_eq_integral G hloc hqt p hp x).1
    (measurable_deformedClusterMass G P p k t D x).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
  rw [Real.norm_of_nonneg (deformedClusterMass_nonneg G P p k t D ω x)]
  exact deformedClusterMass_le_ncard G P hP p k t ht D ω x hω

 

theorem deformedSusceptibility_eq_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D x = ∫ ω, deformedClusterMass G P p k t D ω x ∂law p := by
  have hi := integrable_deformedConnection G P hP p k t ht D x
  have hs : Summable (fun y => ∫ ω, ‖deformedConnection G P p k t D ω x y‖ ∂law p) := by
    simp only [Real.norm_of_nonneg (deformedConnection_nonneg G P p k t D _ x _)]
    exact summable_deformedKernel G hloc hqt P hP p hp k t ht D x
  exact integral_tsum_of_summable_integral_norm hi hs

end DeformedMassIntegrals
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExactComponentRestriction
attribute [local instance] Classical.propDecidable Classical.decEq

 
def OpenClosed (G : BondGraph V E) (ω : Set E) (A : Set V) : Prop :=
  ∀ e ∈ ω, ∀ z ∈ G e, z ∈ A → ∀ a ∈ G e, a ∈ A

theorem openClosed_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    OpenClosed G ω (cluster G ω x) := by
  intro e he z hz hx a ha
  exact hx.trans (conn_of_open_incident G ω e he z a hz ha)

theorem conn_restrict_openClosed (G : BondGraph V E) (ω S : Set E) (hS : S ⊆ ω)
    (A : Set V) (hA : OpenClosed G ω A) (x y : V) (hx : x ∈ A) (hc : Conn G S x y) :
    y ∈ A ∧ Conn G (S ∩ internalEdges G A) x y := by
  induction hc with
  | refl => exact ⟨hx,conn_refl G _ x⟩
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have ha : a ∈ G e := by simp [heq]
    have hb : b ∈ G e := by simp [heq]
    have hei : e ∈ internalEdges G A := hA e (hS he) a ha ih.1
    exact ⟨hei b hb,ih.2.tail ⟨e,⟨he,hei⟩,heq⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_restrict_openClosed (w : RawCorridor G k) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x y : V) (hx : x ∈ A) :
    w.counted (D ∩ A) ω x y ↔ w.counted D ω x y := by
  have hs : ω ∩ internalEdges G (D ∩ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.inter_subset_left)
  have hrest (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
      Conn G (S ∩ internalEdges G (D ∩ A)) x y := by
    apply conn_mono G ?_ (conn_restrict_openClosed G _ S hS A hA x y hx hc).2
    rintro e ⟨he,heA⟩
    exact ⟨he,fun z hz => ⟨(hS he).2 z hz,heA z hz⟩⟩
  constructor
  · intro hc
    apply (w.counted_iff D ω x y).mpr
    refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
    · intro e he
      refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
      intro hbad
      apply (hc.2.2.2.1 e he).2
      apply conn_mono G ?_ (hrest _ Set.sdiff_subset hbad)
      rintro f ⟨⟨⟨hfω,_⟩,hfne⟩,hfnew⟩
      exact ⟨⟨hfω,hfnew⟩,hfne⟩
    · apply Set.disjoint_left.mpr
      intro e he ho
      obtain ⟨z,hzi,hze⟩ := he.1
      have hz : z ∈ A := (hc.2.1 z (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)).2
      have heA : e ∈ internalEdges G (D ∩ A) := fun a ha => ⟨ho.2 a ha,hA e ho z hze hz a ha⟩
      exact Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,heA⟩
  · intro hc
    have hc' : Conn G (ω ∩ internalEdges G (D ∩ A)) x y := by
      apply conn_mono G ?_ (hrest _ (Set.Subset.refl _) hc.2.2.1)
      rintro e ⟨⟨heω,_⟩,heA⟩
      exact ⟨heω,heA⟩
    exact (w.counted_iff _ ω x y).mpr ⟨hc.1,
      corridorCounted_restrict G _ _ Set.inter_subset_left (Set.Subset.refl _) x y hc' hc.2.2⟩

end RawCorridor
end ExactComponentRestriction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InternalWeightedRestriction
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_restrict_openClosed (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x y : V) (hx : x ∈ A) :
    corridorPenalty G P p k (D ∩ A) ω x y = corridorPenalty G P p k D ω x y := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_restrict_openClosed D A ω hA x y hx]

theorem deformedConnection_restrict_openClosed (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x y : V) (hx : x ∈ A) :
    deformedConnection G P p k t (D ∩ A) ω x y = deformedConnection G P p k t D ω x y := by
  have hg : (x ∈ D ∩ A ∧ y ∈ D ∩ A ∧ Conn G (ω ∩ internalEdges G (D ∩ A)) x y) ↔
      (x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y) := by
    constructor
    · exact fun h => ⟨h.1.1,h.2.1.1,conn_mono G
        (Set.inter_subset_inter_right _ (internalEdges_mono G Set.inter_subset_left)) h.2.2⟩
    · rintro ⟨hxD,hyD,hc⟩
      have hh := conn_restrict_openClosed G _ _ (Set.Subset.refl _) A hA x y hx hc
      refine ⟨⟨hxD,hx⟩,⟨hyD,hh.1⟩,conn_mono G ?_ hh.2⟩
      rintro e ⟨⟨heω,heD⟩,heA⟩
      exact ⟨heω,fun z hz => ⟨heD z hz,heA z hz⟩⟩
  simp only [deformedConnection,hg,corridorPenalty_restrict_openClosed G P p k D A ω hA x y hx]

theorem deformedClusterMass_restrict_openClosed (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x : V) (hx : x ∈ A) :
    deformedClusterMass G P p k t (D ∩ A) ω x = deformedClusterMass G P p k t D ω x :=
  tsum_congr (fun y => deformedConnection_restrict_openClosed G P p k t D A ω hA x y hx)

 
theorem deformedClusterMass_restrict_config (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) (S : Set E)
    (hS : internalEdges G D ⊆ S) :
    deformedClusterMass G P p k t D (ω ∩ S) x = deformedClusterMass G P p k t D ω x := by
  have he : (ω ∩ S) ∩ internalEdges G D = ω ∩ internalEdges G D := by
    ext e
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hS h.2⟩,h.2⟩⟩
  apply tsum_congr
  intro y
  have hc (w : RawCorridor G k) : w.counted D (ω ∩ S) x y ↔ w.counted D ω x y := by
    simp only [RawCorridor.counted,corridorCounted,he]
  simp only [deformedConnection,corridorPenalty,corridorPenaltyTerm,hc,he]

end InternalWeightedRestriction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section DisjointCoordinateObservables
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem restriction_functions_independent (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (f g : Set E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ω, f ω = f (ω ∩ S)) (hgT : ∀ ω, g ω = g (ω ∩ T)) :
    IndepFun f g (law p) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have he (h : Set E → ℝ) (U : Set E) (hU : ∀ ω, h ω = h (ω ∩ U)) (C : Set ℝ) :
      (fun ω => ω ∩ U) ⁻¹' (h ⁻¹' C) = h ⁻¹' C := by
    ext ω
    simp only [Set.mem_preimage,←hU ω]
  simpa only [he f S hfS A,he g T hgT B] using
    restriction_events_independent p S T hST (f ⁻¹' A) (g ⁻¹' B)
      (hA.preimage hf) (hB.preimage hg)

theorem integral_mul_disjoint_coordinates (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (f g : Set E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ω, f ω = f (ω ∩ S)) (hgT : ∀ ω, g ω = g (ω ∩ T)) :
    (∫ ω, f ω*g ω ∂law p) = (∫ ω, f ω ∂law p)*(∫ ω, g ω ∂law p) :=
  (restriction_functions_independent p S T hST f g hf hg hfS hgT).integral_mul_eq_mul_integral
    hf.aestronglyMeasurable hg.aestronglyMeasurable

end DisjointCoordinateObservables
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactWeightedClusterCell
attribute [local instance] Classical.propDecidable Classical.decEq

theorem induced_cluster_restrict_incident_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (W : Finset V) (D : Set V) (ω : Set E) (x : V) :
    cluster G ((ω ∩ (incidentSupport G hloc W:Set E)) ∩ internalEdges G D) x = (W:Set V) ↔
      cluster G (ω ∩ internalEdges G D) x = (W:Set V) := by
  rw [Set.inter_right_comm]
  exact cluster_restrict_incident_eq_iff G hloc W _ (Finset.Subset.refl _) _ x

theorem weighted_cluster_cell_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (W : Finset V) (x : V)
    (ω : Set E) :
    (if cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D ω x else 0) =
    (if cluster G ((ω ∩ (incidentSupport G hloc W:Set E)) ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D (ω ∩ (incidentSupport G hloc W:Set E)) x else 0) := by
  simp only [induced_cluster_restrict_incident_iff]
  split_ifs with hW
  · have hx : x ∈ (W:Set V) := hW ▸ conn_refl G _ x
    have hA : OpenClosed G (ω ∩ internalEdges G D) (W:Set V) := hW ▸ openClosed_cluster G _ x
    have hW' := (induced_cluster_restrict_incident_iff G hloc W D ω x).mpr hW
    have hA' : OpenClosed G ((ω ∩ (incidentSupport G hloc W:Set E)) ∩ internalEdges G D) (W:Set V) :=
      hW' ▸ openClosed_cluster G _ x
    rw [←deformedClusterMass_restrict_openClosed G P p k t D W ω hA x hx,
      ←deformedClusterMass_restrict_openClosed G P p k t D W _ hA' x hx]
    symm
    apply deformedClusterMass_restrict_config
    intro e he
    exact (mem_incidentSupport G hloc W e).mpr
      ⟨(G e).out.1,(he _ (Sym2.out_fst_mem _)).2,Sym2.out_fst_mem _⟩
  · rfl

 

theorem weighted_cluster_cell_exposure [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (W : Finset V) (x y : V) :
    (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D ω x else 0) *
        deformedClusterMass G P p k t (D \ (W:Set V)) ω y ∂law p) =
    (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D ω x else 0) ∂law p) *
        deformedSusceptibility G P p k t (D \ (W:Set V)) y := by
  rw [deformedSusceptibility_eq_integral G hloc hqt P hP p hp k t ht]
  apply integral_mul_disjoint_coordinates p (incidentSupport G hloc W:Set E)
    (incidentSupport G hloc W:Set E)ᶜ disjoint_compl_right
  · exact Measurable.ite ((measurableSet_cluster_eq G x W).preimage (measurable_inter_const _))
      (measurable_deformedClusterMass G P p k t D x) measurable_const
  · exact measurable_deformedClusterMass G P p k t _ y
  · exact weighted_cluster_cell_local G hloc P p k t D W x
  · intro ω
    symm
    apply deformedClusterMass_restrict_config
    rw [complement_incidentSupport]
    exact fun e he z hz => (he z hz).2

end ExactWeightedClusterCell
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section InducedClusterPartition
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_induced_cluster_finite_partition [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (D : Set V) (x : V)
    (f : Set E → ℝ) (hf : Integrable f (law p)) :
    (∫ ω, f ω ∂law p) = ∑' W : Finset V,
      ∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then f ω else 0) ∂law p := by
  let F (W : Finset V) (ω : Set E) := if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then f ω else 0
  have hi (W : Finset V) : Integrable (F W) (law p) := by
    have he : F W = {ω : Set E | cluster G (ω ∩ internalEdges G D) x = (W:Set V)}.indicator f := by
      funext ω
      simp only [F,Set.indicator,Set.mem_ofPred_eq]
      split_ifs <;> rfl
    rw [he]
    exact hf.indicator ((measurableSet_cluster_eq G x W).preimage (measurable_inter_const _))
  have hb (S : Finset (Finset V)) (ω : Set E) : (∑ W ∈ S, ‖F W ω‖) ≤ ‖f ω‖ := by
    by_cases hex : ∃ W ∈ S, cluster G (ω ∩ internalEdges G D) x = (W:Set V)
    · obtain ⟨W,hWS,hW⟩ := hex
      rw [Finset.sum_eq_single W]
      · simp only [F,hW,ite_true,le_refl]
      · intro U _ hU
        have hu : cluster G (ω ∩ internalEdges G D) x ≠ (U:Set V) := fun h => hU (Finset.coe_injective (h.symm.trans hW))
        simp only [F,ite_eq_right hu,norm_zero]
      · exact fun h => (h hWS).elim
    · have he (W : Finset V) (hW : W ∈ S) : cluster G (ω ∩ internalEdges G D) x ≠ (W:Set V) := fun h => hex ⟨W,hW,h⟩
      calc
        _ = 0 := Finset.sum_eq_zero (fun W hW => by simp only [F,ite_eq_right (he W hW),norm_zero])
        _ ≤ _ := norm_nonneg _
  have hn : Summable (fun W => ∫ ω, ‖F W ω‖ ∂law p) := by
    apply summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (c := ∫ ω, ‖f ω‖ ∂law p)
    intro S
    rw [←integral_finsetSum _ (fun W _ => (hi W).norm)]
    exact integral_mono (integrable_finsetSum _ (fun W _ => (hi W).norm)) hf.norm (hb S)
  calc
    _ = ∫ ω, ∑' W : Finset V, F W ω ∂law p := by
      apply integral_congr_ae
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      exact (tsum_cluster_cells G (ω ∩ internalEdges G D) x
        (hω.subset (fun _ h => conn_mono G Set.inter_subset_left h)) (f ω)).symm
    _ = _ := (integral_tsum_of_summable_integral_norm hi hn).symm

end InducedClusterPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedClusterProducts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedClusterMass_eq_zero_of_not_mem (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) (hx : x ∉ D) :
    deformedClusterMass G P p k t D ω x = 0 := by
  simp only [deformedClusterMass,deformedConnection,hx,false_and,ite_false,tsum_zero]

theorem deformed_distinct_product_eq_exterior (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    (if ¬Conn G (ω ∩ internalEdges G D) x y then
      deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) =
    deformedClusterMass G P p k t D ω x *
      deformedClusterMass G P p k t (D \ cluster G (ω ∩ internalEdges G D) x) ω y := by
  by_cases hc : Conn G (ω ∩ internalEdges G D) x y
  · rw [ite_eq_right (not_not_intro hc),deformedClusterMass_eq_zero_of_not_mem G P p k t _ ω y
      (fun h => h.2 hc),mul_zero]
  · rw [ite_eq_left hc,deformedClusterMass_delete_other_cluster G P p k t D ω x y hc]

theorem integrable_deformed_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => deformedClusterMass G P p k t D ω x *
      deformedClusterMass G P p k t D ω y) (law p) := by
  apply Integrable.mono' (subcritical_cluster_association G hloc hqt p hp x y).1
    ((measurable_deformedClusterMass G P p k t D x).mul
      (measurable_deformedClusterMass G P p k t D y)).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (deformedClusterMass_nonneg G P p k t D ω x)
    (deformedClusterMass_nonneg G P p k t D ω y))]
  exact mul_le_mul (deformedClusterMass_le_ncard G P hP p k t ht D ω x hx)
    (deformedClusterMass_le_ncard G P hP p k t ht D ω y hy)
    (deformedClusterMass_nonneg G P p k t D ω y) (Nat.cast_nonneg _)

theorem integrable_distinct_deformed_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => if ¬Conn G (ω ∩ internalEdges G D) x y then
      deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) (law p) := by
  have he : (fun ω => if ¬Conn G (ω ∩ internalEdges G D) x y then
      deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) =
      {ω | Conn G (ω ∩ internalEdges G D) x y}ᶜ.indicator
        (fun ω => deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y) := by
    funext ω
    simp only [Set.indicator,Set.mem_compl_iff,Set.mem_ofPred_eq]
  rw [he]
  exact (integrable_deformed_product G hloc hqt P hP p hp k t ht D x y).indicator
    (((measurableSet_conn G x y).preimage (measurable_inter_const (internalEdges G D))).compl)

end DeformedClusterProducts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshWeightedMass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedFreshExteriorMoment (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) (ω : Set E) : ℝ :=
  deformedClusterMass G P p k t D ω x *
    deformedSusceptibility G P p k t (D \ cluster G (ω ∩ internalEdges G D) x) y

theorem deformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    0 ≤ deformedSusceptibility G P p k t D x :=
  tsum_nonneg (deformedKernel_nonneg G P p k t D x)

theorem deformedFreshExteriorMoment_eq_tsum (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) (ω : Set E)
    (hf : (cluster G (ω ∩ internalEdges G D) x).Finite) :
    deformedFreshExteriorMoment G P p k t D x y ω = ∑' W : Finset V,
      if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
        deformedClusterMass G P p k t D ω x * deformedSusceptibility G P p k t (D \ (W:Set V)) y else 0 := by
  rw [←tsum_cluster_cells G (ω ∩ internalEdges G D) x hf (deformedFreshExteriorMoment G P p k t D x y ω)]
  apply tsum_congr
  intro W
  split_ifs with hW
  · simp only [deformedFreshExteriorMoment,hW]
  · rfl

theorem integrable_deformedFreshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (deformedFreshExteriorMoment G P p k t D x y) (law p) := by
  have hm : AEStronglyMeasurable (deformedFreshExteriorMoment G P p k t D x y) (law p) := by
    have hh : Measurable (fun ω => ∑' W : Finset V,
        if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
          deformedClusterMass G P p k t D ω x * deformedSusceptibility G P p k t (D \ (W:Set V)) y else 0) := by
      apply Measurable.tsum
      intro W
      exact Measurable.ite ((measurableSet_cluster_eq G x W).preimage (measurable_inter_const _))
        ((measurable_deformedClusterMass G P p k t D x).mul_const _) measurable_const
    apply hh.aestronglyMeasurable.congr
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    exact (deformedFreshExteriorMoment_eq_tsum G P p k t D x y ω
      (hω.subset (fun _ h => conn_mono G Set.inter_subset_left h))).symm
  apply Integrable.mono' ((integrable_deformedClusterMass G hloc hqt P hP p hp k t ht D x).mul_const
    (susceptibility G p y)) hm
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only [deformedFreshExteriorMoment]
    rw [Real.norm_of_nonneg (mul_nonneg (deformedClusterMass_nonneg G P p k t D ω x)
      (deformedSusceptibility_nonneg G P p k t _ y))]
    exact mul_le_mul_of_nonneg_left (deformedSusceptibility_le G hloc hqt P hP p hp k t ht _ y)
      (deformedClusterMass_nonneg G P p k t D ω x))

end FreshWeightedMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedExposureIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_deformedFreshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    (∫ ω, deformedFreshExteriorMoment G P p k t D x y ω ∂law p) =
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  rw [integral_induced_cluster_finite_partition G p hp D x _
      (integrable_deformedFreshExteriorMoment G hloc hqt P hP p hp k t ht D x y),
    integral_induced_cluster_finite_partition G p hp D x _
      (integrable_distinct_deformed_product G hloc hqt P hP p hp k t ht D x y)]
  apply tsum_congr
  intro W
  have hl : (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
      deformedFreshExteriorMoment G P p k t D x y ω else 0) ∂law p) =
      (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
        deformedClusterMass G P p k t D ω x else 0) ∂law p) *
      deformedSusceptibility G P p k t (D \ (W:Set V)) y := by
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hW : cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      · simp only [hW,ite_true,deformedFreshExteriorMoment]
      · simp only [hW,ite_false,zero_mul])
  rw [hl,←weighted_cluster_cell_exposure G hloc hqt P hP p hp k t ht D W x y]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases hW : cluster G (ω ∩ internalEdges G D) x = (W:Set V)
    · simp only [hW,ite_true]
      rw [deformed_distinct_product_eq_exterior,hW]
    · simp only [hW,ite_false,zero_mul])

end WeightedExposureIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedThreeArmEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_three_arm_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a : V) :
    Summable (fun bz : V×V => twoPoint G p x bz.1 * twoPoint G p bz.1 a * twoPoint G p bz.1 bz.2) := by
  apply (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
  · exact fun bz => mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))
      (twoPoint_nonneg G p _ _)
  · intro bz
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (twoPoint_nonneg G p _ _) (twoPoint_le_one G p _ _))
      (twoPoint_nonneg G p _ _)

theorem three_arm_real_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a z : V) :
    (law p).real {ω | Conn G ω x a ∧ Conn G ω x z} ≤
      ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z := by
  have hs := (summable_three_arm_pair G hloc hqt p hp x a).prod_symm.prod_factor z
  have hn (b : V) : 0 ≤ twoPoint G p x b * twoPoint G p b a * twoPoint G p b z :=
    mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _)
  have he : (∑' b, law p {ω | Conn G ω x b} * law p {ω | Conn G ω b a} * law p {ω | Conn G ω b z}) =
      ENNReal.ofReal (∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hn hs]
    apply tsum_congr
    intro b
    rw [ENNReal.ofReal_mul (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)),
      ENNReal.ofReal_mul (twoPoint_nonneg G p _ _)]
    simp only [twoPoint,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hh := (three_arm_bound G p x a z).trans_eq he
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (tsum_nonneg hn))

 

theorem integral_size_membership_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a : V) :
    (∫ ω, (if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0) ∂law p) ≤
      maxSusceptibility G p * (∑' b, twoPoint G p x b * twoPoint G p b a) := by
  have he := integral_cluster_size_event G hloc hqt p hp x _ (measurableSet_conn G x a)
  simp only [Set.mem_ofPred_eq] at he
  rw [he]
  have hs := summable_three_arm_pair G hloc hqt p hp x a
  have hl : Summable (fun z => (law p).real {ω | Conn G ω x a ∧ Conn G ω x z}) :=
    (summable_twoPoint_subcritical G hloc hqt p hp x).of_nonneg_of_le (fun _ => measureReal_nonneg)
      (fun _ => measureReal_mono (fun _ h => h.2))
  have hb : Summable (fun b => twoPoint G p x b * twoPoint G p b a) :=
    (summable_twoPoint_subcritical G hloc hqt p hp x).of_nonneg_of_le
      (fun b => mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))
      (fun b => mul_le_of_le_one_right (twoPoint_nonneg G p _ _) (twoPoint_le_one G p _ _))
  have hj : Summable (fun b => twoPoint G p x b * twoPoint G p b a * susceptibility G p b) := by
    simpa only [tsum_mul_left,susceptibility] using hs.prod
  calc
    _ ≤ ∑' z, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z :=
      hl.tsum_le_tsum (three_arm_real_bound G hloc hqt p hp x a) hs.prod_symm.prod
    _ = ∑' b, ∑' z, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z := hs.tsum_comm
    _ = ∑' b, twoPoint G p x b * twoPoint G p b a * susceptibility G p b := by
      simp only [tsum_mul_left,susceptibility]
    _ ≤ ∑' b, twoPoint G p x b * twoPoint G p b a * maxSusceptibility G p := by
      apply hj.tsum_le_tsum
        (fun b => mul_le_mul_of_nonneg_left (susceptibility_le_max G hloc hqt p hp b)
          (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))) (hb.mul_right _)
    _ = _ := by rw [tsum_mul_right,mul_comm]

end WeightedThreeArmEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteNeighborhoodMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finset_sum_union_le (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (S T : Finset V) :
    (∑ x ∈ S ∪ T, f x) ≤ (∑ x ∈ S, f x) + ∑ x ∈ T, f x := by
  have he := Finset.sum_union_inter (f := f) (s₁ := S) (s₂ := T)
  have hn := Finset.sum_nonneg (s := S ∩ T) (fun x _ => hf x)
  linarith

theorem finset_sum_biUnion_le (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (W : Finset V) (N : V → Finset V) :
    (∑ z ∈ W.biUnion N, f z) ≤ ∑ a ∈ W, ∑ z ∈ N a, f z := by
  induction W using Finset.induction_on with
  | empty => simp
  | @insert a W ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    exact (finset_sum_union_le f hf _ _).trans (add_le_add (le_refl _) ih)

theorem closedBondNeighborhood_finset (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) :
    closedBondNeighborhood G (W:Set V) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
  ext z
  simp only [closedBondNeighborhood,Set.mem_ofPred_eq,Finset.mem_coe,Finset.mem_union,Finset.mem_biUnion]
  constructor
  · rintro (hz | ⟨e,hz,a,ha,haW⟩)
    · exact Or.inl hz
    · by_cases hza : a = z
      · exact Or.inl (hza ▸ haW)
      · exact Or.inr ⟨a,haW,(mem_neighbors G hloc a z).mpr
          ⟨e,(Sym2.mem_and_mem_iff hza).mp ⟨ha,hz⟩⟩⟩
  · rintro (hz | ⟨a,ha,haz⟩)
    · exact Or.inl hz
    · obtain ⟨e,he⟩ := (mem_neighbors G hloc a z).mp haz
      exact Or.inr ⟨e,he.symm ▸ Sym2.mem_mk_right a z,a,he.symm ▸ Sym2.mem_mk_left a z,ha⟩

theorem neighborhood_mass_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (W : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑' z : closedBondNeighborhood G (W:Set V), f z) ≤
      ∑ a ∈ W, (f a + ∑ z ∈ neighbors G hloc a, f z) := by
  rw [closedBondNeighborhood_finset G hloc W,Finset.tsum_subtype']
  exact (finset_sum_union_le f hf _ _).trans
    ((add_le_add (le_refl _) (finset_sum_biUnion_le f hf W (neighbors G hloc))).trans_eq
      (Finset.sum_add_distrib).symm)

end FiniteNeighborhoodMass
end Percolation

end OAI
