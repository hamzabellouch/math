import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingIntrinsicProduct

namespace OAI

/-! # Mass of actual remaining-root cubes under the intrinsic product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingEuclideanCoordinates_cube (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ p, |c.remainingEuclideanCoordinates hfinal t p| < R := by
  rw [c.timeVectorHomeomorph_cube]
  change (∀ k, |c.timeVectorHomeomorph t k| < R) ↔
    ∀ p, |c.timeVectorHomeomorph t ((c.remainingIndexEquiv hfinal).symm p)| < R
  constructor
  · exact fun h p => h _
  · intro h k
    simpa only [Equiv.symm_apply_apply] using h (c.remainingIndexEquiv hfinal k)

lemma remainingGroup_cube_preimage (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (R : ℝ) :
    (c.remainingGroupCoordinates hP hfinal).symm ⁻¹'
        (c.remainingWordHomeomorph hP hfinal '' c.cube R) =
      Set.univ.pi (fun _ : ↥(allPositiveRoots n \ P) => Ioo (-R) R) := by
  let E := c.remainingGroupCoordinates hP hfinal
  let W := c.remainingWordHomeomorph hP hfinal
  ext v
  constructor
  · rintro ⟨t,ht,he⟩ p _
    have hv : c.remainingEuclideanCoordinates hfinal t = v := by
      have H := congrArg E he
      simpa only [E,remainingGroupCoordinates,Homeomorph.trans_apply,
        Homeomorph.symm_apply_apply,Homeomorph.apply_symm_apply] using H
    rw [←hv]
    exact abs_lt.mp ((c.remainingEuclideanCoordinates_cube hfinal R t).mp ht p)
  · intro hv
    let t := (c.remainingEuclideanCoordinates hfinal).symm v
    refine ⟨t,(c.remainingEuclideanCoordinates_cube hfinal R t).mpr ?_,?_⟩
    · intro p
      rw [show c.remainingEuclideanCoordinates hfinal t = v from
        (c.remainingEuclideanCoordinates hfinal).apply_symm_apply v]
      exact abs_lt.mpr (hv p (mem_univ p))
    · apply E.injective
      change E (W t) = E (E.symm v)
      rw [E.apply_symm_apply]
      change c.remainingEuclideanCoordinates hfinal (W.symm (W t)) = v
      rw [W.symm_apply_apply]
      exact (c.remainingEuclideanCoordinates hfinal).apply_symm_apply v

lemma remainingProduct_cube_mass (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (R : ℝ)
    (ν : ↥(allPositiveRoots n \ P) → Measure ℝ) [∀ p, SigmaFinite (ν p)] :
    (Measure.pi ν).map (c.remainingGroupCoordinates hP hfinal).symm
        (c.remainingWordHomeomorph hP hfinal '' c.cube R) =
      ∏ p, ν p (Ioo (-R) R) := by
  rw [Measure.map_apply (c.remainingGroupCoordinates hP hfinal).symm.measurable
    (((c.remainingWordHomeomorph hP hfinal).isOpenMap _ (c.cube_open R)).measurableSet),
    c.remainingGroup_cube_preimage hP hfinal R,Measure.pi_pi]

theorem ae_remainingIntrinsicProduct_unit (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, c.remainingIntrinsicProduct hP hfinal μ x
      (c.remainingWordHomeomorph hP hfinal '' c.cube 1) = 1 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H (p : ↥(allPositiveRoots (d+1) \ P)) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  filter_upwards [ae_all_iff.mpr H] with x hx
  let : ∀ p : ↥(allPositiveRoots (d+1) \ P), IsLocallyFiniteMeasure
      (intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x) :=
    fun p => (hx p).1
  unfold remainingIntrinsicProduct
  rw [c.remainingProduct_cube_mass hP hfinal]
  apply Finset.prod_eq_one
  intro p _
  have he : Ioo (- (1 : ℝ)) 1 = Metric.ball 0 1 := by
    ext t
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt,mem_Ioo]
  rw [he]
  exact (hx p).2

end EliminationChain
end DukePrimeDegree

end

end OAI
