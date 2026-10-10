import OAI.Analysis.ForestSpace.Polar

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Projections
variable {V : Type} [PartialOrder V]

/-- Completion of restriction to an ancestral head. -/
noncomputable def headJ (H : Set V) (hH : IsLowerSet H) : J V →L[ℝ] J V :=
  (UniformSpace.Completion.toComplL.comp (TestVector.head H hH)).extend
    UniformSpace.Completion.toComplL

@[simp] theorem headJ_coe (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    headJ H hH (u : J V) = (TestVector.cut H u : J V) := by
  exact (UniformSpace.Completion.toComplL.comp (TestVector.head H hH)).extend_eq
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe (TestVector V)) u

noncomputable def tailJ (H : Set V) (hH : IsLowerSet H) : J V →L[ℝ] J V :=
  ContinuousLinearMap.id ℝ (J V) - headJ H hH

@[simp] theorem tailJ_coe (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    tailJ H hH (u : J V) = (TestVector.cut Hᶜ u : J V) := by
  have he : u - TestVector.cut H u = TestVector.cut Hᶜ u := by
    apply sub_eq_iff_eq_add.mpr
    exact (TestVector.cut_add_compl H u).symm.trans (add_comm _ _)
  change (u : J V) - headJ H hH (u : J V) = _
  rw [headJ_coe, ← UniformSpace.Completion.coe_sub, he]

 theorem norm_headJ_le (H : Set V) (hH : IsLowerSet H) (u : J V) :
    ‖headJ H hH u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_le (headJ H hH).continuous.norm continuous_norm) ?_
  intro v
  simpa only [headJ_coe, UniformSpace.Completion.norm_coe] using TestVector.norm_cut_le H hH v

 theorem norm_tailJ_le (H : Set V) (hH : IsLowerSet H) (u : J V) :
    ‖tailJ H hH u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_le (tailJ H hH).continuous.norm continuous_norm) ?_
  intro v
  simpa only [tailJ_coe, UniformSpace.Completion.norm_coe] using TestVector.norm_cut_compl_le H hH v

noncomputable def P (H : Set V) (hH : IsLowerSet H) : FullDual V →L[ℝ] FullDual V :=
  ContinuousLinearMap.precomp ℝ (headJ H hH)

noncomputable def Q (H : Set V) (hH : IsLowerSet H) : FullDual V →L[ℝ] FullDual V :=
  ContinuousLinearMap.precomp ℝ (tailJ H hH)

@[simp] theorem P_coe (H : Set V) (hH : IsLowerSet H) (x : FullDual V) (u : TestVector V) :
    P H hH x (u : J V) = x (TestVector.cut H u : J V) := by
  change x (headJ H hH (u : J V)) = _
  rw [headJ_coe]

@[simp] theorem Q_coe (H : Set V) (hH : IsLowerSet H) (x : FullDual V) (u : TestVector V) :
    Q H hH x (u : J V) = x (TestVector.cut Hᶜ u : J V) := by
  change x (tailJ H hH (u : J V)) = _
  rw [tailJ_coe]

 theorem Q_eq_sub (H : Set V) (hH : IsLowerSet H) (x : FullDual V) : Q H hH x = x - P H hH x := by
  ext u
  change x (u - headJ H hH u) = x u - x (headJ H hH u)
  exact map_sub x _ _

 theorem norm_P_le (H : Set V) (hH : IsLowerSet H) (x : FullDual V) : ‖P H hH x‖ ≤ ‖x‖ := by
  apply (P H hH x).opNorm_le_bound (norm_nonneg _)
  intro u
  exact (x.le_opNorm (headJ H hH u)).trans
    (mul_le_mul_of_nonneg_left (norm_headJ_le H hH u) (norm_nonneg _))

 theorem norm_Q_le (H : Set V) (hH : IsLowerSet H) (x : FullDual V) : ‖Q H hH x‖ ≤ ‖x‖ := by
  apply (Q H hH x).opNorm_le_bound (norm_nonneg _)
  intro u
  exact (x.le_opNorm (tailJ H hH u)).trans
    (mul_le_mul_of_nonneg_left (norm_tailJ_le H hH u) (norm_nonneg _))

 theorem annihilates_P (H : Set V) (hH : IsLowerSet H) (x : FullDual V) :
    Annihilates (P H hH x) Hᶜ := by
  intro u hu
  simp only [P_coe, TestVector.cut_eq_zero_of_compl hu,
    UniformSpace.Completion.coe_zero, map_zero]

 theorem annihilates_Q (H : Set V) (hH : IsLowerSet H) (x : FullDual V) :
    Annihilates (Q H hH x) H := by
  intro u hu
  rw [Q_eq_sub]
  simp only [_root_.sub_apply, P_coe, TestVector.cut_eq_self hu, sub_self]

 theorem P_finite_eq_sum (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : FullDual V) :
    P (H : Set V) hH x = ∑ v ∈ H, x (e v) • eStar v := by
  apply ContinuousLinearMap.ext
  intro u
  refine UniformSpace.Completion.induction_on u (isClosed_eq
    (P (H : Set V) hH x).continuous (map_continuous _)) ?_
  intro f
  rw [P_coe, ← rawRestriction_apply, TestVector.cut_finite_eq_sum]
  simp only [map_sum, map_smul, smul_eq_mul, _root_.sum_apply,
    _root_.smul_apply, eStar_coe, rawRestriction_apply]
  apply Finset.sum_congr rfl
  intro v hv
  change f v * x (e v) = x (e v) * f v
  ring

 theorem P_eStar (H : Set V) (hH : IsLowerSet H) (v : V) :
    P H hH (eStar v) = if v ∈ H then eStar v else 0 := by
  apply ContinuousLinearMap.ext
  intro u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (P H hH (eStar v)).continuous (map_continuous _)) ?_
  intro f
  by_cases hv : v ∈ H <;> simp [hv]

 theorem P_finite_mem_span (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : FullDual V) :
    P (H : Set V) hH x ∈ Submodule.span ℝ (Set.range (eStar (V := V))) := by
  rw [P_finite_eq_sum]
  exact Submodule.sum_mem _ (fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,rfl⟩))

/-- Finite ancestral heads preserve the coordinate completion by their explicit
finite-coordinate formula; tails then do so by subtraction. -/
noncomputable def PX (H : Finset V) (hH : IsLowerSet (H : Set V)) : X V →L[ℝ] X V :=
  ((P (H : Set V) hH).comp (coordinateSubspace V).subtypeL).codRestrict (coordinateSubspace V)
    (fun x => Submodule.le_topologicalClosure _ (P_finite_mem_span H hH x))

noncomputable def QX (H : Finset V) (hH : IsLowerSet (H : Set V)) : X V →L[ℝ] X V :=
  ContinuousLinearMap.id ℝ (X V) - PX H hH

@[simp] theorem PX_val (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : X V) :
    (PX H hH x : FullDual V) = P (H : Set V) hH x := rfl

@[simp] theorem QX_val (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : X V) :
    (QX H hH x : FullDual V) = Q (H : Set V) hH x := by
  exact (Q_eq_sub (H : Set V) hH x).symm

 theorem norm_PX_le (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : X V) :
    ‖PX H hH x‖ ≤ ‖x‖ := norm_P_le (H : Set V) hH x

 theorem norm_QX_le (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : X V) :
    ‖QX H hH x‖ ≤ ‖x‖ := by
  change ‖(QX H hH x : FullDual V)‖ ≤ ‖(x : FullDual V)‖
  rw [QX_val]
  exact norm_Q_le (H : Set V) hH x

 theorem finite_span_support {z : FullDual V}
    (hz : z ∈ Submodule.span ℝ (Set.range (eStar (V := V)))) :
    ∃ S : Finset V, ∀ H : Finset V, ∀ hH : IsLowerSet (H : Set V),
      S ⊆ H → P (H : Set V) hH z = z := by
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  refine ⟨c.support, ?_⟩
  intro H hH hSH
  change P (H : Set V) hH (∑ v ∈ c.support, c v • eStar v) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_smul, P_eStar, ite_eq_left (show v ∈ (H : Set V) from hSH hv)]

/-- Coordinate density plus tail contractivity gives arbitrarily close finite
ancestral heads in the general coordinate completion. -/
 theorem exists_head_approx (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (x : X V) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset V, ∃ hH : IsLowerSet (H : Set V), ‖x - PX H hH x‖ < ε := by
  have hx : (x : FullDual V) ∈ closure
      (Submodule.span ℝ (Set.range (eStar (V := V))) : Set (FullDual V)) := x.property
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨S,hS⟩ := finite_span_support hz
  obtain ⟨H,hSH,hH⟩ := exists_finite_lower_hull hAnc S
  have hzP := hS H hH hSH
  have hzQ : Q (H : Set V) hH z = 0 := by rw [Q_eq_sub, hzP, sub_self]
  have hn := norm_Q_le (H : Set V) hH ((x : FullDual V)-z)
  rw [map_sub, hzQ, sub_zero, Q_eq_sub] at hn
  refine ⟨H,hH, ?_⟩
  change ‖(x : FullDual V) - P (H : Set V) hH x‖ < ε
  exact hn.trans_lt (by simpa only [dist_eq_norm] using hclose)

/-- Restriction to finitely many coordinate values. Its kernel is the particular
closed finite-codimensional subspace used for the modulus. -/
noncomputable def finiteCoordinates (H : Finset V) : X V →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun v : H =>
    ((ContinuousLinearMap.apply ℝ ℝ) (e (V := V) (v : V))).comp (coordinateSubspace V).subtypeL)

@[simp] theorem finiteCoordinates_apply (H : Finset V) (x : X V) (v : H) :
    finiteCoordinates H x v = (x : FullDual V) (e v) := rfl

 theorem finiteCoordinates_kernel_finite (H : Finset V) :
    FiniteDimensional ℝ ((X V) ⧸ (finiteCoordinates H).toLinearMap.ker) := by
  exact Module.Finite.equiv (finiteCoordinates H).toLinearMap.quotKerEquivRange.symm

 theorem P_eq_zero_of_mem_ker_coordinates (H : Finset V) (hH : IsLowerSet (H : Set V))
    {y : X V} (hy : y ∈ (finiteCoordinates H).toLinearMap.ker) :
    P (H : Set V) hH (y : FullDual V) = 0 := by
  have hh : finiteCoordinates H y = 0 := hy
  rw [P_finite_eq_sum]
  apply Finset.sum_eq_zero
  intro v hv
  have hz := congrFun hh ⟨v,hv⟩
  simp only [finiteCoordinates_apply, Pi.zero_apply] at hz
  rw [hz, zero_smul]

 theorem annihilates_of_mem_ker_coordinates (H : Finset V) (hH : IsLowerSet (H : Set V))
    {y : X V} (hy : y ∈ (finiteCoordinates H).toLinearMap.ker) :
    Annihilates (y : FullDual V) (H : Set V) := by
  have he : Q (H : Set V) hH y = y := by
    rw [Q_eq_sub, P_eq_zero_of_mem_ker_coordinates H hH hy, sub_zero]
  rw [← he]
  exact annihilates_Q (H : Set V) hH y

 theorem paired_X (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Finset V) (hH : IsLowerSet (H : Set V)) (x y : X V)
    (hx : x = PX H hH x) (hy : y = QX H hH y) :
    Real.sqrt (‖x‖^2 + ‖y‖^2/12) ≤ (‖x+y‖ + ‖x-y‖)/2 := by
  have hx' : Annihilates (x : FullDual V) (H : Set V)ᶜ := by
    nth_rw 1 [hx]
    exact annihilates_P (H : Set V) hH x
  have hy' : Annihilates (y : FullDual V) (H : Set V) := by
    nth_rw 1 [hy]
    rw [QX_val]
    exact annihilates_Q (H : Set V) hH y
  exact paired_estimate hF hAnc (H : Set V) hH x y hx' hy'

 theorem paired_X_two_parameters (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Finset V) (hH : IsLowerSet (H : Set V)) (x y : X V)
    (hx : x = PX H hH x) (hy : y = QX H hH y)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (‖x‖+s*t*‖y‖)/Real.sqrt (1+12*s^2) ≤ (‖x+t•y‖+‖x-t•y‖)/2 := by
  have hx' : Annihilates (x : FullDual V) (H : Set V)ᶜ := by
    nth_rw 1 [hx]
    exact annihilates_P (H : Set V) hH x
  have hy' : Annihilates (y : FullDual V) (H : Set V) := by
    nth_rw 1 [hy]
    rw [QX_val]
    exact annihilates_Q (H : Set V) hH y
  exact paired_two_parameters hF hAnc (H : Set V) hH x y hx' hy' s t hs ht

end Projections

section CoordinateStructure
variable {V : Type} [PartialOrder V]

noncomputable def eX (v : V) : X V :=
  ⟨eStar v, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v,rfl⟩)⟩

@[simp] theorem eX_val (v : V) : (eX v : FullDual V) = eStar v := rfl
@[simp] theorem norm_eX (v : V) : ‖eX v‖ = 1 := norm_eStar v

 theorem linearIndependent_eStar : LinearIndependent ℝ (eStar (V := V)) := by
  apply linearIndependent_iff'.mpr
  intro S a h v hv
  have hh := congrArg (fun x : FullDual V => x (e v)) h
  simp only [_root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, eStar_e, _root_.zero_apply, mul_ite, mul_one, mul_zero] at hh
  simpa [hv] using hh

 theorem linearIndependent_eX : LinearIndependent ℝ (eX (V := V)) :=
  LinearIndependent.of_comp (coordinateSubspace V).subtype linearIndependent_eStar

 theorem not_finiteDimensional_X [Infinite V] : ¬FiniteDimensional ℝ (X V) := by
  intro h
  let := h
  have : Finite V := linearIndependent_eX.finite
  exact Infinite.not_finite (inferInstance : Finite V)

instance [Nonempty V] : Nontrivial (X V) := by
  obtain ⟨v⟩ := ‹Nonempty V›
  apply nontrivial_iff.mpr
  refine ⟨eX v,0, ?_⟩
  intro he
  have hval : eStar v = 0 := congrArg Subtype.val he
  have hh := congrArg (fun z : FullDual V => z (e v)) hval
  simp at hh

instance : CompleteSpace (X V) := by
  let : IsClosed (coordinateSubspace V : Set (FullDual V)) :=
    Submodule.isClosed_topologicalClosure _
  exact IsClosed.completeSpace_coe

 theorem separable_X [Countable V] : TopologicalSpace.SeparableSpace (X V) := by
  have hs : TopologicalSpace.IsSeparable (Set.range (eStar (V := V))) :=
    (Set.countable_range _).isSeparable
  have hc := (hs.span (R := ℝ)).closure
  exact hc.separableSpace

end CoordinateStructure

end

end ForestSpace

end OAI
