import OAI.Analysis.TracialSplitting.SmallProjections

namespace OAI

noncomputable section

universe uA uD uI

open Filter Topology

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section TraceFamilyRestriction

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

lemma familyTwoNorm_le_uniform (a : D) : familyTwoNorm τ a ≤ uniformTwoNorm a := by
  apply ciSup_le
  intro i
  exact le_ciSup (familyTwoNorm_bdd (fun t : TracialState D => t) a) (τ i)

lemma familyHalvingError_le_uniform (p x : D) :
    familyTraceNorm τ (p*x-(1/2 : ℂ) • x) ≤ uniformHalvingError p x := by
  have hb : BddAbove (Set.range fun t : TracialState D =>
      ‖t.functional (p*x)-(1/2 : ℂ)*t.functional x‖) := by
    refine ⟨‖p*x-(1/2 : ℂ) • x‖,?_⟩
    rintro _ ⟨t,rfl⟩
    simpa only [map_sub,map_smul,smul_eq_mul] using
      trace_norm_le_norm t (p*x-(1/2 : ℂ) • x)
  apply ciSup_le
  intro i
  simpa only [map_sub,map_smul,smul_eq_mul,uniformHalvingError] using le_ciSup hb (τ i)

end TraceFamilyRestriction

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Nontrivial A] [TopologicalSpace.SeparableSpace A]

variable (U : Ultrafilter ℕ) [Nonempty (TracialState A)]

theorem rr_central_splitting_from_diagonals
    (hfree : (U : Filter ℕ) ≤ atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U))
    (diagonals : ∀ (K : Finset (unitary A)) (μ : ℝ), 0 < μ → Nonempty (PositiveDiagonal A K μ)) :
    ∃ p : FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U,
      IsStarProjection p ∧ ∀ x : UniformTracialCompletion (fun τ : TracialState A => τ),
        p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x =
          familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x * p ∧
        ∀ s : ℕ → TracialState A,
          (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
            (p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x) =
          (1/2 : ℂ) *
          (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
            (familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x) := by
  classical
  let τ := fun t : TracialState A => t
  let D := FamilyUltrapower (completionTrace τ) U
  let j : A →⋆ₐ[ℂ] D := (familyUltrapowerMap (completionTrace τ) U).comp (completionMap τ)
  let σ := familyLimitTrace (completionTrace τ) U
  have hTD : Nonempty (TracialState D) := ⟨σ (fun _ => Classical.arbitrary _)⟩
  apply completion_central_splitting_of_finite_stages τ U hfree
  intro K ε hε
  obtain ⟨P,hP,htest⟩ := finite_set_splitting_from_diagonals j hRR hTD
    (fun _ hδ => small_full_projections hsimple hinf j hRR hTD hδ) diagonals K ε hε
  refine ⟨P,hP,?_⟩
  intro u hu
  exact ⟨(familyTwoNorm_le_uniform σ _).trans_lt (htest u hu).1,
    (familyHalvingError_le_uniform σ P (j (u : A))).trans_lt (htest u hu).2⟩

end

open MeasureTheory MeasureTheory.Measure

open scoped TensorProduct

section CompactUnitaryDiagonal

variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma continuous_tensorPair : Continuous (fun p : A × A => tensorPair p.1 p.2) := by
  change Continuous (fun p : A × A => PiTensorProduct.tprodL ℂ ![p.1,p.2])
  apply (PiTensorProduct.tprodL ℂ).cont.comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

lemma compact_unitary_of_finiteDimensional [FiniteDimensional ℂ A] :
    CompactSpace (unitary A) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  apply (Metric.isBounded_closedBall (x := (0 : A)) (r := 1)).subset
  intro u hu
  simpa only [Metric.mem_closedBall,dist_zero_right] using (CStarRing.norm_of_mem_unitary hu).le

local instance (K : Finset (unitary A)) : DecidableEq K := Classical.decEq K

noncomputable def diagonalTestCoordinate (K : Finset (unitary A)) (x : K) :
    (⨂[ℂ] (_ : Fin 2), A) →L[ℝ] DiagonalTestSpace A K := by
  classical
  exact (ContinuousLinearMap.single ℝ (fun _ : K => ⨂[ℂ] (_ : Fin 2), A) x).prod 0

omit [Nontrivial A] in
lemma diagonalTestCoordinate_apply (K : Finset (unitary A)) (x : K)
    (t : ⨂[ℂ] (_ : Fin 2), A) :
    diagonalTestCoordinate K x t = (Pi.single x t,0) := rfl

omit [Nontrivial A] in
lemma diagonalTestAtom_unitary_sum (K : Finset (unitary A)) (u : unitary A) :
    diagonalTestAtom K (u : A) = diagonalTestPoint K +
      ∑ x : K, diagonalTestCoordinate K x
        (tensorPair ((x.val : A)*(u : A)) (star (u : A)) -
          tensorPair (u : A) (star (u : A)*(x.val : A))) := by
  classical
  apply Prod.ext
  · simp only [diagonalTestAtom,diagonalTestPoint,Prod.fst_add,Prod.fst_sum,
      diagonalTestCoordinate_apply,zero_add]
    ext x
    simp
  · simp only [diagonalTestAtom,diagonalTestPoint,Prod.snd_add,Prod.snd_sum,
      diagonalTestCoordinate_apply,Finset.sum_const_zero,add_zero,
      Unitary.mul_star_self_of_mem u.property]

variable [CompactSpace (unitary A)]

theorem diagonalDualBound_of_compactUnitary (K : Finset (unitary A)) :
    DiagonalDualBound K := by
  classical
  let : MeasurableSpace (unitary A) := borel (unitary A)
  let : BorelSpace (unitary A) := ⟨rfl⟩
  let μ : Measure (unitary A) := haarMeasure ⊤
  let : IsProbabilityMeasure μ := ⟨by
    change haarMeasure ⊤ Set.univ = 1
    simpa only [TopologicalSpace.PositiveCompacts.coe_top] using haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (unitary A)))⟩
  intro f c hf
  let g (x : K) (u : unitary A) : ℝ :=
    f (diagonalTestCoordinate K x (tensorPair ((x.val : A)*(u : A)) (star (u : A))))
  have hg (x : K) : Continuous (g x) := by
    exact f.continuous.comp ((diagonalTestCoordinate K x).continuous.comp
      (continuous_tensorPair.comp ((continuous_const.mul continuous_subtype_val).prodMk
        continuous_subtype_val.star)))
  have hint (x : K) : Integrable (g x) μ :=
    (hg x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint' (x : K) : Integrable (fun u => g x (x.val⁻¹ * u)) μ :=
    ((hg x).comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hd (u : unitary A) : f (diagonalTestAtom K (u : A)) =
      f (diagonalTestPoint K) + ∑ x : K, (g x u - g x (x.val⁻¹ * u)) := by
    rw [diagonalTestAtom_unitary_sum,map_add,_root_.map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [map_sub,map_sub]
    congr 1
    dsimp [g]
    congr 2
    simp only [← Unitary.star_eq_inv,Unitary.coe_star,star_mul,star_star,
      ← mul_assoc,Unitary.mul_star_self_of_mem x.val.property,one_mul]
  have hfun : (fun u : unitary A => f (diagonalTestAtom K (u : A))) =
      (fun u => f (diagonalTestPoint K) + ∑ x : K, (g x u - g x (x.val⁻¹*u))) := funext hd
  have hi : Integrable (fun u : unitary A => f (diagonalTestAtom K (u : A))) μ := by
    rw [hfun]
    exact (integrable_const _).add (integrable_finsetSum _ fun x _ => (hint x).sub (hint' x))
  have he : (∫ u : unitary A, f (diagonalTestAtom K (u : A)) ∂μ) = f (diagonalTestPoint K) := by
    have hiSum : Integrable (fun u => ∑ x : K, (g x u - g x (x.val⁻¹*u))) μ :=
      integrable_finsetSum Finset.univ (fun x _ => (hint x).sub (hint' x))
    rw [hfun,integral_add (integrable_const _) hiSum,integral_const]
    simp only [probReal_univ,one_smul]
    rw [integral_finsetSum Finset.univ (f := fun x : K => fun u => g x u - g x (x.val⁻¹*u)) (fun x _ => (hint x).sub (hint' x))]
    have hz (x : K) : (∫ u : unitary A, g x u - g x (x.val⁻¹*u) ∂μ) = 0 := by
      rw [integral_sub (hint x) (hint' x),integral_mul_left_eq_self,sub_self]
    simp only [hz,Finset.sum_const_zero,add_zero]
  rw [← he]
  calc
    _ ≤ ∫ _u : unitary A, c ∂μ := integral_mono hi (integrable_const _) (fun u =>
      hf _ ((CStarRing.norm_coe_unitary u).le))
    _ = c := by simp

end CompactUnitaryDiagonal

theorem positiveDiagonal_of_finiteDimensional {A : Type uA} [CStarAlgebra A]
    [Nontrivial A] [FiniteDimensional ℂ A] (K : Finset (unitary A))
    {ε : ℝ} (hε : 0 < ε) : Nonempty (PositiveDiagonal A K ε) := by
  let := compact_unitary_of_finiteDimensional (A := A)
  exact positiveDiagonal_of_dualBound K (diagonalDualBound_of_compactUnitary K) hε

end CurrentMain

end

end OAI
