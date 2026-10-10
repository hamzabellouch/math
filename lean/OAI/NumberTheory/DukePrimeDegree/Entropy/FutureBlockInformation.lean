import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureInformation

namespace OAI

/-! # Iterated whole-future masses

The same normalization factor occurs for every future index. In
particular every later whole-future atom has positive finite mass once
the zero-future atom does, despite the nonintegrable possible height.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

lemma remainingFutureAtom_shift_index
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (m : ℕ) (x : X n) :
    (c.rootDilation ell 1) ⁻¹' c.remainingFutureAtom ell hell Q m
      (rightAction x (diagonalOneParameter ell hell (-1))) =
      c.remainingFutureAtom ell hell Q (m+1) x := by
  ext u
  simp only [mem_preimage,remainingFutureAtom,Set.mem_ofPred_eq,
    c.remaining_orbit_diagonal ell hell]
  simp only [←Nat.add_assoc,Function.iterate_succ_apply]

theorem ae_remainingTimeProduct_futureAtom_index
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q) (m : ℕ) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell (-1)))
        (c.remainingFutureAtom ell hell Q m
          (rightAction x (diagonalOneParameter ell hell (-1)))) =
      (c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1))⁻¹ *
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q (m+1) x) := by
  filter_upwards [c.ae_remainingTimeProduct_diagonal d hP hf μ hA ell hell (-1)] with x hx
  rw [hx]
  simp only [neg_neg]
  rw [anchorNormalize,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (c.rootDilation ell 1).measurable
      (c.measurableSet_remainingFutureAtom hf ell hell Q hQ m _),
    c.remainingFutureAtom_shift_index ell hell Q m x,
    Measure.map_apply (c.rootDilation ell 1).measurable (c.cube_open 1).measurableSet]

theorem ae_all_futureMass_pos_ne_top
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    ∀ᵐ x ∂μ, ∀ m : ℕ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x) ≠ ∞ := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let M := fun m x => c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x)
  let C := fun x => c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hC := c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA
  apply ae_all_iff.mpr
  intro m
  induction m with
  | zero =>
    filter_upwards [hmass] with x hx
    exact ⟨hx.1,ne_of_lt (hx.2.trans_lt ENNReal.one_lt_top)⟩
  | succ m ih =>
    filter_upwards [hT.quasiMeasurePreserving.ae ih,hC,
      c.ae_remainingTimeProduct_futureAtom_index d hP hf μ hA ell hell Q hQ m]
      with x hx hc hcov
    have he : M (m+1) x=C x*M m (T x) := by
      change M m (T x)=(C x)⁻¹*M (m+1) x at hcov
      rw [hcov,←mul_assoc,ENNReal.mul_inv_cancel hc.1.ne' hc.2,one_mul]
    change 0 < M (m+1) x ∧ M (m+1) x ≠ ∞
    rw [he]
    exact ⟨ENNReal.mul_pos hc.1.ne' hx.1.ne',ENNReal.mul_ne_top hc.2 hx.2⟩

theorem futureBlockInformation_integrable_integral
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    (N : ℕ) :
    let J := fun x => -Real.log
      (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q N x)).toReal
    Integrable J μ ∧ (∫ x, J x ∂μ) = (N : ℝ) *
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let M := fun m x => c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x)
  let C := fun x => c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)
  let J := fun m x => -Real.log (M 0 x/M m x).toReal
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hM := c.ae_all_futureMass_pos_ne_top d hP hf μ hA ell hell Q hQ hmass
  have hC := c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA
  have hI := c.remainingFutureInformation_integrable_integral d hP hf μ hA ell hell Q hQ hmass
  change Integrable (J 1) μ ∧ (∫ x, J 1 x ∂μ) = _ at hI
  change Integrable (J N) μ ∧ (∫ x, J N x ∂μ) = _
  induction N with
  | zero =>
    have hz : J 0 =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hM] with x hx
      change -Real.log (M 0 x/M 0 x).toReal=0
      rw [ENNReal.toReal_div,div_self ((ENNReal.toReal_pos (hx 0).1.ne' (hx 0).2).ne'),Real.log_one,neg_zero]
    refine ⟨(integrable_zero _ _ _).congr hz.symm,?_⟩
    rw [integral_congr_ae hz,integral_zero,Nat.cast_zero,zero_mul]
  | succ N ih =>
    have he : J (N+1) =ᵐ[μ] fun x => J 1 x+J N (T x) := by
      filter_upwards [hM,hC,
        c.ae_remainingTimeProduct_futureAtom_index d hP hf μ hA ell hell Q hQ 0,
        c.ae_remainingTimeProduct_futureAtom_index d hP hf μ hA ell hell Q hQ N]
        with x hx hc hzero hN
      change M 0 (T x)=(C x)⁻¹*M 1 x at hzero
      change M N (T x)=(C x)⁻¹*M (N+1) x at hN
      have hr : (M 0 (T x)/M N (T x)).toReal=(M 1 x/M (N+1) x).toReal := by
        rw [hzero,hN]
        simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_inv]
        have hc' : (C x).toReal ≠ 0 := (ENNReal.toReal_pos hc.1.ne' hc.2).ne'
        field_simp
      dsimp only [J]
      rw [hr]
      simp only [ENNReal.toReal_div]
      have ha : (M 0 x).toReal ≠ 0 := (ENNReal.toReal_pos (hx 0).1.ne' (hx 0).2).ne'
      have hb : (M 1 x).toReal ≠ 0 := (ENNReal.toReal_pos (hx 1).1.ne' (hx 1).2).ne'
      have hn : (M (N+1) x).toReal ≠ 0 := (ENNReal.toReal_pos (hx (N+1)).1.ne' (hx (N+1)).2).ne'
      rw [Real.log_div ha hn,Real.log_div ha hb,Real.log_div hb hn]
      ring
    have hiT : Integrable (fun x => J N (T x)) μ := hT.integrable_comp_of_integrable ih.1
    refine ⟨(hI.1.add hiT).congr he.symm,?_⟩
    have htint : (∫ x, J N (T x) ∂μ)=(∫ x, J N x ∂μ) := by
      have hmeas : AEStronglyMeasurable (J N) (μ.map T) := by
        rw [hT.map_eq]
        exact ih.1.aestronglyMeasurable
      rw [←integral_map hT.measurable.aemeasurable hmeas,hT.map_eq]
    rw [integral_congr_ae he,integral_add hI.1 hiT,htint,hI.2,ih.2]
    push_cast
    ring

end EliminationChain
end DukePrimeDegree

end

end OAI
