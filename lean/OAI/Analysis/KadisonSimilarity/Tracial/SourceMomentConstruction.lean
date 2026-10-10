import OAI.Analysis.KadisonSimilarity.Tracial.SourceIncrementalPatching

namespace OAI

/-! Maximal partial unitaries for ambient moments, ordered inside the source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance momentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

/-- Ambient moment bounds persist under trace-norm limits in the source. -/
theorem source_momentBound_limit {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra) {K N : ℕ} {b : ℝ → ℝ}
    {v : ℕ → PartialUnitary R.toStarSubalgebra} {w : PartialUnitary R.toStarSubalgebra}
    (h : GNSTendsto (vectorPositiveFunctional R υ.vector)
      (fun n => (v n : R.toStarSubalgebra)) atTop (w : R.toStarSubalgebra))
    (hb : ContinuousAt b ((υ.trace (coordinateInclusion hRM w.support)).re))
    (hv : ∀ n, MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N) b
      (SourcePartialUnitary.map (coordinateInclusion hRM) (v n))) :
    MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N) b
      (SourcePartialUnitary.map (coordinateInclusion hRM) w) := by
  let φ := coordinateInclusion hRM
  let τ := vectorPositiveFunctional M υ.vector
  have ht : GNSTendsto τ
      (fun n => (SourcePartialUnitary.map φ (v n) : M.toStarSubalgebra)) atTop
      (SourcePartialUnitary.map φ w : M.toStarSubalgebra) := source_gns_tendsto υ hRM h
  apply momentBound_limit F τ υ.trace_mul_comm
    (v := fun n => SourcePartialUnitary.map φ (v n)) (w := SourcePartialUnitary.map φ w)
    υ.trace_one ht
  · rw [SourcePartialUnitary.support_map]
    exact hb
  · exact hv

include hfactor hdiff hirr in
/-- Partial unitaries of every trace below one satisfy prescribed ambient
moment bounds. The maximality argument is carried out in the source. -/
theorem exists_source_partial_unitary_moments {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, υ.trace (F i) = 0)
    {K N : ℕ} (hK : 0 < K) {δ T : ℝ} (hδ : 0 < δ) (hT0 : 0 ≤ T) (hT : T < 1) :
    ∃ v : PartialUnitary R.toStarSubalgebra,
      (υ.trace (coordinateInclusion hRM v.support)).re = T ∧
      MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N)
        (expBudget δ (patchRate N T)) (SourcePartialUnitary.map (coordinateInclusion hRM) v) := by
  let φ := coordinateInclusion hRM
  let τR := vectorPositiveFunctional R υ.vector
  let τM := vectorPositiveFunctional M υ.vector
  have htrR : ∀ a b, τR (a * b) = τR (b * a) := (restrictedTrace υ hRM).trace_mul_comm
  have h1R : τR 1 = 1 := vectorPositiveFunctional_one R υ.vector υ.norm_vector
  have hfR (a : R.toStarSubalgebra) (ha : τR (star a * a) = 0) : a = 0 := by
    apply (restrictedTrace υ hRM).separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace (restrictedTrace υ hRM) a a).trans ha)
  let b := expBudget δ (patchRate N T)
  let P : PartialUnitary R.toStarSubalgebra → Prop := fun v =>
    (τR v.support).re ≤ T ∧ MomentBound F τM (K := K) (N := N) b (SourcePartialUnitary.map φ v)
  have h0 : P 0 := by
    constructor
    · simpa only [PartialUnitary.support_zero, map_zero, Complex.zero_re] using hT0
    · rw [SourcePartialUnitary.map_zero]
      exact momentBound_zero F τM (by dsimp only [b]; rw [expBudget_zero])
  have hclosed : ∀ (a : ℕ → PartialUnitary R.toStarSubalgebra) (s : PartialUnitary R.toStarSubalgebra),
      Monotone a → (∀ n, P (a n)) →
      GNSTendsto τR (fun n => (a n : R.toStarSubalgebra)) atTop (s : R.toStarSubalgebra) → P s := by
    intro a s _ha hPa ht
    constructor
    · have hs := (ht.star τR htrR).mul τR htrR ht 1
        (fun n => by simpa only [norm_star] using (a n).norm_le_one)
      have htrace := (Complex.continuous_re.tendsto _).comp (trace_tendsto_of_gns τR h1R hs)
      exact le_of_tendsto htrace (Filter.Eventually.of_forall (fun n => (hPa n).1))
    · exact source_momentBound_limit υ hRM F ht
        (expBudget_continuous δ _).continuousAt (fun n => (hPa n).2)
  obtain ⟨v, hv⟩ := PartialUnitary.maximal_of_sequentially_closed
    (concretePredualEquiv R) τR (HochschildSakai.mul_hasPreadjoint (concretePredualEquiv R))
    (vectorPositiveFunctional_normal R υ.vector) htrR hfR P h0 hclosed
  have hs0 : 0 ≤ (τR v.support).re := (τR.map_nonneg v.support_proj.nonneg).1
  have hb : 0 ≤ b ((τR v.support).re) := expBudget_nonneg hδ.le
    ((by norm_num : (0 : ℝ) ≤ 1).trans (patchRate_ge_one hT)) hs0
  refine ⟨v, ?_, hv.1.2⟩
  by_contra hne
  have hsT : (τR v.support).re < T := lt_of_le_of_ne hv.1.1 hne
  obtain ⟨w, horth, hwpos, hwt, hwm⟩ := exists_source_incremental_patch υ hRM hfactor hdiff hirr
    F hF hFτ hK v hb hv.1.2 (hsT.trans hT)
    (patchTolerance_pos hδ (Nat.cast_nonneg N)) (sub_pos.mpr hsT)
  change 0 < (τR w.support).re at hwpos
  change (τR w.support).re < T - (τR v.support).re at hwt
  let z := v.orthogonalSum w horth
  have hzs : (τR z.support).re = (τR v.support).re + (τR w.support).re := by
    rw [PartialUnitary.support_orthogonalSum, map_add, Complex.add_re]
  have hz : P z := by
    constructor
    · rw [hzs]; linarith
    · intro a ha
      have hh := hwm a ha
      have hr := expBudget_patch_bound hδ.le (Nat.cast_nonneg N) hT hs0 hv.1.1 hwpos.le
      change ‖τM (mixedEval F (SourcePartialUnitary.map φ z) a.1 a.2.val)‖ ≤
        b ((τR z.support).re)
      rw [hzs]
      exact hh.trans hr
  have hvz : v ≤ z := v.le_orthogonalSum w horth
  have hzv : z ≤ v := hv.2 hz hvz
  have he : z = v := le_antisymm hzv hvz
  rw [he] at hzs
  linarith

end KadisonSimilarity

end

end OAI
