import OAI.Analysis.IrrationalRotation.Operators.LpOperatorExt
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.Fields

variable {X H ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}

def scalarVectorLp (v : H) : Lp ℂ 2 μ →L[ℂ] Lp H 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ v).compLpL 2 μ

theorem scalarVectorLp_ae (v : H) (f : Lp ℂ 2 μ) :
    scalarVectorLp (μ := μ) v f =ᵐ[μ] fun x => f x • v :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem scalarVectorLp_indicator (v : H) (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) :
    scalarVectorLp (μ := μ) v (indicatorConstLp 2 hs hμs (1 : ℂ)) =
      indicatorConstLp 2 hs hμs v := by
  apply Lp.ext
  filter_upwards [scalarVectorLp_ae v (indicatorConstLp 2 hs hμs (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs) (c := v)]
    with x hx hf hv
  rw [hx, hf, hv]
  by_cases hxs : x ∈ s <;> simp [hxs]

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [SecondCountableTopology X] [T2Space X] [IsFiniteMeasure μ] [μ.WeaklyRegular]

theorem closed_submodule_eq_top_of_continuous_basis
    (e : HilbertBasis ι ℂ H) (K : Submodule ℂ (Lp H 2 μ))
    (hK : IsClosed (K : Set (Lp H 2 μ)))
    (h : ∀ (i : ι) (a : C(X, ℂ)),
      scalarVectorLp (μ := μ) (e i) (ContinuousMap.toLp 2 μ ℂ a) ∈ K) :
    K = ⊤ := by
  have hi (i : ι) (f : Lp ℂ 2 μ) : scalarVectorLp (μ := μ) (e i) f ∈ K := by
    have hs : Set.range (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) → Lp ℂ 2 μ) ⊆
        (scalarVectorLp (μ := μ) (e i)) ⁻¹' (K : Set (Lp H 2 μ)) := by
      rintro _ ⟨a, rfl⟩
      exact h i a
    have hc := closure_minimal hs
      (hK.preimage (scalarVectorLp (μ := μ) (e i)).continuous)
    rw [(ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).closure_range]
      at hc
    exact hc (Set.mem_univ f)
  have hb (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (v : H) :
      indicatorConstLp 2 hs hμs v ∈ K := by
    let C : H →L[ℂ] Lp H 2 μ := indicatorConstLpCLM s hs hμs
    have hbasis : Set.range e ⊆ C ⁻¹' (K : Set (Lp H 2 μ)) := by
      rintro _ ⟨i, rfl⟩
      change indicatorConstLp 2 hs hμs (e i) ∈ K
      rw [← scalarVectorLp_indicator]
      exact hi i _
    have hspan : (Submodule.span ℂ (Set.range e) : Set H) ⊆ C ⁻¹' K := by
      change Submodule.span ℂ (Set.range e) ≤ K.comap C.toLinearMap
      exact Submodule.span_le.mpr hbasis
    have hc := closure_minimal hspan (hK.preimage C.continuous)
    change ((Submodule.span ℂ (Set.range e)).topologicalClosure : Set H) ⊆ _ at hc
    rw [e.dense_span] at hc
    exact hc Submodule.mem_top
  apply top_unique
  intro f _
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun g => g ∈ K) _ _ hK f
  · intro v s hs hμs
    exact hb s hs hμs.ne v
  · intro f g hf hg hdis hfK hgK
    exact K.add_mem hfK hgK

end Invariant233.Fields

end

end OAI
