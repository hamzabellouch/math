import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltralimitSize

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {ι : Type*} {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)] [∀ i, Nontrivial (D i)]

def boundedProductEval (i : ι) : lp D ∞ →⋆ₐ[ℂ] D i where
  toFun u := u i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def boundedProductPositiveEval (i : ι) (a : Positive (lp D ∞)) : Positive (D i) :=
  Positive.map (boundedProductEval i).toNonUnitalStarAlgHom a

lemma boundedProductPositiveEval_add (i : ι) (a b : Positive (lp D ∞)) :
    boundedProductPositiveEval i (Positive.add a b) =
      Positive.add (boundedProductPositiveEval i a) (boundedProductPositiveEval i b) :=
  Subtype.ext (map_add (boundedProductEval i) a.1 b.1)

lemma boundedProductPositiveEval_smul (i : ι) (r : ℝ≥0) (a : Positive (lp D ∞)) :
    boundedProductPositiveEval i (Positive.smul r a) =
      Positive.smul r (boundedProductPositiveEval i a) := by
  apply Subtype.ext
  rfl

variable (T : ∀ i, PositiveQuasitrace (D i)) (U : Ultrafilter ι)
variable (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1)

def quasitraceUltraPositive (a : Positive (lp D ∞)) : ℝ :=
  limUnder (U : Filter ι) (fun i => T i (boundedProductPositiveEval i a))

include hunit

lemma quasitraceUltraPositive_tendsto (a : Positive (lp D ∞)) :
    Tendsto (fun i => T i (boundedProductPositiveEval i a)) (U : Filter ι)
      (nhds (quasitraceUltraPositive T U a)) := by
  apply tendsto_nhds_limUnder
  let g : ι → ℝ := fun i => T i (boundedProductPositiveEval i a)
  have hg (i : ι) : g i ∈ Set.Icc 0 ‖a.1‖ := by
    refine ⟨(T i).nonneg _, ?_⟩
    have h := (T i).le_add_norm (boundedProductPositiveEval i a) Positive.zero
    rw [(T i).map_zero, hunit i, zero_add, mul_one] at h
    have hn : ‖(boundedProductPositiveEval i a).1-Positive.zero.1‖ ≤ ‖a.1‖ := by
      change ‖a.1 i-(0 : D i)‖ ≤ ‖a.1‖
      rw [sub_zero]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero a.1 i
    exact h.trans hn
  obtain ⟨r,_,hr⟩ := isCompact_Icc.ultrafilter_le_nhds' (U.map g)
    (show Set.Icc 0 ‖a.1‖ ∈ U.map g from by
      change {i | g i ∈ Set.Icc 0 ‖a.1‖} ∈ U
      exact Filter.Eventually.of_forall hg)
  exact ⟨r,hr⟩

lemma quasitraceUltraPositive_nonneg (a : Positive (lp D ∞)) :
    0 ≤ quasitraceUltraPositive T U a :=
  ge_of_tendsto (quasitraceUltraPositive_tendsto T U hunit a)
    (Filter.Eventually.of_forall fun i => (T i).nonneg _)

lemma quasitraceUltraPositive_zero : quasitraceUltraPositive T U Positive.zero = 0 := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto T U hunit Positive.zero)
  have he (i : ι) : boundedProductPositiveEval i (Positive.zero : Positive (lp D ∞)) = Positive.zero :=
    Subtype.ext rfl
  simp only [he,PositiveQuasitrace.map_zero]
  exact tendsto_const_nhds

lemma quasitraceUltraPositive_one : quasitraceUltraPositive T U ⟨1,zero_le_one⟩ = 1 := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto T U hunit ⟨1,zero_le_one⟩)
  have he (i : ι) : boundedProductPositiveEval i (⟨1,zero_le_one⟩ : Positive (lp D ∞)) = ⟨1,zero_le_one⟩ :=
    Subtype.ext rfl
  simp only [he,hunit]
  exact tendsto_const_nhds

lemma quasitraceUltraPositive_add (a b : Positive (lp D ∞)) (hab : Commute a.1 b.1) :
    quasitraceUltraPositive T U (Positive.add a b) =
      quasitraceUltraPositive T U a+quasitraceUltraPositive T U b := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto T U hunit (Positive.add a b))
  have he (i : ι) : T i (boundedProductPositiveEval i (Positive.add a b)) =
      T i (boundedProductPositiveEval i a)+T i (boundedProductPositiveEval i b) := by
    rw [boundedProductPositiveEval_add]
    apply (T i).map_add_commute
    exact hab.map (boundedProductEval i)
  simp only [he]
  exact (quasitraceUltraPositive_tendsto T U hunit a).add
    (quasitraceUltraPositive_tendsto T U hunit b)

lemma quasitraceUltraPositive_smul (r : ℝ≥0) (a : Positive (lp D ∞)) :
    quasitraceUltraPositive T U (Positive.smul r a) = (r : ℝ)*quasitraceUltraPositive T U a := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto T U hunit (Positive.smul r a))
  have he (i : ι) : T i (boundedProductPositiveEval i (Positive.smul r a)) =
      (r : ℝ)*T i (boundedProductPositiveEval i a) := by
    rw [boundedProductPositiveEval_smul, (T i).map_smul]
  simp only [he]
  exact (quasitraceUltraPositive_tendsto T U hunit a).const_mul _

lemma quasitraceUltraPositive_polar (u : lp D ∞) :
    quasitraceUltraPositive T U (Positive.starMul u) = quasitraceUltraPositive T U (Positive.mulStar u) := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto T U hunit (Positive.starMul u))
  have he (i : ι) : T i (boundedProductPositiveEval i (Positive.starMul u)) =
      T i (boundedProductPositiveEval i (Positive.mulStar u)) := (T i).polar (u i)
  simp only [he]
  exact quasitraceUltraPositive_tendsto T U hunit (Positive.mulStar u)

lemma quasitraceUltraPositive_monotone : Monotone (quasitraceUltraPositive T U) := by
  intro a b hab
  apply le_of_tendsto_of_tendsto (quasitraceUltraPositive_tendsto T U hunit a)
    (quasitraceUltraPositive_tendsto T U hunit b)
  filter_upwards [] with i
  apply (T i).monotone
  change boundedProductEval i a.1 ≤ boundedProductEval i b.1
  rw [← sub_nonneg, ← map_sub]
  exact map_nonneg (boundedProductEval i) (sub_nonneg.mpr hab)

def ultralimitPositiveQuasitrace : PositiveQuasitrace (lp D ∞) where
  toFun := quasitraceUltraPositive T U
  nonneg := quasitraceUltraPositive_nonneg T U hunit
  map_zero := quasitraceUltraPositive_zero T U hunit
  map_add_commute := quasitraceUltraPositive_add T U hunit
  map_smul := quasitraceUltraPositive_smul T U hunit
  polar := quasitraceUltraPositive_polar T U hunit
  monotone := quasitraceUltraPositive_monotone T U hunit

lemma ultralimitPositiveQuasitrace_metricSize (u : lp D ∞) :
    (ultralimitPositiveQuasitrace T U hunit).metricSize u = quasitraceUltraSize T U u := by
  have ht := (Real.continuous_rpow_const (by positivity : 0 ≤ (3:ℝ)⁻¹)).tendsto
    (quasitraceUltraPositive T U (Positive.starMul u))
  have hc := ht.comp (quasitraceUltraPositive_tendsto T U hunit (Positive.starMul u))
  exact tendsto_nhds_unique hc (quasitraceUltraSize_tendsto T U hunit u)

lemma ultralimitPositiveQuasitrace_metricSize_add
    (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x+(T i).metricSize y)
    (u v : lp D ∞) :
    (ultralimitPositiveQuasitrace T U hunit).metricSize (u+v) ≤
      (ultralimitPositiveQuasitrace T U hunit).metricSize u+
        (ultralimitPositiveQuasitrace T U hunit).metricSize v := by
  simp only [ultralimitPositiveQuasitrace_metricSize]
  exact quasitraceUltraSize_add T U hunit hadd u v

lemma ultralimitPositiveQuasitrace_sqrt_add
    (hsqrt : ∀ i (a b : Positive (D i)), Real.sqrt (T i (Positive.add a b)) ≤
      Real.sqrt (T i a)+Real.sqrt (T i b)) (a b : Positive (lp D ∞)) :
    Real.sqrt ((ultralimitPositiveQuasitrace T U hunit) (Positive.add a b)) ≤
      Real.sqrt ((ultralimitPositiveQuasitrace T U hunit) a)+
        Real.sqrt ((ultralimitPositiveQuasitrace T U hunit) b) := by
  apply le_of_tendsto_of_tendsto
    (Real.continuous_sqrt.continuousAt.tendsto.comp (quasitraceUltraPositive_tendsto T U hunit (Positive.add a b)))
    ((Real.continuous_sqrt.continuousAt.tendsto.comp (quasitraceUltraPositive_tendsto T U hunit a)).add
      (Real.continuous_sqrt.continuousAt.tendsto.comp (quasitraceUltraPositive_tendsto T U hunit b)))
  filter_upwards [] with i
  simp only [Function.comp_def, boundedProductPositiveEval_add]
  exact hsqrt i _ _
end CuntzPureness

end

end OAI
