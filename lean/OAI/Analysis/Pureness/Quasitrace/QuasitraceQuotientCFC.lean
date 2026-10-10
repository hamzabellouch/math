import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFaithfulness

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def cauchySequenceEval (k : ℕ) : T.cauchySequenceAlgebra hadd →⋆ₐ[ℂ] D where
  toFun u := u.1 k
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma cauchyValue_selfAdjoint_add (a b : selfAdjoint (T.cauchySequenceAlgebra hadd))
    (h : Commute a.1 b.1) :
    T.cauchyValue hadd hsqrt (a.1+b.1) = T.cauchyValue hadd hsqrt a.1+T.cauchyValue hadd hsqrt b.1 := by
  have hleft := T.cauchyValue_tendsto hadd hsqrt (a.1+b.1)
  have hright := (T.cauchyValue_tendsto hadd hsqrt a.1).add (T.cauchyValue_tendsto hadd hsqrt b.1)
  have he (k : ℕ) : T.complexValue ((a.1+b.1).1 k) = T.complexValue (a.1.1 k)+T.complexValue (b.1.1 k) := by
    let ak : selfAdjoint D := ⟨a.1.1 k,a.2.map (T.cauchySequenceEval hadd k)⟩
    let bk : selfAdjoint D := ⟨b.1.1 k,b.2.map (T.cauchySequenceEval hadd k)⟩
    have hab : Commute ak.1 bk.1 := h.map (T.cauchySequenceEval hadd k)
    change T.complexValue (ak+bk).1 = T.complexValue ak.1+T.complexValue bk.1
    rw [T.complexValue_selfAdjoint,T.complexValue_selfAdjoint,T.complexValue_selfAdjoint,
      T.selfAdjointValue_add _ _ hab,Complex.ofReal_add]
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

lemma cauchyValue_selfAdjoint_neg (a : selfAdjoint (T.cauchySequenceAlgebra hadd)) :
    T.cauchyValue hadd hsqrt (-a.1) = -T.cauchyValue hadd hsqrt a.1 := by
  have hleft := T.cauchyValue_tendsto hadd hsqrt (-a.1)
  have hright := (T.cauchyValue_tendsto hadd hsqrt a.1).neg
  have he (k : ℕ) : T.complexValue ((-a.1).1 k) = -T.complexValue (a.1.1 k) := by
    let ak : selfAdjoint D := ⟨a.1.1 k,a.2.map (T.cauchySequenceEval hadd k)⟩
    change T.complexValue (-ak).1 = -T.complexValue ak.1
    rw [T.complexValue_selfAdjoint,T.complexValue_selfAdjoint,T.selfAdjointValue_neg,Complex.ofReal_neg]
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

lemma quotientValue_one_sub (x : selfAdjoint (T.CauchyQuotient hadd)) :
    T.quotientValue hadd hsqrt (1-x.1) = T.quotientValue hadd hsqrt 1-T.quotientValue hadd hsqrt x.1 := by
  obtain ⟨u,hu⟩ := T.exists_selfAdjoint_representative hadd x
  have he := T.cauchyValue_selfAdjoint_add hadd hsqrt (1 : selfAdjoint _) (-u) (Commute.one_left _)
  change T.cauchyValue hadd hsqrt (1 + -u.1) =
    T.cauchyValue hadd hsqrt 1+T.cauchyValue hadd hsqrt (-u.1) at he
  rw [T.cauchyValue_selfAdjoint_neg hadd hsqrt u] at he
  rw [← hu,← _root_.map_one (T.cauchyQuotientMap hadd),← map_sub,T.quotientValue_map,T.quotientValue_map,T.quotientValue_map]
  simpa only [sub_eq_add_neg] using he

lemma quotientValue_cfc_add (x : selfAdjoint (T.CauchyQuotient hadd))
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    T.quotientValue hadd hsqrt (cfc f x.1+cfc g x.1) =
      T.quotientValue hadd hsqrt (cfc f x.1)+T.quotientValue hadd hsqrt (cfc g x.1) := by
  obtain ⟨u,hu⟩ := T.exists_selfAdjoint_representative hadd x
  let a : selfAdjoint (T.cauchySequenceAlgebra hadd) := ⟨cfc f u.1,cfc_predicate f u.1⟩
  let b : selfAdjoint (T.cauchySequenceAlgebra hadd) := ⟨cfc g u.1,cfc_predicate g u.1⟩
  have hfa : T.cauchyQuotientMap hadd a.1 = cfc f x.1 := by
    change T.cauchyQuotientStarHom hadd (cfc f u.1) = _
    have hm := (T.cauchyQuotientStarHom hadd).map_cfc f u.1 hf.continuousOn
      (T.cauchyQuotientStarHom_continuous hadd) u.2 (u.2.map _)
    exact hm.trans (congrArg (fun z => cfc f z) hu)
  have hgb : T.cauchyQuotientMap hadd b.1 = cfc g x.1 := by
    change T.cauchyQuotientStarHom hadd (cfc g u.1) = _
    have hm := (T.cauchyQuotientStarHom hadd).map_cfc g u.1 hg.continuousOn
      (T.cauchyQuotientStarHom_continuous hadd) u.2 (u.2.map _)
    exact hm.trans (congrArg (fun z => cfc g z) hu)
  have hab : Commute a.1 b.1 := (((Commute.refl u.1).cfc_real f).symm.cfc_real g).symm
  rw [← hfa,← hgb,← map_add,T.quotientValue_map,T.quotientValue_map,T.quotientValue_map]
  exact T.cauchyValue_selfAdjoint_add hadd hsqrt a b hab
end CuntzPureness.PositiveQuasitrace

end

end OAI
