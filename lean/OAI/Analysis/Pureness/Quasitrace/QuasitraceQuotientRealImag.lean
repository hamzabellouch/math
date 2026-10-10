import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientValue

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace Filter
open scoped Topology NNReal ENNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def cauchyQuotientStarHom : T.cauchySequenceAlgebra hadd →⋆ₐ[ℂ] T.CauchyQuotient hadd :=
  { T.cauchyQuotientMap hadd with map_star' := T.cauchyQuotientMap_star hadd }

lemma exists_selfAdjoint_representative (x : selfAdjoint (T.CauchyQuotient hadd)) :
    ∃ u : selfAdjoint (T.cauchySequenceAlgebra hadd), T.cauchyQuotientMap hadd u.1 = x.1 := by
  obtain ⟨v,hv⟩ := T.cauchyQuotientMap_surjective hadd x.1
  refine ⟨ℜ v,?_⟩
  change T.cauchyQuotientStarHom hadd (ℜ v : T.cauchySequenceAlgebra hadd) = x.1
  rw [map_realPart]
  change (ℜ (T.cauchyQuotientMap hadd v) : T.CauchyQuotient hadd) = x.1
  rw [hv,x.2.coe_realPart]

lemma cauchyValue_real_add_I (a b : selfAdjoint (T.cauchySequenceAlgebra hadd)) :
    T.cauchyValue hadd hsqrt (a.1+Complex.I • b.1) =
      T.cauchyValue hadd hsqrt a.1+Complex.I*T.cauchyValue hadd hsqrt b.1 := by
  have hleft := T.cauchyValue_tendsto hadd hsqrt (a.1+Complex.I • b.1)
  have hright := (T.cauchyValue_tendsto hadd hsqrt a.1).add
    ((T.cauchyValue_tendsto hadd hsqrt b.1).const_mul Complex.I)
  have he (k : ℕ) : T.complexValue ((a.1+Complex.I • b.1).1 k) =
      T.complexValue (a.1.1 k)+Complex.I*T.complexValue (b.1.1 k) := by
    have ha : IsSelfAdjoint (a.1.1 k) := by
      change star (a.1.1 k) = a.1.1 k
      exact congrArg (fun u : lp (fun _ : ℕ => D) ∞ => u k) (congrArg Subtype.val a.2)
    have hb : IsSelfAdjoint (b.1.1 k) := by
      change star (b.1.1 k) = b.1.1 k
      exact congrArg (fun u : lp (fun _ : ℕ => D) ∞ => u k) (congrArg Subtype.val b.2)
    exact T.complexValue_real_add_I ⟨a.1.1 k,ha⟩ ⟨b.1.1 k,hb⟩
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

lemma quotientValue_real_add_I (a b : selfAdjoint (T.CauchyQuotient hadd)) :
    T.quotientValue hadd hsqrt (a.1+Complex.I • b.1) =
      T.quotientValue hadd hsqrt a.1+Complex.I*T.quotientValue hadd hsqrt b.1 := by
  obtain ⟨u,hu⟩ := T.exists_selfAdjoint_representative hadd a
  obtain ⟨v,hv⟩ := T.exists_selfAdjoint_representative hadd b
  rw [← hu,← hv,← _root_.map_smul,← map_add,T.quotientValue_map,T.quotientValue_map,T.quotientValue_map]
  exact T.cauchyValue_real_add_I hadd hsqrt u v

lemma cauchyValue_selfAdjoint_im (a : selfAdjoint (T.cauchySequenceAlgebra hadd)) :
    (T.cauchyValue hadd hsqrt a.1).im = 0 := by
  have ht := (Complex.continuous_im.tendsto (T.cauchyValue hadd hsqrt a.1)).comp
    (T.cauchyValue_tendsto hadd hsqrt a.1)
  have he (k : ℕ) : (T.complexValue (a.1.1 k)).im = 0 := by
    have ha : IsSelfAdjoint (a.1.1 k) := by
      change star (a.1.1 k) = a.1.1 k
      exact congrArg (fun u : lp (fun _ : ℕ => D) ∞ => u k) (congrArg Subtype.val a.2)
    rw [T.complexValue_selfAdjoint ⟨a.1.1 k,ha⟩,Complex.ofReal_im]
  simp only [Function.comp_def,he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma quotientValue_selfAdjoint_im (a : selfAdjoint (T.CauchyQuotient hadd)) :
    (T.quotientValue hadd hsqrt a.1).im = 0 := by
  obtain ⟨u,hu⟩ := T.exists_selfAdjoint_representative hadd a
  rw [← hu,T.quotientValue_map]
  exact T.cauchyValue_selfAdjoint_im hadd hsqrt u
end CuntzPureness.PositiveQuasitrace

end

end OAI
