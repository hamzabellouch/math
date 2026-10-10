import OAI.NumberTheory.DirichletL.Hecke.DetectorRowSpecialization

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily UniqueFactorizationMonoid

def SixthFree (I : Ideal O) : Prop := ∀ P, (normalizedFactors I).count P<6

theorem ideal_decomposition_unique {I J A B : Ideal O}
    (hI : I≠0) (hJ : J≠0) (hA : A≠0) (hB : B≠0)
    (hIf : SixthFree I) (hJf : SixthFree J) (he : I*A^6=J*B^6) :
    I=J ∧ A=B := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hI (pow_ne_zero _ hA),
    normalizedFactors_mul hJ (pow_ne_zero _ hB),normalizedFactors_pow,normalizedFactors_pow] at hf
  have hc (P : Ideal O) := congrArg (Multiset.count P) hf
  have hcounts (P : Ideal O) :
      (normalizedFactors I).count P=(normalizedFactors J).count P ∧
      (normalizedFactors A).count P=(normalizedFactors B).count P := by
    have hh := hc P
    simp only [Multiset.count_add,Multiset.count_nsmul] at hh
    have hi := hIf P
    have hj := hJf P
    omega
  have hIJ : normalizedFactors I=normalizedFactors J :=
    Multiset.ext.mpr (fun P => (hcounts P).1)
  have hAB : normalizedFactors A=normalizedFactors B :=
    Multiset.ext.mpr (fun P => (hcounts P).2)
  constructor
  · simpa only [Ideal.prod_normalizedFactors_eq_self hI,Ideal.prod_normalizedFactors_eq_self hJ]
      using congrArg Multiset.prod hIJ
  · simpa only [Ideal.prod_normalizedFactors_eq_self hA,Ideal.prod_normalizedFactors_eq_self hB]
      using congrArg Multiset.prod hAB

abbrev FreeRow := {u : O // u≠0 ∧ SixthFree (Ideal.span {u})}
abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

def rowMap (p : FreeRow×NonzeroIdeal) : O :=
  p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6

theorem rowMap_ne_zero (p : FreeRow×NonzeroIdeal) : rowMap p≠0 :=
  mul_ne_zero p.1.property.1 (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
    p.2.val p.2.property))

theorem rowMap_span (p : FreeRow×NonzeroIdeal) :
    Ideal.span {rowMap p}=Ideal.span {p.1.val}*p.2.val^6 := by
  unfold rowMap
  rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,
    ConcretePrimeRowBridge.span_idealGenerator]

theorem rowMap_injective : Function.Injective rowMap := by
  intro p q hpq
  have he := congrArg (fun u : O => Ideal.span {u}) hpq
  rw [rowMap_span,rowMap_span] at he
  have hd := ideal_decomposition_unique
    (Ideal.span_singleton_eq_bot.not.mpr p.1.property.1)
    (Ideal.span_singleton_eq_bot.not.mpr q.1.property.1)
    p.2.property q.2.property p.1.property.2 q.1.property.2 he
  have ha : p.2=q.2 := Subtype.ext hd.2
  apply Prod.ext
  · apply Subtype.ext
    change p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6=
      q.1.val*(ConcretePrimeRowBridge.idealGenerator q.2.val)^6 at hpq
    rw [ha] at hpq
    exact mul_right_cancel₀ (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
      q.2.val q.2.property)) hpq
  · exact ha

theorem rowMap_norm (p : FreeRow×NonzeroIdeal) :
    (Ideal.span {rowMap p}).absNorm=(Ideal.span {p.1.val}).absNorm*p.2.val.absNorm^6 := by
  rw [rowMap_span,map_mul,map_pow]

end SevenEighths.HeckeInverseAmplification

end

end OAI
