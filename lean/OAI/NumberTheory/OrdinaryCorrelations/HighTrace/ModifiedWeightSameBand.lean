import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordUntaggedSingleton
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Fiber

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma modifiedWeight_same_band (w : ClosedLine h ℓ) (p q : S.Index)
    (hpq : S.IsCore p ↔ S.IsCore q) (E : Finset (Fin ℓ)) :
    modifiedWeight w p E = modifiedWeight w q E := by
  have ha : S.amplitude p = S.amplitude q := by simp only [amplitude,hpq]
  have hb : S.beta p = S.beta q := by simp only [beta,ha]
  simp only [modifiedWeight,hpq,subtreeUnionWeight,ha,hb]

lemma tokenWeight_same_band (w : ClosedLine h ℓ) (pC pZ : S.Index)
    (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) (p : S.Index)
    (t : TokenType w) (ht : t.1 = true ↔ S.IsCore p) :
    tokenWeight w pC pZ t = modifiedWeight w p t.2.edges.val := by
  unfold tokenWeight
  apply modifiedWeight_same_band
  by_cases hb : t.1 = true
  · simpa only [hb,ite_true,hpC,true_iff] using ht.mp hb
  · have hp : ¬S.IsCore p := fun hp => hb (ht.mpr hp)
    simp only [hb,Bool.false_eq_true,ite_false,hpZ,hp]

def taggedTokens (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (p : S.Index) :
    Finset (LocalToken ℓ) := (recordTokens w hh 𝔏 R p).filter (fun t => t.1 = true)

lemma taggedTokens_of_none (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : untaggedType w hh 𝔏 a p = none) :
    taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p := by
  apply filter_eq_self.mpr
  intro t ht
  by_contra hn
  have hu : t.1 = false := Bool.eq_false_iff.mpr hn
  have hU : HasUntagged w hh 𝔏 (recordAt w hh 𝔏 a) p := ⟨t,ht,hu⟩
  simp only [untaggedType,dite_eq_left hU] at hp
  contradiction

lemma taggedTokens_of_some (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : TokenType w) (hp : untaggedType w hh 𝔏 a p = some t) :
    taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = ∅ := by
  rw [taggedTokens,(untaggedType_some w hh 𝔏 a p t hp).2]
  simp

theorem record_tokens_recovery (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a b : S.FixedResidues w)
    (hT : ∀ p, taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p =
      taggedTokens w hh 𝔏 (recordAt w hh 𝔏 b) p)
    (hU : untaggedType w hh 𝔏 a = untaggedType w hh 𝔏 b) :
    recordAt w hh 𝔏 a = recordAt w hh 𝔏 b := by
  apply recordTokens_injective_on_records w hh 𝔏 a b
  intro p
  rcases he : untaggedType w hh 𝔏 a p with _ | t
  · have hb : untaggedType w hh 𝔏 b p = none := by rw [← hU,he]
    rw [← taggedTokens_of_none w hh 𝔏 a p he,← taggedTokens_of_none w hh 𝔏 b p hb]
    exact hT p
  · have hb : untaggedType w hh 𝔏 b p = some t := by rw [← hU,he]
    rw [(untaggedType_some w hh 𝔏 a p t he).2,(untaggedType_some w hh 𝔏 b p t hb).2]

lemma recordTreeWeight_split (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w)
    (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) (p : S.Index) :
    recordTreeWeight w hh 𝔏 (recordAt w hh 𝔏 a) p =
      (∏ t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p, localTokenWeight w p t) *
        TypeFibers.factor (untaggedType w hh 𝔏 a) (fun t _ => tokenWeight w pC pZ t) p := by
  rw [← recordTokens_weight w hh]
  rcases he : untaggedType w hh 𝔏 a p with _ | t
  · rw [taggedTokens_of_none w hh 𝔏 a p he]
    simp only [TypeFibers.factor,he,mul_one]
  · rw [taggedTokens_of_some w hh 𝔏 a p t he,(untaggedType_some w hh 𝔏 a p t he).2]
    simp only [prod_singleton,prod_empty,one_mul,TypeFibers.factor,he,
      localTokenWeight,Bool.false_eq_true,ite_false,tokenEdges]
    exact (tokenWeight_same_band w pC pZ hpC hpZ p t (untaggedType_some w hh 𝔏 a p t he).1).symm

lemma untagged_implies_used (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : TokenType w) (hp : untaggedType w hh 𝔏 a p = some t) : UsedPrime w 𝔏 p := by
  apply Or.inl
  by_contra hn
  have he := (untaggedType_some w hh 𝔏 a p t hp).2
  simp only [recordTokens,hn,ite_false] at he
  exact (singleton_ne_empty _ he.symm)

def taggedGroupFactor (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) : ℝ :=
  if untaggedType w hh 𝔏 a p = none then
    (if UsedPrime w 𝔏 p then (p : ℝ)⁻¹ else 1) *
      ∏ t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p, localTokenWeight w p t
  else 1

lemma weighted_record_prime_split (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w)
    (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) (p : S.Index) :
    (if UsedPrime w 𝔏 p then (p : ℝ)⁻¹ else 1) * recordTreeWeight w hh 𝔏 (recordAt w hh 𝔏 a) p =
      taggedGroupFactor w hh 𝔏 a p *
        TypeFibers.factor (untaggedType w hh 𝔏 a)
          (fun t (q : S.Index) => tokenWeight w pC pZ t * (q : ℝ)⁻¹) p := by
  rw [recordTreeWeight_split w hh 𝔏 a pC pZ hpC hpZ]
  rcases he : untaggedType w hh 𝔏 a p with _ | t
  · simp only [taggedGroupFactor,he,ite_true,TypeFibers.factor,mul_one]
  · have hu := untagged_implies_used w hh 𝔏 a p t he
    rw [taggedTokens_of_some w hh 𝔏 a p t he]
    simp only [taggedGroupFactor,he,Option.some_ne_none,ite_false,TypeFibers.factor,
      hu,ite_true,prod_empty,one_mul]
    ring

theorem record_weight_factorization (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w)
    (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) :
    (∏ p : S.Index, (if UsedPrime w 𝔏 p then (p : ℝ)⁻¹ else 1) *
      recordTreeWeight w hh 𝔏 (recordAt w hh 𝔏 a) p) =
    (∏ p : S.Index, taggedGroupFactor w hh 𝔏 a p) *
      FactorialAssignments.unorderedWeight (TypeFibers.multiplicity (untaggedType w hh 𝔏 a))
        (fun t (q : S.Index) => tokenWeight w pC pZ t * (q : ℝ)⁻¹)
        (TypeFibers.unordered (untaggedType w hh 𝔏 a)) := by
  simp_rw [weighted_record_prime_split w hh 𝔏 a pC pZ hpC hpZ]
  rw [prod_mul_distrib,TypeFibers.unorderedWeight_eq]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
