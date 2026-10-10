import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairNumerators
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentatives
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeMixedLineFamilies

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairPrimeIntegration
open scoped BigOperators
open Construction HistoryOccurrenceVariables HistoryPairRows HistoryPairPattern
open HistoryPairRepresentatives ClearedCoefficientFlags MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def leftRows (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (x : PairKey h k → ZMod (prime h k r)) :
    Fiber h k r → ZMod (prime h k r) :=
  fun i => eval₂ (Int.castRingHom _) x (leftFlag h k hs ks i.val)

def rightRows (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (x : PairKey h k → ZMod (prime h k r)) :
    Fiber h k r → ZMod (prime h k r) :=
  fun i => eval₂ (Int.castRingHom _) x (rightFlag h k hs ks i.val)

theorem minor_eval (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (i j : Fiber h k r) :
    eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val) =
      PrimeLineFamilies.minor (leftRows h k hs ks r x) (rightRows h k hs ks r x) i j := by
  simp only [minorFlag,ClearedCoefficientFlags.minor,eval₂_sub,eval₂_mul,
    PrimeLineFamilies.minor,leftRows,rightRows,leftFlag,rightFlag]

theorem minors_zero_iff (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) :
    PrimeLineFamilies.AllMinorsZero (leftRows h k hs ks r x) (rightRows h k hs ks r x) ↔
      ∀ i j : Fiber h k r, eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val)=0 := by
  simp only [PrimeLineFamilies.AllMinorsZero,minor_eval]

theorem probability_eq_flags (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) :
    PrimeLineFamilies.probability (prime h k r) (leftRows h k hs ks r x) (rightRows h k hs ks r x) =
      (by classical exact
      if (∀ i : Fiber h k r, eval₂ (Int.castRingHom _) x (leftFlag h k hs ks i.val)=0 ∧
          eval₂ (Int.castRingHom _) x (rightFlag h k hs ks i.val)=0) then 1
      else if (∀ i j : Fiber h k r, eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val)=0) ∧
        (∃ i : Fiber h k r, eval₂ (Int.castRingHom _) x (leftFlag h k hs ks i.val)≠0 ∧
          eval₂ (Int.castRingHom _) x (rightFlag h k hs ks i.val)≠0)
      then (((prime h k r-1:ℕ):ℝ))⁻¹ else 0) := by
  classical
  rw [PrimeLineFamilies.probability_eq_flags,minors_zero_iff]
  dsimp +instances only [PrimeLineFamilies.AllZero,leftRows,rightRows,Fiber]
  split_ifs <;> rfl

theorem family_nonzero (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (i₀ : Fiber h k r)
    (hx : AncestorUnits h k x i₀.val) (hV : ∀ j ≤ l, V j < prime h k r) :
    ¬ PrimeLineFamilies.AllZero (leftRows h k hs ks r x) (rightRows h k hs ks r x) := by
  intro hz
  have hn := flags_nonzero_field h k hs ks i₀.val x hx
    (HistoryPairNumerators.frequency_units h k hs ks _ hV)
  exact hn.elim (fun hh => hh (hz i₀).1) (fun hh => hh (hz i₀).2)

theorem probability_le (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (i₀ : Fiber h k r)
    (hx : AncestorUnits h k x i₀.val) (hV : ∀ j ≤ l, V j < prime h k r) :
    PrimeLineFamilies.probability (prime h k r) (leftRows h k hs ks r x) (rightRows h k hs ks r x) ≤
      (((prime h k r-1:ℕ):ℝ))⁻¹ :=
  PrimeLineFamilies.probability_le_unit_line _ _ _ (family_nonzero h k hs ks r x i₀ hx hV)

theorem mixed_probability_le (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (i₀ : Fiber h k r)
    (hx : AncestorUnits h k x i₀.val) (hV : ∀ j ≤ l, V j < prime h k r) :
    PrimeMixedLineFamilies.probability (prime h k r) (leftRows h k hs ks r x) (rightRows h k hs ks r x) ≤
      (prime h k r:ℝ)⁻¹ :=
  PrimeMixedLineFamilies.probability_le_mixed_line _ _ _ (family_nonzero h k hs ks r x i₀ hx hV)

theorem labeled_probability (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    [∀ r : Representative h k, Fact (prime h k r).Prime]
    (x : ∀ r : Representative h k, PairKey h k → ZMod (prime h k r)) :
    (Nat.card {z : ∀ r : Representative h k, (ZMod (prime h k r))ˣ × (ZMod (prime h k r))ˣ //
      PrimeLineFamilies.LabeledCommonZero (label h k) (prime h k)
        (fun r => leftRows h k hs ks r (x r)) (fun r => rightRows h k hs ks r (x r)) z}:ℝ) /
      Fintype.card (∀ r : Representative h k, (ZMod (prime h k r))ˣ × (ZMod (prime h k r))ˣ) =
      ∏ r : Representative h k, PrimeLineFamilies.probability (prime h k r)
        (leftRows h k hs ks r (x r)) (rightRows h k hs ks r (x r)) :=
  PrimeLineFamilies.labeled_probability (label h k) (prime h k) _ _

theorem weighted_probability (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    [∀ r : Representative h k, Fact (prime h k r).Prime]
    (x : ∀ r : Representative h k, PairKey h k → ZMod (prime h k r)) :
    (∏ i : Occurrences h k, ((slot h k i).value:ℝ)) *
      PrimeLineFamilies.independentProbability (Fiber h k) (prime h k)
        (fun r => leftRows h k hs ks r (x r)) (fun r => rightRows h k hs ks r (x r)) =
      ∏ r : Representative h k, (prime h k r:ℝ)^RepeatedLabels.multiplicity Finset.univ (label h k) r *
        PrimeLineFamilies.probability (prime h k r) (leftRows h k hs ks r (x r)) (rightRows h k hs ks r (x r)) := by
  classical
  exact PrimeLineFamilies.weighted_independentProbability (Fiber h k) (prime h k)
    Finset.univ (label h k) _ _

theorem representative_domination (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (i₀ : Fiber h k r)
    (hx : AncestorUnits h k x i₀.val) (hV : ∀ j ≤ l, V j < prime h k r)
    (μ : Fiber h k r → ℝ) {B : ℝ} (hB : 0≤B)
    (hμ : ∀ i, 0≤μ i) (hbound : ∀ i, (prime h k r:ℝ)*μ i≤B) :
    ((∏ i, μ i)*(prime h k r:ℝ)^Fintype.card (Fiber h k r))*
      PrimeLineFamilies.probability (prime h k r) (leftRows h k hs ks r x) (rightRows h k hs ks r x) ≤
        2*μ i₀*B^(Fintype.card (Fiber h k r)-1) := by
  classical
  exact PrimeLineFamilies.representative_domination _ _ _
    (family_nonzero h k hs ks r x i₀ hx hV) Finset.univ (Finset.mem_univ i₀) hB μ
    (fun i _ => hμ i) (fun i _ => hbound i)

end Ostmann.Arithmetic.HistoryPairPrimeIntegration

end

end OAI
