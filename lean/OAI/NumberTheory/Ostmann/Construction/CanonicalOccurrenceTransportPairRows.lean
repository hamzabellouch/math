import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportDecodedData

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistoryPairPattern Characters.RationalHistory
open Arithmetic.ClearedCoefficientFlags

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ→ℕ}
  {outside : List ℕ} {l : ℕ}

def pairedOccurrenceEquiv (D E : DecodedDraw sources seed V outside l) :
    (Internal seed l ⊕ Internal seed l) ≃ Arithmetic.HistoryPairRows.Occurrences D.history E.history :=
  Equiv.sumCongr (internalEquiv seed D.history D.labels) (internalEquiv seed E.history E.labels)

def pairedBlockEquiv (D E D' E' : DecodedDraw sources seed V outside l)
    (hp : SamePairPattern seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels) : PairKey D.history E.history ≃ PairKey D'.history E'.history :=
  pairKeyEquiv seed D.history E.history D'.history E'.history D.labels E.labels D'.labels E'.labels hp

theorem decoded_pair_rows_rename (D E D' E' : DecodedDraw sources seed V outside l)
    (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
    (hp : SamePairPattern seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels) (i : Internal seed l ⊕ Internal seed l) :
    let r := Arithmetic.HistoryPairRows.row D.history E.history D.supported E.supported
      (pairedOccurrenceEquiv D E i)
    let r' := Arithmetic.HistoryPairRows.row D'.history E'.history D'.supported E'.supported
      (pairedOccurrenceEquiv D' E' i)
    (r.1.rename (pairedBlockEquiv D E D' E' hp),r.2.rename (pairedBlockEquiv D E D' E' hp))=r' := by
  rcases i with i | i
  · have hi := congrFun (DecodedDraw.normalizedRows_eq hD) i
    apply Prod.ext
    · exact rename_left_shared seed D.history E.history D'.history E'.history D.labels E.labels D'.labels E'.labels
        hp _ _ (congrArg Prod.fst hi)
    · exact rename_left_shared seed D.history E.history D'.history E'.history D.labels E.labels D'.labels E'.labels
        hp _ _ (congrArg Prod.snd hi)
  · have hi := congrFun (DecodedDraw.normalizedRows_eq hE) i
    apply Prod.ext
    · exact rename_right_shared seed D.history E.history D'.history E'.history D.labels E.labels D'.labels E'.labels
        hp _ _ (congrArg Prod.fst hi)
    · exact rename_right_shared seed D.history E.history D'.history E'.history D.labels E.labels D'.labels E'.labels
        hp _ _ (congrArg Prod.snd hi)

lemma leftCoefficient_rename {ι κ : Type} (f : ι→κ) (a b : Expr ι) :
    MvPolynomial.rename f (leftCoefficient a b)=leftCoefficient (a.rename f) (b.rename f) := by
  simp only [leftCoefficient,Expr.numerator_rename,Expr.denominator_rename,map_mul]

lemma rightCoefficient_rename {ι κ : Type} (f : ι→κ) (a b : Expr ι) :
    MvPolynomial.rename f (rightCoefficient a b)=rightCoefficient (a.rename f) (b.rename f) := by
  simp only [rightCoefficient,Expr.numerator_rename,Expr.denominator_rename,map_mul]

lemma minor_rename {ι κ : Type} (f : ι→κ) (a b c d : Expr ι) :
    MvPolynomial.rename f (minor a b c d)=minor (a.rename f) (b.rename f) (c.rename f) (d.rename f) := by
  simp only [minor,map_sub,map_mul,leftCoefficient_rename,rightCoefficient_rename]

theorem decoded_pair_flags_rename (D E D' E' : DecodedDraw sources seed V outside l)
    (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
    (hp : SamePairPattern seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels) (i : Internal seed l ⊕ Internal seed l) :
    MvPolynomial.rename (pairedBlockEquiv D E D' E' hp)
      (Arithmetic.HistoryPairRows.leftFlag D.history E.history D.supported E.supported (pairedOccurrenceEquiv D E i))=
      Arithmetic.HistoryPairRows.leftFlag D'.history E'.history D'.supported E'.supported (pairedOccurrenceEquiv D' E' i) ∧
    MvPolynomial.rename (pairedBlockEquiv D E D' E' hp)
      (Arithmetic.HistoryPairRows.rightFlag D.history E.history D.supported E.supported (pairedOccurrenceEquiv D E i))=
      Arithmetic.HistoryPairRows.rightFlag D'.history E'.history D'.supported E'.supported (pairedOccurrenceEquiv D' E' i) := by
  have hi := decoded_pair_rows_rename D E D' E' hD hE hp i
  have h1 := congrArg Prod.fst hi
  have h2 := congrArg Prod.snd hi
  dsimp only at h1 h2
  constructor
  · simp only [Arithmetic.HistoryPairRows.leftFlag,leftCoefficient_rename,h1,h2]
  · simp only [Arithmetic.HistoryPairRows.rightFlag,rightCoefficient_rename,h1,h2]

theorem decoded_pair_minor_rename (D E D' E' : DecodedDraw sources seed V outside l)
    (hD : D.SameFrequencies D') (hE : E.SameFrequencies E')
    (hp : SamePairPattern seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels) (i j : Internal seed l ⊕ Internal seed l) :
    MvPolynomial.rename (pairedBlockEquiv D E D' E' hp)
      (Arithmetic.HistoryPairRows.minorFlag D.history E.history D.supported E.supported
        (pairedOccurrenceEquiv D E i) (pairedOccurrenceEquiv D E j))=
    Arithmetic.HistoryPairRows.minorFlag D'.history E'.history D'.supported E'.supported
      (pairedOccurrenceEquiv D' E' i) (pairedOccurrenceEquiv D' E' j) := by
  obtain ⟨hi1,hi2⟩ := decoded_pair_flags_rename D E D' E' hD hE hp i
  obtain ⟨hj1,hj2⟩ := decoded_pair_flags_rename D E D' E' hD hE hp j
  change MvPolynomial.rename _ (_*_ - _*_) = _*_ - _*_
  rw [map_sub,map_mul,map_mul]
  exact congrArg₂ (fun a b => a-b) (congrArg₂ (fun a b => a*b) hi1 hj2)
    (congrArg₂ (fun a b => a*b) hi2 hj1)

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
