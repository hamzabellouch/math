import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverageCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverageLocal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage
open Construction HistorySignedSpectatorCRT HistorySignedSpectatorDiagram
open HistoryCRTIntegration HistoryRepresentativeSourceSeparation ResidueHaar

theorem unit_average_eq_diagram_averages {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (g : (q:ℕ)→ZMod q→ℂ)
    (hg : ∀q∈outside,g q 0=0) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    average (fun z : UnitPair outside.prod=>
      residuePairSpectator g outside outside.prod h k (z.1,z.2))=
      ∏i:Fin outside.length,average (localDiagramPair h k hs ks (primeAt outside i)
        (List.get_mem outside i) (hp _ (List.get_mem outside i))
        (hV _ (List.get_mem outside i)) g) := by
  let := outsideNeZero hp
  let := primeAtNeZero hp
  rw [unit_average_eq_prime_averages h k hs ks had hp g]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext z
  exact primePair_eq_localDiagramPair h k hs ks _ (List.get_mem outside i)
    (hp _ (List.get_mem outside i)) (hV _ (List.get_mem outside i)) g
    (hg _ (List.get_mem outside i)) z

theorem mixed_average_eq_diagram_averages {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (g : (q:ℕ)→ZMod q→ℂ)
    (hg : ∀q∈outside,g q 0=0) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    average (fun z : MixedPair outside.prod=>
      residuePairSpectator g outside outside.prod h k (z.1,z.2))=
      ∏i:Fin outside.length,average (localMixedDiagramPair h k hs ks (primeAt outside i)
        (List.get_mem outside i) (hp _ (List.get_mem outside i))
        (hV _ (List.get_mem outside i)) g) := by
  let := outsideNeZero hp
  let := primeAtNeZero hp
  rw [mixed_average_eq_prime_averages h k hs ks had hp g]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext z
  exact primePair_eq_localMixedDiagramPair h k hs ks _ (List.get_mem outside i)
    (hp _ (List.get_mem outside i)) (hV _ (List.get_mem outside i)) g
    (hg _ (List.get_mem outside i)) z

theorem actual_unit_average_eq_diagram_averages (d : Decomposition)
    {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    average (fun z : UnitPair outside.prod=>
      residuePairSpectator (residueTransform d) outside outside.prod h k (z.1,z.2))=
      ∏i:Fin outside.length,average (localDiagramPair h k hs ks (primeAt outside i)
        (List.get_mem outside i) (hp _ (List.get_mem outside i))
        (hV _ (List.get_mem outside i)) (residueTransform d)) :=
  unit_average_eq_diagram_averages h k hs ks had hp hV (residueTransform d)
    (fun q _=>actual_residueTransform_zero d q)

theorem actual_mixed_average_eq_diagram_averages (d : Decomposition)
    {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    average (fun z : MixedPair outside.prod=>
      residuePairSpectator (residueTransform d) outside outside.prod h k (z.1,z.2))=
      ∏i:Fin outside.length,average (localMixedDiagramPair h k hs ks (primeAt outside i)
        (List.get_mem outside i) (hp _ (List.get_mem outside i))
        (hV _ (List.get_mem outside i)) (residueTransform d)) :=
  mixed_average_eq_diagram_averages h k hs ks had hp hV (residueTransform d)
    (fun q _=>actual_residueTransform_zero d q)

end Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage

end

end OAI
