import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverageBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage
open Construction HistorySignedSpectatorCRT HistorySignedSpectatorDiagram
open HistoryCRTIntegration HistoryRepresentativeSourceSeparation ResidueHaar

theorem unit_average_eq_prime_averages {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime)
    (g : (q:ℕ)→ZMod q→ℂ) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    average (fun z : UnitPair outside.prod=>
      residuePairSpectator g outside outside.prod h k (z.1,z.2))=
      ∏i:Fin outside.length,average (fun z : UnitPair (primeAt outside i)=>
        primePair h k g outside (primeAt outside i) (z.1,z.2)) := by
  let := outsideNeZero hp
  let := primeAtNeZero hp
  have hd : (∏i,primeAt outside i)∣outside.prod := by rw [primeAt_prod]
  have he := unit_projected_product_average (primeAt outside) (primeAt_pairwise h hs) hd
    (fun i=>primePair h k g outside (primeAt outside i))
  calc
    _ = average (fun z : UnitPair outside.prod=>∏i:Fin outside.length,
        primePair h k g outside (primeAt outside i)
          (projectedRingPair ((Finset.dvd_prod_of_mem (primeAt outside)
            (Finset.mem_univ i)).trans hd) ((z.1:ZMod outside.prod),(z.2:ZMod outside.prod)))) := by
      congr 1
      funext z
      exact residuePair_eq_projected_product h k hs ks had g (z.1,z.2)
    _ = _ := he

theorem mixed_average_eq_prime_averages {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime)
    (g : (q:ℕ)→ZMod q→ℂ) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    average (fun z : MixedPair outside.prod=>
      residuePairSpectator g outside outside.prod h k (z.1,z.2))=
      ∏i:Fin outside.length,average (fun z : MixedPair (primeAt outside i)=>
        primePair h k g outside (primeAt outside i) (z.1,z.2)) := by
  let := outsideNeZero hp
  let := primeAtNeZero hp
  have hd : (∏i,primeAt outside i)∣outside.prod := by rw [primeAt_prod]
  have he := mixed_projected_product_average (primeAt outside) (primeAt_pairwise h hs) hd
    (fun i=>primePair h k g outside (primeAt outside i))
  calc
    _ = average (fun z : MixedPair outside.prod=>∏i:Fin outside.length,
        primePair h k g outside (primeAt outside i)
          (projectedRingPair ((Finset.dvd_prod_of_mem (primeAt outside)
            (Finset.mem_univ i)).trans hd) (z.1,(z.2:ZMod outside.prod)))) := by
      congr 1
      funext z
      exact residuePair_eq_projected_product h k hs ks had g (z.1,z.2)
    _ = _ := he

end Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage

end

end OAI
