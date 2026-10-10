import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjectedProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagram

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage
open Construction HistorySignedSpectatorCRT HistorySignedSpectatorDiagram
open HistoryCRTIntegration HistoryRepresentativeSourceSeparation ResidueHaar

abbrev primeAt (outside : List ℕ) (i : Fin outside.length) : ℕ := outside.get i

theorem primeAtNeZero {outside : List ℕ} (hp : ∀q∈outside,q.Prime) :
    ∀i,NeZero (primeAt outside i) :=
  fun i=>⟨(hp _ (List.get_mem _ i)).ne_zero⟩

theorem outsideNeZero {outside : List ℕ} (hp : ∀q∈outside,q.Prime) : NeZero outside.prod :=
  ⟨(List.prod_pos (fun q hq=>(hp q hq).pos)).ne'⟩

theorem primeAt_prod (outside : List ℕ) : (∏i,primeAt outside i)=outside.prod := by
  simpa only [primeAt,List.get_eq_getElem,id_eq,List.map_id] using Fin.prod_univ_fun_getElem outside id

theorem primeAt_pairwise {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    Pairwise (fun i j=>Nat.Coprime (primeAt outside i) (primeAt outside j)) := by
  have ho := (List.pairwise_append.mp (History.supported_root_coprime hs)).2.1
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ho.rel_get_of_lt hij
  · exact (ho.rel_get_of_lt hji).symm

def primePair {l : ℕ} (h k : History l) (g : (q:ℕ)→ZMod q→ℂ)
    (outside : List ℕ) (q : ℕ) (z : ZMod q×ZMod q) : ℂ :=
  primeSpectator q (g q) ((outsideProduct outside/q:ℕ):ZMod q) h z.1 z.2 *
    conj (primeSpectator q (g q) ((outsideProduct outside/q:ℕ):ZMod q) k z.1 z.2)

theorem residuePair_eq_projected_product {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (g : (q:ℕ)→ZMod q→ℂ)
    (z : ZMod outside.prod×ZMod outside.prod) :
    residuePairSpectator g outside outside.prod h k z=
      ∏i:Fin outside.length,primePair h k g outside (primeAt outside i)
        (projectedRingPair (List.dvd_prod (List.get_mem outside i)) z) := by
  rw [residuePairSpectator_eq_primeProduct_actual h k hs ks had]
  symm
  simpa only [primePair,primeAt,List.get_eq_getElem,projectedRingPair,ZMod.castHom_apply] using
    Fin.prod_univ_fun_getElem outside (fun q=>primePair h k g outside q (ZMod.cast z.1,ZMod.cast z.2))

end Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage

end

end OAI
