import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramProductBasic

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistorySignedResidues HistorySignedSpectatorCRT
open HistoryRepresentativeSourceSeparation

theorem residueSpectator_eq_primeProduct {l : ℕ} (h : History l)
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ) (R : ℤ) (N : ℕ)
    (hd : ∀ q ∈ outside, q ∣ N) (hdiv : DivisorData R h)
    (hc : Nat.Coprime R.natAbs N) (Xp Xm : ZMod N) :
    residueSpectator g outside N h Xp Xm =
      (outside.map (fun q => primeSpectator q (g q)
        ((outsideProduct outside/q:ℕ):ZMod q) h (ZMod.cast Xp) (ZMod.cast Xm))).prod := by
  induction h generalizing Xp Xm with
  | leaf a => rfl
  | node a p u hp hm left right il ir =>
    have hcop := hc.of_dvd_left (Int.natAbs_dvd_natAbs.mpr hdiv.2.1)
    simp only [residueSpectator]
    rw [il hdiv.2.2.1,ir hdiv.2.2.2,map_list_prod,List.map_map,← List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro q hq
    simp only [primeSpectator,Function.comp_def]
    rw [residuePivot_cast (hd q hq) a left.root.frequency right.root.frequency u hp hm Xp Xm hcop]

theorem residuePairSpectator_eq_primeProduct {l : ℕ} (h k : History l)
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ) (R : ℤ) (N : ℕ)
    (hd : ∀ q ∈ outside, q ∣ N) (hh : DivisorData R h) (hk : DivisorData R k)
    (hc : Nat.Coprime R.natAbs N) (z : ZMod N × ZMod N) :
    residuePairSpectator g outside N h k z =
      (outside.map (fun q =>
        primeSpectator q (g q) ((outsideProduct outside/q:ℕ):ZMod q)
          h (ZMod.cast z.1) (ZMod.cast z.2) *
        conj (primeSpectator q (g q) ((outsideProduct outside/q:ℕ):ZMod q)
          k (ZMod.cast z.1) (ZMod.cast z.2)))).prod := by
  rw [residuePairSpectator,residueSpectator_eq_primeProduct h g outside R N hd hh hc,
    residueSpectator_eq_primeProduct k g outside R N hd hk hc,
    map_list_prod,List.map_map,List.prod_map_mul]
  rfl

theorem residuePairSpectator_eq_primeProduct_actual {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (g : (q : ℕ) → ZMod q → ℂ)
    (z : ZMod outside.prod × ZMod outside.prod) :
    residuePairSpectator g outside outside.prod h k z =
      (outside.map (fun q =>
        primeSpectator q (g q) ((outsideProduct outside/q:ℕ):ZMod q)
          h (ZMod.cast z.1) (ZMod.cast z.2) *
        conj (primeSpectator q (g q) ((outsideProduct outside/q:ℕ):ZMod q)
          k (ZMod.cast z.1) (ZMod.cast z.2)))).prod := by
  have hd := paired_divisorData h k hs ks
  exact residuePairSpectator_eq_primeProduct h k g outside (pairedDivisorProduct h k)
    outside.prod (fun q hq => List.dvd_prod hq) hd.1 hd.2
    (pairedDivisorProduct_coprime_outside h k hs ks had) z

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
