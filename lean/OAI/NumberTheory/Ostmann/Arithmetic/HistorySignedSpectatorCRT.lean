import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTSources

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorCRT
open Construction HistorySignedDecode HistorySignedResidues
open HistoryRepresentativeSourceSeparation

theorem residuePairSpectator_intCast_actual {l : ℕ} (h k : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (g : (q:ℕ)→ZMod q→ℂ) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (ki : (rebuild k Xp Xm).IntegralGuard) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm)=
      HistorySignedSpectator.pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm) := by
  have hd := paired_divisorData h k hs ks
  have hc := pairedDivisorProduct_coprime_outside h k hs ks had
  rw [residuePairSpectator,HistorySignedSpectator.pairSpectator,
    residueSpectator_intCast h g outside _ outside.prod (fun q hq=>List.dvd_prod hq) hd.1 hc Xp Xm hi,
    residueSpectator_intCast k g outside _ outside.prod (fun q hq=>List.dvd_prod hq) hd.2 hc Xp Xm ki]

theorem norm_residueLeaf_le (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hg : ∀q∈outside,∀x,‖g q x‖≤1) (N : ℕ) (a : State) (Xp Xm : ZMod N) :
    ‖residueLeaf g outside N a Xp Xm‖≤1 := by
  apply HistorySignedSpectator.norm_prod_le_one
  intro z hz
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
  exact hg q hq _

theorem norm_residueSpectator_le (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hg : ∀q∈outside,∀x,‖g q x‖≤1) (N : ℕ) {l : ℕ} (h : History l)
    (Xp Xm : ZMod N) : ‖residueSpectator g outside N h Xp Xm‖≤1 := by
  induction h generalizing Xp Xm with
  | leaf a => exact norm_residueLeaf_le g outside hg N a Xp Xm
  | node a p u hp hm left right il ir =>
    simpa only [residueSpectator,norm_mul,Complex.norm_conj,one_mul] using
      mul_le_mul (il (residuePivot N a left.root.frequency right.root.frequency u hp hm Xp Xm) Xp)
        (ir (residuePivot N a left.root.frequency right.root.frequency u hp hm Xp Xm) Xm)
        (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem norm_residuePairSpectator_le (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hg : ∀q∈outside,∀x,‖g q x‖≤1) (N : ℕ) {l : ℕ} (h k : History l)
    (z : ZMod N×ZMod N) : ‖residuePairSpectator g outside N h k z‖≤1 := by
  simpa only [residuePairSpectator,norm_mul,Complex.norm_conj,one_mul] using
    mul_le_mul (norm_residueSpectator_le g outside hg N h z.1 z.2)
      (norm_residueSpectator_le g outside hg N k z.1 z.2)
      (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

end Ostmann.Arithmetic.HistorySignedSpectatorCRT

end

end OAI
