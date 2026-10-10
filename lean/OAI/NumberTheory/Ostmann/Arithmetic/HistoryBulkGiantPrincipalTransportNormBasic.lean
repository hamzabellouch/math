import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistorySignedSpectatorCRT HistorySignedResidues

theorem norm_residueLeaf_le_product (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (B : ℕ → ℝ) (hB : ∀q∈outside,0≤B q)
    (hg : ∀q∈outside,∀x,‖g q x‖≤B q) (N : ℕ) (a : State) (Xp Xm : ZMod N) :
    ‖residueLeaf g outside N a Xp Xm‖≤(outside.map B).prod :=
  norm_map_prod_le outside _ B hB (fun q hq=>hg q hq _)

theorem norm_residueSpectator_le_power (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (B : ℕ → ℝ) (hB : ∀q∈outside,0≤B q)
    (hg : ∀q∈outside,∀x,‖g q x‖≤B q) (N : ℕ) {l : ℕ} (h : History l)
    (Xp Xm : ZMod N) : ‖residueSpectator g outside N h Xp Xm‖≤(outside.map B).prod^(2^l) := by
  have hP : 0≤(outside.map B).prod := List.prod_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hB q hq)
  induction h generalizing Xp Xm with
  | leaf a =>
    simpa only [residueSpectator,pow_zero,pow_one] using
      norm_residueLeaf_le_product g outside B hB hg N a Xp Xm
  | @node l a p u hp hm left right il ir =>
    simp only [residueSpectator,norm_mul,Complex.norm_conj]
    calc
      _ ≤ (outside.map B).prod^(2^l)*(outside.map B).prod^(2^l) :=
        mul_le_mul (il _ Xp) (ir _ Xm) (norm_nonneg _) (pow_nonneg hP _)
      _ = (outside.map B).prod^(2^(l+1)) := by rw [pow_succ,pow_mul,pow_two]

theorem norm_residuePairSpectator_le_power (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (B : ℕ → ℝ) (hB : ∀q∈outside,0≤B q)
    (hg : ∀q∈outside,∀x,‖g q x‖≤B q) (N : ℕ) {l : ℕ} (h k : History l)
    (z : ZMod N×ZMod N) : ‖residuePairSpectator g outside N h k z‖≤(outside.map B).prod^(2^(l+1)) := by
  have hP : 0≤(outside.map B).prod := List.prod_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hB q hq)
  rw [residuePairSpectator,norm_mul,Complex.norm_conj]
  calc
    _ ≤ (outside.map B).prod^(2^l)*(outside.map B).prod^(2^l) :=
      mul_le_mul (norm_residueSpectator_le_power g outside B hB hg N h z.1 z.2)
        (norm_residueSpectator_le_power g outside B hB hg N k z.1 z.2)
        (norm_nonneg _) (pow_nonneg hP _)
    _ = (outside.map B).prod^(2^(l+1)) := by rw [pow_succ,pow_mul,pow_two]

theorem norm_actual_residuePairSpectator_le (d : Decomposition) (outside : List ℕ)
    (hout : ∀q∈outside,q.Prime) (N : ℕ) {l : ℕ} (h k : History l) (z : ZMod N×ZMod N) :
    ‖residuePairSpectator (residueTransform d) outside N h k z‖≤(outside.prod:ℝ)^(2^(l+1)) := by
  simpa only [Nat.cast_list_prod] using norm_residuePairSpectator_le_power
    (residueTransform d) outside (fun q=>(q:ℝ)) (fun q _=>Nat.cast_nonneg q)
    (fun q hq x=>residueTransform_norm_le_prime d q (hout q hq) x) N h k z

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
