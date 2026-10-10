import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.UniformStep
import OAI.Combinatorics.SharpRamsey.Marking.TrackedSelection

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Marking
open scoped Classical BigOperators
noncomputable section
variable {Ω α : Type} [Fintype Ω] [Fintype α] {n m : ℕ}
  {p : Law Ω} {G : Ω→Fin n→α} {B C L : ℝ}

lemma ContextOutput.log_size (e : ContextOutput p G m B C L) {J : ℝ}
    (hJ : 0 ≤ J) (hB : B ≤ exp J) : ∀ z i,log (e.domains z i).card ≤ J := by
  intro z i
  by_cases hz : (e.domains z i).card=0
  · simpa only [hz,Nat.cast_zero,log_zero] using hJ
  · have hp : (0:ℝ) < (e.domains z i).card:=by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (log_le_log hp ((e.size z i).trans hB)).trans_eq (log_exp _)

lemma ContextOutput.count_bound (e : ContextOutput p G m B C L) (P : α→Prop)
    {M : ℝ} (h : ∀ x,p.mass x≠0→((univ.filter (fun i=>P (G x i))).card:ℝ) ≤ M) :
    ∀ x,((univ.filter (fun i=>P (G (e.source x) (e.chosen x i)))).card:ℝ) ≤ M := by
  intro x
  have hh:=count_injective_restriction (e.chosen x).toEmbedding (fun i=>P (G (e.source x) i))
  apply le_trans _ (h _ (e.supported x))
  exact (Nat.cast_le (α:=ℝ)).mpr hh

lemma ContextOutput.tracked_linear [Nonempty α] {β : Type} [Fintype β] {N n m : ℕ}
    {H : Ω→Fin n→β} (e : ContextOutput p H m B C L)
    (stream : Ω→Fin N→α) (F : Ω→Fin n→α)
    (φ : α→β) (hφ : Function.Injective φ) (hH : ∀ x i,H x i=φ (F x i))
    {d : ℕ} (hd : 1 ≤ d) (hm : 0 < m) (hn : n ≤ N)
    {D q σ η c : ℝ} (hD : 0 < D) (hL : 0 < L) (hq : 0 < q) (hσ : 1 ≤ σ)
    (hη : 0 ≤ η) (hc : 0 < c)
    (hdom : ∀ g,(p.map stream).mass g ≤ D/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ m)
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (m:ℝ)*((d:ℝ)*log q)-(1+|log c|+|log (2*(L*D))|)*m ≤
      entropy (e.μ.map (fun x i=>H (e.source x) (e.chosen x i))) := by
  have hh:=e.tracked_entropy stream F φ hφ hH hd hm hn hD hL hq (by linarith) hc
    hdom hselect hsize hlength halphabet
  have hpos : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hgain : 0 ≤ (m:ℝ)*(η*log σ):=mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hη (log_nonneg hσ))
  have hm' : |log (2*(L*D))| ≤ (m:ℝ)*|log (2*(L*D))|:=le_mul_of_one_le_left (abs_nonneg _) hpos
  have hc':=mul_le_mul_of_nonneg_left (neg_abs_le (log c)) (Nat.cast_nonneg m)
  nlinarith only [hh,hgain,hm',hc',le_abs_self (log (2*(L*D)))]
end
end SharpLogRamsey.Selection

end

end OAI
