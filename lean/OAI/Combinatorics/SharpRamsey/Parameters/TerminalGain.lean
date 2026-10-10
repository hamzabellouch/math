import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TrackedStep

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance gainFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance gainFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance gainProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance gainDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance gainDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

lemma flag_context_gain (i q : ℕ) [Fact q.Prime] (σ η c Lstar : ℝ)
    (hσ : 1 ≤ σ) (hη : 0 ≤ η) (hc : 0 < c) (hLs : 0 < Lstar)
    (he : exp σ=(q:ℝ))
    (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
    (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (B Λ L : ℝ) (hLL : L ≤ Lstar) (hkn : k ≤ N)
    (hdom : ∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*σ)
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m B Λ L)
    (hmlo : c*(q:ℝ)*σ^(1+η) ≤ m) :
    (m:ℝ)*(((i+3:ℕ):ℝ)*σ+η*log σ)-(1+|log c|+|log (2*(Lstar*2))|)*m ≤
      entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) := by
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hσ0 : 0 < σ:=by linarith
  have hm : 0 < m:=by
    have hscale : 0 < σ^(1+η):=
      lt_of_lt_of_le zero_lt_one (one_le_rpow hσ (by linarith only [hη]))
    have : (0:ℝ) < m:=(mul_pos (mul_pos hc hq0) hscale).trans_le hmlo
    exact_mod_cast this
  have halphabet:=flag_alphabet_lower i q
  have : Nonempty (Flag (ZMod q) (Fin (i+4)→ZMod q)):=Fintype.card_pos_iff.mp (by
    have : (0:ℝ) < (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ):=(pow_pos hq0 _).trans_le halphabet
    exact_mod_cast this)
  let ee:=e.mono (le_refl _) (le_refl _) hLL
  have hh:=ee.tracked_entropy stream F flagPair flagPair_injective (by intros;rfl)
    (by omega : 1 ≤ i+3) hm hkn (by norm_num : (0:ℝ) < 2) hLs hq0 hσ0 hc
    hdom hselect hN hmlo halphabet
  have hlogq : log (q:ℝ)=σ:=by rw [←he,log_exp]
  rw [hlogq] at hh
  dsimp only [ee,ContextOutput.mono] at hh
  have hh' : (m:ℝ)*(((i+3:ℕ):ℝ)*σ+η*log σ+log c-1)-log (2*(Lstar*2)) ≤
      entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) := by
    convert hh using 1
    first | ring | congr!
  have hpos : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hm' : |log (2*(Lstar*2))| ≤ (m:ℝ)*|log (2*(Lstar*2))|:=le_mul_of_one_le_left (abs_nonneg _) hpos
  have hc':=mul_le_mul_of_nonneg_left (neg_abs_le (log c)) (Nat.cast_nonneg m)
  nlinarith only [hh',hm',hc',le_abs_self (log (2*(Lstar*2)))]

end
end SharpLogRamsey.Marking

end

end OAI
