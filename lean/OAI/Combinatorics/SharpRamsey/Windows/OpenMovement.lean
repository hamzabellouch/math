import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.IntegerRealization

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ}
local instance moveDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
local instance moveSlotDec : DecidableEq (Slot w (n+k)) :=
  @instDecidableEqProd (Fin w) (Fin (4*(n+k))) (@instDecidableEqFin w) (@instDecidableEqFin (4*(n+k)))
local instance moveBlockDec : DecidableEq (Block w) := Classical.decEq _
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (z : (model w n k p θ G t).FreshHistory)
  (hz : ((model w n k p θ G t).freshLaw hp).mass z≠0)
local notation "M" => model w n k p θ G t
local notation "q" => ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst z)

include hp hz

theorem open_window_deletion
    (hdim : Module.finrank K V=d+3)
    (r : ℕ) (hr : r≤d+3) (κ gap J D a : ℝ) (hgap : 0≤gap)
    (u : (M).Index z.1→ℝ)
    (hband : ∀ i,OpenBand r (log (Nat.card K)) gap (u i))
    (hsmall : log 1024+3*κ<gap) (hκ : log (200/97)≤κ)
    (hsparse : (4*exp 1)^2*(20000*((d:ℝ)+3)^2*a)≤1/(4*(Nat.card K:ℝ)))
    (hcon : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
    (hsupp :
      let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) (fun _ _=>0) J D a z.2
      ∀ i,i∉bad→
      let qi:=(q).marginal i
      let MA:=1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
      let MB:=1024*exp (u i)
      let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
      Nonempty (AuxiliarySupport qi.fst (univ.filter (goodFirst qi MA L κ (1/50))) MA κ) ∧
      Nonempty (AuxiliarySupport qi.snd (univ.filter (goodSecond qi MB L κ (1/50))) MB κ)) :
    let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) (fun _ _=>0) J D a z.2
    let live:=univ\badWindows ((M).representative z) bad
    gap*((live.filter (fun i=>gap<u ((M).representative z (i,false))-
      u ((M).representative z (i,true)))).card:ℝ)≤
      log (Nat.card K)+(2*κ+log 64)*w := by
  dsimp only
  let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) (fun _ _=>0) J D a z.2
  let live:=univ\badWindows ((M).representative z) bad
  have hgood : ∀ i∈live,∀ c,(M).representative z (i,c)∉bad := by
    intro i hi v
    have hh:¬((M).representative z (i,false)∈bad ∨ (M).representative z (i,true)∈bad) := by
      simpa only [live,mem_sdiff,mem_univ,true_and,badWindows,mem_filter,true_and] using hi
    cases v
    · exact fun h=>hh (Or.inl h)
    · exact fun h=>hh (Or.inr h)
  have hcross : ∀ i∈live,∀ j∈live,i<j→
      u ((M).representative z (j,false))≤u ((M).representative z (i,true))+(2*κ+log 64) := by
    intro i hi j hj hij
    let ii:=(M).representative z (i,true)
    let jj:=(M).representative z (j,false)
    have he:=prepared_open_event n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz position hcon ii jj
      (representative_before w n k p θ G t z i j hij true false)
      1024 κ gap (u ii) (u jj) J D a (d+2) r
      (by simpa [Nat.add_assoc] using hdim) (by norm_num) (by omega)
      (hband ii) (hband jj) hsmall hκ
      (Or.inl ⟨hgood i hi true,representative_other w n k p θ G t z (j,false) (i,true) (by simp)⟩)
    have hh:=chronological_order_of_good_event hdim q ii jj 1024 κ (u ii) (u jj)
      (((d+2:ℕ):ℝ)*log (Nat.card K)) (1/50) (20000*((d:ℝ)+3)^2*a) (by norm_num)
      (hsupp ii (hgood i hi true)).1.some (hsupp jj (hgood j hj false)).2.some
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,show (d:ℝ)+2+1=(d:ℝ)+3 by ring] using he)
      hsparse
    simpa only [add_assoc] using hh
  have hlog : 0≤log (Nat.card K:ℝ) := by
    apply log_nonneg
    exact_mod_cast (show 1≤Nat.card K from Finite.card_pos)
  have hκ0 : 0≤κ := (log_nonneg (by norm_num : (1:ℝ)≤200/97)).trans hκ
  have hh:=downward_deleted live
    (fun i=>u ((M).representative z (i,false)))
    (fun i=>u ((M).representative z (i,true)))
    (((r:ℝ)-1)*log (Nat.card K)) ((r:ℝ)*log (Nat.card K)) (2*κ+log 64) gap
    (by nlinarith) (by have hl:=log_nonneg (show (1:ℝ)≤64 by norm_num); linarith)
    (by intro i hi; have hb:=(hband ((M).representative z (i,true))).1; linarith)
    (by intro i hi; have hb:=(hband ((M).representative z (i,false))).2; linarith)
    hcross
  simp only [Fintype.card_fin] at hh
  convert hh using 1
  ring
end
end SharpLogRamsey.Selection.Windows

end

end OAI
