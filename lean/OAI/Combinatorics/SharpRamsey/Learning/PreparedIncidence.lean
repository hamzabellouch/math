import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedSource

namespace OAI

section
namespace SharpLogRamsey.Selection.ExposureModel
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ ι C : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype Ω] [Fintype Θ]
  [Fintype ι] [DecidableEq ι] [Fintype C]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
variable (n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→ι→Projectivization K (Module.Dual K V)×Projectivization K V)
  (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
  (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
  (z : (contextual n k p θ G e own t).FreshHistory)
  (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
  (pos : ι→ℕ)
  (hcon : ∀ ω,p.mass ω≠0→∀ i j,pos i<pos j→
    (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
include hp hz hcon

omit [Finite K] [FiniteDimensional K V] in
lemma prepared_consistency
    (i j : (contextual n k p θ G e own t).Index z.1)
    (hij : pos ((contextual n k p θ G e own t).origin z.1 i)<
      pos ((contextual n k p θ G e own t).origin z.1 j)) :
    ∀ y,((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0→
      (y i).1.rep (y j).2.rep=0→(y j).1.rep (y i).2.rep=0 := by
  intro y hy
  exact prepared_pair_property n k p θ G e own t hp z hz
    (fun _ i j a b=>pos i<pos j→a.1.rep b.2.rep=0→b.1.rep a.2.rep=0)
    hcon i j y hy hij

theorem prepared_integer_event
    (i j : (contextual n k p θ G e own t).Index z.1)
    (hij : pos ((contextual n k p θ G e own t).origin z.1 i)<
      pos ((contextual n k p θ G e own t).origin z.1 j))
    (P κ gap u v J D a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hP : 0<P) (hr : r≤d+1)
    (hu : IntegerBand r (log (Nat.card K)) gap u)
    (hv : IntegerBand r (log (Nat.card K)) gap v)
    (hsmall : log P+3*κ+gap<log (Nat.card K)) (hκ : log (200/97)≤κ)
    (hgood :
      let M:=contextual n k p θ G e own t
      let c:=reciprocalCharges (M.tupleLaw z.1) Projectivization.rep Projectivization.rep
        (1/(100*((d:ℝ)+1))) r (d+1-r)
      (i∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) c J D a z.2 ∧
        j∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 i) ∨
      (j∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) c J D a z.2 ∧
        i∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 j)) :
    let q:=(contextual n k p θ G e own t).tupleLaw z.1
    ((q.marginal i).fst.prod (q.marginal j).snd).event (univ.filter (fun ay=>
      goodFirst (q.marginal i) (P*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (q.marginal j) (P*exp v) ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0))≤(20000*((d:ℝ)+1)^2+8)*a := by
  let M:=contextual n k p θ G e own t
  apply integer_band_event_le (M.tupleLaw z.1) i j P κ gap u v a d r hdim hP hr
    hu hv hsmall hκ
    (prepared_consistency n k p θ G e own t hp z hz pos hcon i j hij)
  exact good_charge_either (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    _ (reciprocalCharges_symm _ _ _ _ _ _) J D a z.2 i j hgood

theorem prepared_open_event
    (i j : (contextual n k p θ G e own t).Index z.1)
    (hij : pos ((contextual n k p θ G e own t).origin z.1 i)<
      pos ((contextual n k p θ G e own t).origin z.1 j))
    (P κ gap u v J D a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hP : 0<P) (hr : r≤d+1)
    (hu : OpenBand r (log (Nat.card K)) gap u)
    (hv : OpenBand r (log (Nat.card K)) gap v)
    (hsmall : log P+3*κ<gap) (hκ : log (200/97)≤κ)
    (hgood :
      let M:=contextual n k p θ G e own t
      (i∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J D a z.2 ∧
        j∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 i) ∨
      (j∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J D a z.2 ∧
        i∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 j)) :
    let q:=(contextual n k p θ G e own t).tupleLaw z.1
    ((q.marginal i).fst.prod (q.marginal j).snd).event (univ.filter (fun ay=>
      goodFirst (q.marginal i) (P*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (q.marginal j) (P*exp v) ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0))≤(20000*((d:ℝ)+1)^2)*a := by
  let M:=contextual n k p θ G e own t
  apply open_band_event_le (M.tupleLaw z.1) i j P κ gap u v a d r hdim hP hr
    hu hv hsmall hκ
    (prepared_consistency n k p θ G e own t hp z hz pos hcon i j hij)
  have hh:=good_charge_either (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    (fun _ _=>0) (by intros; rfl) J D a z.2 i j hgood
  simpa only [NNReal.coe_zero,add_zero] using hh

end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
