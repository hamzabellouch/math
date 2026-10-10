import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.HighRankReplacement
import OAI.Combinatorics.SharpRamsey.Windows.GoodPopulation
import OAI.Combinatorics.SharpRamsey.Reciprocal.PreparedReciprocal
import OAI.Combinatorics.SharpRamsey.Marking.HighRankConflict

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankPrepared_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

local instance flat_ActualHighRankPrepared_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankPrepared_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankPrepared_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

theorem eventually_prepared_high {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2≤r → r≤d → d+2≤r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
        (z : (model w n k p θ G t).FreshHistory),
        ((model w n k p θ G t).freshLaw hp).mass z≠0 →
      ∀ i : Fin w,
      let M:=model w n k p θ G t
      let q:=M.tupleLaw z.1
      let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
      let bad:=badIndices q (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J (D*σ^beta η) a z.2
      M.representative z (i,false)∉bad →
      0<(goodMiddle w n k p θ G t z bad i).card →
      Nonempty (Replacement q (fun y j=>y (goodTarget w n k p θ G t z bad i j))
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_replacement hη d hd] with σ he
  intro K Ω Θ _ _ _ _ hlog w n k p θ G S D J r r' hDl hDu hJ hr hrd hrr hS hf hcon hcap t hp z hz i
  dsimp only
  let M:=model w n k p θ G t
  let q:=M.tupleLaw z.1
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let bad:=badIndices q (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J (D*σ^beta η) a z.2
  let rep:=M.representative z (i,false)
  let T:=goodTarget w n k p θ G t z bad i
  intro hrep hlen
  have hc:=prepared_context_property n k p θ G (fun _=>embedding w (n+k))
    (fun _=>owner w (n+k)) t hp z hz (fun θ=>∀ i,Caps σ r r' (S θ i)) hcap
  have entropy_good j (hj : j∉bad) : (d:ℝ)*σ-entropy (q.marginal j)≤D*σ^beta η := by
    have hh:=((not_badIndices q (M.embedding z.1) (M.owner z.1)
      (fun _ _=>0) J (D*σ^beta η) a z.2 j).mp hj).1
    exact (sub_le_sub_right hJ _).trans hh
  have targetgood j : T j∉bad := goodTarget_not_bad w n k p θ G t z bad i j
  have targetbefore j : position (M.origin z.1 rep)<position (M.origin z.1 (T j)) := by
    exact (target_between w n k p θ G t z i ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j)).1
  have hsrc y (hy : q.mass y≠0) := contextual_fresh_source n k p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp z hz y hy
  apply he K _ hlog _ hlen (q.marginal rep) (S z.1.1 (M.origin z.1 rep)) q
    (fun y j=>y (T j)) (fun j=>S z.1.1 (M.origin z.1 (T j))) D hDl hDu r r' hr hrd hrr
  · exact prepared_marginal_domain n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz S hS rep
  · exact hc _
  · exact entropy_good rep hrep
  · intro y hy j
    obtain ⟨ω,hω,hθ,hG⟩:=hsrc y hy
    have hvalue : G ω (M.origin z.1 (T j))=y (T j) := hG (T j)
    simpa only [hθ,hvalue] using hS ω hω (M.origin z.1 (T j))
  · intro y hy j
    obtain ⟨ω,hω,hθ,hG⟩:=hsrc y hy
    have hvalue : G ω (M.origin z.1 (T j))=y (T j) := hG (T j)
    simpa only [hvalue] using hf ω hω (M.origin z.1 (T j))
  · intro j
    exact hc _
  · intro j
    exact entropy_good (T j) (targetgood j)
  · intro j
    have hi : (pairInformation q rep (T j):ℝ)≤a := by
      have hh:=good_charge_reversed q (M.embedding z.1) (M.owner z.1)
        (fun _ _=>0) (by simp) J (D*σ^beta η) a z.2 (T j) rep (targetgood j)
        (target_other w n k p θ G t z (i,false) i
          ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j))
      simpa only [NNReal.coe_zero,add_zero] using hh
    have hh:=high_original_conflict q rep (T j) (by
      intro y hy hzero
      obtain ⟨ω,hω,hθ,hG⟩:=hsrc y hy
      have hc':=hcon ω hω (M.origin z.1 rep) (M.origin z.1 (T j)) (targetbefore j)
      rw [hG,hG] at hc'
      exact hc' hzero)
    exact hh.trans (by
      calc
        2*(pairInformation q rep (T j):ℝ) ≤ 2*a := mul_le_mul_of_nonneg_left hi (by norm_num)
        _ = _ := by dsimp [a]; ring)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
