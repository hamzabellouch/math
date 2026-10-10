import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.HighRankMixture
import OAI.Combinatorics.SharpRamsey.Learning.HighRankPrepared
import OAI.Combinatorics.SharpRamsey.Marking.HighGoodHistory

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankStream_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
local instance flat_ActualHighRankStream_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankStream_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankStream_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance flat_ActualHighRankStream_5 {K : Type} [Field K] {d : ℕ} : DecidableEq (Projectivization K (Module.Dual K (Fin (d+1)→K)) × Projectivization K (Fin (d+1)→K)) := Classical.decEq _

theorem eventually_high_stream {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 0<n → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot 1 (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot 1 (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2≤r → r≤d → d+2≤r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      ∀ (t : Fin k) (hp : ∀ z,0<(model 1 n k p θ G t).remaining z),
      let M:=model 1 n k p θ G t
      let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
      let bad:=M.freshBad (fun _ _ _=>0) J (D*σ^beta η) a
      ∀ A : ℝ, A≤((2*(n+k):ℕ):ℝ)/20 →
      (∑ z,(M.freshLaw hp).mass z*((bad z).card:ℝ))≤A →
      (n:ℝ)*(∑ z,(M.freshLaw hp).mass z*((M.freshSelected z∩bad z).card:ℝ))≤A →
      Nonempty (StreamReplacement p G position ((n+k)/2)
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_prepared_high hη d hd] with σ he
  intro K Ω Θ _ _ _ _ hlog n k hn hkn p θ G S D J r r' hDl hDu hJ hr hrd hrr hS hf hcon hcap t hp
  dsimp only
  intro A hA hb hs
  let M:=model 1 n k p θ G t
  let μ:=M.freshLaw hp
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let bad:=M.freshBad (fun _ _ _=>0) J (D*σ^beta η) a
  let E:=univ.filter (fun z=>M.representative z (0,false)∉bad z ∧
    ((2*(n+k):ℕ):ℝ)/2≤(goodMiddle 1 n k p θ G t z (bad z) 0).card)
  let H:=E.filter (fun z=>μ.mass z≠0)
  have hH : (1:ℝ)/2≤μ.event H := by
    rw [Law.event_nonzero_filter]
    exact high_good_history_half n k hn hkn p θ G t hp bad A hb hs hA
  have hzpos (z : H) : μ.mass z.val≠0 := (mem_filter.mp z.property).2
  have hrep (z : H) : M.representative z.val (0,false)∉bad z.val :=
    (mem_filter.mp (mem_filter.mp z.property).1).2.1
  let ℓ:=fun z : H=>(goodMiddle 1 n k p θ G t z.val (bad z.val) 0).card
  have hℓ (z : H) : n+k≤ℓ z := by
    have hh:=(mem_filter.mp (mem_filter.mp z.property).1).2.2
    have he : ((2*(n+k):ℕ):ℝ)/2=(n+k:ℕ) := by push_cast; ring
    rw [he] at hh
    exact_mod_cast hh
  let Q:=fun z : M.FreshHistory=>M.Index z.1→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)
  let q : ∀ z,Law (Q z):=fun z=>M.tupleLaw z.1
  let target:=fun (z : H) (y : Q z.val) (i : Fin (ℓ z))=>
    y (goodTarget 1 n k p θ G t z.val (bad z.val) 0 i)
  let DD:=fun code=>rawDomain (K:=K) (d:=d) (h:=rawRows σ η) code r (rawThreshold σ η)
  let B₀:=highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D)
  let C₀:=4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ)
  have hex (z : H) : Nonempty (Replacement (q z.val) (target z) DD B₀ C₀) := by
    apply he K Ω Θ hlog 1 n k p θ G S D J r r' hDl hDu hJ hr hrd hrr hS hf hcon hcap t hp z.val
      (hzpos z) 0 (hrep z)
    exact (by omega : 0<n+k).trans_le (hℓ z)
  let e :=fun z=>Classical.choice (hex z)
  have hrestore : (μ.sigma q).map (fun z=>M.restore z.1.1 z.2)=p.map G := by
    apply (M.afterDraw hp).restored_map
    intro φ
    rw [afterDraw_preserves,contextual_preserves,Law.sum_map]
  let loc:=fun (z : H) (i : Fin (ℓ z))=>M.origin z.val.1
    (goodTarget 1 n k p θ G t z.val (bad z.val) 0 i)
  have hloc : ∀ z,StrictMono (fun i=>position (loc z i)) := by
    intro z i j hij
    exact goodTarget_before 1 n k p θ G t z.val (bad z.val) 0 i j hij
  have hval : ∀ z y i,M.restore z.val.1 y (loc z i)=target z y i := by
    intro z y i
    exact M.restore_origin z.val.1 y _
  have hm : ∀ z,(n+k)/2≤ℓ z/2 := fun z=>Nat.div_le_div_right (hℓ z)
  have hcost : ∀ (Y : Type) [Fintype Y] (ν : Law Y)
      (msg : Y→((Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))×
        (Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))),
      entropy (ν.map msg)≤C₀ := by
    intro Y _ ν msg
    have hh:=raw_entropy (by simp : Module.finrank K (Fin (d+1)→K)=d+1) ν msg
    rwa [hlog] at hh
  have mix0 := mix_stream_replacement (Γ:=
      ((Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))×
        (Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))))
      p G position μ Q q
  have mix1 := mix0 (fun z=>M.restore z.1) hrestore H hH ℓ target loc hloc hval
  have mix2 := mix1 ((n+k)/2) hm DD B₀ C₀
  have hh:=mix2 e hcost
  exact hh

end
end SharpLogRamsey.Selection.Windows

end

end OAI
