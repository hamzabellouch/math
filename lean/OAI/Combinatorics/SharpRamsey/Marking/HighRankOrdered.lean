import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.StreamTransport
import OAI.Combinatorics.SharpRamsey.Marking.HighRankExperiment
import OAI.Combinatorics.SharpRamsey.Marking.HighRankClass

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankOrdered_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankOrdered_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankOrdered_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankOrdered_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance flat_ActualHighRankOrdered_5 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

theorem eventually_high_ordered {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d)
    (C c : ℝ) (hC : 0≤C) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 2≤n → 0<k → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (F : Ω→Fin (4*(n+k))→ProjectivePair (K:=K) (V:=Fin (d+1)→K))
        (S : Θ→Fin (4*(n+k))→Finset (ProjectivePair (K:=K) (V:=Fin (d+1)→K)))
        (D J budget gap : ℝ) (r r' : Fin (d+1)), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      (∀ ω,p.mass ω≠0→∀ i,F ω i∈S (θ ω) i) →
      (∀ z i,log (S z i).card≤J) →
      (∀ ω,p.mass ω≠0→∀ i,Incidence.Incident (F ω i).1 (F ω i).2) →
      (∀ ω,p.mass ω≠0→ScanConsistent ((List.ofFn (F ω)).map toScan)) →
      (∀ ω,p.mass ω≠0→∀ i,ValidSlotClass d gap (S (θ ω) i) (.inr (r,r'))) →
      (∀ z i,((S z i).card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∑ z : Θ,(p.map θ).mass z*(((4*(n+k):ℕ):ℝ)*J-
          entropy ((p.cond θ z).map F)))≤budget →
      budget≤C*((2*(n+k):ℕ):ℝ)*D*σ^(-beta η) →
      c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
      Nonempty (StreamReplacement p F Fin.val ((n+k)/2)
        (fun code=>(rawDomain (h:=rawRows σ η) code r.val (rawThreshold σ η)).map
          (Equiv.prodComm _ _).toEmbedding)
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_high_experiment hη d hd C c hC hc] with σ he
  intro K Ω Θ _ _ _ _ hlog n k hn hk hkn p θ F S D J budget gap r r' hDl hDu hJ
    hS hSJ hf hcon hclass hsize hbudget hb hk0
  have hpos : ∃ ω,p.mass ω≠0 := by
    by_contra hh
    have hz : ∀ ω,p.mass ω=0 := by simpa only [not_exists,not_not] using hh
    have hh:=p.total
    simp only [hz,sum_const_zero] at hh
    norm_num at hh
  obtain ⟨ω,hω⟩:=hpos
  let i0 : Fin (4*(n+k)):=⟨0,by omega⟩
  obtain ⟨hr,hrd,hrr,_⟩:=covectorDomain_high (S (θ ω) i0) r r' (hclass ω hω i0) (hsize _ _)
  let G:=fun ω=>singleTuple (covectorTuple (F ω))
  let T:=fun z (i : Slot 1 (n+k))=>covectorDomain (S z i.2)
  have hG : ∀ ω,p.mass ω≠0→∀ i,G ω i∈T (θ ω) i := by
    intro ω hω i
    exact (covectorDomain_mem _ _).mpr (hS ω hω i.2)
  have hT : ∀ z i,log (T z i).card≤J := by
    intro z i
    simpa only [T,covectorDomain_card] using hSJ z i.2
  have hflag : ∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0 := by
    intro ω hω i
    exact covectorTuple_flag (F ω) (hf ω hω) i.2
  have hchron : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0 := by
    intro ω hω i j hij
    apply covectorTuple_consistent (F ω) (hcon ω hω)
    change i.2.val<j.2.val
    simpa only [single_position] using hij
  have hcap : ∀ ω,p.mass ω≠0→∀ i,Caps σ r.val r'.val (T (θ ω) i) := by
    intro ω hω i
    have hh:=(covectorDomain_high (S (θ ω) i.2) r r' (hclass ω hω i.2) (hsize _ _)).2.2.2
    rwa [hlog] at hh
  have hbud : (∑ z,(p.map θ).mass z*((Fintype.card (Slot 1 (n+k)):ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget := by
    apply le_trans (le_of_eq ?_) hbudget
    apply sum_congr rfl
    intro z _
    rw [single_entropy]
    simp only [Slot,Fintype.card_prod,Fintype.card_fin,Nat.one_mul]
    congr 2
    convert covectorTuple_entropy (K:=K) (V:=Fin (d+1)→K) (p.cond θ z) F using 1 <;> congr!
  obtain ⟨e⟩:=he K Ω Θ hlog n k hn hk hkn p θ G T D J budget r.val r'.val hDl hDu hJ
    hr hrd hrr hG hT hflag hchron hcap hbud hb hk0
  exact ⟨e.transport (Equiv.prodComm _ _) Prod.snd F Fin.val
    (fun i=>(single_position i).symm) (fun _ _=>rfl)⟩
end
end SharpLogRamsey.Marking

end

end OAI
