import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.InformationScales
import OAI.Combinatorics.SharpRamsey.Marking.HighRankStream

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankExperiment_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
local instance flat_ActualHighRankExperiment_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankExperiment_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankExperiment_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

theorem eventually_high_experiment {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d)
    (C c : ℝ) (hC : 0≤C) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 2≤n → 0<k → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot 1 (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot 1 (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J budget : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2≤r → r≤d → d+2≤r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ z i,log (S z i).card≤J) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      (∑ z,(p.map θ).mass z*((Fintype.card (Slot 1 (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
      budget≤C*((2*(n+k):ℕ):ℝ)*D*σ^(-beta η) →
      c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
      Nonempty (StreamReplacement p G position ((n+k)/2)
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_high_stream hη d hd,
    SourceScales.eventually_information_bad_small η C c (1/20) hη hC hc (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ he hsmall hσ
  intro K Ω Θ _ _ _ _ hlog n k hn hk hkn p θ G S D J budget r r' hDl hDu hJ hr hrd hrr
    hS hSJ hf hcon hcap hbudget hb hk0
  have hσ0 : 0<σ := by linarith
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have ha : 0<σ^(-2000*beta η)/(Nat.card K:ℝ) := div_pos (rpow_pos_of_pos hσ0 _) hq
  have hΔ : 0<D*σ^beta η := mul_pos hD (rpow_pos_of_pos hσ0 _)
  obtain ⟨t,hbad,hselected,hrestore⟩:=actual_realized_zero n k hn hk J (D*σ^beta η)
    (σ^(-2000*beta η)/(Nat.card K:ℝ)) budget hΔ ha p θ G
    (fun _=>embedding 1 (n+k)) (fun _=>owner 1 (n+k)) (fun _=>embedding_owner 1 (n+k)) S hS hSJ hbudget
  apply he K Ω Θ hlog n k (by omega) hkn p θ G S D J r r' hDl hDu hJ hr hrd hrr
    hS hf hcon hcap t (contextual_positive n k (by omega) p θ G
      (fun _=>embedding 1 (n+k)) (fun _=>owner 1 (n+k)) t)
    (budget/(D*σ^beta η)+2*budget/((k:ℝ)*(σ^(-2000*beta η)/(Nat.card K:ℝ))))
  · have hh:=hsmall (Nat.card K) D (2*(n+k):ℕ) budget k hq hD (by positivity) hb hk0
    simpa only [div_eq_mul_inv,one_div,one_mul,SourceScales.beta,HighRankBudgets.beta] using hh
  · exact hbad
  · exact hselected
end
end SharpLogRamsey.Selection.Windows

end

end OAI
