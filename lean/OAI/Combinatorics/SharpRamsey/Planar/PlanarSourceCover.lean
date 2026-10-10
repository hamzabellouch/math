import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.PlanarScales
import OAI.Combinatorics.SharpRamsey.Planar.PlanarCover

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarSourceCover_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarSourceCover_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarSourceCover_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem source_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop, ∀ D R, Admissible σ η D R →
    exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V)) (n : ℕ) (b τ : ℝ),
    0<n → n≤U.card → 100*(Nat.card K:ℝ)*scaleP σ η D R≤n →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let M := ⌈2*(Nat.card K:ℝ)*P⌉₊
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S,Input U n b τ S → ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤2*((M:ℝ)*log ((U.card:ℝ)/n)+2*P*τ+log 4+log (H+1))+log 3+
        log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [eventually_budget hη,
    eventually_training_loss hη C (1/1000000) (by linarith) (by norm_num),
    eventually_exceptional_training hη C (by linarith),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20)),
    eventually_ge_atTop (1:ℝ)] with σ hb hl he ht hσ
  intro D R had hex hdim U n b τ hn hnu hnlarge hb0 hbu hτ hτu
  obtain ⟨p,h,hbud⟩ := hb D R had
  let P := scaleP σ η D R
  let L := Real.toNNReal (scaleL σ η D)
  let c := Real.toNNReal ((Nat.card K:ℝ)/n)
  let M := ⌈2*(Nat.card K:ℝ)*P⌉₊
  have hL0 : 0≤ scaleL σ η D := (L_pos (by linarith) had).le
  have hLL : (L:ℝ)=scaleL σ η D := coe_toNNReal _ hL0
  have hc : (c:ℝ)=(Nat.card K:ℝ)/n := coe_toNNReal _ (by positivity)
  have hLP : scaleL σ η D≤P := by
    have hR : (1:ℝ)≤R := by exact_mod_cast (show 1≤R by have := hbud.Rlarge; omega)
    exact le_mul_of_one_le_right hL0 hR
  have hloss : b+2*P*τ≤P/1000000 := by
    have hh := hl D R had b τ hbu hτu
    dsimp [P]
    nlinarith
  have herr : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800 := by
    rw [hLL]
    exact he D R had b τ hbu hτu
  obtain ⟨messages,hsize,hcapture,hlen⟩ := public_cover hdim U n hn hnu σ P b τ L c R p h M
    hex hc hbud hb0 hτ (hτu.trans ht.le) hnlarge hloss herr (Nat.le_ceil _)
  refine ⟨messages.image (fun z => decode U n L z.1 z.2),?_,?_,?_⟩
  · intro W hW
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hW
    exact ⟨inter_subset_left,hsize z hz⟩
  · intro S hS
    obtain ⟨z,hz,hcap⟩ := hcapture S hS
    exact ⟨_,mem_image.mpr ⟨z,hz,rfl⟩,hcap⟩
  · apply le_trans _ hlen
    apply log_le_log (by positivity)
    have hc := card_image_le (s:=messages) (f:=fun z => decode U n L z.1 z.2)
    have hc' : (((messages.image (fun z => decode U n L z.1 z.2)).card):ℝ) ≤ messages.card := by
      exact_mod_cast hc
    linarith only [hc']

end
end SharpLogRamsey.PlanarLearning

end

end OAI
