import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialCostsActual

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_JoinedSpatialComplete_1 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) :=
  Fintype.ofFinite _
local instance flat_JoinedSpatialComplete_2 (q : ℕ) [Fact q.Prime] : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) :=
  Module.finite_of_finite (ZMod q)
local instance flat_JoinedSpatialComplete_3 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) :=
  Fintype.ofFinite _
local instance flat_JoinedSpatialComplete_4 (q : ℕ) [Fact q.Prime] : Finite (Submodule (ZMod q) (Fin 4 → ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4 → ZMod q) => (W:Set (Fin 4 → ZMod q)))
    SetLike.coe_injective

theorem complete_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q)))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → n≤t → (n:ℝ)≤2*(q:ℝ)^2 →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (q:ℝ)^4*exp (-b)≤(n:ℝ)*t → (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤5000*(q:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [source_cover hη C hC,HeavyPlaneRestriction.public_heavy_cover hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (1:ℝ)),eventually_uniform_R hη 1,
    eventually_header_budget,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with σ hs hh hL hR hbud htau
  intro q _ hq hex D R had U UT n t b τ hn ht0 hnu htu hnt hnup hb hbu hτ hτu
  let P := scaleP σ η D R
  let d := log ((U.card:ℝ)/n)
  let dT := log ((UT.card:ℝ)/t)
  let Z := (q:ℝ)*P*(d+dT+P)
  have hq' : (3:ℝ)≤q := by exact_mod_cast hq
  have hP : 1≤P := one_le_mul_of_one_le_of_one_le (hL D R had) (hR D R had)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht0
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn').mpr (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤dT := log_nonneg ((le_div_iff₀ ht').mpr (by simpa only [one_mul] using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  have hqZ : (q:ℝ)≤Z := by
    calc
      _ ≤ (q:ℝ)*P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ Z := le_mul_of_one_le_right (by positivity) (by linarith)
  have hZ : 1≤Z := by linarith
  have h2 : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  change ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))), _ ∧ _ ∧ log ((caps.card:ℝ)+1)≤5000*(q:ℝ)*P*(d+dT+P)
  rw [show 5000*(q:ℝ)*P*(d+dT+P)=5000*Z by dsimp [Z]; ring]
  by_cases hsmall : (n:ℝ)≤200*(q:ℝ)*P
  · obtain ⟨hsize,hcapture,hlen⟩ := DescriptionEnumeration.public_cover U n hn hnu
    refine ⟨U.powersetCard n,?_,?_,hlen.trans ?_⟩
    · intro W hW
      obtain ⟨hWU,hnW⟩ := hsize W hW
      refine ⟨hWU,?_⟩
      rw [hnW]
      exact le_mul_of_one_le_right (by positivity) (one_le_exp_iff.mpr (by linarith))
    · intro S T hSU hSn _ _ _ _
      obtain ⟨W,hW,he⟩ := hcapture S hSU hSn
      refine ⟨W,hW,?_⟩
      rw [he,hSn]
      linarith
    · have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤d+1 by linarith)
      have hz : (q:ℝ)*P*(d+1)≤Z := by
        dsimp only [Z]
        gcongr
        linarith
      dsimp only [d] at hh hz
      nlinarith
  · have hdimm : Module.finrank (ZMod q) (Fin 4 → ZMod q)=4 := by simp
    have hcard : Nat.card (ZMod q)=q := by simp
    obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex D R had U n b τ hn hnu hnup
      (le_of_not_ge hsmall) hb hbu hτ hτu
    have hAl' : log ((A.card:ℝ)+1)≤4000*Z :=
      prepared_cost q σ P τ dT U n hq hex hn hnu hnup hP (hτu.trans htau.le) hdT
        (by rwa [hex] at hbud) A.card (by positivity) hAl
    obtain ⟨B,hBs,hBc,hBl⟩ := hh (ZMod q) (Fin 4 → ZMod q) D R had
      (by simpa only [hcard] using hex) hdimm U UT n t b τ hn ht0 hnu htu hb hbu hτ hτu
    have hBl' : log ((B.card:ℝ)+1)≤4500*Z := heavy_cost q P d dT UT n hq hnup hP hd hdT
      B.card (by positivity) (by simpa only [hcard] using hBl)
    refine ⟨A∪B,?_,?_,(union_log_bound A B (hAl'.trans (by nlinarith)) hBl').trans (by linarith)⟩
    · intro W hW
      rcases mem_union.mp hW with hW|hW
      · exact hAs W hW
      · simpa only [hcard] using hBs W hW
    · intro S T hSU hSn hTU hTt hprod hsp
      rcases hAc S T hSU hSn (card_pos.mp (by omega)) (by omega)
        (by rwa [hSn,hTt]) (by rwa [hSn,hTt]) with hheavy|⟨W,hW,hcap⟩
      · obtain ⟨W,hW,hcap⟩ := hBc S T hSU hSn hTU hTt
          (by simpa only [hcard] using hprod) (by simpa only [hcard] using hsp) hheavy
        exact ⟨W,mem_union_right _ hW,hcap⟩
      · exact ⟨W,mem_union_left _ hW,by linarith⟩

end
end SharpLogRamsey.SpatialPublic

end

end OAI
