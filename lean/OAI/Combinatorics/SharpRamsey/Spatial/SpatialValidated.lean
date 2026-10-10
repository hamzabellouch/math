import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialTransport
import OAI.Combinatorics.SharpRamsey.Validation.ValidationGapCosts

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation
open scoped Classical Topology
noncomputable section

theorem validated_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=4 → ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) V))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    (q:ℝ)^4*exp (-b)≤(n:ℝ)*t → (n:ℝ)*t≤2*(q:ℝ)^4 →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization (ZMod q) V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤100000*(q:ℝ)^4/t) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
        ∃ W∈caps,(99/100:ℝ)*n≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤7000*(q:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  have hdec : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [complete_cover_any hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (200000:ℝ)),eventually_uniform_R hη 1,
    eventually_training_loss hη C 1 (by linarith) (by norm_num),
    hdec.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/1000000)),
    eventually_ge_atTop (1:ℝ)]
    with σ hs hL hR hbsmall hτsmall hσ
  intro q _ hq hex V _ _ _ hdim D R had U UT n t b τ hn ht hnu htu hb hbu hτ hτu hplo hphi
  let P := scaleP σ η D R
  have hL' := hL D R had
  have hLP : scaleL σ η D≤P := le_mul_of_one_le_right (by linarith) (hR D R had)
  have hP : 200000≤P := hL'.trans hLP
  have hbP : b≤P := by
    have hh := hbsmall D R had b 0 hbu (mul_nonneg (by linarith) (rpow_nonneg (by linarith) _))
    simp only [mul_zero,add_zero,one_mul] at hh
    exact hh.trans hLP
  have hsmall : τ≤1/1000000 := hτu.trans hτsmall.le
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hcard : Nat.card (ZMod q)=q := by simp
  have hd4 : Module.finrank (ZMod q) V=1+3 := hdim
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have he : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr
    (by simpa using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  have hz : 0≤(q:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by positivity
  have hspval (S : Finset (Projectivization (ZMod q) V))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (hsp : (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q) :
      (incidenceCount S T:ℝ)≤(n:ℝ)*t/(1000000*Nat.card (ZMod q)) := by
    rw [hcard]
    apply hsp.trans
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤(n:ℝ)*t/q by positivity)
    convert hh using 1 <;> ring
  by_cases hnt : n≤t
  · have hnup : (n:ℝ)≤2*(q:ℝ)^2 := by
      have hnt' : (n:ℝ)≤t := by exact_mod_cast hnt
      nlinarith [sq_nonneg ((n:ℝ)-2*(q:ℝ)^2),sq_nonneg ((q:ℝ)^2)]
    obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex V hdim D R had U UT n t b τ
      hn ht hnu htu hnt hnup hb hbu hτ hτu
    obtain ⟨F,hFs,hFc,hFl⟩ := return_gap_cover hd4 A U UT n t hn ht hnu htu P b hP hb hbP
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
      (by simpa only [hcard] using hplo)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      exact hFc S T hSU hSn hTU hTt (hspval S T hsp) (hAc S T hSU hSn hTU hTt hplo hsp)
    · simp only [hcard,Nat.cast_one] at hFl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]
  · have htn : t≤n := le_of_not_ge hnt
    have htup : (t:ℝ)≤2*(q:ℝ)^2 := by
      have htn' : (t:ℝ)≤n := by exact_mod_cast htn
      nlinarith [sq_nonneg ((t:ℝ)-2*(q:ℝ)^2),sq_nonneg ((q:ℝ)^2)]
    let e := bidual (K:=ZMod q) (V:=V)
    have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
    have hddual : Module.finrank (ZMod q) (Module.Dual (ZMod q) V)=4 := Subspace.dual_finrank_eq.trans hdim
    obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex (Module.Dual (ZMod q) V) hddual D R had UT (U.image e) t n b τ
      ht hn htu (by rwa [hcU]) htn htup hb hbu hτ hτu
    obtain ⟨F,hFs,hFc,hFl⟩ := reverse_gap_cover hd4 A U UT n t hn ht hnu htu P hP
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      have hcS : (S.image e).card=n := (card_image_of_injective _ e.injective).trans hSn
      have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
      have hspread : (incidenceCount T (S.image e):ℝ)≤τ*(t:ℝ)*n/q := by
        rw [hinc]
        convert hsp using 1; ring
      have hplo' : (q:ℝ)^4*exp (-b)≤(t:ℝ)*n := by simpa only [mul_comm] using hplo
      exact hFc S T hSU hSn hTt (hspval S T hsp)
        (hAc T (S.image e) hTU hTt (image_subset_image hSU) hcS hplo' hspread)
    · simp only [hcard,Nat.cast_one] at hFl
      rw [hcU] at hAl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]

end
end SharpLogRamsey.SpatialPublic

end

end OAI
