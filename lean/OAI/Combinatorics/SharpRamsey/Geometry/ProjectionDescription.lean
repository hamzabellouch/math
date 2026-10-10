import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionFullDescription

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection
open scoped Classical
noncomputable section

lemma expansion_cap {q P b N T : ℝ} {r : ℕ} (hN : 0<N) (hT : 0<T)
    (hP : 1000000≤P) (hb : b≤P) (hprod : q^r*exp (-b)≤N*T) :
    900000*q^r/T≤N*exp (6*P) := by
  have he := mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  have heq : exp (-b)*exp b=1 := by rw [←exp_add]; simp only [neg_add_cancel,exp_zero]
  have hq : q^r≤N*T*exp b := by
    simpa only [mul_assoc,heq,mul_one] using he
  have hc : (900000:ℝ)≤exp P := by have hh := add_one_le_exp P; linarith
  have hh := mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤900000 by norm_num)
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ 900000*(N*T*exp b) := hh
    _ ≤ exp P*(N*T*exp b) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = N*T*exp (P+b) := by rw [exp_add]; ring
    _ ≤ N*T*exp (6*P) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by positivity)
    _ = _ := by ring

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem smaller_side_description (i : ℕ) (hdim : Module.finrank K V=i+5)
    (σ : ℝ) (hσ : 1000000000000≤σ) (hex : exp σ=(Nat.card K:ℝ))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (N T : ℕ) (b τ P H : ℝ) (hN : 0<N) (hT : 0<T) (hNT : N≤T)
    (hNU : N≤U.card) (hTU : T≤UT.card) (hP : 1000000≤P) (hH : 0≤H)
    (hbP : b≤P) (hbσ : b≤σ/5) (hτ : 0<τ) (hτsmall : τ≤1/8000)
    (hprod : (Nat.card K:ℝ)^(i+5)*exp (-b)≤(N:ℝ)*T)
    (hprodup : (N:ℝ)*T≤2*(Nat.card K:ℝ)^(i+5))
    (low : ∀ (z : Projectivization K V) a c,
      HeaderOK (Nat.card K) b (i+1) N T
        (projected U z).card (quotientCut UT z).card UT.card a c →
      Validated (Nat.card K) P H (i+4) (projected U z) (quotientCut UT z) a c (400*τ)) :
    ∃ F : Finset (Finset (Projectivization K V)),
      (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤N*exp (6*P)) ∧
      (∀ S T',S⊆U → S.card=N → T'⊆UT → T'.card=T →
        (incidenceCount S T':ℝ)≤τ*(N:ℝ)*T/Nat.card K →
        ∃ W∈F,(N:ℝ)/100≤(S∩W).card) ∧
      log ((F.card:ℝ)+1)≤(16*H+24*(i:ℝ)+1000)*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  have hd : 0≤log ((U.card:ℝ)/N) := log_nonneg ((le_div_iff₀ hn).mpr
    (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU)))
  have he : 0≤log ((UT.card:ℝ)/T) := log_nonneg ((le_div_iff₀ ht).mpr
    (by simpa only [one_mul] using (show (T:ℝ)≤UT.card by exact_mod_cast hTU)))
  let Z := (Nat.card K:ℝ)*P*(log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P)
  have hZ : 0≤Z := by dsimp only [Z]; positivity
  by_cases hsmall : (N:ℝ)≤200*(Nat.card K:ℝ)*P
  · obtain ⟨hs,hc,hl⟩ := DescriptionEnumeration.public_cover U N hN hNU
    refine ⟨U.powersetCard N,?_,?_,?_⟩
    · intro W hW
      refine ⟨(hs W hW).1,?_⟩
      rw [(hs W hW).2]
      exact le_mul_of_one_le_right hn.le (one_le_exp_iff.mpr (by positivity))
    · intro S T' hSU hSN _hTU _hTt _hsp
      obtain ⟨W,hW,hSW⟩ := hc S hSU hSN
      refine ⟨W,hW,?_⟩
      rw [hSW,hSN]
      linarith
    · have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤log ((U.card:ℝ)/N)+1 by linarith)
      have hh2 := mul_le_mul_of_nonneg_left
        (show log ((U.card:ℝ)/N)+1≤log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P by linarith)
        (show 0≤200*(Nat.card K:ℝ)*P by positivity)
      have hZ1 : 1≤Z := by
        have hbase : 1≤P*(log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) :=
          one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
        have hm := one_le_mul_of_one_le_of_one_le hq hbase
        simpa only [Z,mul_assoc] using hm
      have hl2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      have hcoef : (201:ℝ)≤16*H+24*(i:ℝ)+1000 := by have hi := Nat.cast_nonneg (α:=ℝ) i; linarith
      have hzcoef := mul_le_mul_of_nonneg_right hcoef hZ
      have hfinal : log (((U.powersetCard N).card:ℝ)+1)≤(16*H+24*(i:ℝ)+1000)*Z := by
        nlinarith only [hl,hh,hh2,hZ1,hl2,hzcoef]
      simpa only [Z,mul_assoc] using hfinal
  · have hN100 : 100≤N := by
      have hm := mul_le_mul_of_nonneg_right hq (show 0≤200*P by positivity)
      have hn100 : (100:ℝ)≤N := by nlinarith
      exact_mod_cast hn100
    obtain ⟨hs,ht',hh,hpow⟩ := source_numeric hσ hex hn ht
      (by exact_mod_cast hNT) hbσ hprod hprodup
    obtain ⟨F,hFs,hFc,hFl⟩ := projection_description i hdim U UT N T b τ P H hN100 hT hNU hTU
      (by linarith) hH hτ hτsmall hs ht' hprod hh hpow low
    refine ⟨F,?_,?_,?_⟩
    · intro W hW
      exact ⟨(hFs W hW).1,(hFs W hW).2.trans (expansion_cap hn ht hP hbP hprod)⟩
    · intro S T' hSU hSN hTU hTt hsp
      obtain ⟨W,hW,hcap⟩ := hFc S T' hSU hSN hTU hTt hsp
      exact ⟨W,hW,by linarith⟩
    · apply hFl.trans
      have hh := mul_le_mul_of_nonneg_right
        (show 16*H+24*(i:ℝ)+200≤16*H+24*(i:ℝ)+1000 by linarith) hZ
      simpa only [Z,mul_assoc] using hh

end
end SharpLogRamsey.GeometricCover

end

end OAI
