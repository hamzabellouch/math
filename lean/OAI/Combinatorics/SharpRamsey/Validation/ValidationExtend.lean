import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.ValidationCover

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma incidenceCount_mono_left {S S' : Finset (Projectivization K V)}
    (h : S'⊆S) (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount S' T≤ incidenceCount S T := by
  unfold incidenceCount
  exact sum_le_sum (fun _ _ => card_le_card (filter_subset_filter _ h))

theorem extend_cover {n : ℕ} (hdim : Module.finrank K V=n+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t≤U.card) (b : ℝ) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let E := 2*((h:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E∈caps,E⊆U ∧ (E.card:ℝ)≤2000*q^(n+3)/N) ∧
      (∀ S T,S.card=N → T⊆U → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(20000*q) →
        (∃ W∈descriptions,(N:ℝ)/2≤(S∩W).card) →
        ∃ E∈caps,(99/100:ℝ)*t≤(T∩E).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let E := 2*((h:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
  have hlog2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hE : 0≤E := by
    have hH : 0≤H := mul_nonneg (by positivity) hlog2
    have hlogH : 0≤log (H+1) := log_nonneg (by linarith)
    have hlog3 : 0≤log (3:ℝ) := log_nonneg (by norm_num)
    dsimp only [E]
    positivity
  have hall (W : Finset (Projectivization K V)) :
      ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
        (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(n+3)/N) ∧
        (∀ z,CoverInput W U N t 2 (b+log 2) z →
          ∃ F∈caps,(99/100:ℝ)*t≤(z.2∩F).card) ∧
        log ((caps.card:ℝ)+1)≤E := by
    by_cases hW : W.Nonempty
    · obtain ⟨caps,hs,hc,hl⟩ := public_validation_cover hdim W hW U N t hN ht htu
        2 (b+log 2) (by norm_num) (add_nonneg hb hlog2) hprod
      refine ⟨caps,?_,hc,hl⟩
      intro F hF
      simpa only [show (1000:ℝ)*2=2000 by norm_num] using hs F hF
    · have hw : W=∅ := not_nonempty_iff_eq_empty.mp hW
      refine ⟨∅,by simp,?_,?_⟩
      · intro z hz
        exact (hz.1.ne_empty (subset_empty.mp (hw ▸ hz.2.1))).elim
      · simpa using hE
  choose family hfsize hfcapture hflen using hall
  let caps := descriptions.biUnion family
  refine ⟨caps,?_,?_,?_⟩
  · intro F hF
    obtain ⟨W,_,hWF⟩ := mem_biUnion.mp hF
    exact hfsize W F hWF
  · intro S T hSN hTU hTt hsp hcap
    obtain ⟨W,hW,hcapture⟩ := hcap
    let X := S∩W
    have hnr : (0:ℝ)<N := by exact_mod_cast hN
    have hxr : (0:ℝ)<X.card := (half_pos hnr).trans_le hcapture
    have hX : X.Nonempty := card_pos.mp (by exact_mod_cast hxr)
    have hNX : (N:ℝ)≤2*X.card := by linarith
    have hratio : (W.card:ℝ)≤exp (b+log 2)*X.card := by
      apply (hsize W hW).trans
      rw [exp_add,exp_log (by norm_num : (0:ℝ)<2)]
      nlinarith only [mul_le_mul_of_nonneg_right hNX (exp_pos b).le]
    have hq : 0<q := by
      dsimp only [q]
      exact_mod_cast Nat.card_pos (α:=K)
    have hspX : (incidenceCount X T:ℝ)≤(X.card:ℝ)*T.card/(10000*Nat.card K) := by
      have hmono : (incidenceCount X T:ℝ)≤ incidenceCount S T := by
        exact_mod_cast incidenceCount_mono_left inter_subset_left T
      apply hmono.trans (hsp.trans _)
      rw [hTt]
      have ht0 : (0:ℝ)≤t := by positivity
      have hh := mul_le_mul_of_nonneg_right hNX ht0
      dsimp only [q] at hq ⊢
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hh,mul_nonneg (show 0≤2*(X.card:ℝ)*t-N*t by linarith) hq.le]
    have hi : CoverInput W U N t 2 (b+log 2) (X,T) :=
      ⟨hX,inter_subset_right,hNX,hratio,hTU,hTt,hspX⟩
    obtain ⟨F,hF,hcapF⟩ := hfcapture W (X,T) hi
    exact ⟨F,mem_biUnion.mpr ⟨W,hW,hF⟩,hcapF⟩
  · have he := one_le_exp_iff.mpr hE
    have hf (W : Finset (Projectivization K V)) : ((family W).card:ℝ)≤exp E := by
      have hh := exp_le_exp.mpr (hflen W)
      rw [exp_log (by positivity)] at hh
      linarith
    have hc : (caps.card:ℝ)≤(descriptions.card:ℝ)*exp E := by
      calc
        _ ≤ ∑ W∈descriptions,((family W).card:ℝ) := by exact_mod_cast card_biUnion_le (s:=descriptions) (t:=family)
        _ ≤ ∑ _W∈descriptions,exp E := sum_le_sum (fun W _ => hf W)
        _ = _ := by simp
    have hbound : (caps.card:ℝ)+1≤((descriptions.card:ℝ)+1)*exp E := by nlinarith
    have hl := log_le_log (by positivity : (0:ℝ)<caps.card+1) hbound
    rwa [log_mul (by positivity) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.Validation

end

end OAI
