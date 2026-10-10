import OAI.Combinatorics.HadwigerCounterexample.ParameterExistence
import OAI.Combinatorics.HadwigerCounterexample.FinalContradiction
import OAI.Combinatorics.HadwigerCounterexample.ExponentialGraphTransfer
import OAI.Combinatorics.HadwigerMatching.Main

namespace OAI

/-!
# Counterexamples to Hadwiger's conjecture

The binary frame construction yields arbitrarily large graphs with independence
number at most two and small touching matchings. The matching–minor inequality
then separates their complete-minor order from their ordinary chromatic number.

This formalizes the construction theorem and the ordinary chromatic consequence
in OpenAI, *A counterexample to Hadwiger's conjecture* (September 23, 2026).
-/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset
open scoped BigOperators Topology

variable {p:Shape} {n N M s0 :ℕ} {b: PreparationParameters}
open PreparationParameters

def conflictLowerBound (p: Shape) (m:Mixer p n) (N:ℕ) (b:PreparationParameters) :=
   ∀ w:Wgt (UnitType p n N), b.nascent p N w m → carried w (rawHoles m).unit →
     bp (-100*p.g*(N:ℝ))≤ pr (pairW w w) (fun i=>(rawHoles m).conflict i.1 i.2)

set_option maxHeartbeats 1600000 in
theorem eventual_conflict_lower_bound (h:AnalyticParameters p M b s0) :
    ∀ᶠ n : ℕ in atTop,∀ m:Mixer p n,unaryGood m b.pins s0→binaryGood m→conflictLowerBound p m (M*n) b := by
  classical
  let P:= fun n:ℕ=> ∃ (m:Mixer p n),unaryGood m b.pins s0∧binaryGood m∧
    ∃ w:Wgt (UnitType p n (M*n)), b.nascent p (M*n) w m ∧ carried w (rawHoles m).unit ∧
      conflicted p m (M*n) w
  suffices hf : ¬∃ᶠ n:ℕ in atTop,P n by
    have hx := not_frequently.mp hf
    refine hx.mono (fun n hn m hm hv w hw hx=>?_); by_contra! hT
    exact hn ⟨m,hm,hv,w,hw,hx,hT⟩
  intro hc
  have hn := frequently_iff_neBot.mp hc
  obtain ⟨U,hU⟩:= Filter.exists_ultrafilter_le (atTop⊓principal {n|P n})

  let l:Filter ℕ:= U
  have hl : l≤atTop := hU.trans inf_le_left
  have hr : ∀ᶠ n in l,P n :=
    (show ∀ᶠ n in principal {i|P i},P n from Filter.eventually_principal.mpr fun x hx=>hx).filter_mono
      (hU.trans inf_le_right)
  let (n:ℕ) : Nonempty (Mixer p n) := ⟨⟨0,0,0⟩⟩
  obtain ⟨m,hm⟩ := taking hr
  obtain ⟨w,hw⟩ := taking (hm.mono fun i h=> h.2.2)
  have hF : ∀ᶠ n in l, ∃ s : LeafMixture p n (M*n),b.entered p (M*n) (m n) (w n) s := by
    filter_upwards [hw,h.enter.hF.filter_mono hl] with n hn ht
    exact ht _ _ hn.1 hn.2.1
  obtain ⟨s,hS⟩:= taking hF
  obtain ⟨v,hv,hV⟩:= prepare U hl h.enter.first (hw.mono fun i hi=>hi.1) hS
  refine StatusAnalysis.refuteVeil ⟨h,hl,hv,(hm.and hw).mono fun n ⟨h1,h2⟩=>
    ⟨h2.1,h1.1,h1.2.1,h2.2.2⟩⟩ (show NeBot (U:Filter ℕ) from inferInstance) hV

open HadwigerMatching LinearListHadwiger

/-- Arbitrarily large finite graphs of independence number at most two and
touching-matching number less than one hundredth of the number of vertices. -/
theorem exists_graphs (M : ℕ) : ∃ m:ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G:ℚ) < (m:ℚ)/100 := by
  classical
  obtain ⟨p,b,k,r,h,hg,hd,he⟩:= exists_parameters
  have ht:=h.enter.first
  let B:=4*num (Comp p.g)
  let Y (n:ℕ):=k*n
  have hy := (trend_sizes atTop le_rfl ht.hM).1
  have hp : 0 < p.g := lt_of_lt_of_le (by norm_num) ht.hG
  have hs : ∀ᶠ n:ℕ in atTop, ∃ m:ℕ, max M 5 ≤ m ∧
      ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G:ℚ)<(m:ℚ)/100 := by
    filter_upwards [eventual_conflict_lower_bound h,ht.wrap,goodMixers p b.pins r (by linarith only [ht.hG])
      ht.hJ (by have hi:=h.profiles; omega) h.bigJ,hy.eventually
      (transfer_scales hp (show 0≤B from mul_nonneg (by norm_num) (Nat.cast_nonneg _))),
      ((tendsto_ord hp).comp hy).eventually (eventually_ge_atTop (max M 5))] with n hn ht hl hq hN
    let N:=Y n
    obtain ⟨m,hm,he'⟩:=hl
    have hT:= hn m hm he'; have hV:2*num (Full p n)<(N:ℝ):=ht.1
    have hC : num (UnitType p n N)≤bp (B*N^ (2:ℕ)) := by
      rw [unit_size]; apply bp_le
      have hf : num (Full p n) ≤ N := by linarith only [hV,(Nat.cast_nonneg N : 0≤(N:ℝ))]
      unfold B
      calc _ ≤ num (Comp p.g)*4*(N:ℝ)*N := mul_le_mul_of_nonneg_left hf (by unfold num; positivity)
           _ = _ := by ring
    obtain ⟨x,hx,hX⟩:=hq (Orient p n N) (rawHoles m) (raw m N) (raw_law m hV) hC (by
      intro w hw hC hU
      apply hT w _ hU
      apply born w hw m
      rw [hd,he]; simpa only [N,Y,Nat.cast_mul,Nat.cast_ofNat] using hC)
    exact ⟨ord p.g N,hN,(rawHoles m).graph x,hx,hX⟩
  obtain ⟨n,hn⟩:=hs.exists; exact hn

/-- Arbitrarily large counterexamples to Hadwiger's conjecture, with the full
rational bounds and finiteness of the ordinary chromatic number. -/
theorem exists_counterexamples (M : ℕ) : ∃ m : ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G : ℚ) < (m : ℚ) / 100 ∧
      (hadwigerNumber G : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
      26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧ (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ) ∧
      hadwigerNumber G < G.chromaticNumber.toNat ∧
      G.chromaticNumber ≠ ⊤ ∧ G.chromaticNumber = ↑(G.chromaticNumber.toNat) := by
  obtain ⟨m,hm,G,ha,hc⟩:= exists_graphs M
  have he : 5≤ m:=(le_max_right ..).trans hm
  have : NeZero m:= ⟨by omega⟩
  have hx:=full_matching_minor_proposition (Fin m) G
  dsimp only at hx
  rw [Fintype.card_fin] at hx
  obtain ⟨h1,h2,h3⟩:= hx.2 ha hc he
  have hk:G.chromaticNumber ≠ ⊤:= by
    intro h; have hs := G.chromaticNumber_le_card; simp [h] at hs
  refine ⟨m,hm,G,ha,hc,h1,h2,h3,?_,hk,?_⟩
  · exact_mod_cast ((h1.trans h2).trans_le h3)
  exact (ENat.natCast_toNat_eq_self.mpr hk).symm

theorem not_hadwiger_conjecture : ¬ (∀ (m:ℕ)(G:SimpleGraph (Fin m)), G.chromaticNumber ≤ ↑(hadwigerNumber G)) := by
  intro h; obtain ⟨m,hM,G,h1,h2,h3,h4,h5,h6,he,hC⟩:=exists_counterexamples 0
  have ht:=h m G; rw [hC] at ht
  exact h6.not_ge (by exact_mod_cast ht)
end HadwigerCounterexample

end

end OAI
