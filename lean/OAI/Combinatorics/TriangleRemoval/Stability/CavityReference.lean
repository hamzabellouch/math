import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.IncidentTriangleThird
import OAI.Combinatorics.TriangleRemoval.Process.ActivePairMembership
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixHorizon

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma goodPrefix_active_degree {n : ℕ} {c C : ℝ} {G : Graph n}
    (h : GoodPrefixGraph n c C G) (hD : 0 < prefixD n) (e : G) :
    |((messageCandidates (activeHypergraph G) e none).card : ℝ)/prefixD n-1| ≤
      (n : ℝ)^(-c) := by
  classical
  rw [active_messageCandidates_card]
  obtain ⟨u,v,huv,hev⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp (h.1 e.property))
  have heG : ({u,v} : Finset (Fin n)) ∈ G := hev ▸ e.property
  rw [hev,triangleDegree_eq_codegree h.1 heG]
  have hcode := h.2.2.2.1 u v huv
  have heq : (currentCodegree G u v : ℝ)/prefixD n-1 =
      ((currentCodegree G u v : ℝ)-prefixD n)/prefixD n := by
    rw [sub_div,div_self hD.ne']
  rw [heq,abs_div,abs_of_pos hD]
  exact (div_le_iff₀ hD).mpr hcode

lemma cavityTime_prefixHorizon {n : ℕ} (hD : 0 < prefixD n) :
    cavityTime (prefixD n) (prefixHorizon n) = 1 := by
  unfold cavityTime prefixHorizon
  rw [show 2*(Real.log (1+2*prefixD n)/2)=Real.log (1+2*prefixD n) by ring,
    Real.exp_log (by linarith : 0 < 1+2*prefixD n)]
  field_simp
  ring

theorem goodPrefix_cavity_continuation {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ a < min c (1/1000 : ℝ) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ s ∈ Set.Icc (0 : ℝ) (prefixHorizon n),
        (∀ e : G, Real.exp (-s-(n : ℝ)^(-a)/2) ≤
            cavityLimit (activeHypergraph G) e none (cavityTime (prefixD n) s) ∧
          cavityLimit (activeHypergraph G) e none (cavityTime (prefixD n) s) ≤
            Real.exp (-s+(n : ℝ)^(-a)/2)) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          cavityMessage (activeHypergraph G) (prefixD n) e T s ≤ 12*s/prefixD n) := by
  obtain ⟨C₁,hC₁,J,hsem⟩ := goodPrefix_cavity_semigroup hc
  obtain ⟨a,ha,hac,hnum⟩ := prefix_bootstrap_numerics hc hC₁ J
  refine ⟨a,ha,hac,?_⟩
  filter_upwards [hsem,hnum,prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)]
    with n hsem hnum hp hn
  intro C G h
  have hD : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hδc : (n : ℝ)^(-c) ≤ (n : ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      (by linarith [(lt_min_iff.mp hac).1])
  apply cavity_closed_continuation (activeHypergraph G)
    (K := C₁*(1+Real.log (n : ℝ))^J) hD hnum.2.2.1 hnum.1 hnum.2.1
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)
    (activeHypergraph_card G) (goodPrefix_active_degree h hD)
  · intro e
    have hh := (abs_le.mp (goodPrefix_active_degree h hD e)).2
    linarith [hnum.2.1]
  · exact (cavityTime_prefixHorizon hD).le
  · exact hnum.2.2.2.2.1
  · exact hnum.2.2.2.2.2
  · intro s hs
    exact hsem C G h s ⟨hs.1,hs.2.trans hnum.2.2.2.1⟩

noncomputable def cavityReference (D t : ℝ) : ℝ := (1+2*D*t)^(-(1/2 : ℝ))
noncomputable def cavityClock (D t : ℝ) : ℝ := Real.log (1+2*D*t)/2

lemma cavityClock_mem {D t : ℝ} (hD : 0 < D) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cavityClock D t ∈ Set.Icc (0 : ℝ) (Real.log (1+2*D)/2) := by
  have harg : 1 ≤ 1+2*D*t := by nlinarith [ht.1]
  have hlo := Real.log_nonneg harg
  have hhi := Real.log_le_log (by linarith : 0 < 1+2*D*t)
    (by nlinarith [ht.2] : 1+2*D*t ≤ 1+2*D)
  exact ⟨by dsimp [cavityClock]; linarith,by dsimp [cavityClock]; linarith⟩

lemma cavityTime_clock {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    cavityTime D (cavityClock D t) = t := by
  unfold cavityTime cavityClock
  rw [show 2*(Real.log (1+2*D*t)/2)=Real.log (1+2*D*t) by ring,
    Real.exp_log (by nlinarith : 0 < 1+2*D*t)]
  field_simp
  ring

lemma cavityReference_exp {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    cavityReference D t = Real.exp (-cavityClock D t) := by
  rw [cavityReference,Real.rpow_def_of_pos (by nlinarith : 0 < 1+2*D*t)]
  congr 1
  dsimp [cavityClock]
  ring

lemma cavityReference_pos {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    0 < cavityReference D t := by rw [cavityReference_exp hD ht]; positivity

theorem goodPrefix_cavity_relative {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      let δ := (n : ℝ)^(-a)
      let Imax := 12*prefixHorizon n/prefixD n
      Imax ≤ 1/4 ∧ ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ e : G, Real.exp (-δ/2) ≤ cavityLimit (activeHypergraph G) e none t /
            cavityReference (prefixD n) t ∧
          cavityLimit (activeHypergraph G) e none t / cavityReference (prefixD n) t ≤
            Real.exp (δ/2)) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t ≤ Imax ∧
          Real.exp (-δ/2) ≤ cavityLimit (activeHypergraph G) e (some T) t /
            cavityReference (prefixD n) t ∧
          cavityLimit (activeHypergraph G) e (some T) t / cavityReference (prefixD n) t ≤
            Real.exp (δ/2)/(1-Imax)) := by
  obtain ⟨a,ha,hac,hcont⟩ := goodPrefix_cavity_continuation hc
  obtain ⟨C₁,hC₁,J,_⟩ := goodPrefix_cavity_semigroup hc
  obtain ⟨b,hb,_,hnum⟩ := prefix_bootstrap_numerics hc hC₁ J
  refine ⟨a,ha,?_⟩
  filter_upwards [hcont,hnum,prefix_scales_eventually_pos] with n hcavity hn hp
  dsimp only
  have hD : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hI : 12*prefixHorizon n/prefixD n ≤ 1/4 := hn.2.2.2.2.1
  refine ⟨hI,?_⟩
  intro C G h t ht
  let s := cavityClock (prefixD n) t
  have hs : s ∈ Set.Icc (0 : ℝ) (prefixHorizon n) := cavityClock_mem hD ht
  have hst : cavityTime (prefixD n) s = t := cavityTime_clock hD ht.1
  obtain ⟨hq,hmsg⟩ := hcavity C G h s hs
  rw [hst] at hq
  have href := cavityReference_exp hD ht.1
  have href0 := cavityReference_pos hD ht.1
  have helo : Real.exp (-s-(n : ℝ)^(-a)/2) =
      Real.exp (-(n : ℝ)^(-a)/2)*cavityReference (prefixD n) t := by
    rw [href,← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  have hehi : Real.exp (-s+(n : ℝ)^(-a)/2) =
      Real.exp ((n : ℝ)^(-a)/2)*cavityReference (prefixD n) t := by
    rw [href,← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  have hroot (e : G) := hq e
  simp only [helo,hehi] at hroot
  constructor
  · intro e
    exact ⟨(le_div_iff₀ href0).mpr (hroot e).1,(div_le_iff₀ href0).mpr (hroot e).2⟩
  · intro e T he
    let I := messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t
    have hI0 : 0 ≤ I := (messageIntegral_mem_unit _ _ (continuous_cavityLimit _)
      (cavityLimit_mem_unit _) _ _ _).1
    have hIm : I ≤ 12*prefixHorizon n/prefixD n := by
      have hh := hmsg e T he
      change messageIntegral _ _ _ _ (cavityTime (prefixD n) s) ≤ _ at hh
      rw [hst] at hh
      exact hh.trans (div_le_div_of_nonneg_right (by linarith [hs.2]) hD.le)
    have hIf : 0 < 1-I := by linarith
    have hMax : 0 < 1-12*prefixHorizon n/prefixD n := by linarith
    have ho := cavityLimit_omission (activeHypergraph G) e T he t
    change cavityLimit (activeHypergraph G) e none t =
      cavityLimit (activeHypergraph G) e (some T) t * (1-I) at ho
    have hparent : cavityLimit (activeHypergraph G) e (some T) t =
      cavityLimit (activeHypergraph G) e none t/(1-I) := (eq_div_iff hIf.ne').mpr ho.symm
    refine ⟨hIm,?_,?_⟩
    · apply (le_div_iff₀ href0).mpr
      have hpar0 := (cavityLimit_mem_unit (activeHypergraph G) e (some T) t).1
      have hm : cavityLimit (activeHypergraph G) e none t ≤
          cavityLimit (activeHypergraph G) e (some T) t := by rw [ho]; nlinarith
      exact (hroot e).1.trans hm
    · rw [hparent]
      calc
        _ = (cavityLimit (activeHypergraph G) e none t/cavityReference (prefixD n) t)/(1-I) := by ring
        _ ≤ Real.exp ((n : ℝ)^(-a)/2)/(1-12*prefixHorizon n/prefixD n) :=
          div_le_div₀ (by positivity) ((div_le_iff₀ href0).mpr (hroot e).2) hMax (by linarith)
end SharpTerminalLeave

end

end OAI
