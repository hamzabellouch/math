import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Domain
import OAI.Combinatorics.ThinTrees.Continuation.Gains
import OAI.Combinatorics.ThinTrees.Continuation.PartitionResponse
import OAI.Combinatorics.ThinTrees.Continuation.PartitionUncrossing

namespace OAI

/-! Continuation feasibility. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

lemma slack_top {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]
    (left right : E → V) (w : E → ℝ) (Q : ℝ) :
    slack left right w Q ⊤=0 := by
  simp [slack,capacity,crossingIndicator,partCount_top]

end
end AlgorithmicThinTrees.Partitions

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma capacity_change_worst (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t : ℝ} (ht : 0 ≤ t) :
    -4*t*m ≤ (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-
      (∑e ∈ F, (u e+κ)) := by
  have hh := capacity_change_loss F u hu0 hu1 good (κ:=κ) ht
  have hcard : (((F ∩ active u).filter (fun e => ¬good e)).card:ℝ) ≤ m := by
    exact_mod_cast (show ((F ∩ active u).filter (fun e => ¬good e)).card ≤ m by
      simpa only [Fintype.card_fin] using card_le_univ ((F ∩ active u).filter (fun e => ¬good e)))
  have hm := mul_le_mul_of_nonpos_left hcard (by linarith : -4*t ≤ 0)
  exact hm.trans hh

lemma continuation_fraction_cutoff :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      (r:ℝ)^(-1/3:ℝ) ≤ 1/10 ∧ 32*(r:ℝ)^(-1/3:ℝ) ≤ (r:ℝ)^(-1/8:ℝ) := by
  open Filter in
  have he : ∀ᶠ x : ℝ in atTop,
      10*x^(-1/3:ℝ) ≤ x^(0:ℝ) ∧ 32*x^(-1/3:ℝ) ≤ x^(-1/8:ℝ) :=
    (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 10 (by norm_num)).and
      (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 32 (by norm_num))
  open Filter in
  have heN : ∀ᶠ r : ℕ in atTop,
      10*(r:ℝ)^(-1/3:ℝ) ≤ (r:ℝ)^(0:ℝ) ∧
        32*(r:ℝ)^(-1/3:ℝ) ≤ (r:ℝ)^(-1/8:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun r : ℕ => (r:ℝ)) atTop atTop).eventually he
  obtain ⟨r0,hr0⟩ := heN.exists_forall_of_atTop
  refine ⟨max 8 r0,le_max_left _ _,?_⟩
  intro r hr
  have hh := hr0 r ((le_max_right _ _).trans hr)
  refine ⟨?_,hh.2⟩
  rw [Real.rpow_zero] at hh
  linarith only [hh.1]

lemma chain_continuation_feasible (H : MultiGraph n m) (hn : 2 ≤ n) (_hconn : H.Connected univ)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1)
    {r : ℕ} {κ t Q s g : ℝ}
    (hr : 8 ≤ r) (hκ : 0 ≤ κ) (hκm : κ*m < 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (htm : 4*t*m ≤ 1)
    (hQ : 3*(r:ℝ)/4 ≤ Q) (hQr : Q ≤ r) (hg : 0 ≤ g)
    (hε : (r:ℝ)^(-1/3:ℝ) ≤ 1/10) (hεg : 32*(r:ℝ)^(-1/3:ℝ) ≤ g)
    (_hs : 0 < s) (_hsr : s ≤ (r:ℝ)^(1/4:ℝ))
    (hinv : ∀p, 0 ≤ slack H.left H.right (fun e => u e+κ) Q p)
    (hgeom : ∀J : Finset (Setoid (Fin n)), IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      (∀p ∈ J, ∀A ∈ parts p, (H.restrict (active u)).EdgeConnectedReal A (r/2:ℕ)) →
      (H.restrict (active u)).EdgeConnectedReal univ (r/2:ℕ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
        (((crossing H p ∩ active u).filter (fun e =>
          ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ active u).card)
    (J : Finset (Setoid (Fin n))) (hJ : IsChain (· ≤ ·) (J : Set (Setoid (Fin n)))) :
    ∃x ∈ admissible H s u, ∀p ∈ J, 0 ≤ responseSlack H κ t (Q-g*r*t) u p x := by
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hrR : (8:ℝ) ≤ r := by exact_mod_cast hr
  have hQ0 : 0 ≤ Q := by linarith only [hrR,hQ]
  have hh : ((r/2:ℕ):ℝ) ≤ Q-2 := by
    have hdiv : (2:ℝ)*((r/2:ℕ):ℝ) ≤ r := by exact_mod_cast Nat.mul_div_le r 2
    linarith only [hdiv,hrR,hQ]
  let K := J.filter (fun p => p ≠ ⊤ ∧ slack H.left H.right (fun e => u e+κ) Q p ≤ 1)
  have hK : IsChain (· ≤ ·) (K : Set (Setoid (Fin n))) := hJ.mono (by
    intro p hp
    exact (mem_filter.mp hp).1)
  have hlocal : ∀p ∈ K, ∀A ∈ parts p, (H.restrict (active u)).EdgeConnectedReal A (r/2:ℕ) := by
    intro p hp A hA
    exact near_tight_locally_connected H u hu0 hu1 hκ hκm hQ0 hh hinv (mem_filter.mp hp).2.2 hA
  have hroot : (H.restrict (active u)).EdgeConnectedReal univ (r/2:ℕ) :=
    near_tight_locally_connected H u hu0 hu1 hκ hκm hQ0 hh hinv
      (by rw [slack_top]; norm_num) (by rw [parts_top]; exact mem_singleton_self _)
  obtain ⟨Y,hY,hYP,hbad⟩ := hgeom K hK hlocal hroot
  let good : Fin m → Prop := fun e => (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y
  let y := booleanResponse good
  have hresponse : (Y,y) ∈ admissible H s u := by
    refine ⟨hY,booleanResponse_bounds good,?_⟩
    intro e _
    by_cases he : good e
    · change (6*s*booleanResponse good e) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y
      simpa only [booleanResponse,ite_eq_left he,mul_one] using he
    · change (6*s*booleanResponse good e) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y
      simp only [booleanResponse,ite_eq_right he,mul_zero,zero_smul]
      exact Matrix.nonneg_iff_posSemidef.mpr (domain_psd H hY)
  refine ⟨(Y,y),hresponse,?_⟩
  intro p hp
  by_cases htop : p=⊤
  · subst p
    simp only [responseSlack,slack_top,le_refl]
  have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
  have hβ : 0 ≤ g*(r:ℝ)*t*((partCount p:ℝ)-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hg (Nat.cast_nonneg r)) ht) (by linarith)
  have hcap := hinv p
  unfold slack at hcap
  rw [capacity_eq_sum] at hcap
  unfold responseSlack slack
  rw [capacity_eq_sum]
  change 0 ≤ (∑e ∈ crossing H p, lowerCapacity κ t (u e) (booleanResponse good e))-
    (Q-g*r*t)*((partCount p:ℝ)-1)
  by_cases hnear : slack H.left H.right (fun e => u e+κ) Q p ≤ 1
  · have hKp : p ∈ K := mem_filter.mpr ⟨hp,htop,hnear⟩
    have hb : (((crossing H p ∩ active u).filter (fun e => ¬good e)).card:ℝ) ≤
        (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ active u).card := hbad p hKp
    have hnear' : (∑e ∈ crossing H p, (u e+κ)) ≤ Q*((partCount p:ℝ)-1)+1 := by
      unfold slack at hnear
      rw [capacity_eq_sum] at hnear
      linarith only [hnear]
    by_cases hfew : ((crossing H p ∩ active u).card:ℝ) ≤ 8*r*((partCount p:ℝ)-1)
    · have hloss := few_edges_loss_bound (crossing H p) u hu0 hu1 good (κ:=κ) ht
        (Real.rpow_nonneg (Nat.cast_nonneg r) (-1/3:ℝ)) hεg (Nat.cast_nonneg r)
        (by linarith : 1 ≤ (partCount p:ℝ)) hb hfew
      nlinarith only [hloss,hcap]
    · have hgain := many_edges_gain_bound (crossing H p) u hu0 hu1 good (κ:=κ) ht ht1 hκ
        (by linarith : (1:ℝ) ≤ r) hd hQr hε hnear' hb (lt_of_not_ge hfew)
      nlinarith only [hgain,hβ,hcap]
  · have hfar : 1 < (∑e ∈ crossing H p, (u e+κ))-Q*((partCount p:ℝ)-1) := by
      have hh := lt_of_not_ge hnear
      simpa only [slack,capacity_eq_sum] using hh
    have hloss := capacity_change_worst (crossing H p) u hu0 hu1 good (κ:=κ) ht
    nlinarith only [hloss,hβ,hfar,htm]

def continuationBaseline (m : ℕ) : ℝ := 1/((m:ℝ)+1)

def continuationStep (m : ℕ) : ℝ := continuationBaseline m/32

lemma continuation_parameters (m : ℕ) :
    0 < continuationBaseline m ∧ continuationBaseline m ≤ 1 ∧
    continuationBaseline m*m < 1 ∧
    0 ≤ continuationStep m ∧ continuationStep m ≤ 1/32 ∧
    4*continuationStep m ≤ continuationBaseline m ∧ 4*continuationStep m*m ≤ 1 := by
  have hmp : (0:ℝ) < m+1 := by positivity
  have hκ : 0 < continuationBaseline m := one_div_pos.mpr hmp
  have hκeq : continuationBaseline m*((m:ℝ)+1)=1 := div_mul_cancel₀ 1 (ne_of_gt hmp)
  have hκm : 0 ≤ continuationBaseline m*m := mul_nonneg hκ.le (Nat.cast_nonneg m)
  have hκ1 : continuationBaseline m ≤ 1 := by nlinarith only [hκeq,hκm]
  have hκm1 : continuationBaseline m*m < 1 := by nlinarith only [hκeq,hκ]
  refine ⟨hκ,hκ1,hκm1,?_,?_,?_,?_⟩ <;> unfold continuationStep <;>
    nlinarith only [hκ,hκ1,hκm1,hκm]

theorem feasible_continuation_response :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(u : Fin m → ℝ), (∀e, 0 ≤ u e) → (∀e, u e ≤ 1) →
      ∀(s Q g : ℝ), 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ Q → Q ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ g → g ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      (∀p, 0 ≤ slack H.left H.right (fun e => u e+continuationBaseline m) Q p) →
      ∃x ∈ admissible H s u,
        ∀p, 0 ≤ responseSlack H (continuationBaseline m) (continuationStep m)
          (Q-g*r*continuationStep m) u p x := by
  obtain ⟨r0,hr0,hgeom⟩ := finite_chain_response
  obtain ⟨r1,hr1,hfrac⟩ := continuation_fraction_cutoff
  refine ⟨max r0 r1,hr1.trans (le_max_right _ _),?_⟩
  intro r hr n m H hn hconn u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hinv
  have hr0' : r0 ≤ r := (le_max_left _ _).trans hr
  have hr1' : r1 ≤ r := (le_max_right _ _).trans hr
  have hr8 : 8 ≤ r := hr1.trans hr1'
  have hrR : (8:ℝ) ≤ r := by exact_mod_cast hr8
  have hg0 : 0 ≤ g := (Real.rpow_nonneg (Nat.cast_nonneg r) _).trans hg
  have hg2 : g ≤ 2 := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1:ℝ) ≤ r)
      (by norm_num : (-1/8:ℝ) ≤ 0)
    linarith only [hp,hgg]
  obtain ⟨hκ,hκ1,hκm,ht,ht1,hκt,htm⟩ := continuation_parameters m
  have hq : 0 ≤ Q-g*r*continuationStep m := by
    have hgt := mul_le_mul hg2 ht1 ht (by norm_num : (0:ℝ) ≤ 2)
    have hh := mul_le_mul_of_nonneg_right hgt (Nat.cast_nonneg r)
    nlinarith only [hh,hrR,hQ]
  have hchains : ∀J : Finset (Setoid (Fin n)), IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      ∃x ∈ admissible H s u, ∀p ∈ J, 0 ≤ responseSlack H (continuationBaseline m)
        (continuationStep m) (Q-g*r*continuationStep m) u p x := by
    intro J hJ
    apply chain_continuation_feasible H hn hconn u hu0 hu1 hr8 hκ.le hκm ht
      (by linarith : continuationStep m ≤ 1/2) htm hQ hQr hg0
      (hfrac r hr1').1 ((hfrac r hr1').2.trans hg) hs hsr hinv _ J hJ
    intro K hK hlocal hroot
    exact hgeom r hr0' n m H hn hconn (active u) K hK hlocal hroot s hs hsr
  exact feasible_of_chain_feasible (admissible H s u) (admissible_compact H (by omega) s u)
    (admissible_nonempty H s u) (admissible_convex H s u)
    (responseSlack H (continuationBaseline m) (continuationStep m) (Q-g*r*continuationStep m) u)
    (fun p => (responseSlack_continuous H _ _ _ u p).continuousOn)
    (fun p => responseSlack_concave H _ _ _ s u p)
    (fun _ hx p q => responseSlack_submodular H u ht hκt hq hx p q) hchains

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
