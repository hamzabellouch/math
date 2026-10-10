import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Interior

namespace OAI

/-! Continuation margin. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

lemma partCount_le_card {V : Type*} [Fintype V] (p : Setoid V) :
    partCount p ≤ Fintype.card V :=
  Fintype.card_le_of_surjective (Quotient.mk p) Quotient.mk_surjective

lemma crossingIndicator_le_one {V : Type*} (p : Setoid V) (a b : V) :
    crossingIndicator p a b ≤ 1 := by
  unfold crossingIndicator
  split_ifs <;> norm_num

lemma slack_combo {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (w z : E → ℝ) (q a b : ℝ) (hab : a+b=1)
    (p : Setoid V) :
    slack left right (a • w+b • z) q p=
      a*slack left right w q p+b*slack left right z q p := by
  simp only [slack,capacity,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    add_mul,sum_add_distrib,mul_assoc,←mul_sum]
  linear_combination (q*((partCount p:ℝ)-1))*hab

lemma slack_change_target {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (w : E → ℝ) (q β : ℝ) (p : Setoid V) :
    slack left right w (q-β) p=slack left right w q p+β*((partCount p:ℝ)-1) := by
  unfold slack
  ring

end
end AlgorithmicThinTrees.Partitions

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

namespace StepFree

lemma multiplier_combo (a b : ℝ) (x w : StepFree n m) (ijk : DistinctTriple n) :
    (a • x+b • w).multiplier ijk=a*x.multiplier ijk+b*w.multiplier ijk := rfl

lemma y_combo (a b : ℝ) (x w : StepFree n m) (e : Fin m) :
    (a • x+b • w).y e=a*x.y e+b*w.y e := rfl

lemma z_combo (a b : ℝ) (x w : StepFree n m) (e : Fin m) :
    (a • x+b • w).z e=a*x.z e+b*w.z e := rfl

lemma Close.refl (x : StepFree n m) {η : ℝ} (hη : 0 ≤ η) : Close x x η := by
  simp only [Close,sub_self,abs_zero]
  exact ⟨fun _ _ => hη,fun _ => hη,fun _ => hη,fun _ => hη⟩

lemma close_add_rescale {x c w : StepFree n m} {a η : ℝ} (ha : 0 < a)
    (h : Close x c (a*η)) : Close (w+a⁻¹ • (x-c)) w η := by
  have he (v z w : ℝ) (hh : |v-z| ≤ a*η) : |w+a⁻¹*(v-z)-w| ≤ η := by
    rw [add_sub_cancel_left,abs_mul,abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹*(a*η) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ha.le)
      _ = η := by rw [←mul_assoc,inv_mul_cancel₀ (ne_of_gt ha),one_mul]
  refine ⟨fun i j => ?_,fun ijk => ?_,fun e => ?_,fun e => ?_⟩
  · exact he _ _ _ (h.1 i j)
  · exact he _ _ _ (h.2.1 ijk)
  · exact he _ _ _ (h.2.2.1 e)
  · exact he _ _ _ (h.2.2.2 e)

lemma Close.capacities {x w : StepFree n m} {η : ℝ} (hη : 0 ≤ η)
    (h : Close x w η) (κ : ℝ) (u : Fin m → ℝ) (e : Fin m) :
    |x.capacities κ u e-w.capacities κ u e| ≤ η := by
  unfold StepFree.capacities
  split_ifs
  · exact h.2.2.2 e
  · simpa only [sub_self,abs_zero] using hη

lemma Close.slack (H : MultiGraph n m) {x w : StepFree n m} {η : ℝ}
    (hη : 0 ≤ η) (h : Close x w η) (κ q : ℝ) (u : Fin m → ℝ) (p : Setoid (Fin n)) :
    |slack H.left H.right (x.capacities κ u) q p-
      slack H.left H.right (w.capacities κ u) q p| ≤ (m : ℝ)*η := by
  simp only [Partitions.slack,sub_sub_sub_cancel_right,capacity,←sum_sub_distrib,←sub_mul]
  calc
    _ ≤ ∑e, |(x.capacities κ u e-w.capacities κ u e)*crossingIndicator p (H.left e) (H.right e)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑_e : Fin m, η := by
      apply sum_le_sum
      intro e _
      rw [abs_mul,abs_of_nonneg (crossingIndicator_nonneg _ _ _)]
      exact (mul_le_mul (h.capacities hη κ u e) (crossingIndicator_le_one _ _ _)
        (crossingIndicator_nonneg _ _ _) hη).trans_eq (mul_one η)
    _ = _ := by simp

end StepFree

lemma stepCore_convex (H : MultiGraph n m) (s κ t : ℝ) (u : Fin m → ℝ) :
    Convex ℝ (stepCore H s κ t u) := by
  intro x hx w hw a b ha hb hab
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [StepFree.lowerPencil_combo H a b hab]
    exact (hx.1.smul ha).add (hw.1.smul hb)
  · rw [StepFree.upperPencil_combo H a b hab]
    exact (hx.2.1.smul ha).add (hw.2.1.smul hb)
  · intro ijk
    rw [StepFree.multiplier_combo]
    exact add_nonneg (mul_nonneg ha (hx.2.2.1 ijk)) (mul_nonneg hb (hw.2.2.1 ijk))
  · intro e
    rw [StepFree.y_combo]
    exact ⟨add_nonneg (mul_nonneg ha (hx.2.2.2.1 e).1) (mul_nonneg hb (hw.2.2.2.1 e).1),
      calc
        _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2.1 e).2 ha)
          (mul_le_mul_of_nonneg_left (hw.2.2.2.1 e).2 hb)
        _ = 1 := by simpa using hab⟩
  · intro e
    rw [StepFree.z_combo]
    exact ⟨add_nonneg (mul_nonneg ha (hx.2.2.2.2.1 e).1) (mul_nonneg hb (hw.2.2.2.2.1 e).1),
      calc
        _ ≤ a*(κ+1)+b*(κ+1) := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2.2.1 e).2 ha)
          (mul_le_mul_of_nonneg_left (hw.2.2.2.2.1 e).2 hb)
        _ = κ+1 := by rw [←add_mul,hab,one_mul]⟩
  · intro e he
    refine ⟨?_,?_⟩
    · rw [StepFree.edgePencil_combo]
      exact ((hx.2.2.2.2.2 e he).1.smul ha).add ((hw.2.2.2.2.2 e he).1.smul hb)
    · rw [StepFree.y_combo,StepFree.z_combo]
      calc
        _ ≤ a*(κ+u e+t*(5*x.y e-4))+b*(κ+u e+t*(5*w.y e-4)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2.2.2 e he).2 ha)
            (mul_le_mul_of_nonneg_left (hw.2.2.2.2.2 e he).2 hb)
        _ = _ := by linear_combination (κ+u e-4*t)*hab

lemma stepFeasible_convex (H : MultiGraph n m) (s κ t q : ℝ) (u : Fin m → ℝ) :
    Convex ℝ (stepFeasible H s κ t q u) := by
  intro x hx w hw a b ha hb hab
  refine ⟨stepCore_convex H s κ t u hx.1 hw.1 ha hb hab,fun p => ?_⟩
  rw [StepFree.capacities_combo κ a b hab,slack_combo _ _ _ _ q a b hab]
  exact add_nonneg (mul_nonneg ha (hx.2 p)) (mul_nonneg hb (hw.2 p))

lemma convex_innerCube (K : Set (StepFree n m)) (hK : Convex ℝ K)
    (z c : StepFree n m) (hz : z ∈ K) {a η : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : ∀x, x.Close c η → x ∈ K) {x : StepFree n m}
    (hx : x.Close ((1-a) • z+a • c) (a*η)) : x ∈ K := by
  have hu := hc _ (StepFree.close_add_rescale ha hx)
  have hh := hK hz hu (sub_nonneg.mpr ha1) ha.le (by ring : 1-a+a=1)
  have he : (1-a) • z+a • (c+a⁻¹ • (x-((1-a) • z+a • c)))=x := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
    abel
  rwa [he] at hh

lemma auxiliary_slack (H : MultiGraph n m) (hn : 0 < n)
    (u : Fin m → ℝ) {q : ℝ} (hq : q ≤ m) (p : Setoid (Fin n)) :
    -(graphSize n m)^2 ≤ slack H.left H.right
      ((auxiliaryPoint H (continuationBaseline m)).capacities (continuationBaseline m) u) q p := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hd0 : 0 ≤ (partCount p:ℝ)-1 := by
    have hh : (1:ℝ) ≤ partCount p := by exact_mod_cast partCount_pos p
    linarith only [hh]
  have hd : (partCount p:ℝ)-1 ≤ n := by
    have hh : (partCount p:ℝ) ≤ n := by exact_mod_cast (show partCount p ≤ n by simpa using partCount_le_card p)
    linarith only [hh]
  have hκ : 0 < continuationBaseline m := (continuation_parameters m).1
  have hcap : 0 ≤ capacity H.left H.right
      ((auxiliaryPoint H (continuationBaseline m)).capacities (continuationBaseline m) u) p := by
    apply sum_nonneg
    intro e _
    apply mul_nonneg _ (crossingIndicator_nonneg _ _ _)
    unfold StepFree.capacities
    split_ifs
    · change 0 ≤ continuationBaseline m/2
      positivity
    · exact hκ.le
  have hm : (m:ℝ) ≤ graphSize n m := by unfold graphSize; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnP : (n:ℝ) ≤ graphSize n m := by unfold graphSize; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hh : q*((partCount p:ℝ)-1) ≤ (graphSize n m)^2 := by
    calc
      _ ≤ (m:ℝ)*n := mul_le_mul hq hd hd0 (Nat.cast_nonneg m)
      _ ≤ graphSize n m*graphSize n m := mul_le_mul hm hnP (Nat.cast_nonneg n) graphSize_pos.le
      _ = _ := (pow_two _).symm
  unfold slack
  linarith only [hcap,hh]

lemma mixing_numbers {P β : ℝ} (hP : 5 ≤ P) (hmP : (m:ℝ) ≤ P)
    (hβ : P⁻¹/32 ≤ β) :
    0 < P^(-8:ℤ) ∧ P^(-8:ℤ) ≤ 1 ∧
    β/2 ≤ (1-P^(-8:ℤ))*β-P^(-8:ℤ)*P^2 ∧
    P^(-30:ℤ) ≤ P^(-8:ℤ)*P^(-20:ℤ) ∧
    (m:ℝ)*P^(-30:ℤ) ≤ β/2 := by
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hβ0 : 0 ≤ β := (by positivity : 0 ≤ P⁻¹/32).trans hβ
  have hθ0 : 0 < P^(-8:ℤ) := zpow_pos hP0 _
  have h4 : (4:ℝ) ≤ P^8 := (by linarith : (4:ℝ) ≤ P).trans
    (by simpa using pow_le_pow_right₀ hP1 (by norm_num : 1 ≤ 8))
  have hθ4 : 4*P^(-8:ℤ) ≤ 1 := by
    simpa using scaled_inverse_power hP0 0 8 h4
  have h128 : (128:ℝ) ≤ P^5 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hP 5
    norm_num at hh
    linarith only [hh]
  have he : 128*P^(-6:ℤ) ≤ P⁻¹ := by
    simpa using scaled_inverse_power hP0 1 5 h128
  have hθP : P^(-8:ℤ)*P^2=P^(-6:ℤ) := by
    rw [←zpow_natCast,←zpow_add₀ (ne_of_gt hP0)]
    norm_num
  have hθβ := mul_le_mul_of_nonneg_right hθ4 hβ0
  have hmδ : (m:ℝ)*P^(-30:ℤ) ≤ P^(-6:ℤ) := by
    calc
      _ ≤ P*P^(-30:ℤ) := mul_le_mul_of_nonneg_right hmP (zpow_pos hP0 _).le
      _ = P^(-29:ℤ) := by simpa using (zpow_add₀ (ne_of_gt hP0) 1 (-30)).symm
      _ ≤ _ := inverse_power_mono hP1 (by norm_num : 6 ≤ 29)
  refine ⟨hθ0,by linarith only [hθ4],?_,?_,?_⟩
  · rw [hθP]
    nlinarith only [hθβ,he,hβ]
  · rw [←zpow_add₀ (ne_of_gt hP0)]
    norm_num only [show (-8:ℤ)+(-20) = -28 by norm_num]
    exact inverse_power_mono hP1 (by norm_num : 28 ≤ 30)
  · linarith only [hmδ,he,hβ,hβ0]

theorem step_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    {s q β : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : q ≤ m) (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (q+β) u) :
    let θ := (graphSize n m)^(-8:ℤ)
    let c := (1-θ) • z+θ • auxiliaryPoint H (continuationBaseline m)
    ∀x, x.Close c ((graphSize n m)^(-30:ℤ)) →
      x ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) q u := by
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let P := graphSize n m
  let θ := P^(-8:ℤ)
  let aux := auxiliaryPoint H (continuationBaseline m)
  let c := (1-θ) • z+θ • aux
  have hP := connected_size_five H hn hconn
  have hmP : (m:ℝ) ≤ P := by dsimp [P,graphSize]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨hθ,hθ1,hmix,hδ,hpert⟩ := mixing_numbers hP hmP hβ
  have hβ0 : 0 ≤ β := (div_nonneg (inv_nonneg.mpr (graphSize_pos (n:=n) (m:=m)).le) (by norm_num) : 0 ≤ (graphSize n m)⁻¹/32).trans hβ
  change ∀x : StepFree n m, x.Close c (P^(-30:ℤ)) → _
  intro x hx
  refine ⟨?_,fun p => ?_⟩
  · apply convex_innerCube (stepCore H s (continuationBaseline m) (continuationStep m) u)
      (stepCore_convex H _ _ _ u) z aux hz.1 hθ hθ1 _ (hx.mono hδ)
    intro w hw
    exact auxiliary_cube H hn hconn hs hsP u hu0 hw
  · by_cases hp : p=⊤
    · subst p
      rw [slack_top]
    have hd : 1 ≤ (partCount p:ℝ)-1 := by
      have hh : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount hp
      linarith only [hh]
    have hzβ : β ≤ slack H.left H.right (z.capacities (continuationBaseline m) u) q p := by
      have hz' := hz.2 p
      have he := slack_change_target H.left H.right (z.capacities (continuationBaseline m) u) (q+β) β p
      rw [add_sub_cancel_right] at he
      have hdβ := mul_le_mul_of_nonneg_left hd hβ0
      rw [he]
      nlinarith only [hz',hdβ]
    have haux := auxiliary_slack H (by omega) u hq p
    have hc : β/2 ≤ slack H.left H.right (c.capacities (continuationBaseline m) u) q p := by
      dsimp only [c]
      rw [StepFree.capacities_combo _ (1-θ) θ (by ring),slack_combo _ _ _ _ q _ _ (by ring)]
      have hh := add_le_add (mul_le_mul_of_nonneg_left hzβ (sub_nonneg.mpr hθ1))
        (mul_le_mul_of_nonneg_left haux hθ.le)
      change (1-θ)*β+θ*(-P^2) ≤ _ at hh
      exact hmix.trans (by nlinarith only [hh])
    have hp' := (abs_le.mp (hx.slack H (zpow_pos graphSize_pos _).le
      (continuationBaseline m) q u p)).1
    linarith only [hc,hp',hpert]

lemma gain_at_least_one {R g : ℝ} (hR : 1 ≤ R) (hg : R^(-1/8:ℝ) ≤ g) :
    1 ≤ g*R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hh : 1 ≤ R^((7:ℝ)/8) := Real.one_le_rpow hR (by norm_num)
  calc
    1 ≤ R^((7:ℝ)/8) := hh
    _ = R^(-1/8:ℝ)*R := by
      rw [show (7:ℝ)/8 = -1/8+1 by norm_num,Real.rpow_add hR0,Real.rpow_one]
    _ ≤ g*R := mul_le_mul_of_nonneg_right hg hR0.le

lemma continuation_margin_lower {r : ℕ} {g : ℝ} (hr : 1 ≤ r)
    (hg : (r:ℝ)^(-1/8:ℝ) ≤ g) :
    (graphSize n m)⁻¹/32 ≤ g*r*continuationStep m := by
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  calc
    _ ≤ continuationBaseline m/32 := div_le_div_of_nonneg_right baseline_lower (by norm_num)
    _ ≤ g*r*continuationStep m := by
      change continuationStep m ≤ _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (gain_at_least_one hr1 hg)
        (continuation_parameters m).2.2.2.1

theorem uniform_continuation_inner_cube :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
      ∀(u : Fin m → ℝ), (∀e, 0 ≤ u e) → (∀e, u e ≤ 1) →
      ∀(s Q g : ℝ), 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ Q → Q ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ g → g ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      (∀p, 0 ≤ slack H.left H.right (fun e => u e+continuationBaseline m) Q p) →
      ∃c : StepFree n m, ∀x, x.Close c ((graphSize n m)^(-30:ℤ)) →
        x ∈ stepFeasible H s (continuationBaseline m) (continuationStep m)
          (Q-2*g*r*continuationStep m) u := by
  obtain ⟨r0,hr0,hr⟩ := feasible_continuation_response
  refine ⟨r0,hr0,?_⟩
  intro r hrr n m H hn hconn hrm u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hinv
  have hr1 : 1 ≤ r := by omega
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
  have hsP : s ≤ graphSize n m := by
    calc
      s ≤ (r:ℝ)^(1/4:ℝ) := hsr
      _ ≤ (r:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hrR (by norm_num)
      _ = r := Real.rpow_one _
      _ ≤ m := by exact_mod_cast hrm
      _ ≤ _ := by unfold graphSize; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hβ := continuation_margin_lower (n:=n) (m:=m) hr1 hg
  have hβ0 : 0 ≤ g*r*continuationStep m := (div_nonneg (inv_nonneg.mpr (graphSize_pos (n:=n) (m:=m)).le) (by norm_num) : 0 ≤ (graphSize n m)⁻¹/32).trans hβ
  obtain ⟨w,hw,hp⟩ := hr r hrr n m H hn hconn u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hinv
  obtain ⟨z,hz,_,_⟩ := response_to_stepFeasible H (by omega)
    (continuation_parameters m).2.2.2.1 (continuation_parameters m).2.2.2.2.2.1 hw hp
  have hq : Q-2*g*r*continuationStep m ≤ m := by
    have hh : (r:ℝ) ≤ m := by exact_mod_cast hrm
    linarith only [hβ0,hh,hQr]
  have hz' : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m)
      ((Q-2*g*r*continuationStep m)+(g*r*continuationStep m)) u := by
    rw [show (Q-2*g*r*continuationStep m)+(g*r*continuationStep m) =
      Q-g*r*continuationStep m by ring]
    exact hz
  exact ⟨_,step_inner_cube H hn hconn hs.le hsP hq hβ u hu0 hz'⟩

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
