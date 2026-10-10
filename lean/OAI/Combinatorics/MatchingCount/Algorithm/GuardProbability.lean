import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.Guard

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

def ScaleState.certificateActivity {j : ℕ} (s : ScaleState G j) : Fin G.n → Fin G.n → ℚ :=
  fun a b => (if (min a b,max a b) ∈ G.edges then 1 else 0) * s.scale a * s.scale b
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_cast [Nontrivial (Fin G.n)] {j : ℕ} (s : ScaleState G j) :
    (fun a b => (s.certificateActivity a b : ℝ)) = s.toReal.certificateActivity := by
  funext a b
  unfold ScaleState.certificateActivity Trial.ScaleState.certificateActivity GraphBridge.rawActivity
  split_ifs <;> simp [ScaleState.toReal]

noncomputable def ScaleState.certificate {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) : ℚ :=
  RationalSource.observableD s.activity s.certificateActivity K (RationalSource.sourceMarkedEquiv s.activity K a)

lemma ScaleState.certificate_cast {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) :
    (s.certificate K a : ℝ) = observableD (fun x y => (s.activity x y : ℝ))
      (fun x y => (s.certificateActivity x y : ℝ)) K a :=
  RationalSource.observableD_cast _ _ _ _

lemma ScaleState.certificate_range {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) :
    0 ≤ s.certificate K a ∧ s.certificate K a ≤ 1 := by
  have h : 0 ≤ (s.certificate K a : ℝ) ∧ (s.certificate K a : ℝ) ≤ 1 := by
    rw [s.certificate_cast]
    apply observableD_range _ _ (fun x y => by exact_mod_cast s.activity_pos x y)
    · intro x y
      have hc := s.toReal.certificateActivity_nonneg x y
      rw [←s.certificateActivity_cast] at hc
      exact hc
    · intro x y
      have hc := s.toReal.certificateActivity_le x y
      rw [←s.certificateActivity_cast, ←s.activity_cast] at hc
      exact hc
  exact_mod_cast h

theorem ScaleState.drawOne_certificate_zero (p : Trial.Parameters G) {j : ℕ}
    (hj : j ≤ p.K) (s : ScaleState G j) (hZ : Z G = 0) (b : Fin (oneBits p) → Bool) :
    s.certificate p.K (s.drawOne p hj b) = 0 := by
  have hs : 0 < sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D (s.drawOne p hj b) :=
    RationalSource.fixedSampler_support _ _ _ _ _ _ _ _ _ _ _ _
  have hc := s.toReal.certificate_zero (K:=p.K) p.even hZ p.D
  rw [←s.activity_cast, ←s.certificateActivity_cast] at hc
  have hh := hc (s.drawOne p hj b) hs
  rw [←s.certificate_cast] at hh
  exact_mod_cast hh

lemma ScaleState.certificate_mean_lower (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (1:ℝ)/4 ≤ ∑ a : SourceMarked (fun x y => (s.activity x y : ℝ)) p.K,
      sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D a * (s.certificate p.K a : ℝ) := by
  have h := s.toReal.certificate_mean_lower p hs hZ
  rw [←s.activity_cast, ←s.certificateActivity_cast] at h
  simp_rw [←s.certificate_cast] at h
  convert h using 1
  exact Variation.sum_instances _ _ _

lemma ScaleState.runLaw_tv (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (s : ScaleState G j) :
    tv (s.runLaw p hj).mass (sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D) ≤
      3/(1000*p.K*p.S) := by
  have hN : 2 ≤ Fintype.card (SourceVertex (Fin G.n) p.K) := by
    have h := sourceVertex_card_ge (V:=Fin G.n) p.K
    simp only [Fintype.card_fin] at h
    have hn := p.hn
    omega
  have h := RationalSource.finiteSourceLaw_tv s.activity s.activity_pos p.K p.D
    (1000*p.K*p.S) (sourceD_one p.K) hN (RationalSource.sampling_denominator_gt _ _ p.K_pos p.S_pos)
    (s.cap hj) p.q_pos (RationalSource.startMatching _ _ p.even) (1/(1000*p.K*p.S)) (by have := p.K_pos; have := p.S_pos; positivity)
  rw [RationalSource.sampling_budget _ _ p.K_pos p.S_pos] at h
  convert h using 1
  exact tv_instances _ _ _ _

theorem ScaleState.guard_success (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (1:ℝ)/5 ≤ (s.runLaw p le_rfl).event (fun a => 0 < s.certificate p.K a) := by
  let q := sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D
  have hz : 0 < sourceBagZ (fun x y => (s.activity x y : ℝ)) p.K p.D := by
    rw [s.activity_cast]
    exact sourceBagZ_pos _ s.toReal.activity_pos (s.toReal.partition_pos p.even) _ _
  have hq0 : ∀ a, 0 ≤ q a := sourceLaw_nonneg _ (fun x y => by exact_mod_cast s.activity_pos x y) _ _ hz.le
  have hq1 : ∑ a, q a = 1 := by
    convert sourceLaw_sum (fun x y => (s.activity x y : ℝ)) p.K p.D hz.ne' using 1
    exact Variation.sum_instances _ _ _
  have hm := (s.certificate_mean_lower p hs hZ).trans
    (mean_le_positive_event q (fun a => (s.certificate p.K a : ℝ)) hq0
      (fun a => by exact_mod_cast s.certificate_range p.K a))
  have hev : event q (fun a => 0 < (s.certificate p.K a : ℝ)) =
      event q (fun a => 0 < s.certificate p.K a) := by
    congr 1
    ext a
    exact_mod_cast Iff.rfl
  rw [hev] at hm
  have hd := event_sub_le (s.runLaw p le_rfl).mass q ((s.runLaw p le_rfl).total.trans hq1.symm)
    (fun a => 0 < s.certificate p.K a)
  have ht := s.runLaw_tv p le_rfl
  have hk : (1:ℝ) ≤ p.K := by exact_mod_cast p.K_pos
  have hS : (1:ℝ) ≤ p.S := by exact_mod_cast p.S_pos
  have hc : 3/(1000*(p.K:ℝ)*p.S) ≤ (3:ℝ)/1000 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [mul_le_mul hk hS (by norm_num) (by positivity)]
  have hh := (abs_sub_le_iff.mp hd).2
  change 1/5 ≤ event (s.runLaw p le_rfl).mass (fun a => 0 < s.certificate p.K a)
  dsimp only [q] at *
  linarith

end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Adaptive
open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

lemma Law.iid_all (μ : Law Ω) (r : ℕ) (P : Ω → Prop) :
    (μ.iid r).event (fun x => ∀ i, P (x i)) = (μ.event P)^r := by
  unfold Law.event Law.iid Variation.iid
  calc
    _ = ∑ x : Fin r → Ω, ∏ i, if P (x i) then μ (x i) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : ∀ i, P (x i)
      · simp [hx]
      · obtain ⟨i, hi⟩ := not_forall.mp hx
        simp only [hx, ite_false]
        symm
        apply prod_eq_zero (mem_univ i)
        simp [hi]
    _ = ∏ _ : Fin r, (∑ x, if P x then μ x else 0) := by
      convert (Fintype.prod_sum (fun (_ : Fin r) (x : Ω) => if P x then μ x else 0)).symm using 1
    _ = _ := by simp

lemma Law.iid_no_certificate (μ : Law Ω) (P : Ω → Prop) (hP : (1:ℝ)/5 ≤ μ.event P) :
    (μ.iid 16).event (fun x => ¬∃ i, P (x i)) ≤ 1/16 := by
  have hc : μ.event (fun x => ¬P x) ≤ 4/5 := by
    have h := Variation.event_complement μ.mass P
    change μ.event P + μ.event (fun x => ¬P x) = ∑ x, μ.mass x at h
    rw [μ.total] at h
    linarith
  have he : (fun x : Fin 16 → Ω => ¬∃ i, P (x i)) = (fun x => ∀ i, ¬P (x i)) := by
    funext x
    simp
  rw [he]
  have hi := μ.iid_all 16 (fun x => ¬P x)
  change Variation.event _ _ = _ at hi
  have hie : (μ.iid 16).event (fun x => ∀ i, ¬P (x i)) = (μ.event (fun x => ¬P x))^16 := by
    convert hi using 1
    exact Variation.sum_instances _ _ _
  rw [hie]
  calc
    _ ≤ (4/5:ℝ)^16 := pow_le_pow_left₀ (μ.event_nonneg _) hc _
    _ ≤ 1/16 := by norm_num

end MatchingFPRAS.Adaptive

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

abbrev GuardSamples (p : Trial.Parameters G) (s : ScaleState G p.K) :=
  Fin 16 → SourceMarked (fun x y => (s.activity x y : ℝ)) p.K
noncomputable def guardPass (p : Trial.Parameters G) (s : ScaleState G p.K) (x : GuardSamples p s) : Prop :=
  ∃ i, 0 < s.certificate p.K (x i)
noncomputable def guardLaw (p : Trial.Parameters G) (s : ScaleState G p.K) : Law (GuardSamples p s) :=
  (s.runLaw p le_rfl).iid 16
lemma guard_failure (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (guardLaw p s).event (fun x => ¬guardPass p s x) ≤ 1/16 := by
  have h := (s.runLaw p le_rfl).iid_no_certificate
    (fun x => 0 < s.certificate p.K x) (s.guard_success p hs hZ)
  exact h

abbrev GuardedTrial (p : Trial.Parameters G) :=
  Σ x : (layers p p.K le_rfl).Ω, GuardSamples p ((layers p p.K le_rfl).state x)
noncomputable def guardedLaw (p : Trial.Parameters G) : Law (GuardedTrial p) :=
  (layers p p.K le_rfl).law.sigma (fun x => guardLaw p ((layers p p.K le_rfl).state x))
noncomputable def guardedOutput (p : Trial.Parameters G) (x : GuardedTrial p) : ℚ :=
  if guardPass p ((layers p p.K le_rfl).state x.1) x.2 then output p x.1 else 0
lemma guardedOutput_nonneg (p : Trial.Parameters G) (x : GuardedTrial p) : 0 ≤ guardedOutput p x := by
  unfold guardedOutput
  split_ifs
  · exact output_nonneg _ _
  · rfl

theorem guarded_trial_failure (p : Trial.Parameters G) (hZ : 0 < Z G) :
    (guardedLaw p).event (fun x => ¬Accurate p (guardedOutput p x)) ≤ 1/10 := by
  have hf := first_failure_sigma (layers p p.K le_rfl).law
    (fun x => guardLaw p ((layers p p.K le_rfl).state x))
    ((layers p p.K le_rfl).good p) (fun x => Accurate p (guardedOutput p x)) (1/16) (by norm_num)
    (fun x hx => ((guardLaw p ((layers p p.K le_rfl).state x)).event_mono
      (fun y hy hp => by
        apply hy
        simp only [guardedOutput, hp, ite_true]
        exact good_output p hZ x hx)).trans (guard_failure p _ hx.1 hZ))
  have hb := layers_failure p p.K le_rfl
  have hk : (p.K:ℝ) ≠ 0 := by exact_mod_cast p.K_pos.ne'
  have he : (p.K:ℝ) * (13/(1000*p.K)) = 13/1000 := by field_simp
  rw [he] at hb
  change (guardedLaw p).event _ ≤ _ at hf
  linarith

end MatchingFPRAS.FiniteTrial

end OAI
