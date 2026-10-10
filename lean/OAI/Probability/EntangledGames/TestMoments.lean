import OAI.Probability.EntangledGames.RepeatedModel

namespace OAI

universe u_I u_Ω

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)
def event (c : Finset I) (ω : Ω) : ℝ := if ∀ i ∈ c, win ω i then 1 else 0
def mass (c : Finset I) : ℝ := ρ.avg (event win c)
def rate (ω : Ω) : ℝ := (uniform (R := I)).avg (fun i => if win ω i then 1 else 0)
def moment (c : Finset I) (t : ℕ) : ℝ := ρ.avg (fun ω => event win c ω*(rate win ω)^t)

omit [Nonempty I] [Fintype Ω] in
lemma event_nonneg (c : Finset I) (ω : Ω) : 0 ≤ event win c ω := by unfold event; split_ifs <;> norm_num
omit [Nonempty I] [Fintype Ω] in
lemma event_le_one (c : Finset I) (ω : Ω) : event win c ω ≤ 1 := by unfold event; split_ifs <;> norm_num
omit [Nonempty I] in
lemma mass_nonneg (c : Finset I) : 0 ≤ mass ρ win c := ρ.avg_nonneg (event_nonneg win c)
omit [Nonempty I] in
lemma mass_le_one (c : Finset I) : mass ρ win c ≤ 1 := ρ.avg_le_const (event_le_one win c)
omit [DecidableEq I] [Fintype Ω] in
lemma rate_nonneg (ω : Ω) : 0 ≤ rate win ω := by
  apply avg_nonneg; intro i; split_ifs <;> norm_num
omit [DecidableEq I] [Fintype Ω] in
lemma rate_le_one (ω : Ω) : rate win ω ≤ 1 := by
  apply avg_le_const; intro i; split_ifs <;> norm_num
omit [Nonempty I] [Fintype Ω] in
lemma event_empty (ω : Ω) : event win ∅ ω = 1 := by simp [event]
omit [Nonempty I] in
lemma mass_empty : mass ρ win ∅ = 1 := by
  unfold mass
  conv_lhs => arg 2; ext ω; rw [event_empty]
  exact avg_const _ 1
omit [Nonempty I] [Fintype Ω] in
lemma event_insert (c : Finset I) (i : I) (ω : Ω) :
    event win (insert i c) ω = event win c ω*(if win ω i then 1 else 0) := by
  simp only [event, Finset.forall_mem_insert]
  split_ifs <;> simp_all
omit [Fintype Ω] in
lemma avg_event_insert (c : Finset I) (ω : Ω) :
    (uniform (R := I)).avg (fun i => event win (insert i c) ω) = event win c ω*rate win ω := by
  simp only [event_insert]
  change (uniform (R := I)).avg (fun i => event win c ω • (if win ω i then (1:ℝ) else 0)) = _
  rw [avg_smul]; rfl
lemma moment_zero (c : Finset I) : moment ρ win c 0 = mass ρ win c := by simp only [moment, pow_zero, mul_one, mass]
lemma moment_step (c : Finset I) (t : ℕ) :
    moment ρ win c (t+1) = (uniform (R := I)).avg (fun i => moment ρ win (insert i c) t) := by
  unfold moment
  rw [avg_comm]
  apply congrArg ρ.avg
  funext ω
  have he : (fun i => event win (insert i c) ω * rate win ω^t) =
      (fun i => (rate win ω^t) • event win (insert i c) ω) := by funext i; simp only [smul_eq_mul, mul_comm]
  rw [he, avg_smul, avg_event_insert, pow_succ]
  change _ = _*_
  ring

lemma moment_upper {r e : ℝ} (hr : 0 ≤ r) (_he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ r*mass ρ win c+e) :
    ∀ t : ℕ, ∀ c : Finset I, c.card+t ≤ T →
      moment ρ win c t ≤ r^t*mass ρ win c + e*∑ s ∈ Finset.range t, r^s := by
  intro t
  induction t with
  | zero => intro c hc; simp only [moment_zero, pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]; exact le_rfl
  | succ t ih =>
    intro c hc
    rw [moment_step]
    have hbound := (uniform (R := I)).avg_mono (fun i => ih (insert i c) (by
      have hi := Finset.card_insert_le i c
      omega))
    have heq : (uniform (R := I)).avg (fun i => r^t*mass ρ win (insert i c)+e*∑ s ∈ Finset.range t, r^s) =
        r^t*(uniform (R := I)).avg (fun i => mass ρ win (insert i c))+e*∑ s ∈ Finset.range t, r^s := by
      rw [avg_add, avg_const]
      change (uniform (R := I)).avg (fun i => (r^t) • mass ρ win (insert i c)) + _ = _
      rw [avg_smul]; rfl
    rw [heq] at hbound
    have hs := mul_le_mul_of_nonneg_left (hstep c (by omega)) (pow_nonneg hr t)
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

lemma threshold_moment_lower {q : ℝ} (hq : 0 ≤ q) (t : ℕ) :
    (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t ≤ moment ρ win ∅ t := by
  have he : (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t =
      ρ.avg (fun ω => if q ≤ rate win ω then q^t else 0) := by
    rw [mul_comm]
    change (q^t) • ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0) = _
    rw [← avg_smul]
    congr 1; funext ω; split_ifs <;> simp
  rw [he]
  apply ρ.avg_mono
  intro ω
  simp only [event_empty, one_mul]
  split_ifs with h
  · exact pow_le_pow_left₀ hq h _
  · exact pow_nonneg (rate_nonneg win ω) _
end Tests
end ThresholdParallelRepetition.FiniteProbability

end

end OAI
