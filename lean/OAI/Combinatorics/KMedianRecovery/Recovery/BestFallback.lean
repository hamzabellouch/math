import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Average

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

lemma success_of_mean (cost : Ω → ℝ) {M B : ℝ} (hB : 0 < B)
    (hc : ∀ s, 0 ≤ cost s) (hm : average cost ≤ M) :
    1 - M/B ≤ probability (fun s => cost s ≤ B) := by
  have h := average_on_good cost (fun s => cost s ≤ B) hc
    (fun s hs => (lt_of_not_ge hs).le)
  have hp := le_trans h hm
  have hp' : 1 - probability (fun s => cost s ≤ B) ≤ M/B :=
    (le_div_iff₀ hB).mpr hp
  linarith

lemma completion_constant_success (cost : Ω → ℝ) (P : ℝ) (hP : 0 < P)
    (hc : ∀ s, 0 ≤ cost s) (hm : average cost ≤ (97/50 : ℝ)*P) :
    (3/197 : ℝ) ≤ probability (fun s => cost s ≤ (197/100 : ℝ)*P) := by
  have hh := success_of_mean cost (by positivity : 0 < (197/100 : ℝ)*P) hc hm
  have he : 1 - ((97/50 : ℝ)*P)/((197/100 : ℝ)*P) = 3/197 := by
    field_simp [hP.ne']
    ring
  rwa [he] at hh

lemma probability_all_fin (P : Ω → Prop) (n : ℕ) :
    probability (fun s : Fin n → Ω => ∀ i, P (s i)) = (probability P)^n := by
  classical
  induction n with
  | zero => simp [probability,average_const]
  | succ n ih =>
    unfold probability
    rw [average_fin_succ]
    have he (x : Ω) :
        probability (fun s : Fin n → Ω =>
          ∀ i, P ((Fin.cons x s : Fin (n+1) → Ω) i)) =
        (if P x then (1:ℝ) else 0) * probability (fun s : Fin n → Ω => ∀ i, P (s i)) := by
      unfold probability
      rw [← average_const_mul]
      apply average_congr
      intro s
      simp only [Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
      split_ifs <;> simp_all
    change average (fun x => probability (fun s : Fin n → Ω =>
      ∀ i, P ((Fin.cons x s : Fin (n+1) → Ω) i))) = _
    rw [average_congr he,average_mul_const,ih,pow_succ']
    rfl

noncomputable def bestWithFallback [DecidableEq Y] (cost : Y → ℝ)
    (fallback : Y) (trial : Ω → Y) (n : ℕ) (s : Fin n → Ω) : Y :=
  Classical.choose (Finset.exists_min_image (insert fallback (Finset.univ.image (fun i => trial (s i))))
    cost (Finset.insert_nonempty _ _))

omit [Fintype Ω] [Nonempty Ω] in
lemma bestWithFallback_mem [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) (n : ℕ) (s : Fin n → Ω) :
    bestWithFallback cost fallback trial n s = fallback ∨
      ∃ i, bestWithFallback cost fallback trial n s = trial (s i) := by
  classical
  have hh := (Classical.choose_spec (Finset.exists_min_image
    (insert fallback (Finset.univ.image (fun i => trial (s i)))) cost
    (Finset.insert_nonempty _ _))).1
  rcases Finset.mem_insert.mp hh with h | h
  · exact Or.inl h
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i,hi.symm⟩

omit [Fintype Ω] [Nonempty Ω] in
lemma bestWithFallback_le [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) (n : ℕ) (s : Fin n → Ω) :
    cost (bestWithFallback cost fallback trial n s) ≤ cost fallback ∧
    ∀ i, cost (bestWithFallback cost fallback trial n s) ≤ cost (trial (s i)) := by
  classical
  have hh := (Classical.choose_spec (Finset.exists_min_image
    (insert fallback (Finset.univ.image (fun i => trial (s i)))) cost
    (Finset.insert_nonempty _ _))).2
  exact ⟨hh _ (Finset.mem_insert_self _ _),fun i => hh _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))⟩

lemma bestWithFallback_failure [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) (n : ℕ) (B : ℝ) {p : ℝ}
    (hp : p ≤ probability (fun s => cost (trial s) ≤ B)) :
    probability (fun s : Fin n → Ω => B < cost (bestWithFallback cost fallback trial n s)) ≤
      (1-p)^n := by
  have hle : probability (fun s : Fin n → Ω => B < cost (bestWithFallback cost fallback trial n s)) ≤
      probability (fun s : Fin n → Ω => ∀ i, B < cost (trial (s i))) :=
    probability_mono (fun s hs i =>
      lt_of_lt_of_le hs ((bestWithFallback_le cost fallback trial n s).2 i))
  refine hle.trans ?_
  rw [probability_all_fin (fun s : Ω => B < cost (trial s)) n]
  have he : probability (fun s => B < cost (trial s)) =
      1 - probability (fun s => cost (trial s) ≤ B) := by
    rw [← probability_compl]
    exact probability_congr (fun _ => not_le.symm)
  rw [he]
  exact pow_le_pow_left₀ (sub_nonneg.mpr (probability_le_one _)) (by linarith :
    1 - probability (fun s => cost (trial s) ≤ B) ≤ 1-p) n

lemma exponential_failure_bound {p : ℝ} (hp1 : p ≤ 1) (n : ℕ) :
    (1-p)^n ≤ Real.exp (-p*(n:ℝ)) := by
  have hh : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hp1) hh n
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_comm (n:ℝ) (-p)] using hp

lemma repetition_count_suffices {p zeta : ℝ} (hp : 0 < p) (hzeta : 0 < zeta)
    (n : ℕ) (hn : Real.log (1/zeta)/p ≤ (n:ℝ)) :
    Real.exp (-p*(n:ℝ)) ≤ zeta := by
  have hn' : Real.log (1/zeta) ≤ (n:ℝ)*p := (div_le_iff₀ hp).mp hn
  have hl : Real.log (1/zeta) = - Real.log zeta := by simp
  rw [hl] at hn'
  calc
    Real.exp (-p*(n:ℝ)) ≤ Real.exp (Real.log zeta) := Real.exp_le_exp.mpr (by nlinarith)
    _ = zeta := Real.exp_log hzeta

lemma average_le_threshold_add_failure (X : Ω → ℝ) {B M : ℝ}
    (hB : 0 ≤ B) (hX : ∀ s, X s ≤ M) :
    average X ≤ B + probability (fun s => B < X s)*M := by
  classical
  unfold probability
  rw [← average_mul_const, ← average_const (Ω := Ω) B, ← average_add]
  apply average_mono
  intro s
  simp only [average_const]
  by_cases hs : B < X s
  · simpa [hs] using (hX s).trans (le_add_of_nonneg_left hB)
  · simp only [hs,ite_false,zero_mul,add_zero]
    exact le_of_not_gt hs

theorem amplified_output [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) {B M p zeta : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfall : cost fallback ≤ M) (hp : 0 < p)
    (hsuccess : p ≤ probability (fun s => cost (trial s) ≤ B))
    (hzeta : 0 < zeta) (n : ℕ) (hn : Real.log (1/zeta)/p ≤ (n:ℝ)) :
    (∀ s, cost (bestWithFallback cost fallback trial n s) ≤ M) ∧
    probability (fun s : Fin n → Ω => cost (bestWithFallback cost fallback trial n s) ≤ B)
      ≥ 1-zeta ∧
    average (fun s : Fin n → Ω => cost (bestWithFallback cost fallback trial n s)) ≤ B+M*zeta := by
  have hpoint (s : Fin n → Ω) := ((bestWithFallback_le cost fallback trial n s).1).trans hfall
  have hp1 : p ≤ 1 := hsuccess.trans (probability_le_one _)
  have hfail := (bestWithFallback_failure cost fallback trial n B hsuccess).trans
    ((exponential_failure_bound hp1 n).trans (repetition_count_suffices hp hzeta n hn))
  refine ⟨hpoint,?_,?_⟩
  · have he : probability (fun s : Fin n → Ω => B < cost (bestWithFallback cost fallback trial n s)) =
        1 - probability (fun s : Fin n → Ω => cost (bestWithFallback cost fallback trial n s) ≤ B) := by
      rw [← probability_compl]
      exact probability_congr (fun _ => not_le.symm)
    rw [he] at hfail
    linarith
  · exact (average_le_threshold_add_failure _ hB hpoint).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hfail hM])

end MetricKMedianRecovery.FiniteSampling

end OAI
