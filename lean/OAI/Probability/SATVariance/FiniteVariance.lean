import OAI.Probability.SATVariance.Moments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sum.{u_1, u_2} {α : Type u_1} {ι : Type u_2} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    favg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, favg (f i) := by
  simp only [favg, Finset.sum_div]
  exact Finset.sum_comm

lemma favg_sq_sub_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    favg (fun a => (f a-c)^2) = favg (fun a => (f a)^2) - 2*c*favg f + c^2 := by
  have he : (fun a => (f a-c)^2) = (fun a => (f a)^2 - (2*c)*f a + c^2) := by
    funext a; ring
  rw [he, favg_add, favg_sub, favg_mul, favg_const]

def fvariance.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ) : ℝ :=
  favg (fun a => (f a)^2) - (favg f)^2

lemma fvariance_centered.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    fvariance f = favg (fun a => (f a-favg f)^2) := by
  rw [favg_sq_sub_const, fvariance]; ring

lemma fvariance_nonneg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    0 ≤ fvariance f := by
  rw [fvariance_centered]
  exact favg_nonneg fun a => sq_nonneg _

lemma favg_sq_le.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (favg f)^2 ≤ favg (fun a => (f a)^2) := sub_nonneg.mp (fvariance_nonneg f)

lemma fvariance_le_sq_sub.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    fvariance f ≤ favg (fun a => (f a-c)^2) := by
  rw [favg_sq_sub_const, fvariance]
  nlinarith [sq_nonneg (favg f-c)]

lemma fvariance_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    fvariance (fun a => f (e a)) = fvariance f := by
  unfold fvariance
  rw [favg_equiv e (fun b => (f b)^2), favg_equiv e f]

lemma fvariance_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    fvariance f = favg (fun b => fvariance (fun a => f (a,b))) +
      fvariance (fun b => favg (fun a => f (a,b))) := by
  simp only [fvariance, favg_sub, favg_prod]
  rw [favg_comm (fun a b => (f (a,b))^2), favg_comm (fun a b => f (a,b))]
  ring

lemma favg_cons.{u_1} {α : Type u_1} [Fintype α] {m : ℕ} (f : (Fin (m+1) → α) → ℝ) :
    favg f = favg (fun t : Fin m → α => favg (fun a : α => f (Fin.cons a t))) := by
  rw [← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, favg_prod, favg_comm]
  rfl

lemma coordinate_omission.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (m : ℕ)
    (f : (Fin m → α) → ℝ) (g : Fin m → (Fin m → α) → ℝ)
    (hg : ∀ i x a, g i (Function.update x i a) = g i x) :
    fvariance f ≤ ∑ i, favg (fun x => (f x-g i x)^2) := by
  classical
  induction m with
  | zero => simp [fvariance, favg]
  | succ m ih =>
    let F (t : Fin m → α) := favg (fun a : α => f (Fin.cons a t))
    let G (i : Fin m) (t : Fin m → α) := favg (fun a : α => g i.succ (Fin.cons a t))
    have hG : ∀ i t a, G i (Function.update t i a) = G i t := by
      intro i t a
      dsimp [G]
      congr 1
      funext b
      rw [Fin.cons_update, hg]
    have hi := ih F G hG
    have hdec : fvariance f = favg (fun t : Fin m → α =>
        fvariance (fun a : α => f (Fin.cons a t))) + fvariance F := by
      rw [← fvariance_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, fvariance_prod]
      rfl
    have h0 : favg (fun t : Fin m → α => fvariance (fun a : α => f (Fin.cons a t))) ≤
        favg (fun x => (f x-g 0 x)^2) := by
      rw [favg_cons]
      apply favg_mono
      intro t
      let a₀ : α := Classical.choice ‹Nonempty α›
      convert fvariance_le_sq_sub (fun a : α => f (Fin.cons a t)) (g 0 (Fin.cons a₀ t)) using 1
      congr 1
      funext a
      rw [show g 0 (Fin.cons a t) = g 0 (Fin.cons a₀ t) by
        simpa only [Fin.update_cons_zero] using hg 0 (Fin.cons a₀ t) a]
    have hh : ∑ i : Fin m, favg (fun t => (F t-G i t)^2) ≤
        ∑ i : Fin m, favg (fun x => (f x-g i.succ x)^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [favg_cons]
      apply favg_mono
      intro t
      simpa only [F, G, favg_sub] using
        favg_sq_le (fun a : α => f (Fin.cons a t)-g i.succ (Fin.cons a t))
    rw [hdec, Fin.sum_univ_succ]
    exact add_le_add h0 (hi.trans hh)

lemma integral_uniform.{u_1} {α : Type u_1} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ∫ a, f a ∂uniformOn Set.univ = favg f := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton,
    one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    ← Finset.mul_sum, favg]
  ring

lemma variance_uniform.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ProbabilityTheory.variance f (uniformOn Set.univ) = fvariance f := by
  have hm : MemLp f 2 (uniformOn Set.univ) :=
    (memLp_two_iff_integrable_sq (measurable_of_countable f).aestronglyMeasurable).mpr
      Integrable.of_finite
  rw [variance_eq_sub hm, integral_uniform, integral_uniform]
  rfl

def finiteSAT {n k L : ℕ} (cs : Fin L → Clause n k) (m : ℕ) : Prop :=
  ∃ a : Assignment n, ∀ j : Fin L, j.val < m → Satisfies (cs j) a

def finiteTime {n k L : ℕ} (cs : Fin L → Clause n k) : ℝ :=
  ∑ m : Fin L, if finiteSAT cs m.val then 1 else 0

def omittedTime {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) : ℝ :=
  ∑ m : Fin L, if (∃ a : Assignment n,
    ∀ j : Fin L, j.val < m.val → j ≠ i → Satisfies (cs j) a) then 1 else 0

lemma omittedTime_update {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) (c : Clause n k) :
    omittedTime i (Function.update cs i c) = omittedTime i cs := by
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply propext
  constructor <;> rintro ⟨a, ha⟩ <;> refine ⟨a, fun j hj hji => ?_⟩
  · simpa only [Function.update_of_ne hji] using ha j hj hji
  · simpa only [Function.update_of_ne hji] using ha j hj hji

lemma finiteSAT_stream {n k L m : ℕ} (ω : Stream n k) (hm : m ≤ L) :
    finiteSAT (fun j : Fin L => ω j) m ↔ PrefixSAT ω m := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j hj => ha ⟨j, hj.trans_le hm⟩ hj⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j hj => ha j hj⟩

lemma sum_fin_indicator_lt {L N : ℕ} (hN : N ≤ L) :
    (∑ j : Fin L, if j.val < N then (1 : ℝ) else 0) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < N then (1 : ℝ) else 0) L]
  calc
    (∑ j ∈ Finset.range L, if j < N then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range N, if j < N then (1 : ℝ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj]
    _ = ∑ _j ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ite_eq_left (Finset.mem_range.mp hj)
    _ = N := by simp

lemma finiteTime_stream {n k L : ℕ} (ω : Stream n k) :
    finiteTime (fun j : Fin L => ω j) = ((min (firstFailure ω) (L : ℕ∞)).toNat : ℝ) := by
  let N := (min (firstFailure ω) (L : ℕ∞)).toNat
  have htop : min (firstFailure ω) (L : ℕ∞) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by simp))
  have hcoe : (N : ℕ∞) = min (firstFailure ω) (L : ℕ∞) := ENat.natCast_toNat htop
  have hN : N ≤ L := by
    exact_mod_cast (hcoe ▸ min_le_right (firstFailure ω) (L : ℕ∞))
  have hh (m : Fin L) : finiteSAT (fun j : Fin L => ω j) m.val ↔ m.val < N := by
    rw [finiteSAT_stream ω m.isLt.le, ← lt_firstFailure_iff]
    have hm : (m.val : ℕ∞) < (L : ℕ∞) := by exact_mod_cast m.isLt
    rw [← ENat.natCast_lt_natCast, hcoe, lt_min_iff, and_iff_left hm]
  unfold finiteTime
  simp_rw [hh]
  exact sum_fin_indicator_lt hN

lemma capped_coordinate_omission {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ProbabilityTheory.variance (T B : Stream n k → ℝ) (streamLaw n k) ≤
      ∑ i : Fin (cap n B), favg (fun cs : Fin (cap n B) → Clause n k =>
        (omittedTime i cs - finiteTime cs)^2) := by
  let := clause_nonempty n k hkn
  have hm : Measurable (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) := by
    exact Measurable.of_eval fun j => measurable_pi_apply (j.val)
  have he : (T B : Stream n k → ℝ) =
      finiteTime ∘ (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) := by
    funext ω
    exact (finiteTime_stream ω).symm
  rw [he, ← variance_map (measurable_of_countable finiteTime).aemeasurable hm.aemeasurable,
    prefixLaw hkn, variance_uniform]
  have hh := coordinate_omission (cap n B) (finiteTime (n := n) (k := k)) omittedTime
    omittedTime_update
  simpa only [sub_sq_comm] using hh

end RandomKSAT

end

end OAI
