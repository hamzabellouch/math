import OAI.Analysis.LipschitzEquivalence.WeightedGraph

namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def WeakNull (u : ℕ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 0)

def CompletelyContinuous (T : E →L[ℝ] F) : Prop :=
  ∀ u : ℕ → E, WeakNull u → Tendsto (fun n => T (u n)) atTop (𝓝 0)

def WeakCauchy (u : ℕ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, CauchySeq (fun n => f (u n))

def WeakSequentiallyComplete (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ u : ℕ → E, WeakCauchy u → ∃ x : E,
    ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))

theorem WeakNull.map {u : ℕ → E} (hu : WeakNull u) (T : E →L[ℝ] F) :
    WeakNull (fun n => T (u n)) := fun f => hu (f.comp T)

theorem WeakNull.subseq {u : ℕ → E} (hu : WeakNull u) {a : ℕ → ℕ} (ha : StrictMono a) :
    WeakNull (fun n => u (a n)) := fun f => (hu f).comp ha.tendsto_atTop

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

theorem summable_norm (x : RealL1) : Summable (fun i => |x i|) := by
  simpa using (lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x).summable

theorem summable_pair (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) (x : RealL1) :
    Summable (fun i => b i * x i) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ (summable_norm x)
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hb i)

def pairing (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) : RealL1 →L[ℝ] ℝ :=
  ({ toFun := fun x => ∑' i, b i * x i
     map_add' := by
       intro x y
       change (∑' i, b i * (x i + y i)) = _
       simp_rw [mul_add]
       exact (summable_pair b hb x).tsum_add (summable_pair b hb y)
     map_smul' := by
       intro c x
       change (∑' i, b i * (c * x i)) = c * ∑' i, b i * x i
       simp_rw [mul_left_comm (b _) c]
       exact tsum_mul_left } : RealL1 →ₗ[ℝ] ℝ).mkContinuous 1 (by
         intro x
         simp only [one_mul]
         calc
           ‖∑' i, b i * x i‖ ≤ ∑' i, |b i * x i| :=
             norm_tsum_le_tsum_norm (summable_pair b hb x).norm
           _ ≤ ∑' i, |x i| := Summable.tsum_le_tsum
             (fun i => by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hb i))
             (summable_pair b hb x).abs (summable_norm x)
           _ = ‖x‖ := (WeightedGraph.norm_l1 x).symm)

@[simp] theorem pairing_apply (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) (x : RealL1) :
    pairing b hb x = ∑' i, b i * x i := rfl

theorem norm_pairing_le_one (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) : ‖pairing b hb‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def trunc (N : ℕ) : RealL1 →L[ℝ] RealL1 :=
  ∑ i ∈ Finset.range N,
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 1 i).comp
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i)

theorem trunc_eq_sum (N : ℕ) (x : RealL1) :
    trunc N x = ∑ i ∈ Finset.range N, lp.single 1 i (x i) := by
  unfold trunc
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

@[simp] theorem trunc_apply (N : ℕ) (x : RealL1) (i : ℕ) :
    trunc N x i = if i < N then x i else 0 := by
  rw [trunc_eq_sum, lp.coeFn_sum]
  simp [Finset.sum_apply, lp.single_apply]

theorem tendsto_trunc (x : RealL1) : Tendsto (fun N => trunc N x) atTop (𝓝 x) := by
  simp_rw [trunc_eq_sum]
  exact (lp.hasSum_single (by simp) x).tendsto_sum_nat

theorem WeakNull.trunc {u : ℕ → RealL1} (hu : WeakNull u) (N : ℕ) :
    Tendsto (fun n => trunc N (u n)) atTop (𝓝 0) := by
  have hi (i : ℕ) : Tendsto (fun n => u n i) atTop (𝓝 0) :=
    hu (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i)
  have hj (i : ℕ) : Tendsto (fun n => lp.single (E := fun _ : ℕ => ℝ) 1 i (u n i))
      atTop (𝓝 (0 : RealL1)) := by
    have h := (lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 1) i).continuous.tendsto 0
    rw [lp.single_zero] at h
    exact h.comp (hi i)
  simp_rw [trunc_eq_sum]
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range N) (fun i _ => hj i)

theorem exists_common_sign (z : ℕ → RealL1)
    (hz : ∀ j k, j ≠ k → ∀ i, z j i = 0 ∨ z k i = 0) :
    ∃ b : ℕ → ℝ, (∀ i, |b i| ≤ 1) ∧ ∀ j i, b i * z j i = |z j i| := by
  classical
  let b : ℕ → ℝ := fun i => if h : ∃ j, z j i ≠ 0 then
    Real.sign (z (Classical.choose h) i) else 0
  refine ⟨b, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ j, z j i ≠ 0
    · have heq : b i = Real.sign (z (Classical.choose hi) i) := dite_eq_left hi
      rw [heq]
      rcases Real.sign_apply_eq (z (Classical.choose hi) i) with h | h | h <;> rw [h] <;> norm_num
    · have heq : b i = 0 := dite_eq_right hi
      rw [heq]
      norm_num
  · intro j i
    by_cases hji : z j i = 0
    · simp [hji]
    · have hex : ∃ k, z k i ≠ 0 := ⟨j, hji⟩
      have heq : Classical.choose hex = j := by
        by_contra hne
        cases hz (Classical.choose hex) j hne i with
        | inl h => exact Classical.choose_spec hex h
        | inr h => exact hji h
      simp only [b, dite_eq_left hex, heq]
      rcases lt_trichotomy (z j i) 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · simp [h]
      · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

theorem schur {u : ℕ → RealL1} (hu : WeakNull u) : Tendsto u atTop (𝓝 0) := by
  classical
  by_contra hn
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε, hε, hlarge⟩ := hn
  simp only [dist_zero_right] at hlarge
  have hε8 : 0 < ε / 8 := by positivity
  have chooseStep (p : ℕ × ℕ) : ∃ q : ℕ × ℕ,
      p.1 < q.1 ∧ p.2 < q.2 ∧ ε ≤ ‖u q.1‖ ∧
      ‖trunc p.2 (u q.1)‖ < ε / 8 ∧ ‖u q.1 - trunc q.2 (u q.1)‖ < ε / 8 := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (hu.trunc p.2) (ε / 8) hε8
    obtain ⟨n, hn, hnorm⟩ := hlarge (max M (p.1 + 1))
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 (tendsto_trunc (u n)) (ε / 8) hε8
    refine ⟨(n, max K (p.2 + 1)), ?_, ?_, hnorm, ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.lt_succ_self p.1) ((le_max_right _ _).trans hn)
    · exact (Nat.lt_succ_self p.2).trans_le (le_max_right _ _)
    · simpa only [dist_zero_right] using hM n ((le_max_left _ _).trans hn)
    · have h := hK (max K (p.2 + 1)) (le_max_left _ _)
      rwa [dist_comm, dist_eq_norm] at h
  let next (p : ℕ × ℕ) := Classical.choose (chooseStep p)
  let r : ℕ → ℕ × ℕ := fun j => Nat.rec (0, 0) (fun _ p => next p) j
  have hr (j : ℕ) :
      (r j).1 < (r (j+1)).1 ∧ (r j).2 < (r (j+1)).2 ∧ ε ≤ ‖u (r (j+1)).1‖ ∧
      ‖trunc (r j).2 (u (r (j+1)).1)‖ < ε / 8 ∧
      ‖u (r (j+1)).1 - trunc (r (j+1)).2 (u (r (j+1)).1)‖ < ε / 8 :=
    Classical.choose_spec (chooseStep (r j))
  have hmono₁ : StrictMono (fun j => (r j).1) := strictMono_nat_of_lt_succ (fun j => (hr j).1)
  have hmono₂ : StrictMono (fun j => (r j).2) := strictMono_nat_of_lt_succ (fun j => (hr j).2.1)
  let a : ℕ → ℕ := fun j => (r (j+1)).1
  have ha : StrictMono a := fun _ _ h => hmono₁ (Nat.add_lt_add_right h 1)
  let z : ℕ → RealL1 := fun j => trunc (r (j+1)).2 (u (a j)) - trunc (r j).2 (u (a j))
  have herr (j : ℕ) : ‖u (a j) - z j‖ < ε / 4 := by
    have hid : u (a j) - z j = (u (a j) - trunc (r (j+1)).2 (u (a j))) +
        trunc (r j).2 (u (a j)) := by dsimp [z]; abel
    rw [hid]
    apply (norm_add_le _ _).trans_lt
    have h₁ := (hr j).2.2.2.1
    have h₂ := (hr j).2.2.2.2
    change ‖trunc (r j).2 (u (a j))‖ < ε / 8 at h₁
    change ‖u (a j) - trunc (r (j+1)).2 (u (a j))‖ < ε / 8 at h₂
    linarith
  have hzlower (j : ℕ) : 3 * ε / 4 < ‖z j‖ := by
    have h := norm_le_norm_sub_add (u (a j)) (z j)
    have hj := (hr j).2.2.1
    change ε ≤ ‖u (a j)‖ at hj
    linarith [herr j]
  have hsupport (j i : ℕ) (h : z j i ≠ 0) : (r j).2 ≤ i ∧ i < (r (j+1)).2 := by
    have hcut := (hr j).2.1
    constructor
    · by_contra hn
      have hlo : i < (r j).2 := Nat.lt_of_not_ge hn
      have hhi : i < (r (j+1)).2 := hlo.trans hcut
      simp [z, trunc_apply, hlo, hhi] at h
    · by_contra hn
      have hlo : ¬ i < (r j).2 := fun hi => hn (hi.trans hcut)
      simp [z, trunc_apply, hlo, hn] at h
  have hdisj (j k : ℕ) (hjk : j ≠ k) (i : ℕ) : z j i = 0 ∨ z k i = 0 := by
    by_cases hj : z j i = 0
    · exact Or.inl hj
    by_cases hk : z k i = 0
    · exact Or.inr hk
    have hs := hsupport j i hj
    have ht := hsupport k i hk
    exfalso
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · have hc := hmono₂.monotone (Nat.succ_le_of_lt hjk)
      change (r (j+1)).2 ≤ (r k).2 at hc
      omega
    · have hc := hmono₂.monotone (Nat.succ_le_of_lt hkj)
      change (r (k+1)).2 ≤ (r j).2 at hc
      omega
  obtain ⟨b, hb, hbz⟩ := exists_common_sign z hdisj
  have hpair (j : ℕ) : pairing b hb (z j) = ‖z j‖ := by
    simp_rw [pairing_apply, hbz]
    exact (WeightedGraph.norm_l1 (z j)).symm
  have hbound (x : RealL1) : |pairing b hb x| ≤ ‖x‖ := by
    exact (pairing b hb).le_opNorm x |>.trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_pairing_le_one b hb))
  have hpos (j : ℕ) : ε / 2 < pairing b hb (u (a j)) := by
    have h := (hbound (u (a j) - z j)).trans_lt (herr j)
    rw [map_sub, hpair] at h
    have hl := (abs_lt.mp h).1
    linarith [hzlower j]
  have hlim := (hu.subseq ha) (pairing b hb)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  have h := hN N le_rfl
  rw [dist_zero_right, Real.norm_eq_abs] at h
  change |pairing b hb (u (a N))| < ε / 2 at h
  linarith [hpos N, le_abs_self (pairing b hb (u (a N)))]

end WeakSequences

end LipschitzCounterexample
end

end OAI
