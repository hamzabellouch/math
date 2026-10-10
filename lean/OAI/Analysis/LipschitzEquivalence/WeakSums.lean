import OAI.Analysis.LipschitzEquivalence.Schur

namespace OAI

universe uE uF uG

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakCauchy.map {u : ℕ → E} (hu : WeakCauchy u) (T : E →L[ℝ] F) :
    WeakCauchy (fun n => T (u n)) := fun f => hu (f.comp T)

theorem WeakCauchy.bounded {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => NormedSpace.inclusionInDoubleDual ℝ E (u n))
    (fun f => by
      obtain ⟨C, hC⟩ := (hu f).isBounded_range.exists_norm_le
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩)
  refine ⟨C, fun n => ?_⟩
  have h := (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (u n)
  exact h ▸ hC n

theorem schur_cauchy {u : ℕ → RealL1} (hu : WeakCauchy u) : CauchySeq u := by
  by_contra hn
  rw [Metric.cauchySeq_iff] at hn
  push Not at hn
  obtain ⟨ε, hε, hn⟩ := hn
  choose a ha b hb hab using hn
  have hweak : WeakNull (fun n => u (a n) - u (b n)) := by
    intro f
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hu f) δ hδ
    refine ⟨N, fun n hn => ?_⟩
    simpa only [map_sub, dist_zero_right, ← dist_eq_norm] using
      hN (a n) (hn.trans (ha n)) (b n) (hn.trans (hb n))
  have hlim := schur hweak
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  have h := hN N le_rfl
  rw [dist_zero_right, ← dist_eq_norm] at h
  exact (not_lt_of_ge (hab N)) h

theorem wsc_realL1 : WeakSequentiallyComplete RealL1 := by
  intro u hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (schur_cauchy hu)
  exact ⟨x, fun f => f.continuous.continuousAt.tendsto.comp hx⟩

abbrev SumL1 (E : ℕ → Type uE) [∀ i, NormedAddCommGroup (E i)] := lp E 1
variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

omit [∀ i, NormedSpace ℝ (G i)] in
theorem sumL1_norm (x : SumL1 G) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

omit [∀ i, NormedSpace ℝ (G i)] in
theorem sumL1_summable (x : SumL1 G) : Summable (fun i => ‖x i‖) := by
  simpa using (lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x).summable

def coordinateTests (f : ∀ i, G i →L[ℝ] ℝ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    SumL1 G →L[ℝ] RealL1 :=
  ({ toFun := fun x => ⟨fun i => f i (x i), memℓp_gen (by
       simp only [ENNReal.toReal_one, Real.rpow_one]
       apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ (sumL1_summable x)
       intro i
       simpa using (f i).le_of_opNorm_le (hf i) (x i))⟩
     map_add' := by intro x y; apply lp.ext; funext i; exact map_add (f i) _ _
     map_smul' := by intro c x; apply lp.ext; funext i; exact map_smul (f i) c _ } :
       SumL1 G →ₗ[ℝ] RealL1).mkContinuous 1 (by
         intro x
         simp only [one_mul]
         rw [sumL1_norm, sumL1_norm]
         apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable x)
         intro i
         simpa using (f i).le_of_opNorm_le (hf i) (x i))

@[simp] theorem coordinateTests_apply (f : ∀ i, G i →L[ℝ] ℝ) (hf : ∀ i, ‖f i‖ ≤ 1)
    (x : SumL1 G) (i : ℕ) : coordinateTests f hf x i = f i (x i) := rfl

def headL1 (N : ℕ) : SumL1 G →L[ℝ] SumL1 G :=
  ∑ i ∈ Finset.range N, (lp.singleContinuousLinearMap ℝ G 1 i).comp (lp.evalCLM ℝ G 1 i)

def tailL1 (N : ℕ) : SumL1 G →L[ℝ] SumL1 G := ContinuousLinearMap.id ℝ _ - headL1 N

theorem headL1_eq_sum (N : ℕ) (x : SumL1 G) :
    headL1 N x = ∑ i ∈ Finset.range N, lp.single 1 i (x i) := by
  unfold headL1
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

@[simp] theorem headL1_apply (N : ℕ) (x : SumL1 G) (i : ℕ) :
    headL1 N x i = if i < N then x i else 0 := by
  rw [headL1_eq_sum, lp.coeFn_sum]
  simp [Finset.sum_apply, lp.single_apply]

@[simp] theorem tailL1_apply (N : ℕ) (x : SumL1 G) (i : ℕ) :
    tailL1 N x i = if N ≤ i then x i else 0 := by
  change x i - headL1 N x i = _
  rw [headL1_apply]
  split_ifs <;> simp_all
  all_goals omega

theorem tendsto_tailL1 (x : SumL1 G) : Tendsto (fun N => tailL1 N x) atTop (𝓝 0) := by
  have hh : Tendsto (fun N => headL1 N x) atTop (𝓝 x) := by
    simp_rw [headL1_eq_sum]
    exact (lp.hasSum_single (by simp) x).tendsto_sum_nat
  simpa [tailL1] using (tendsto_const_nhds (x := x)).sub hh

theorem norm_tailL1_le (N : ℕ) (x : SumL1 G) : ‖tailL1 N x‖ ≤ ‖x‖ := by
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable _)
  intro i
  rw [tailL1_apply]
  split_ifs <;> simp

theorem norm_tailL1_antitone (x : SumL1 G) : Antitone (fun N => ‖tailL1 N x‖) := by
  intro n m hnm
  dsimp only
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable _)
  intro i
  simp only [tailL1_apply]
  split_ifs <;> simp_all
  all_goals omega

theorem uniform_tails_of_cauchy (u : ℕ → SumL1 G) (hu : CauchySeq u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  obtain ⟨m, hm⟩ := Metric.cauchySeq_iff.1 hu (ε/2) (half_pos hε)
  have hh : ∀ᶠ N in atTop, ∀ k ∈ Finset.range (m+1), ‖tailL1 N (u k)‖ < ε/2 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact (NormedAddGroup.tendsto_nhds_zero.1 (tendsto_tailL1 (u k))) _ (half_pos hε)
  obtain ⟨N, hN⟩ := hh.exists
  refine ⟨N, fun k => ?_⟩
  by_cases hk : k ≤ m
  · exact (hN k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hk))).trans (by linarith)
  · have hkm : m ≤ k := Nat.le_of_not_ge hk
    have hid : tailL1 N (u k) = tailL1 N (u k - u m) + tailL1 N (u m) := by
      rw [map_sub]; abel
    rw [hid]
    apply (norm_add_le _ _).trans_lt
    have h₁ := (norm_tailL1_le N (u k - u m)).trans_lt (by
      simpa [dist_eq_norm] using hm k hkm m le_rfl)
    have h₂ := hN m (Finset.mem_range.2 (Nat.lt_succ_self m))
    linarith

theorem exists_common_functionals (z : ℕ → SumL1 G)
    (hz : ∀ j k, j ≠ k → ∀ i, z j i = 0 ∨ z k i = 0) :
    ∃ f : ∀ i, G i →L[ℝ] ℝ, (∀ i, ‖f i‖ ≤ 1) ∧ ∀ j i, f i (z j i) = ‖z j i‖ := by
  classical
  let f : ∀ i, G i →L[ℝ] ℝ := fun i => if h : ∃ j, z j i ≠ 0 then
    Classical.choose (exists_dual_vector'' ℝ (z (Classical.choose h) i)) else 0
  refine ⟨f, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ j, z j i ≠ 0
    · simp only [f, dite_eq_left hi]
      exact (Classical.choose_spec (exists_dual_vector'' ℝ (z (Classical.choose hi) i))).1
    · simp [f, hi]
  · intro j i
    by_cases hji : z j i = 0
    · simp [hji]
    · have hex : ∃ k, z k i ≠ 0 := ⟨j, hji⟩
      have heq : Classical.choose hex = j := by
        by_contra hne
        cases hz (Classical.choose hex) j hne i with
        | inl h => exact Classical.choose_spec hex h
        | inr h => exact hji h
      simp only [f, dite_eq_left hex, heq]
      exact (Classical.choose_spec (exists_dual_vector'' ℝ (z j i))).2

theorem uniform_tails_of_weakCauchy (u : ℕ → SumL1 G) (hu : WeakCauchy u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  classical
  by_contra hn
  push Not at hn
  have chooseStep (n : ℕ) : ∃ q : ℕ × ℕ, n < q.1 ∧
      ε ≤ ‖tailL1 n (u q.2)‖ ∧ ‖tailL1 q.1 (u q.2)‖ < ε/2 := by
    obtain ⟨k, hk⟩ := hn n
    obtain ⟨m, hm⟩ := Metric.tendsto_atTop.1 (tendsto_tailL1 (u k)) (ε/2) (half_pos hε)
    refine ⟨(max m (n+1), k), ?_, hk, ?_⟩
    · exact (Nat.lt_succ_self n).trans_le (le_max_right _ _)
    · simpa only [dist_zero_right] using hm (max m (n+1)) (le_max_left _ _)
  let next (n : ℕ) := Classical.choose (chooseStep n)
  let n : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => (next p).1) j
  let a (j : ℕ) := (next (n j)).2
  have hr (j : ℕ) : n j < n (j+1) ∧ ε ≤ ‖tailL1 (n j) (u (a j))‖ ∧
      ‖tailL1 (n (j+1)) (u (a j))‖ < ε/2 := Classical.choose_spec (chooseStep (n j))
  have hmono : StrictMono n := strictMono_nat_of_lt_succ (fun j => (hr j).1)
  let z : ℕ → SumL1 G := fun j => headL1 (n (j+1)) (u (a j)) - headL1 (n j) (u (a j))
  have hzi (j i : ℕ) : z j i = @ite (G i) (n j ≤ i ∧ i < n (j+1))
      (Classical.propDecidable _) (u (a j) i) 0 := by
    change headL1 (n (j+1)) (u (a j)) i - headL1 (n j) (u (a j)) i = _
    simp only [headL1_apply]
    rcases Classical.em (i < n j) with hlo | hlo
    · have hhi : i < n (j+1) := hlo.trans (hr j).1
      rw [ite_eq_left hhi, ite_eq_left hlo, ite_eq_right (by omega)]
      exact sub_self _
    · rcases Classical.em (i < n (j+1)) with hhi | hhi
      · rw [ite_eq_left hhi, ite_eq_right hlo, ite_eq_left ⟨Nat.le_of_not_gt hlo, hhi⟩, sub_zero]
      · rw [ite_eq_right hhi, ite_eq_right hlo, ite_eq_right (by omega), sub_self]
  have hzlower (j : ℕ) : ε/2 < ‖z j‖ := by
    have hid : tailL1 (n j) (u (a j)) = z j + tailL1 (n (j+1)) (u (a j)) := by
      dsimp [z, tailL1]; simp only [sub_apply, ContinuousLinearMap.id_apply]; abel
    have hh := norm_add_le (z j) (tailL1 (n (j+1)) (u (a j)))
    rw [← hid] at hh
    linarith [(hr j).2.1, (hr j).2.2]
  have hdisj (j k : ℕ) (hjk : j ≠ k) (i : ℕ) : z j i = 0 ∨ z k i = 0 := by
    rcases Classical.em (n j ≤ i ∧ i < n (j+1)) with hj | hj
    · apply Or.inr
      have hk : ¬ (n k ≤ i ∧ i < n (k+1)) := by
        intro hk
        rcases lt_or_gt_of_ne hjk with hjk | hkj
        · have hm := hmono.monotone (Nat.succ_le_of_lt hjk)
          change n (j+1) ≤ n k at hm
          omega
        · have hm := hmono.monotone (Nat.succ_le_of_lt hkj)
          change n (k+1) ≤ n j at hm
          omega
      rw [hzi, ite_eq_right hk]
    · apply Or.inl
      rw [hzi, ite_eq_right hj]
  obtain ⟨f, hf, hfz⟩ := exists_common_functionals z hdisj
  let T := coordinateTests f hf
  have hnorm (j : ℕ) : ‖T (z j)‖ = ‖z j‖ := by
    rw [sumL1_norm, sumL1_norm]
    apply tsum_congr
    intro i
    change ‖f i (z j i)‖ = ‖z j i‖
    rw [hfz, norm_norm]
  have hle (j : ℕ) : ‖z j‖ ≤ ‖tailL1 (n j) (T (u (a j)))‖ := by
    rw [← hnorm, sumL1_norm, sumL1_norm]
    apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable _)
    intro i
    change ‖f i (z j i)‖ ≤ _
    rw [hzi, tailL1_apply]
    rcases Classical.em (n j ≤ i ∧ i < n (j+1)) with hi | hi
    · rw [ite_eq_left hi, ite_eq_left hi.1]
      exact le_rfl
    · rw [ite_eq_right hi, map_zero, norm_zero]
      exact norm_nonneg _
  obtain ⟨N, hN⟩ := uniform_tails_of_cauchy (fun k => T (u k))
    (schur_cauchy (hu.map T)) (ε/2) (half_pos hε)
  have ht : ‖tailL1 (n N) (T (u (a N)))‖ < ε/2 :=
    (norm_tailL1_antitone (T (u (a N))) (hmono.id_le N)).trans_lt (hN (a N))
  linarith [hle N, hzlower N]

theorem finite_norm_le_of_weak_limits (v : ℕ → ∀ i, G i) (y : ∀ i, G i)
    (hy : ∀ i (f : G i →L[ℝ] ℝ), Tendsto (fun n => f (v n i)) atTop (𝓝 (f (y i))))
    (s : Finset ℕ) (C : ℝ) (hb : ∀ n, ∑ i ∈ s, ‖v n i‖ ≤ C) :
    ∑ i ∈ s, ‖y i‖ ≤ C := by
  choose f hf hfval using fun i => exists_dual_vector'' ℝ (y i)
  have ht : Tendsto (fun n => ∑ i ∈ s, f i (v n i)) atTop (𝓝 (∑ i ∈ s, ‖y i‖)) := by
    simpa [hfval] using tendsto_finsetSum s (fun i _ => hy i (f i))
  apply le_of_tendsto ht
  filter_upwards [] with n
  apply le_trans _ (hb n)
  apply Finset.sum_le_sum
  intro i hi
  calc
    f i (v n i) ≤ ‖f i (v n i)‖ := le_abs_self _
    _ ≤ ‖v n i‖ := by simpa using (f i).le_of_opNorm_le (hf i) (v n i)

theorem wsc_sumL1 (hG : ∀ i, WeakSequentiallyComplete (G i)) :
    WeakSequentiallyComplete (SumL1 G) := by
  intro u hu
  have hcoord (i : ℕ) : WeakCauchy (fun k => u k i) := hu.map (lp.evalCLM ℝ G 1 i)
  choose y hy using fun i => hG i (fun k => u k i) (hcoord i)
  obtain ⟨C, hC⟩ := hu.bounded
  have hfinite (s : Finset ℕ) : ∑ i ∈ s, ‖y i‖ ≤ C := by
    apply finite_norm_le_of_weak_limits (fun k i => u k i) y hy s C
    intro k
    apply le_trans _ (hC k)
    rw [sumL1_norm]
    exact (sumL1_summable (u k)).sum_le_tsum s (fun i hi => norm_nonneg _)
  have hsummable : Summable (fun i => ‖y i‖) :=
    summable_of_sum_le (fun i => norm_nonneg _) hfinite
  let x : SumL1 G := ⟨y, memℓp_gen (by simpa using hsummable)⟩
  refine ⟨x, fun f => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hden : 0 < 3 * (‖f‖ + 1) := by positivity
  let δ := ε / (3 * (‖f‖ + 1))
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨N₁, hN₁⟩ := uniform_tails_of_weakCauchy u hu δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (tendsto_tailL1 x) δ hδ
  let N := max N₁ N₂
  have hxN : ‖tailL1 N x‖ < δ := by
    simpa only [dist_zero_right] using hN₂ N (le_max_right _ _)
  have huN (k : ℕ) : ‖tailL1 N (u k)‖ < δ :=
    (norm_tailL1_antitone (u k) (le_max_left _ _)).trans_lt (hN₁ k)
  have hhead : Tendsto (fun k => f (headL1 N (u k))) atTop (𝓝 (f (headL1 N x))) := by
    simp only [headL1_eq_sum, map_sum]
    apply tendsto_finsetSum
    intro i hi
    exact hy i (f.comp (lp.singleContinuousLinearMap ℝ G 1 i))
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.1 hhead (ε/3) (by positivity)
  refine ⟨m, fun k hk => ?_⟩
  have hid : f (u k) - f x = (f (headL1 N (u k)) - f (headL1 N x)) +
      f (tailL1 N (u k)) - f (tailL1 N x) := by
    simp only [tailL1, sub_apply, ContinuousLinearMap.id_apply, map_sub]; ring
  have hsmall : ‖f‖ * δ < ε/3 := by
    calc
      ‖f‖ * δ < (‖f‖ + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = ε/3 := by dsimp [δ]; field_simp
  have h₁ : ‖f (tailL1 N (u k))‖ < ε/3 := by
    calc
      ‖f (tailL1 N (u k))‖ ≤ ‖f‖ * ‖tailL1 N (u k)‖ := f.le_opNorm _
      _ ≤ ‖f‖ * δ := mul_le_mul_of_nonneg_left (huN k).le (norm_nonneg _)
      _ < ε/3 := hsmall
  have h₂ : ‖f (tailL1 N x)‖ < ε/3 := by
    calc
      ‖f (tailL1 N x)‖ ≤ ‖f‖ * ‖tailL1 N x‖ := f.le_opNorm _
      _ ≤ ‖f‖ * δ := mul_le_mul_of_nonneg_left hxN.le (norm_nonneg _)
      _ < ε/3 := hsmall
  rw [dist_eq_norm, hid]
  apply (norm_sub_le _ _).trans_lt
  have h₃ := norm_add_le (f (headL1 N (u k)) - f (headL1 N x)) (f (tailL1 N (u k)))
  have h₄ := hm k hk
  rw [dist_eq_norm] at h₄
  linarith

end WeakSequences

namespace WeakSequences
open Filter Topology
open scoped NNReal ENNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weakLimit_mem {s : Set E} (hs : Convex ℝ s) (hc : IsClosed s)
    {u : ℕ → E} (hu : ∀ n, u n ∈ s) {x : E}
    (hx : ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) : x ∈ s := by
  by_contra hn
  obtain ⟨f, c, hf, hfx⟩ := geometric_hahn_banach_closed_point hs hc hn
  have hh : f x ≤ c := le_of_tendsto (hx f) (Eventually.of_forall (fun n => (hf _ (hu n)).le))
  exact hfx.not_ge hh

theorem wsc_submodule (hE : WeakSequentiallyComplete E) (p : Submodule ℝ E)
    (hp : IsClosed (p : Set E)) : WeakSequentiallyComplete p := by
  intro u hu
  obtain ⟨x, hx⟩ := hE (fun n => (u n : E)) (hu.map p.subtypeL)
  have hxp : x ∈ p := weakLimit_mem p.convex hp (fun n => (u n).property) hx
  refine ⟨⟨x, hxp⟩, fun f => ?_⟩
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq p f
  simpa only [← hg] using hx g

theorem wsc_equiv (e : E ≃L[ℝ] F) (hF : WeakSequentiallyComplete F) :
    WeakSequentiallyComplete E := by
  intro u hu
  obtain ⟨y, hy⟩ := hF (fun n => e (u n)) (hu.map e.toContinuousLinearMap)
  refine ⟨e.symm y, fun f => ?_⟩
  simpa using hy (f.comp e.symm.toContinuousLinearMap)

abbrev ScalarC0 := NullSequences.C0 (H := ℝ)
open NullSequences

def initialOnes (N : ℕ) : ScalarC0 := ∑ i ∈ Finset.range N, single i (1 : ℝ)

@[simp] theorem initialOnes_apply (N i : ℕ) : initialOnes N i = if i < N then 1 else 0 := by
  simp [initialOnes, NullSequences.sum_apply, single_apply]

theorem summable_c0_dual (f : ScalarC0 →L[ℝ] ℝ) :
    Summable (fun i => |f (single i 1)|) := by
  classical
  apply summable_of_sum_le (fun _ => abs_nonneg _) (fun s => ?_) (c := ‖f‖)
  let w : ScalarC0 := ∑ i ∈ s, Real.sign (f (single i 1)) • single i 1
  have hw : ‖w‖ ≤ 1 := by
    apply (norm_le zero_le_one).2
    intro i
    change ‖(∑ j ∈ s, Real.sign (f (single j (1 : ℝ))) • single j (1 : ℝ)) i‖ ≤ 1
    rw [NullSequences.sum_apply]
    by_cases hi : i ∈ s
    · simp only [ZeroAtInftyContinuousMap.smul_apply, single_apply]
      rw [Finset.sum_eq_single i]
      · simp only [ite_true, smul_eq_mul, mul_one]
        rcases Real.sign_apply_eq (f (single i 1)) with h | h | h <;> rw [h] <;> norm_num
      · intro j hj hji
        simp [Ne.symm hji]
      · exact fun h => (h hi).elim
    · have hz : ∀ j ∈ s, (Real.sign (f (single j (1 : ℝ))) • single j (1 : ℝ)) i = 0 := by
        intro j hj
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp [hij]
      simp only [Finset.sum_eq_zero hz, norm_zero, zero_le_one]
  have hf : f w = ∑ i ∈ s, |f (single i 1)| := by
    simp only [w, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rcases lt_trichotomy (f (single i 1)) 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]
  rw [← hf]
  exact (le_abs_self _).trans ((f.le_opNorm w).trans (mul_le_of_le_one_right (norm_nonneg _) hw))

theorem initialOnes_weakCauchy : WeakCauchy initialOnes := by
  intro f
  have hs : Summable (fun i => f (single i 1)) := (summable_c0_dual f).of_abs
  have ht := hs.hasSum.tendsto_sum_nat
  exact (show Tendsto (fun n => f (initialOnes n)) atTop (𝓝 (∑' i, f (single i 1))) from by
    simpa [initialOnes] using ht).cauchySeq

theorem not_wsc_c0 : ¬ WeakSequentiallyComplete ScalarC0 := by
  intro h
  obtain ⟨x, hx⟩ := h initialOnes initialOnes_weakCauchy
  have hones : ∀ i, x i = 1 := by
    intro i
    have hlim : Tendsto (fun n => evalCLM (H := ℝ) i (initialOnes n)) atTop (𝓝 (1 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with n hn
      change 1 = initialOnes n i
      simp [hn]
    exact tendsto_nhds_unique (hx (evalCLM i)) hlim
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds
    (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) by
      have ht := tendsto_zero x
      have he : (fun n => x n) = (fun _ : ℕ => (1 : ℝ)) := funext hones
      simpa only [he] using ht)
  exact one_ne_zero this

theorem no_c0_of_wsc [CompleteSpace E] (hE : WeakSequentiallyComplete E) (T : ScalarC0 →L[ℝ] E)
    (a : ℝ) (ha : 0 < a) (hT : ∀ x, a * ‖x‖ ≤ ‖T x‖) : False := by
  let K : ℝ≥0 := ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
  have hanti : AntilipschitzWith K T := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simp only [dist_eq_norm, ← map_sub]
    change ‖x - y‖ ≤ a⁻¹ * ‖T (x-y)‖
    exact (le_inv_mul_iff₀ ha).2 (hT (x-y))
  have hc : IsClosed (Set.range T) := hanti.isClosed_range T.uniformContinuous
  have hw : WeakSequentiallyComplete T.range := wsc_submodule hE T.range hc
  exact not_wsc_c0 (wsc_equiv (T.equivRange hanti.injective hc) hw)

end WeakSequences

end LipschitzCounterexample
end

end OAI
