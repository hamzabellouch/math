import OAI.Probability.DilutedSpin.UpperCommonCoefficient

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def mixedLogAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) (t : ℝ) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      logInsertion (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
        m (mixedTreeD z sel V x r i) t))

lemma mixedQMoment_eq (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) (k : ℕ) :
    qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n) =
      (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
        (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
          qMoment m (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
            (fun y => -mixedTreeD z sel V x r i y) k (single n))) := by
  unfold mixedLeafAvg
  rw [qExpect_expect]
  apply FiniteLaw.expect_congr
  intro i
  rw [qExpect_expect]
  rfl

lemma mixedLogAvg_negative_tail (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (z : InteractionSample p) (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |mixedLogAvg T Q U V x m z sel t-∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n)| ≤
        ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  simp only [mixedLogAvg,mixedQMoment_eq]
  simp_rw [← FiniteLaw.expect_mul_left,← FiniteLaw.expect_sum,← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro i
  apply FiniteLaw.abs_expect_le
  intro r
  exact logInsertion_negative_tail _ m hm hpos hnz hroot hend _
    (fun y => mixedFactor_bound z hz sel _ _) ht K

lemma measurable_mixedLogAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (sel : Fin p → Bool) (t : ℝ) :
    Measurable (fun z => mixedLogAvg T Q U V x m z sel t) := by
  apply FiniteLaw.measurable_expect
  intro i
  apply FiniteLaw.measurable_expect
  intro r
  apply KernelTower.measurable_backwardLog
  intro y
  exact ((measurable_mixedFactor sel _ _).const_mul t |>.const_add 1).log

lemma integrable_mixedLogAvg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) :
    Integrable (fun z => mixedLogAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_mixedLogAvg T Q U V x m sel t).aestronglyMeasurable
    (∑' k : ℕ,|t|^(k+1)/(k+1))
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs,Finset.range_zero,Finset.sum_empty,sub_zero,Nat.add_zero,
    Nat.cast_zero,add_zero] using mixedLogAvg_negative_tail T Q U V x m hm hpos hnz hroot hend
      z (fun s => (hz.2 s).2.le) sel ht 0

lemma integral_mixedLogAvg_negative_tail (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |(∫ z,mixedLogAvg T Q U V x m z sel t ∂M.disorder.toMeasure)-∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qExpect m
        (fun S => ∫ z,mixedLeafAvg S T Q U V x z sel ∂M.disorder.toMeasure) k (single n)| ≤
        ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  have hi (S : PrescribedTree n) := integrable_mixedLeafAvg M hM S T Q U V x sel
  simp_rw [← integral_qExpect _ m _ hi,← integral_const_mul]
  rw [← integral_finsetSum _ (fun k _ => (integrable_qExpect _ m _ hi k (single n)).const_mul _)]
  rw [← integral_sub (integrable_mixedLogAvg M hM T Q U V x m hm hpos hnz hroot hend sel ht)
    (integrable_finsetSum _ (fun k _ => (integrable_qExpect _ m _ hi k (single n)).const_mul _))]
  have hb : ∀ᵐ z ∂M.disorder.toMeasure,
      ‖mixedLogAvg T Q U V x m z sel t-∑ k∈Finset.range K,
        -(t^(k+1)/(k+1))*qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n)‖ ≤
          ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
    filter_upwards [hM.factorization] with z hz
    simpa only [Real.norm_eq_abs] using mixedLogAvg_negative_tail T Q U V x m hm hpos hnz hroot hend
      z (fun s => (hz.2 s).2.le) sel ht K
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

lemma negative_series_combination {A B C a b t R : ℝ} (ha : 0≤a) (hb : 0≤b)
    (ht : 0≤t) (f g h : ℕ → ℝ) (K : ℕ)
    (hA : |A-∑ k∈Finset.range K,-(t^(k+1)/(k+1))*f k|≤R)
    (hB : |B-∑ k∈Finset.range K,-(t^(k+1)/(k+1))*g k|≤R)
    (hC : |C-∑ k∈Finset.range K,-(t^(k+1)/(k+1))*h k|≤R)
    (hc : ∀ k, 0≤f k-a*g k+b*h k) : A-a*B+b*C≤(1+a+b)*R := by
  have hs : (∑ k∈Finset.range K,-(t^(k+1)/(k+1))*f k)-
      a*(∑ k∈Finset.range K,-(t^(k+1)/(k+1))*g k)+
      b*(∑ k∈Finset.range K,-(t^(k+1)/(k+1))*h k) ≤0 := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_nonpos
    intro k _
    have he : -(t^(k+1)/(k+1))*f k-a*(-(t^(k+1)/(k+1))*g k)+
        b*(-(t^(k+1)/(k+1))*h k)=-(t^(k+1)/(k+1))*(f k-a*g k+b*h k) := by ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (pow_nonneg ht _) (by positivity))) (hc k)
  have hA' := (abs_le.mp hA).2
  have hB' := mul_le_mul_of_nonneg_left (abs_le.mp hB).1 ha
  have hC' := mul_le_mul_of_nonneg_left (abs_le.mp hC).2 hb
  nlinarith only [hs,hA',hB',hC']

/-- The common-tree regularized interpolation derivative has the required
sign under the original factorization and positivity hypotheses. -/
lemma integral_mixedLog_combination_nonpos (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    (∫ z,mixedLogAvg T Q U V x m z (fun _ => true) t ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedLogAvg T Q U V x m z (fun l => decide (l=j)) t ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedLogAvg T Q U V x m z (fun _ => false) t ∂M.disorder.toMeasure) ≤0 := by
  have ht' : |t|<1 := by rwa [abs_of_nonneg ht0]
  have hlim : Tendsto (fun K : ℕ => (1+(p:ℝ)+((p-1:ℕ):ℝ))*
      ∑' k : ℕ,|t|^(k+K+1)/(k+K+1)) atTop (𝓝 0) := by
    convert (tendsto_sum_nat_add (fun k : ℕ => |t|^(k+1)/(k+1))).const_mul
      (1+(p:ℝ)+((p-1:ℕ):ℝ)) using 1 <;> simp
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun K => negative_series_combination (Nat.cast_nonneg p)
    (Nat.cast_nonneg (p-1)) ht0 _ _ _ K
    (integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (fun k => mixedQMoment_combination_nonneg M hM T Q U V x m hm hpos k (single n) j))

end DilutedSpinGlass.PrescribedTree

end

end OAI
