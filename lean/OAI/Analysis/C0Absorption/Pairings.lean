import OAI.Analysis.C0Absorption.Lists

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def completedPairing (f : S → ℝ) : TestSpace L o → ℝ :=
  Completion.extension (fun m : PreSpace L o => pairing S f m)

def initialPairing (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) : PreSpace L o →L[ℝ] ℝ :=
  (show PreSpace L o →ₗ[ℝ] ℝ from pairing S f).mkContinuous (E := PreSpace L o) K
    (fun m => h m)

theorem initialPairing_lipschitz (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) :
    LipschitzWith K (fun m : PreSpace L o => pairing S f m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let T := initialPairing L o f K h
  change dist (T x) (T y) ≤ K * dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact h (x-y)

@[simp] theorem completedPairing_coe (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (m : PreSpace L o) :
    completedPairing L o f (toTestSpace L o m) = pairing S f m :=
  Completion.extension_coe (initialPairing_lipschitz L o f K h).uniformContinuous m

theorem completedPairing_lipschitz (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) :
    LipschitzWith K (completedPairing L o f) :=
  completion_lipschitz (initialPairing_lipschitz L o f K h)

def completedTest (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) : TestSpace L o →L[ℝ] ℝ :=
  (initialPairing L o f K h).extend (toTestSpace L o)

theorem completedTest_eq (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (z : TestSpace L o) :
    completedTest L o f K h z = completedPairing L o f z := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (completedTest L o f K h).continuous Completion.continuous_extension
  | ih m =>
    change (initialPairing L o f K h).extend (toTestSpace L o) (toTestSpace L o m) =
      completedPairing L o f (toTestSpace L o m)
    rw [ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
      (Completion.isUniformInducing_coe (PreSpace L o)), completedPairing_coe L o f K h]
    rfl

def AdmissibleList.singleton {L₀ : Set (S → ℝ)} {C : ℝ≥0}
    (f : S → ℝ) (hf : f ∈ L₀) (hC : LipschitzWith C f) : AdmissibleList L₀ C where
  length := 1
  test _ := f
  mem _ := hf
  signed_lipschitz ε hε := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Fin.sum_univ_one, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul]
    exact hC.dist_le_mul s t

theorem singleton_norm {L₀ : Set (S → ℝ)} {C : ℝ≥0}
    (f : S → ℝ) (hf : f ∈ L₀) (hC : LipschitzWith C f)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : Molecule S) :
    ‖(AdmissibleList.singleton f hf hC).eval p m‖ = |pairing S f m| := by
  change ‖WithLp.toLp p (fun _ : Fin 1 => pairing S f m)‖ = |pairing S f m|
  apply le_antisymm
  · simpa only [Fin.sum_univ_one, WithLp.ofLp_toLp] using
      finite_lp_norm_le_sum p (WithLp.toLp p (fun _ : Fin 1 => pairing S f m))
  · exact PiLp.norm_apply_le (WithLp.toLp p (fun _ : Fin 1 => pairing S f m)) 0

theorem test_pairing_bound (n : ℕ) (f : S → ℝ) (hf : f ∈ L (triple n).1)
    (hC : LipschitzWith (listConstant n) f) (m : PreSpace L o) :
    |pairing S f m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h₁ := list_le_sigma (L (triple n).1) (listConstant n) (listExponent n) o
    (AdmissibleList.singleton f hf hC) (show Molecule S from m)
  have hs := singleton_norm f hf hC (listExponent n) (show Molecule S from m)
  change ‖(AdmissibleList.singleton f hf hC).eval (listExponent n) m‖ ≤ _ at h₁
  rw [hs] at h₁
  exact h₁.trans (sigma_le_preNorm L o n m)

theorem list_test_pairing_bound (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (i : Fin l.length)
    (m : PreSpace L o) : |pairing S (l.test i) m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h := PiLp.norm_apply_le (l.eval (listExponent n) (show Molecule S from m)) i
  change |pairing S (l.test i) m| ≤ ‖l.eval (listExponent n) m‖ at h
  exact h.trans ((list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

theorem completedList_apply (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) (i : Fin l.length) :
    completedList L o n l z i = completedPairing L o (l.test i) z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((PiLp.proj (listExponent n) (𝕜 := ℝ) (fun _ : Fin l.length => ℝ) i).continuous.comp
      (completedList L o n l).continuous) Completion.continuous_extension
  | ih m =>
    change completedList L o n l (toTestSpace L o m) i =
      completedPairing L o (l.test i) (toTestSpace L o m)
    rw [completedList_coe, completedPairing_coe L o (l.test i) ((squareWeight n)⁻¹)
      (list_test_pairing_bound L o n l i)]
    rfl

theorem pairing_tendsto {S : Type*} [MetricSpace S]
    (f : ℕ → S → ℝ) (g : S → ℝ)
    (h : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s)))
    (m : Molecule S) :
    Filter.Tendsto (fun n => pairing S (f n) m) Filter.atTop (nhds (pairing S g m)) := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]
  exact tendsto_finsetSum _ (fun s _ => (h s).const_mul (m.val s))

theorem completedPairing_tendsto (f : ℕ → S → ℝ) (g : S → ℝ) (K : ℝ≥0)
    (hbound : ∀ n (m : PreSpace L o), |pairing S (f n) m| ≤ K * ‖m‖)
    (hpoint : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s))) :
    (∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖) ∧
    ∀ z : TestSpace L o,
      Filter.Tendsto (fun n => completedPairing L o (f n) z) Filter.atTop
        (nhds (completedPairing L o g z)) := by
  have hg : ∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖ := by
    intro m
    exact le_of_tendsto (pairing_tendsto f g hpoint (show Molecule S from m)).abs
      (Filter.Eventually.of_forall fun n => hbound n m)
  refine ⟨hg, ?_⟩
  intro z
  apply tendsto_of_dense_lipschitz (toTestSpace L o) Completion.denseRange_coe
    (fun n => completedPairing L o (f n)) (completedPairing L o g) K
    (fun n => completedPairing_lipschitz L o (f n) K (hbound n))
    (completedPairing_lipschitz L o g K hg) _ z
  intro m
  have heq : (fun n => completedPairing L o (f n) (toTestSpace L o m)) =
      (fun n => pairing S (f n) m) :=
    funext (fun n => completedPairing_coe L o (f n) K (hbound n) m)
  rw [heq, completedPairing_coe L o g K hg]
  exact pairing_tendsto f g hpoint m

def transferredList (n n' : ℕ) (hL : (triple n').1 = (triple n).1)
    (hC : listConstant n' = listConstant n)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    AdmissibleList (L (triple n').1) (listConstant n') where
  length := l.length
  test := l.test
  mem i := by rw [hL]; exact l.mem i
  signed_lipschitz ε hε := by rw [hC]; exact l.signed_lipschitz ε hε

theorem listExponent_toReal_pos (n : ℕ) : 0 < (listExponent n).toReal := by
  rw [listExponent_toReal]
  positivity

theorem exists_smaller_exponent (n : ℕ) :
    ∃ n', (triple n').1 = (triple n).1 ∧ listConstant n' = listConstant n ∧
      (listExponent n').toReal < (listExponent n).toReal := by
  obtain ⟨n', hn'⟩ := triple_surjective ((triple n).1, (triple n).2.1, (triple n).2.2 + 1)
  refine ⟨n', by rw [hn'], by simp [listConstant, hn'], ?_⟩
  rw [listExponent_toReal, listExponent_toReal, hn']
  simp only [Nat.cast_add, Nat.cast_one]
  have hh : 1 / ((triple n).2.2 + 1 + 1 : ℝ) < 1 / ((triple n).2.2 + 1 : ℝ) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

theorem fixed_sigma_detector (n : ℕ) (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TestSpace L o,
      a ≤ completedSigma L o n z → ‖z‖ ≤ M →
      ∃ f ∈ L (triple n).1, δ ≤ |completedPairing L o f z| := by
  obtain ⟨n', hL, hC, hp⟩ := exists_smaller_exponent n
  let B := (squareWeight n' : ℝ)⁻¹ * M + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨δ, hδ, hdetect⟩ := exists_uniform_lp_detector (listExponent n) (listExponent n')
    (listExponent_toReal_pos n) (listExponent_toReal_pos n') hp (a / 2) B (by positivity) hB
  refine ⟨δ, hδ, ?_⟩
  intro z hsig hz
  have hex : ∃ l : AdmissibleList (L (triple n).1) (listConstant n),
      a / 2 < ‖completedList L o n l z‖ := by
    by_contra! hl
    have hs : completedSigma L o n z ≤ a / 2 := by
      rw [completedSigma_eq_iSup]
      exact ciSup_le hl
    linarith
  obtain ⟨l, hl⟩ := hex
  let l' := transferredList L n n' hL hC l
  let x : Fin l.length → ℝ := fun i => completedPairing L o (l.test i) z
  have heq : completedList L o n l z = WithLp.toLp (listExponent n) x := by
    apply PiLp.ext
    intro i
    exact completedList_apply L o n l z i
  have heq' : completedList L o n' l' z = WithLp.toLp (listExponent n') x := by
    apply PiLp.ext
    intro i
    exact completedList_apply L o n' l' z i
  have hu : ‖WithLp.toLp (listExponent n') x‖ ≤ B := by
    rw [← heq']
    calc
      ‖completedList L o n' l' z‖ ≤ completedSigma L o n' z := completedList_le_sigma L o n' l' z
      _ ≤ (squareWeight n' : ℝ)⁻¹ * ‖z‖ := completedSigma_le L o n' z
      _ ≤ (squareWeight n' : ℝ)⁻¹ * M :=
        mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (squareWeight n').coe_nonneg)
      _ ≤ B := by dsimp [B]; linarith
  rw [heq] at hl
  obtain ⟨i, hi⟩ := hdetect l.length x hl.le hu
  exact ⟨l.test i, l.mem i, hi.le⟩

end CompletedPairings

section FurtherDetectors

 theorem nonnegative_has_positive_subsequence (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hn : ¬ Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, a ≤ f (φ i) := by
  rw [Metric.tendsto_nhds] at hn
  push Not at hn
  obtain ⟨a, ha, hfrequent⟩ := hn
  have hf' : ∃ᶠ i in Filter.atTop, a ≤ f i := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hf _)] using hfrequent
  obtain ⟨φ, hm, hl⟩ := Filter.extraction_of_frequently_atTop hf'
  exact ⟨a, ha, φ, hm, hl⟩

theorem bounded_signs_norm_each {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) (i : ℕ) :
    ‖m i‖ ≤ M := by
  have hM : 0 ≤ M := by simpa using hsum 0 Fin.elim0
  let ε : Fin (i+1) → Bool := fun _ => true
  let j : Fin (i+1) := ⟨i, Nat.lt_succ_self i⟩
  have h := seminorm_sign_pair (normSeminorm ℝ X) (fun j : Fin (i+1) => m j) ε j
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (hsum (i+1) ε) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (hsum (i+1) (flipSign j ε)) 2
  change 2 * ‖m i‖ ^ 2 ≤ ‖∑ k : Fin (i+1), realSign (ε k) • m k‖ ^ 2 +
    ‖∑ k : Fin (i+1), realSign (flipSign j ε k) • m k‖ ^ 2 at h
  nlinarith [norm_nonneg (m i)]

theorem bounded_signs_weak_null {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (u : X →L[ℝ] ℝ) : Filter.Tendsto (fun i => u (m i)) Filter.atTop (nhds 0) := by
  classical
  have hb (n : ℕ) : ∑ i : Fin n, |u (m i)| ≤ ‖u‖ * M := by
    let ε : Fin n → Bool := fun i => if 0 ≤ u (m i) then true else false
    have hε (i : Fin n) : realSign (ε i) * u (m i) = |u (m i)| := by
      dsimp [ε]
      split
      · rw [realSign_true, one_mul, abs_of_nonneg ‹_›]
      · rw [realSign_false, neg_one_mul, abs_of_neg (lt_of_not_ge ‹_›)]
    have heq : u (∑ i : Fin n, realSign (ε i) • m i) = ∑ i : Fin n, |u (m i)| := by
      simp only [map_sum, map_smul, smul_eq_mul, hε]
    calc
      ∑ i : Fin n, |u (m i)| = ‖u (∑ i : Fin n, realSign (ε i) • m i)‖ := by
        rw [heq, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      _ ≤ ‖u‖ * ‖∑ i : Fin n, realSign (ε i) • m i‖ := u.le_opNorm _
      _ ≤ ‖u‖ * M := mul_le_mul_of_nonneg_left (hsum n ε) (norm_nonneg _)
  have hs : Summable (fun i => |u (m i)|) :=
    summable_of_sum_range_le (c := ‖u‖ * M) (fun i => abs_nonneg _) (fun n => by
      rw [Finset.sum_range]
      exact hb n)
  have hs' : Summable (fun i => u (m i)) := summable_norm_iff.mp (by simpa using hs)
  exact hs'.tendsto_atTop_zero

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedCoordinate_eq_weight_sigma (n : ℕ) (z : TestSpace L o) :
    completedCoordinate L o n z = (squareWeight n : ℝ) * completedSigma L o n z := by
  change completedCoordinate L o n z = (squareWeight n : ℝ) *
    ((squareWeight n : ℝ)⁻¹ * completedCoordinate L o n z)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul]

theorem one_class_detects (m : ℕ → TestSpace L o) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ℕ → S → ℝ, ∀ i, f i ∈ L h ∧ δ ≤ |completedPairing L o (f i) (m (φ i))| := by
  have hnorm := bounded_signs_norm_each m M hsum
  have hM : 0 < M := hr.trans_le ((hlower 0).trans (hnorm 0))
  obtain ⟨n, hn⟩ := exists_nonzero_coordinate (completedCoordinate L o)
    (completedCoordinate_summable L o) (completedNorm_sq L o) m M r hr hlower hsum
  have hnσ : ¬ Filter.Tendsto (fun i => completedSigma L o n (m i))
      Filter.atTop (nhds 0) := by
    intro hh
    apply hn
    have hh' := hh.const_mul (squareWeight n : ℝ)
    simpa only [mul_zero, ← completedCoordinate_eq_weight_sigma] using hh'
  obtain ⟨a, ha, φ, hφ, hφa⟩ := nonnegative_has_positive_subsequence
    (fun i => completedSigma L o n (m i)) (fun i => apply_nonneg _ _) hnσ
  obtain ⟨δ, hδ, hδdetect⟩ := fixed_sigma_detector L o n a M ha hM
  have hchoose : ∀ i, ∃ f ∈ L (triple n).1, δ ≤ |completedPairing L o f (m (φ i))| :=
    fun i => hδdetect (m (φ i)) (hφa i) (hnorm (φ i))
  choose f hf hd using hchoose
  exact ⟨(triple n).1, δ, hδ, φ, hφ, f, fun i => ⟨hf i, hd i⟩⟩

end FurtherDetectors

end
end C0Absorption

end OAI
