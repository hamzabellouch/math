import OAI.Analysis.LipschitzEquivalence.RadiusReduction

namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def Near (A : Finset M) (δ : ℝ) : Set M :=
  {x | ∃ a ∈ A, dist x a ≤ δ}

omit [Zero M] in
theorem near_mono {A B : Finset M} (h : A ⊆ B) (δ : ℝ) : Near A δ ⊆ Near B δ := by
  rintro x ⟨a,ha,hxa⟩
  exact ⟨a,h ha,hxa⟩

omit [Zero M] in
theorem subset_near (A : Finset M) {δ : ℝ} (hδ : 0 ≤ δ) : (A : Set M) ⊆ Near A δ := by
  intro x hx
  exact ⟨x,hx,by simpa using hδ⟩

theorem prefix_finite_approx (μ : ℕ → Space M) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset M, (0 : M) ∈ A ∧ ∀ i < N, Approximable (μ i) (A : Set M) ε := by
  classical
  induction N with
  | zero => exact ⟨{0},by simp,by simp⟩
  | succ N ih =>
    obtain ⟨A,hA,hN⟩ := ih
    obtain ⟨a,ha⟩ := exists_finite_approx (μ N) hε
    refine ⟨A ∪ a.support,Finset.mem_union_left _ hA,?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · exact (hN i hi).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact ⟨Finsupp.linearCombination ℝ point a,
        combination_mem_supported a (fun x hx => Finset.mem_union_right _ hx),ha⟩

theorem cutoff_product_bound (f : M → ℝ) {C s : ℝ≥0} (hf : LipschitzWith C f)
    (hf0 : f 0 = 0) (hs : 0 < s) (x : M) : |f x * cutoff 0 s x| ≤ C*s := by
  have hfval : |f x| ≤ C*dist x 0 := by simpa [Real.dist_eq,hf0] using hf.dist_le_mul x 0
  rw [abs_mul,abs_of_nonneg (cutoff_nonneg 0 s x)]
  by_cases hz : cutoff 0 s x = 0
  · rw [hz,mul_zero]; positivity
  · have hx : dist x 0 < s := by
      by_contra h
      exact hz (cutoff_zero 0 hs (le_of_not_gt h))
    exact (mul_le_of_le_one_right (abs_nonneg _) (cutoff_le_one _ _ _)).trans
      (hfval.trans (mul_le_mul_of_nonneg_left hx.le C.coe_nonneg))

theorem finite_escape_step {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    {R : ℝ≥0} (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hfail : ∀ A : Finset M, (0 : M) ∈ A → ∃ i, ¬ Approximable (μ i) (Near A δ) ε)
    (p : ℕ) (A : Finset M) : ∃ i : ℕ, ∃ B : Finset M, ∃ g : M → ℝ,
      p < i ∧ (0 : M) ∈ B ∧
      LipschitzWith (3+(2/δ)*(2*R+2)) g ∧ g 0 = 0 ∧
      (∀ x ∈ Near A δ, g x = 0) ∧ (∀ x, g x ≠ 0 → x ∈ Near B δ) ∧
      ∀ hg : LipschitzWith (3+(2/δ)*(2*R+2)) g, ε/2 < |test (normalized g hg) (μ i)| := by
  classical
  obtain ⟨P,hP,hprefix⟩ := prefix_finite_approx μ hε (p+1)
  obtain ⟨i,hi⟩ := hfail (A ∪ P) (Finset.mem_union_right _ hP)
  have hip : p < i := by
    by_contra h
    apply hi
    exact ((hprefix i (Nat.lt_succ_of_le (le_of_not_gt h))).mono
      (by intro x hx; exact Finset.mem_union_right _ hx)).mono
        (subset_near _ (show (0 : ℝ) ≤ δ from δ.coe_nonneg))
  have hfar : ∀ ν : Space M, ν ∈ supported (Near (A ∪ P) δ) → ε ≤ ‖μ i-ν‖ := by
    intro ν hν
    exact le_of_not_gt (fun h => hi ⟨ν,hν,h⟩)
  obtain ⟨f,hf,hf0,hfA,hlarge⟩ := exists_vanishing_test (Near (A ∪ P) δ) (μ i) hfar
  let s : ℝ≥0 := 2*R+2
  have hs : 0 < s := by dsimp [s]; positivity
  let f' : M → ℝ := fun x => f x * cutoff 0 s x
  have hf' : LipschitzWith 3 f' := by
    simpa only [mul_one] using cutoff_product_lipschitz 0 hs f hf hf0
  have hf'0 : f' 0 = 0 := by simp [f',hf0]
  have hf'bound (x : M) : |f' x| ≤ s := by
    simpa only [NNReal.coe_one,one_mul] using cutoff_product_bound f hf hf0 hs x
  have hfeq : test (normalized f hf) (μ i) = test (normalized f' hf') (μ i) := by
    apply test_eq_of_agree (by simp) f f' hf hf' ?_ (hsupp i)
    intro x hx
    have hdist : dist x 0 ≤ (s : ℝ)/2 := by
      change dist x 0 ≤ (↑(2*R+2 : ℝ≥0))/2
      push_cast
      change dist x 0 ≤ (R : ℝ) at hx
      linarith
    simp [f',cutoff_one 0 hs hdist]
  let C : ℝ≥0 := 3+(2/δ)*s
  have hC : 0 < (3+C : ℝ≥0) := by dsimp [C]; positivity
  obtain ⟨a,ha⟩ := exists_finite_approx (μ i) (show 0 < ε/(8*(3+C : ℝ≥0)) by positivity)
  let B : Finset M := insert 0 a.support
  let g : M → ℝ := fun x => setCutoff (B : Set M) δ x * f' x
  have hg : LipschitzWith C g := by
    simpa only [one_mul,smul_eq_mul] using
      lipschitz_effective_smul f' (setCutoff (B : Set M) δ) hf' (setCutoff_lipschitz _ _)
        (A := 1) (P := s)
        (fun x => by rw [abs_of_nonneg (setCutoff_nonneg _ _ _)]; exact setCutoff_le_one _ _ _)
        (fun x _ => hf'bound x)
  refine ⟨i,B,g,hip,by simp [B],hg,by simp [g,hf'0],?_,?_,?_⟩
  · intro x hx
    have hz := hfA x (near_mono Finset.subset_union_left _ hx)
    simp [g,f',hz]
  · intro x hx
    have hcut : setCutoff (B : Set M) δ x ≠ 0 := fun h => hx (by simp [g,h])
    obtain ⟨y,hy,hxy⟩ := (Metric.infDist_lt_iff (show (B : Set M).Nonempty from
      ⟨0,by simp [B]⟩)).mp (setCutoff_nonzero hδ hcut)
    exact ⟨y,hy,hxy.le⟩
  · intro hg'
    have he (x : M) (hx : x ∈ (B : Set M)) : f' x = g x := by
      have hdist : Metric.infDist x (B : Set M) ≤ (δ : ℝ)/2 := by
        rw [Metric.infDist_zero_of_mem hx]
        positivity
      simp [g,setCutoff_one hδ hdist]
    have hdiff := pairing_difference_le (show (0 : M) ∈ (B : Set M) from by simp [B])
      f' g hf' hg' he (μ i) (Finsupp.linearCombination ℝ point a)
      (combination_mem_supported a (fun x hx => Finset.mem_insert_of_mem hx))
    have hl := hlarge hf
    rw [hfeq] at hl
    have heps : (3+C : ℝ≥0)*‖μ i-Finsupp.linearCombination ℝ point a‖ < ε/8 := by
      have hh := (lt_div_iff₀ (show (0 : ℝ) < 8*(3+C : ℝ≥0) by positivity)).mp ha
      push_cast at hh ⊢
      nlinarith
    have habs := le_abs_self (test (normalized f' hf') (μ i)-test (normalized g hg') (μ i))
    have habsg := le_abs_self (test (normalized g hg') (μ i))
    change |test (normalized f' hf') (μ i)-test (normalized g hg') (μ i)| ≤
      (3+C : ℝ≥0)*‖μ i-Finsupp.linearCombination ℝ point a‖ at hdiff
    linarith

theorem uniform_finite_neighborhood_approx {μ : ℕ → Space M}
    (hw : WeakSequences.WeakNull μ) {R : ℝ≥0}
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset M, (0 : M) ∈ A ∧ ∀ i, Approximable (μ i) (Near A δ) ε := by
  classical
  by_contra h
  have hfail : ∀ A : Finset M, (0 : M) ∈ A → ∃ i, ¬ Approximable (μ i) (Near A δ) ε := by
    intro A hA
    by_contra! h'
    exact h ⟨A,hA,h'⟩
  choose idx pts tests hip hpts hequi hz hinner houter hlarge using
    finite_escape_step hε hsupp hδ hfail
  let seq : ℕ → ℕ × Finset M := fun n =>
    Nat.rec (0,{0}) (fun _ q => (idx q.1 q.2,q.2 ∪ pts q.1 q.2)) n
  have hidx : StrictMono (fun n => (seq n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hip _ _
  have hsets : Monotone (fun n => (seq n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    exact Finset.subset_union_left
  let g : ℕ → M → ℝ := fun n => tests (seq n).1 (seq n).2
  have hg (n : ℕ) : LipschitzWith (3+(2/δ)*(2*R+2)) (g n) := hequi _ _
  have hexcl (j k : ℕ) (hjk : j < k) (x : M) (hj : g j x ≠ 0) : g k x = 0 := by
    have hx := houter (seq j).1 (seq j).2 x hj
    apply hinner
    apply near_mono (hsets (Nat.succ_le_of_lt hjk)) _
    exact near_mono Finset.subset_union_right _ hx
  have hd : DisjointTests g := by
    intro x j k hj hk
    by_contra hjk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact hk (hexcl j k hjk x hj)
    · exact hj (hexcl k j hkj x hk)
  have hw' := hw.subseq (show StrictMono (fun n => (seq (n+1)).1) from
    fun _ _ hnk => hidx (Nat.add_lt_add_right hnk 1))
  have ht := disjoint_tests_vanish hd hg hw'
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  have hn := hN N le_rfl
  simp only [dist_zero_right,Real.norm_eq_abs] at hn
  exact (not_lt_of_gt (hlarge (seq N).1 (seq N).2 (hg N))) hn

end LipschitzCounterexample.FreeSpace

end

end OAI
