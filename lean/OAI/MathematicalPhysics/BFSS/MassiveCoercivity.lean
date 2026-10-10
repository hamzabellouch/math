import Mathlib

namespace OAI

/-! Matrix potential coercivity via normalized escaping configurations. -/

namespace BFSS

noncomputable section

open scoped Matrix

abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

def Color (N : ℕ) := { x : Mat N // x.IsHermitian ∧ Matrix.trace x = 0 }

abbrev Configuration (N : ℕ) := Fin 9 → Color N

def realBracket {N : ℕ} (x y : Mat N) : Mat N :=
  (-Complex.I) • (x * y - y * x)

def hsNormSq {N : ℕ} (x : Mat N) : ℝ :=
  ∑ a, ∑ b, Complex.normSq (x a b)

def configurationNormSq {N : ℕ} (x : Configuration N) : ℝ :=
  ∑ i, hsNormSq (x i).val

def massivePotential {N : ℕ} (h m : ℝ) (x : Configuration N) : ℝ :=
  (hsNormSq ((h : ℂ) • realBracket (x 0).val (x 1).val - (2 * m : ℝ) • (x 2).val) +
   hsNormSq ((h : ℂ) • realBracket (x 1).val (x 2).val - (2 * m : ℝ) • (x 0).val) +
   hsNormSq ((h : ℂ) • realBracket (x 2).val (x 0).val - (2 * m : ℝ) • (x 1).val) +
   h ^ 2 * (∑ i : Fin 9, ∑ j : Fin 9,
     if i < j ∧ 3 ≤ j.val then hsNormSq (realBracket (x i).val (x j).val) else 0)
   + m ^ 2 * (∑ i : Fin 9, if 3 ≤ i.val then hsNormSq (x i).val else 0)) / 2

def MassiveCoercivity (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ x : Configuration N,
    R ≤ Real.sqrt (configurationNormSq x) →
    c * configurationNormSq x ≤ massivePotential 1 1 x

lemma hsNormSq_nonneg {N : ℕ} (x : Mat N) : 0 ≤ hsNormSq x := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma hsNormSq_real_smul {N : ℕ} (r : ℝ) (x : Mat N) :
    hsNormSq (r • x) = r ^ 2 * hsNormSq x := by
  simp only [hsNormSq, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, Finset.mul_sum, pow_two]

lemma hsNormSq_complex_smul {N : ℕ} (r : ℂ) (x : Mat N) :
    hsNormSq (r • x) = Complex.normSq r * hsNormSq x := by
  simp only [hsNormSq, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]

lemma hsNormSq_trace {N : ℕ} (x : Mat N) :
    (hsNormSq x : ℂ) = Matrix.trace (xᴴ * x) := by
  simp only [hsNormSq, Complex.ofReal_sum, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  exact Complex.normSq_eq_conj_mul_self

lemma hsNormSq_unitary {N : ℕ} (u : Matrix.unitaryGroup (Fin N) ℂ) (x : Mat N) :
    hsNormSq ((u : Mat N) * x * star (u : Mat N)) = hsNormSq x := by
  apply Complex.ofReal_injective
  rw [hsNormSq_trace, hsNormSq_trace]
  change Matrix.trace (star ((u : Mat N) * x * star (u : Mat N)) *
    ((u : Mat N) * x * star (u : Mat N))) = _
  have hu : star (u : Mat N) * (u : Mat N) = 1 := Unitary.coe_star_mul_self u
  have hm : star ((u : Mat N) * x * star (u : Mat N)) *
      ((u : Mat N) * x * star (u : Mat N)) =
      (u : Mat N) * (star x * x) * star (u : Mat N) := by
    simp only [star_mul, star_star]
    calc
      _ = ((u : Mat N) * star x) * (star (u : Mat N) * (u : Mat N)) *
            (x * star (u : Mat N)) := by simp only [mul_assoc]
      _ = _ := by rw [hu, mul_one]; simp only [mul_assoc]
  rw [hm, Matrix.trace_mul_cycle, hu, one_mul]
  rfl

lemma realBracket_real_smul {N : ℕ} (r : ℝ) (x y : Mat N) :
    realBracket (r • x) (r • y) = r ^ 2 • realBracket x y := by
  simp only [realBracket, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_smul,
    pow_two]
  exact smul_comm _ _ _

open Filter Topology
open scoped Matrix.Norms.Elementwise

lemma internal_commutator_trace {N : ℕ} (S : Finset (Fin N)) (B C : Mat N) :
    (∑ i ∈ S, ∑ j ∈ S, (B i j * C j i - C i j * B j i)) = 0 := by
  simp only [Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  exact mul_comm _ _

lemma block_commutator_trace {N : ℕ} (S : Finset (Fin N)) (B C : Mat N) :
    (∑ i ∈ S, realBracket B C i i) =
      -Complex.I * ∑ i ∈ S, ∑ j ∈ Sᶜ, (B i j * C j i - C i j * B j i) := by
  simp only [realBracket, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.mul_apply, ← Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  have hsplit : (∑ i ∈ S, ∑ j : Fin N, (B i j * C j i - C i j * B j i)) =
      (∑ i ∈ S, ∑ j ∈ S, (B i j * C j i - C i j * B j i)) +
      (∑ i ∈ S, ∑ j ∈ Sᶜ, (B i j * C j i - C i j * B j i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_add_sum_compl S _).symm
  rw [hsplit, internal_commutator_trace, zero_add]

lemma tendsto_of_mul_tendsto {f g : ℕ → ℂ} {a b : ℂ}
    (hf : Tendsto f atTop (𝓝 a)) (ha : a ≠ 0)
    (hfg : Tendsto (fun n => f n * g n) atTop (𝓝 b)) :
    Tendsto g atTop (𝓝 (b / a)) := by
  have hn : ∀ᶠ n in atTop, f n ≠ 0 := hf.eventually (eventually_ne_nhds ha)
  apply (hfg.div hf ha).congr'
  filter_upwards [hn] with n hn
  exact mul_div_cancel_left₀ (g n) hn

lemma diagonal_escape_vanishes {N : ℕ}
    (u : ℕ → ℂ) (l : ℕ → Fin N → ℂ) (B C : ℕ → Mat N)
    (a : Fin N → ℂ) (b c : Mat N)
    (hu : Tendsto u atTop (𝓝 0))
    (hl : ∀ i, Tendsto (fun n => u n * l n i) atTop (𝓝 (a i)))
    (hB : ∀ i j, Tendsto (fun n => u n * B n i j) atTop (𝓝 (b i j)))
    (hC : ∀ i j, Tendsto (fun n => u n * C n i j) atTop (𝓝 (c i j)))
    (hAB : ∀ i j, Tendsto (fun n => u n *
      (realBracket (Matrix.diagonal (l n)) (B n) i j - 2 * C n i j))
      atTop (𝓝 0))
    (hCA : ∀ i j, Tendsto (fun n => u n *
      (realBracket (C n) (Matrix.diagonal (l n)) i j - 2 * B n i j))
      atTop (𝓝 0))
    (hBC : ∀ i, Tendsto (fun n => u n *
      (realBracket (B n) (C n) i i - 2 * l n i)) atTop (𝓝 0)) :
    a = 0 := by
  classical
  have hBoff : ∀ i j, a i ≠ a j → ∃ v : ℂ, Tendsto (fun n => B n i j) atTop (𝓝 v) := by
    intro i j hij
    have he := ((hl i).sub (hl j)).const_mul (-Complex.I)
    have he0 : -Complex.I * (a i - a j) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (sub_ne_zero.mpr hij)
    have hp : Tendsto (fun n => (-Complex.I * (u n * l n i - u n * l n j)) * B n i j)
        atTop (𝓝 (2 * c i j)) := by
      convert (hAB i j).add ((hC i j).const_mul 2) using 1
      · ext n
        simp only [realBracket, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
          Matrix.diagonal_mul, Matrix.mul_diagonal]
        ring
      · simp
    exact ⟨_, tendsto_of_mul_tendsto he he0 hp⟩
  have hCoff : ∀ i j, a i ≠ a j → ∃ v : ℂ, Tendsto (fun n => C n i j) atTop (𝓝 v) := by
    intro i j hij
    have he := ((hl i).sub (hl j)).const_mul Complex.I
    have he0 : Complex.I * (a i - a j) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hij)
    have hp : Tendsto (fun n => (Complex.I * (u n * l n i - u n * l n j)) * C n i j)
        atTop (𝓝 (2 * b i j)) := by
      convert (hCA i j).add ((hB i j).const_mul 2) using 1
      · ext n
        simp only [realBracket, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
          Matrix.diagonal_mul, Matrix.mul_diagonal]
        ring
      · simp
    exact ⟨_, tendsto_of_mul_tendsto he he0 hp⟩
  have hcross : ∀ i j, a i ≠ a j → Tendsto (fun n => u n *
      (B n i j * C n j i - C n i j * B n j i)) atTop (𝓝 0) := by
    intro i j hij
    obtain ⟨bij, hbij⟩ := hBoff i j hij
    obtain ⟨bji, hbji⟩ := hBoff j i hij.symm
    obtain ⟨cij, hcij⟩ := hCoff i j hij
    obtain ⟨cji, hcji⟩ := hCoff j i hij.symm
    simpa using hu.mul ((hbij.mul hcji).sub (hcij.mul hbji))
  ext i
  let S : Finset (Fin N) := Finset.univ.filter (fun j => a j = a i)
  have hiS : i ∈ S := by simp [S]
  have htrace0 : Tendsto (fun n => u n * ∑ j ∈ S, realBracket (B n) (C n) j j)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => ∑ j ∈ S, ∑ k ∈ Sᶜ,
        u n * (B n j k * C n k j - C n j k * B n k j)) atTop (𝓝 0) := by
      convert tendsto_finsetSum S (fun j hj => tendsto_finsetSum Sᶜ
        (fun k hk => hcross j k (by
          have hj' : a j = a i := (Finset.mem_filter.mp hj).2
          have hk' : a k ≠ a i := by simpa [S] using hk
          exact fun he => hk' (he.symm.trans hj')))) using 1
      simp
    convert hsum.const_mul (-Complex.I) using 1
    · ext n
      rw [block_commutator_trace]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    · simp
  have htracel : Tendsto (fun n => u n * ∑ j ∈ S, realBracket (B n) (C n) j j)
      atTop (𝓝 (2 * ∑ j ∈ S, a j)) := by
    have hres := tendsto_finsetSum S (fun j _ => (hBC j).add ((hl j).const_mul 2))
    convert hres using 1
    · ext n
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · simp only [zero_add, ← Finset.mul_sum]
  have hzero : (2 : ℂ) * ∑ j ∈ S, a j = 0 := tendsto_nhds_unique htracel htrace0
  have hsum : (∑ j ∈ S, a j) = (S.card : ℂ) * a i := by
    calc
      _ = ∑ _j ∈ S, a i := Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2)
      _ = _ := by simp
  rw [hsum] at hzero
  have hc : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨i, hiS⟩)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (by norm_num))).resolve_left hc

@[simp] lemma hsNormSq_zero {N : ℕ} : hsNormSq (0 : Mat N) = 0 := by
  simp [hsNormSq]

lemma normSq_entry_le_hsNormSq {N : ℕ} (x : Mat N) (i j : Fin N) :
    Complex.normSq (x i j) ≤ hsNormSq x := by
  apply le_trans (Finset.single_le_sum
    (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j))
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (x k l))
    (Finset.mem_univ i)

lemma norm_le_one_of_hsNormSq_le_one {N : ℕ} (x : Mat N) (h : hsNormSq x ≤ 1) :
    ‖x‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  intro i j
  have he := (normSq_entry_le_hsNormSq x i j).trans h
  rw [Complex.normSq_eq_norm_sq] at he
  nlinarith [norm_nonneg (x i j)]

lemma continuous_hsNormSq {N : ℕ} : Continuous (hsNormSq (N := N)) := by
  unfold hsNormSq
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

lemma tendsto_entry_zero_of_hsNormSq {N : ℕ} {x : ℕ → Mat N}
    (hx : Tendsto (fun n => hsNormSq (x n)) atTop (𝓝 0)) (i j : Fin N) :
    Tendsto (fun n => x n i j) atTop (𝓝 0) := by
  have he : Tendsto (fun n => Complex.normSq (x n i j)) atTop (𝓝 0) :=
    squeeze_zero (fun n => Complex.normSq_nonneg _)
      (fun n => normSq_entry_le_hsNormSq (x n) i j) hx
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  simpa only [Function.comp_def, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hs

lemma hsNormSq_conjStarAlgAut {N : ℕ} (u : Matrix.unitaryGroup (Fin N) ℂ) (x : Mat N) :
    hsNormSq (Unitary.conjStarAlgAut ℂ (Mat N) u x) = hsNormSq x := by
  rw [Unitary.conjStarAlgAut_apply]
  exact hsNormSq_unitary u x

lemma realBracket_conjStarAlgAut {N : ℕ} (u : Matrix.unitaryGroup (Fin N) ℂ) (x y : Mat N) :
    realBracket (Unitary.conjStarAlgAut ℂ (Mat N) u x)
      (Unitary.conjStarAlgAut ℂ (Mat N) u y) =
      Unitary.conjStarAlgAut ℂ (Mat N) u (realBracket x y) := by
  simp only [realBracket, map_smul, map_sub, map_mul]

lemma map_realBracket {N : ℕ} (f : Mat N ≃⋆ₐ[ℂ] Mat N) (x y : Mat N) :
    f (realBracket x y) = realBracket (f x) (f y) := by
  simp only [realBracket, map_smul, map_sub, map_mul]

lemma normalized_triple_first_norm_zero {N : ℕ}
    (u : ℕ → ℂ) (A B C : ℕ → Mat N) (q : ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    (hu : Tendsto u atTop (𝓝 0))
    (hAb : ∀ n, hsNormSq (u n • A n) ≤ 1)
    (hBb : ∀ n, hsNormSq (u n • B n) ≤ 1)
    (hCb : ∀ n, hsNormSq (u n • C n) ≤ 1)
    (hAq : Tendsto (fun n => hsNormSq (u n • A n)) atTop (𝓝 q))
    (hAB : Tendsto (fun n => hsNormSq (u n •
      (realBracket (A n) (B n) - (2 : ℂ) • C n))) atTop (𝓝 0))
    (hBC : Tendsto (fun n => hsNormSq (u n •
      (realBracket (B n) (C n) - (2 : ℂ) • A n))) atTop (𝓝 0))
    (hCA : Tendsto (fun n => hsNormSq (u n •
      (realBracket (C n) (A n) - (2 : ℂ) • B n))) atTop (𝓝 0)) :
    q = 0 := by
  classical
  let φ (n : ℕ) : Mat N ≃⋆ₐ[ℂ] Mat N :=
    Unitary.conjStarAlgAut ℂ (Mat N) (star (hA n).eigenvectorUnitary)
  let l (n : ℕ) (i : Fin N) : ℂ := (hA n).eigenvalues i
  have hdiag (n : ℕ) : φ n (A n) = Matrix.diagonal (l n) :=
    (hA n).conjStarAlgAut_star_eigenvectorUnitary
  have hφ (n : ℕ) (X : Mat N) : hsNormSq (φ n X) = hsNormSq X :=
    hsNormSq_conjStarAlgAut _ _
  let X (n : ℕ) : Fin 3 → Mat N := ![A n, B n, C n]
  let Y (n : ℕ) (k : Fin 3) : Mat N := u n • φ n (X n k)
  have hY (n : ℕ) : Y n ∈ Metric.closedBall (0 : Fin 3 → Mat N) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    apply norm_le_one_of_hsNormSq_le_one
    change hsNormSq (u n • φ n (X n k)) ≤ 1
    rw [← map_smul, hφ]
    fin_cases k
    · exact hAb n
    · exact hBb n
    · exact hCb n
  obtain ⟨y, hy, σ, hσ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin 3 → Mat N) 1).tendsto_subseq hY
  have hentry (k : Fin 3) (i j : Fin N) :=
    ((hlim.apply_nhds k).apply_nhds i).apply_nhds j
  have hl (i : Fin N) : Tendsto (fun n => u (σ n) * l (σ n) i)
      atTop (𝓝 (y 0 i i)) := by
    simpa only [Function.comp_def, Y, X, Matrix.cons_val_zero, hdiag,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq] using hentry 0 i i
  have hre (P Q R : ℕ → Mat N)
      (hr : Tendsto (fun n => hsNormSq (u n •
        (realBracket (P n) (Q n) - (2 : ℂ) • R n))) atTop (𝓝 0)) (i j : Fin N) :
      Tendsto (fun n => u (σ n) *
        (realBracket (φ (σ n) (P (σ n))) (φ (σ n) (Q (σ n))) i j -
          2 * φ (σ n) (R (σ n)) i j)) atTop (𝓝 0) := by
    have he : Tendsto (fun n => hsNormSq (u n • φ n
        (realBracket (P n) (Q n) - (2 : ℂ) • R n))) atTop (𝓝 0) := by
      simpa only [← map_smul, hφ] using hr
    simpa only [Function.comp_def, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, map_sub, map_smul, map_realBracket] using
      tendsto_entry_zero_of_hsNormSq (he.comp hσ.tendsto_atTop) i j
  have hz : (fun i => y 0 i i) = 0 := by
    apply diagonal_escape_vanishes
      (fun n => u (σ n)) (fun n => l (σ n))
      (fun n => φ (σ n) (B (σ n))) (fun n => φ (σ n) (C (σ n)))
      (fun i => y 0 i i) (y 1) (y 2) (hu.comp hσ.tendsto_atTop) hl
    · intro i j
      simpa only [Function.comp_def, Y, X, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.smul_apply, smul_eq_mul] using hentry 1 i j
    · intro i j
      simpa [Function.comp_def, Y, X] using hentry 2 i j
    · intro i j
      simpa only [hdiag] using hre A B C hAB i j
    · intro i j
      simpa only [hdiag] using hre C A B hCA i j
    · intro i
      simpa only [hdiag, Matrix.diagonal_apply_eq] using hre B C A hBC i i
  have hYzero : Tendsto (fun n => Y (σ n) 0) atTop (𝓝 (0 : Mat N)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Y, X, Matrix.cons_val_zero, hdiag, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_eq, congrFun hz i, Pi.zero_apply, Matrix.zero_apply] using hl i
    · have heq : (fun n => Y (σ n) 0 i j) = fun _ => (0 : ℂ) := by
        ext n
        simp only [Y, X, Matrix.cons_val_zero, hdiag, Matrix.smul_apply, smul_eq_mul,
          Matrix.diagonal_apply_ne _ hij, mul_zero]
      rw [heq]
      exact tendsto_const_nhds
  have hhs : Tendsto (fun n => hsNormSq (u (σ n) • A (σ n))) atTop (𝓝 0) := by
    have hn := continuous_hsNormSq.continuousAt.tendsto.comp hYzero
    simpa only [Function.comp_def, Y, X, Matrix.cons_val_zero, ← map_smul, hφ,
      hsNormSq_zero] using hn
  exact tendsto_nhds_unique (hAq.comp hσ.tendsto_atTop) hhs

lemma configurationNormSq_nonneg {N : ℕ} (x : Configuration N) :
    0 ≤ configurationNormSq x := Finset.sum_nonneg (fun _ _ => hsNormSq_nonneg _)

lemma hsNormSq_le_configurationNormSq {N : ℕ} (x : Configuration N) (i : Fin 9) :
    hsNormSq (x i).val ≤ configurationNormSq x := by
  unfold configurationNormSq
  exact Finset.single_le_sum (fun j _ => hsNormSq_nonneg (x j).val) (Finset.mem_univ i)

lemma hsNormSq_ofReal_smul {N : ℕ} (r : ℝ) (x : Mat N) :
    hsNormSq ((r : ℂ) • x) = r ^ 2 * hsNormSq x := by
  simp only [hsNormSq_complex_smul, Complex.normSq_ofReal, pow_two]

lemma massivePotential_bounds {N : ℕ} (x : Configuration N) :
    0 ≤ massivePotential 1 1 x ∧
    hsNormSq (realBracket (x 0).val (x 1).val - (2 : ℂ) • (x 2).val) ≤
      2 * massivePotential 1 1 x ∧
    hsNormSq (realBracket (x 1).val (x 2).val - (2 : ℂ) • (x 0).val) ≤
      2 * massivePotential 1 1 x ∧
    hsNormSq (realBracket (x 2).val (x 0).val - (2 : ℂ) • (x 1).val) ≤
      2 * massivePotential 1 1 x ∧
    (∀ i : Fin 9, 3 ≤ i.val → hsNormSq (x i).val ≤ 2 * massivePotential 1 1 x) := by
  let p := hsNormSq (realBracket (x 0).val (x 1).val - (2 : ℂ) • (x 2).val)
  let q := hsNormSq (realBracket (x 1).val (x 2).val - (2 : ℂ) • (x 0).val)
  let r := hsNormSq (realBracket (x 2).val (x 0).val - (2 : ℂ) • (x 1).val)
  let t := ∑ i : Fin 9, ∑ j : Fin 9,
    if i < j ∧ 3 ≤ j.val then hsNormSq (realBracket (x i).val (x j).val) else 0
  let s := ∑ i : Fin 9, if 3 ≤ i.val then hsNormSq (x i).val else 0
  have ht : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> first | exact le_refl 0 | exact hsNormSq_nonneg _
  have hs : 0 ≤ s := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> first | exact le_refl 0 | exact hsNormSq_nonneg _
  have hp : 0 ≤ p := hsNormSq_nonneg _
  have hq : 0 ≤ q := hsNormSq_nonneg _
  have hr : 0 ≤ r := hsNormSq_nonneg _
  have heq : massivePotential 1 1 x = (p + q + r + t + s) / 2 := by
    simp only [massivePotential, Complex.ofReal_one, one_smul, mul_one, one_pow, one_mul,
      two_smul, p, q, r, t, s]
  rw [heq]
  refine ⟨by linarith, by dsimp only [p] at hp ⊢; linarith,
    by dsimp only [q] at hq ⊢; linarith,
    by dsimp only [r] at hr ⊢; linarith, ?_⟩
  intro i hi
  have hsi : hsNormSq (x i).val ≤ s := by
    have hsingle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin 9 => if 3 ≤ j.val then hsNormSq (x j).val else 0)
      (fun j _ => by split_ifs <;> first | exact le_refl 0 | exact hsNormSq_nonneg _) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using hsingle
  linarith

theorem massive_coercivity (N : ℕ) (_hN : 2 ≤ N) : MassiveCoercivity N := by
  classical
  by_contra h
  unfold MassiveCoercivity at h
  push Not at h
  have hc (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  choose x hxR hxU using (fun n : ℕ => h (1 / ((n : ℝ) + 1)) (hc n) ((n : ℝ) + 1))
  let r (n : ℕ) := Real.sqrt (configurationNormSq (x n))
  let u (n : ℕ) := 1 / r n
  have hr (n : ℕ) : 0 < r n := lt_of_lt_of_le (by positivity) (hxR n)
  have hrsq (n : ℕ) : (r n) ^ 2 = configurationNormSq (x n) :=
    Real.sq_sqrt (configurationNormSq_nonneg (x n))
  have hunorm (n : ℕ) : (u n) ^ 2 * configurationNormSq (x n) = 1 := by
    rw [← hrsq n]
    dsimp only [u]
    field_simp [ne_of_gt (hr n)]
  have hu : Tendsto u atTop (𝓝 0) := by
    apply squeeze_zero (fun n => le_of_lt (one_div_pos.mpr (hr n)))
      (fun n => one_div_le_one_div_of_le (by positivity) (hxR n))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have huc : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  have hUn (n : ℕ) : 0 ≤ (u n) ^ 2 * massivePotential 1 1 (x n) :=
    mul_nonneg (sq_nonneg _) (massivePotential_bounds (x n)).1
  have hUb (n : ℕ) : (u n) ^ 2 * massivePotential 1 1 (x n) ≤ 1 / ((n : ℝ) + 1) := by
    calc
      _ ≤ (u n) ^ 2 * ((1 / ((n : ℝ) + 1)) * configurationNormSq (x n)) :=
        mul_le_mul_of_nonneg_left (hxU n).le (sq_nonneg _)
      _ = _ := by rw [mul_left_comm, hunorm n, mul_one]
  have hUlim : Tendsto (fun n => (u n) ^ 2 * massivePotential 1 1 (x n)) atTop (𝓝 0) :=
    squeeze_zero hUn hUb tendsto_one_div_add_atTop_nhds_zero_nat
  have hres (Z : ℕ → Mat N)
      (hZ : ∀ n, hsNormSq (Z n) ≤ 2 * massivePotential 1 1 (x n)) :
      Tendsto (fun n => hsNormSq ((u n : ℂ) • Z n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hsNormSq_nonneg _)
      (fun n => show hsNormSq ((u n : ℂ) • Z n) ≤ 2 * ((u n) ^ 2 * massivePotential 1 1 (x n)) from by
        rw [hsNormSq_ofReal_smul]
        calc
          _ ≤ (u n) ^ 2 * (2 * massivePotential 1 1 (x n)) :=
            mul_le_mul_of_nonneg_left (hZ n) (sq_nonneg _)
          _ = _ := by ring)
    simpa using hUlim.const_mul 2
  have h01 := hres (fun n => realBracket (x n 0).val (x n 1).val - (2 : ℂ) • (x n 2).val)
    (fun n => (massivePotential_bounds (x n)).2.1)
  have h12 := hres (fun n => realBracket (x n 1).val (x n 2).val - (2 : ℂ) • (x n 0).val)
    (fun n => (massivePotential_bounds (x n)).2.2.1)
  have h20 := hres (fun n => realBracket (x n 2).val (x n 0).val - (2 : ℂ) • (x n 1).val)
    (fun n => (massivePotential_bounds (x n)).2.2.2.1)
  let q (n : ℕ) (i : Fin 9) := hsNormSq ((u n : ℂ) • (x n i).val)
  have hqb (n : ℕ) (i : Fin 9) : q n i ≤ 1 := by
    unfold q
    rw [hsNormSq_ofReal_smul, ← hunorm n]
    exact mul_le_mul_of_nonneg_left (hsNormSq_le_configurationNormSq (x n) i) (sq_nonneg _)
  have hqn (n : ℕ) (i : Fin 9) : 0 ≤ q n i := hsNormSq_nonneg _
  have hqsum (n : ℕ) : (∑ i : Fin 9, q n i) = 1 := by
    simp only [q, hsNormSq_ofReal_smul, ← Finset.mul_sum]
    exact hunorm n
  have hqm (n : ℕ) : q n ∈ Metric.closedBall (0 : Fin 9 → ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hqn n i)] using hqb n i
  obtain ⟨a, ha, σ, hσ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin 9 → ℝ) 1).tendsto_subseq hqm
  have htriple (i j k : Fin 9)
      (hij : Tendsto (fun n => hsNormSq ((u n : ℂ) •
        (realBracket (x n i).val (x n j).val - (2 : ℂ) • (x n k).val))) atTop (𝓝 0))
      (hjk : Tendsto (fun n => hsNormSq ((u n : ℂ) •
        (realBracket (x n j).val (x n k).val - (2 : ℂ) • (x n i).val))) atTop (𝓝 0))
      (hki : Tendsto (fun n => hsNormSq ((u n : ℂ) •
        (realBracket (x n k).val (x n i).val - (2 : ℂ) • (x n j).val))) atTop (𝓝 0)) :
      a i = 0 := by
    apply normalized_triple_first_norm_zero
      (fun n => (u (σ n) : ℂ))
      (fun n => (x (σ n) i).val) (fun n => (x (σ n) j).val) (fun n => (x (σ n) k).val)
      (a i) (fun n => (x (σ n) i).property.1) (huc.comp hσ.tendsto_atTop)
      (fun n => hqb (σ n) i) (fun n => hqb (σ n) j) (fun n => hqb (σ n) k)
    · exact hlim.apply_nhds i
    · exact hij.comp hσ.tendsto_atTop
    · exact hjk.comp hσ.tendsto_atTop
    · exact hki.comp hσ.tendsto_atTop
  have h0 := htriple 0 1 2 h01 h12 h20
  have h1 := htriple 1 2 0 h12 h20 h01
  have h2 := htriple 2 0 1 h20 h01 h12
  have hlarge (i : Fin 9) (hi : 3 ≤ i.val) : a i = 0 := by
    have he := hres (fun n => (x n i).val)
      (fun n => (massivePotential_bounds (x n)).2.2.2.2 i hi)
    exact tendsto_nhds_unique (hlim.apply_nhds i) (he.comp hσ.tendsto_atTop)
  have hall (i : Fin 9) : a i = 0 := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    all_goals exact hlarge _ (by decide)
  have hsum : Tendsto (fun n => ∑ i : Fin 9, q (σ n) i) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hall, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hlim.apply_nhds i)
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [hqsum] using hsum)
  norm_num at he

end
end BFSS

end OAI
