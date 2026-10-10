import Mathlib
import OAI.Probability.BinarySweep.Processes.GridSweepPath

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section FiniteRandomWalkConvergence
variable {G : Type*} [Fintype G] [Group G]

lemma pointMassOne_probability : IsProbability (pointMassOne : G → ℝ) := by
  classical
  constructor
  · intro g; unfold pointMassOne; split_ifs <;> norm_num
  · simp [pointMassOne]

lemma convolution_one_left (p : G → ℝ) : convolution pointMassOne p = p := by
  classical
  funext g
  simp [convolution, pointMassOne, ite_mul]

lemma convolution_one_right (p : G → ℝ) : convolution p pointMassOne = p := by
  classical
  funext g
  simp [convolution, pointMassOne, mul_ite, inv_mul_eq_one]

lemma convolutionPower_probability {p : G → ℝ} (hp : IsProbability p) (n : ℕ) :
    IsProbability (convolutionPower p n) := by
  induction n with
  | zero => exact pointMassOne_probability
  | succ n ih => exact convolution_probability hp ih

lemma convolutionPower_add (p : G → ℝ) (m n : ℕ) :
    convolutionPower p (m + n) = convolution (convolutionPower p m) (convolutionPower p n) := by
  induction m with
  | zero => simp [convolutionPower, convolution_one_left]
  | succ m ih =>
    simpa only [Nat.succ_add, convolutionPower, ih] using
      (convolution_assoc p (convolutionPower p m) (convolutionPower p n)).symm

lemma convolutionPower_one (p : G → ℝ) : convolutionPower p 1 = p :=
  convolution_one_right p

lemma convolutionPower_succ_right (p : G → ℝ) (n : ℕ) :
    convolutionPower p (n + 1) = convolution (convolutionPower p n) p := by
  rw [convolutionPower_add, convolutionPower_one]

lemma convolutionPower_block_bound {p : G → ℝ} (hp : IsProbability p) (L : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ 1 - δ)
    (hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g) (k : ℕ) :
    totalVariation (convolutionPower p (L * k)) (uniformLaw G) ≤ (1 - δ) ^ k := by
  induction k with
  | zero =>
    simp only [mul_zero, pow_zero]
    exact totalVariation_le_one (convolutionPower_probability hp 0) uniformLaw_probability
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm, convolutionPower_add]
    calc
      _ ≤ (1 - δ) * totalVariation (convolutionPower p (L * k)) (uniformLaw G) :=
        convolution_minorization (convolutionPower_probability hp L)
          (convolutionPower_probability hp (L * k)) δ hδ
      _ ≤ (1 - δ) * (1 - δ) ^ k := mul_le_mul_of_nonneg_left ih hδ0
      _ = _ := by rw [pow_succ]; ring

lemma convolutionPower_all_time_bound {p : G → ℝ} (hp : IsProbability p) (L : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ 1 - δ)
    (hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g) (t : ℕ) :
    totalVariation (convolutionPower p t) (uniformLaw G) ≤ (1 - δ) ^ (t / L) := by
  have he := convolutionPower_add p (t % L) (L * (t / L))
  rw [Nat.mod_add_div] at he
  rw [he, ← convolution_uniform_right (convolutionPower_probability hp (t % L)).2]
  have hc := convolution_tv_contract (convolutionPower_probability hp (t % L)).1
    (convolutionPower p (L * (t / L))) (uniformLaw G)
  rw [(convolutionPower_probability hp (t % L)).2, one_mul] at hc
  exact hc.trans (convolutionPower_block_bound hp L hδ0 hδ (t / L))

lemma uniformLaw_le_one (g : G) : uniformLaw G g ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  exact (inv_le_one₀ (by linarith)).mpr hc

theorem convolutionPower_tendsto_uniform {p : G → ℝ} (hp : IsProbability p)
    {L : ℕ} (hL : 0 < L) (hpos : ∀ g, 0 < convolutionPower p L g) :
    Filter.Tendsto (fun t => totalVariation (convolutionPower p t) (uniformLaw G))
      Filter.atTop (nhds 0) := by
  classical
  let ε := Finset.univ.inf' Finset.univ_nonempty (convolutionPower p L)
  have hε : 0 < ε := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun g _ => hpos g)
  let δ : ℝ := min (1 / 2) ε
  have hδpos : 0 < δ := lt_min (by norm_num) hε
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδ0 : 0 ≤ 1 - δ := by linarith
  have hδ : ∀ g, δ * uniformLaw G g ≤ convolutionPower p L g := by
    intro g
    calc
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (uniformLaw_le_one g) hδpos.le
      _ = δ := mul_one _
      _ ≤ ε := min_le_right _ _
      _ ≤ _ := Finset.inf'_le _ (Finset.mem_univ g)
  apply squeeze_zero (fun _ => totalVariation_nonneg _ _)
    (convolutionPower_all_time_bound hp L hδ0 hδ)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 (by linarith)).comp
    (Nat.tendsto_div_const_atTop hL.ne')

end FiniteRandomWalkConvergence

lemma finiteLaw_pos_of_mem {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (ω : Ω) : 0 < finiteLaw f (f ω) := by
  classical
  have : Nonempty Ω := ⟨ω⟩
  apply Finset.sum_pos'
  · intro a _; split_ifs <;> positivity
  · exact ⟨ω, Finset.mem_univ _, by simp [Fintype.card_pos]⟩

section ReachableRandomWalk
variable {G Ω : Type*} [Fintype G] [Group G] [Fintype Ω] [Nonempty Ω]

lemma convolution_pos_at_mul {p q : G → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    {g h : G} (hg : 0 < p g) (hh : 0 < q h) : 0 < convolution p q (g * h) := by
  classical
  apply Finset.sum_pos'
  · intro x _; exact mul_nonneg (hp x) (hq _)
  · refine ⟨g, Finset.mem_univ _, ?_⟩
    simpa using mul_pos hg hh

lemma convolutionPower_pos_list (f : Ω → G) (l : List Ω) :
    0 < convolutionPower (finiteLaw f) l.length (l.map f).prod := by
  induction l with
  | nil => simp [convolutionPower, pointMassOne]
  | cons a l ih =>
    simpa only [List.length_cons, List.map_cons, List.prod_cons, convolutionPower] using
      convolution_pos_at_mul (finiteLaw_nonneg f)
        (convolutionPower_probability ⟨finiteLaw_nonneg f, finiteLaw_sum f⟩ l.length).1
        (finiteLaw_pos_of_mem f a) ih

lemma convolutionPower_pos_later {p : G → ℝ} (hp : IsProbability p) (h1 : 0 < p 1)
    {g : G} {n m : ℕ} (hn : 0 < convolutionPower p n g) (hnm : n ≤ m) :
    0 < convolutionPower p m g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    change 0 < convolution p (convolutionPower p (n + k)) g
    simpa only [one_mul] using
      convolution_pos_at_mul hp.1 (convolutionPower_probability hp (n + k)).1 h1 ih

lemma finiteLaw_fullSupport_power (f : Ω → G) (ω₀ : Ω) (hω₀ : f ω₀ = 1)
    (hgen : ∀ g : G, ∃ l : List Ω, (l.map f).prod = g) :
    ∃ L : ℕ, 0 < L ∧ ∀ g, 0 < convolutionPower (finiteLaw f) L g := by
  classical
  choose l hl using hgen
  let L := 1 + ∑ g : G, (l g).length
  refine ⟨L, by dsimp [L]; omega, ?_⟩
  intro g
  apply convolutionPower_pos_later ⟨finiteLaw_nonneg f, finiteLaw_sum f⟩
    (hω₀ ▸ finiteLaw_pos_of_mem f ω₀)
  · rw [← hl g]
    exact convolutionPower_pos_list f (l g)
  · exact (Finset.single_le_sum (fun i _ => Nat.zero_le ((l i).length))
      (Finset.mem_univ g)).trans (Nat.le_add_left _ _)

end ReachableRandomWalk

theorem fixed_dimension_sweep_convergence (d : ℕ) :
    Filter.Tendsto (fun t => totalVariation (sweepLaw d t)
      (uniformLaw (Equiv.Perm (Slot d)))) Filter.atTop (nhds 0) := by
  obtain ⟨L, hL, hpos⟩ := finiteLaw_fullSupport_power (binarySweep d)
    (fun _ _ => false) (binarySweep_zero d) (every_permutation_sweepReachable d)
  exact convolutionPower_tendsto_uniform
    ⟨finiteLaw_nonneg (binarySweep d), finiteLaw_sum (binarySweep d)⟩ hL hpos

variable {G Ω Ξ : Type*} [Fintype G] [Group G] [Fintype Ω] [Fintype Ξ]

omit [Group G] in
lemma finiteLaw_reindex (e : Ω ≃ Ξ) (f : Ξ → G) : finiteLaw (f ∘ e) = finiteLaw f := by
  classical
  funext g
  unfold finiteLaw
  rw [Fintype.card_congr e]
  exact Equiv.sum_comp e (fun ξ => if f ξ = g then (Fintype.card Ξ : ℝ)⁻¹ else 0)

lemma finiteLaw_independent_mul (f : Ω → G) (k : Ξ → G) :
    finiteLaw (fun a : Ω × Ξ => f a.1 * k a.2) = convolution (finiteLaw f) (finiteLaw k) := by
  classical
  funext g
  rw [convolution, finiteLaw_expectation]
  simp only [finiteLaw, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    Finset.mul_sum, eq_inv_mul_iff_mul_eq]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ξ _
  split_ifs <;> ring

end BinaryCoordinateSweeps
end

end OAI
