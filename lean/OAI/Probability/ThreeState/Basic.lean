import Mathlib

namespace OAI

/-! Three-state symmetric broadcast experiments, posterior advantage and total variation. -/

namespace ThreeState

abbrev Spin := Fin 3

 
def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

 
noncomputable def channel (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

 

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

theorem channel_nonneg {lam : ℝ} (h : Admissible lam) (i j : Spin) :
    0 ≤ channel lam i j := by
  unfold channel
  split_ifs
  · dsimp [Admissible] at h
    linarith [h.1]
  · dsimp [Admissible] at h
    linarith [h.2]

theorem channel_sum (lam : ℝ) (i : Spin) : ∑ j, channel lam i j = 1 := by
  fin_cases i <;> simp [channel, Fin.sum_univ_succ] <;> ring

noncomputable def channelPMF (lam : ℝ) (h : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j => ENNReal.ofReal (channel lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => channel_nonneg h i j)]
    simp [channel_sum])

 
noncomputable def iidList {α : Type*} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun a => (iidList p n).map (List.cons a)

 

noncomputable def observedLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Spin → PMF (Observation n)
  | 0, i => PMF.pure i
  | n + 1, i => offspring.bind fun k =>
      (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h n)) k).map
        (fun xs : List (Observation n) => (xs : Multiset (Observation n)))

noncomputable def uniformSpin : PMF Spin := PMF.ofFintype (fun _ => 1 / 3) (by
  simp
  exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness))

 
noncomputable def marginal {α : Type*} (law : Spin → PMF α) : PMF α :=
  uniformSpin.bind law

 
noncomputable def posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) : ℝ :=
  if marginal law y = 0 then 1 / 3
  else (law i y).toReal / (3 * (marginal law y).toReal)

 

noncomputable def advantage {α : Type*} (law : Spin → PMF α) : ℝ :=
  ∑' y, (marginal law y).toReal *
    ((∑ i : Spin, |posterior law y i - 1 / 3|) / 2)

noncomputable def regularLaw (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) :=
  observedLaw (PMF.pure b) lam h n

 
noncomputable def poissonOffspring (d : ℝ) (hd : 0 ≤ d) : PMF ℕ := by
  refine ⟨fun k => ENNReal.ofReal (Real.exp (-d) * d ^ k / (k.factorial : ℝ)), ?_⟩
  apply ENNReal.hasSum_coe.2
  have hsum : HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / (k.factorial : ℝ)) 1 :=
    ProbabilityTheory.hasSum_one_poissonMeasure ⟨d, hd⟩
  simpa using hsum.toNNReal (fun k => by positivity)

noncomputable def poissonLaw (d : ℝ) (hd : 0 ≤ d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) :=
  observedLaw (poissonOffspring d hd) lam h n

noncomputable def regularAdvantage (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (regularLaw b lam h n)

noncomputable def poissonAdvantage (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (poissonLaw d (le_trans (by norm_num) hd.le) lam h n)

 
def Reconstructs (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Filter.Tendsto a Filter.atTop (nhds L)

 
def Nonreconstructs (a : ℕ → ℝ) : Prop :=
  Filter.Tendsto a Filter.atTop (nhds 0)

end ThreeState
namespace ThreeState

noncomputable def mass {α : Type*} (p : PMF α) (a : α) : ℝ := (p a).toReal

lemma mass_nonneg {α : Type*} (p : PMF α) (a : α) : 0 ≤ mass p a := ENNReal.toReal_nonneg
lemma mass_sum {α : Type*} (p : PMF α) : ∑' a, mass p a = 1 := by
  simp only [mass, ← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe,
    ENNReal.toReal_one]
lemma mass_summable {α : Type*} (p : PMF α) : Summable (mass p) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

lemma mass_bind {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    mass (p.bind k) b = ∑' a, mass p a * mass (k a) b := by
  simp only [mass, PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b)), ENNReal.toReal_mul]

lemma mass_uniform (i : Spin) : mass uniformSpin i = 1/3 := by
  simp [mass, uniformSpin, PMF.ofFintype_apply]

lemma mass_marginal {α : Type*} (law : Spin → PMF α) (y : α) :
    mass (marginal law) y = (∑ i : Spin, mass (law i) y)/3 := by
  simp only [marginal, mass_bind, tsum_fintype, mass_uniform]
  rw [← Finset.mul_sum]
  ring

lemma mass_eq_zero {α : Type*} (p : PMF α) (a : α) : mass p a = 0 ↔ p a = 0 := by
  simp [mass, ENNReal.toReal_eq_zero_iff, p.apply_ne_top a]

lemma marginal_zero {α : Type*} (law : Spin → PMF α) (y : α)
    (h : marginal law y = 0) (i : Spin) : law i y = 0 := by
  apply (mass_eq_zero (law i) y).mp
  have hh : mass (marginal law) y = 0 := (mass_eq_zero _ _).mpr h
  rw [mass_marginal] at hh
  have hs : ∑ j : Spin, mass (law j) y = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mass_nonneg (law j) y)).mp hs i (by simp)

lemma posterior_nonneg {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    0 ≤ posterior law y i := by
  unfold posterior
  split_ifs <;> positivity

lemma posterior_sum {α : Type*} (law : Spin → PMF α) (y : α) :
    ∑ i : Spin, posterior law y i = 1 := by
  classical
  have hn := (marginal law).apply_ne_top y
  by_cases h : marginal law y = 0
  · simp [posterior, h]
  · have hm : mass (marginal law) y ≠ 0 := mt (mass_eq_zero _ _).mp h
    simp only [posterior, ite_eq_right h, ← Finset.sum_div]
    change (∑ i : Spin, mass (law i) y)/(3*mass (marginal law) y) = 1
    have he := mass_marginal law y
    field_simp
    linarith

 
lemma weighted_posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    mass (marginal law) y * (posterior law y i-1/3) =
      (mass (law i) y-mass (marginal law) y)/3 := by
  classical
  by_cases h : marginal law y = 0
  · have hi := marginal_zero law y h i
    simp [mass, h, hi, posterior]
  · have hm : mass (marginal law) y ≠ 0 := mt (mass_eq_zero _ _).mp h
    simp only [posterior, ite_eq_right h]
    change mass (marginal law) y * (mass (law i) y / (3*mass (marginal law) y)-1/3) = _
    field_simp

lemma weighted_abs_posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    mass (marginal law) y * |posterior law y i-1/3| =
      |mass (law i) y-mass (marginal law) y|/3 := by
  calc
    mass (marginal law) y * |posterior law y i-1/3| =
        |mass (marginal law) y * (posterior law y i-1/3)| := by
      rw [abs_mul, abs_of_nonneg (mass_nonneg (marginal law) y)]
    _ = _ := by rw [weighted_posterior, abs_div]; norm_num

lemma mass_le_one {α : Type*} (p : PMF α) (a : α) : mass p a ≤ 1 := by
  simpa [mass] using ENNReal.toReal_mono (by finiteness) (p.coe_le_one a)

noncomputable def tvMass {α : Type*} (p q : PMF α) : ℝ :=
  (∑' a, |mass p a-mass q a|)/2

lemma mass_diff_summable {α : Type*} (p q : PMF α) :
    Summable (fun a => |mass p a-mass q a|) :=
  ((mass_summable p).sub (mass_summable q)).abs

lemma tvMass_nonneg {α : Type*} (p q : PMF α) : 0 ≤ tvMass p q := by
  exact div_nonneg (tsum_nonneg (fun a => abs_nonneg _)) (by norm_num)

lemma tvMass_le_one {α : Type*} (p q : PMF α) : tvMass p q ≤ 1 := by
  have h := (mass_diff_summable p q).tsum_le_tsum
    (fun a => (abs_sub (mass p a) (mass q a)).trans_eq (by
      rw [abs_of_nonneg (mass_nonneg p a), abs_of_nonneg (mass_nonneg q a)]))
    ((mass_summable p).add (mass_summable q))
  rw [(mass_summable p).tsum_add (mass_summable q), mass_sum, mass_sum] at h
  dsimp [tvMass]
  linarith

lemma advantage_eq_tvMass {α : Type*} (law : Spin → PMF α) :
    advantage law = (∑ i : Spin, tvMass (law i) (marginal law))/3 := by
  have ht (y : α) : mass (marginal law) y *
      ((∑ i : Spin, |posterior law y i-1/3|)/2) =
      (∑ i : Spin, |mass (law i) y-mass (marginal law) y|)/6 := by
    rw [← mul_div_assoc, Finset.mul_sum]
    simp_rw [weighted_abs_posterior]
    rw [← Finset.sum_div]
    ring
  change (∑' y, mass (marginal law) y *
    ((∑ i : Spin, |posterior law y i-1/3|)/2)) = _
  simp_rw [ht]
  rw [tsum_div_const, Summable.tsum_finsetSum (fun i _ => mass_diff_summable (law i) (marginal law))]
  simp only [tvMass, ← Finset.sum_div]
  ring

lemma advantage_nonneg {α : Type*} (law : Spin → PMF α) : 0 ≤ advantage law := by
  rw [advantage_eq_tvMass]
  exact div_nonneg (Finset.sum_nonneg (fun i _ => tvMass_nonneg _ _)) (by norm_num)

lemma advantage_le_one {α : Type*} (law : Spin → PMF α) : advantage law ≤ 1 := by
  rw [advantage_eq_tvMass]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (i : Spin) _ => tvMass_le_one (law i) (marginal law))
  norm_num at h
  linarith

lemma kernel_mass_summable {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    Summable (fun a => mass p a*mass (k a) b) := by
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (mass_nonneg p a) (mass_nonneg (k a) b))
    (fun a => mul_le_of_le_one_right (mass_nonneg p a) (mass_le_one (k a) b))
    (mass_summable p)

lemma weighted_kernel_summable {α β : Type*} (p q : PMF α) (k : α → PMF β) (b : β) :
    Summable (fun a => |mass p a-mass q a| *mass (k a) b) := by
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (abs_nonneg _) (mass_nonneg (k a) b))
    (fun a => mul_le_of_le_one_right (abs_nonneg _) (mass_le_one (k a) b))
    (mass_diff_summable p q)

lemma mass_diff_bind_le {α β : Type*} (p q : PMF α) (k : α → PMF β) (b : β) :
    |mass (p.bind k) b-mass (q.bind k) b| ≤
      ∑' a, |mass p a-mass q a| *mass (k a) b := by
  rw [mass_bind, mass_bind, ← (kernel_mass_summable p k b).tsum_sub (kernel_mass_summable q k b)]
  simp_rw [← sub_mul]
  have hnorm : Summable (fun a => ‖(mass p a-mass q a)*mass (k a) b‖) :=
    (weighted_kernel_summable p q k b).congr (fun a => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg (k a) b)])
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg (k _) b)] using
    norm_tsum_le_tsum_norm hnorm

lemma tvMass_bind_le {α β : Type*} (p q : PMF α) (k : α → PMF β) :
    tvMass (p.bind k) (q.bind k) ≤ tvMass p q := by
  have hrow (a : α) : (∑' b, |mass p a-mass q a| *mass (k a) b) =
      |mass p a-mass q a| := by
    rw [(mass_summable (k a)).tsum_mul_left, mass_sum, mul_one]
  have hs : Summable (Function.uncurry (fun a b => |mass p a-mass q a| *mass (k a) b)) := by
    apply (summable_prod_of_nonneg (fun ab => mul_nonneg (abs_nonneg _) (mass_nonneg _ _))).mpr
    change (∀ a, Summable (fun b => |mass p a-mass q a| * mass (k a) b)) ∧
      Summable (fun a => ∑' b, |mass p a-mass q a| * mass (k a) b)
    constructor
    · intro a
      exact (mass_summable (k a)).mul_left |mass p a-mass q a|
    ·
      simpa only [hrow] using mass_diff_summable p q
  have h := Summable.tsum_le_tsum (mass_diff_bind_le p q k)
    (mass_diff_summable (p.bind k) (q.bind k)) hs.prod_symm.prod
  rw [hs.tsum_comm] at h
  simp_rw [hrow] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

lemma marginal_bind {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    marginal (fun i => (law i).bind k) = (marginal law).bind k := by
  simp only [marginal, PMF.bind_bind]

 
theorem advantage_bind_le {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    advantage (fun i => (law i).bind k) ≤ advantage law := by
  rw [advantage_eq_tvMass, advantage_eq_tvMass, marginal_bind]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => tvMass_bind_le (law i) (marginal law) k))
    (by norm_num)

end ThreeState

end OAI
