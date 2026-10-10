import OAI.Probability.FreeIsing.Estimates.FiniteCavity
import OAI.Probability.FreeIsing.Estimates.InhomogeneousSpinChain

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePathGibbs

def rawKernel (beta : ℝ) (h : ℕ → ℝ) (i : ℕ) (a b : IsingSpin) : ℝ :=
  Real.exp ((h i + beta * spinSign a) * spinSign b)

theorem rawKernel_pos (beta : ℝ) (h : ℕ → ℝ) (i : ℕ) (a b : IsingSpin) :
    0 < rawKernel beta h i a b := Real.exp_pos _

def tailPartition (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) : ℝ :=
  ∑ x : Fin n → IsingSpin, InhomogeneousChain.weight (rawKernel beta h) n a x

@[simp] theorem tailPartition_zero (beta : ℝ) (h : ℕ → ℝ) (a : IsingSpin) :
    tailPartition beta h 0 a = 1 := by
  simp [tailPartition]

theorem tailPartition_pos (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    0 < tailPartition beta h n a := by
  let : Nonempty (Fin n → IsingSpin) := ⟨fun _ => .pos⟩
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro x _
  rw [InhomogeneousChain.weight_eq_prod]
  exact Finset.prod_pos fun i _ => rawKernel_pos beta h i _ _

theorem tailPartition_succ (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    tailPartition beta h (n + 1) a =
      ∑ b, rawKernel beta h 0 a b *
        tailPartition beta (fun i => h (i + 1)) n b := by
  unfold tailPartition
  rw [FiniteChain.sum_cons]
  simp only [InhomogeneousChain.weight_cons, ← Finset.mul_sum]
  rfl

def backwardField (beta : ℝ) (h : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, 0 => h 0 +
      (Real.log (tailPartition beta (fun i => h (i + 1)) n .pos) -
        Real.log (tailPartition beta (fun i => h (i + 1)) n .neg)) / 2
  | n + 1, i + 1 => backwardField beta (fun j => h (j + 1)) n i

theorem normalize_binary (w : IsingSpin → ℝ) (hw : ∀ a, 0 < w a) (b : IsingSpin) :
    w b / (∑ a, w a) =
      (1 + spinSign b * Real.tanh
        ((Real.log (w .pos) - Real.log (w .neg)) / 2)) / 2 := by
  rw [← binary_mean_eq_tanh_half_log (hw .pos) (hw .neg), sum_isingSpin]
  have hsum : w .pos + w .neg ≠ 0 := (add_pos (hw .pos) (hw .neg)).ne'
  have hsum' : w .neg + w .pos ≠ 0 := (add_pos (hw .neg) (hw .pos)).ne'
  cases b <;> simp only [spinSign_neg, spinSign_pos] <;>
    field_simp [hsum, hsum'] <;> ring

theorem normalized_head (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a b : IsingSpin) :
    rawKernel beta h 0 a b * tailPartition beta (fun i => h (i + 1)) n b /
      tailPartition beta h (n + 1) a =
    PosteriorChain.transition beta (backwardField beta h (n + 1) 0) a b := by
  let w : IsingSpin → ℝ := fun b =>
    rawKernel beta h 0 a b * tailPartition beta (fun i => h (i + 1)) n b
  have hw : ∀ b, 0 < w b := fun b =>
    mul_pos (rawKernel_pos beta h 0 a b)
      (tailPartition_pos beta (fun i => h (i + 1)) n b)
  rw [tailPartition_succ]
  change w b / (∑ s, w s) = _
  rw [normalize_binary w hw]
  have hlog : (Real.log (w .pos) - Real.log (w .neg)) / 2 =
      backwardField beta h (n + 1) 0 + beta * spinSign a := by
    dsimp [w, rawKernel, backwardField]
    rw [Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_exp, Real.log_exp]
    ring
  rw [hlog]
  rfl

theorem normalized_path (beta : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (a : IsingSpin) (x : Fin n → IsingSpin) :
    InhomogeneousChain.weight
      (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n a x =
    InhomogeneousChain.weight (rawKernel beta h) n a x / tailPartition beta h n a := by
  induction n generalizing h a with
  | zero => simp
  | succ n ih =>
    rw [InhomogeneousChain.weight, InhomogeneousChain.weight]
    change PosteriorChain.transition beta (backwardField beta h (n + 1) 0) a (x 0) *
      InhomogeneousChain.weight
        (fun i => PosteriorChain.transition beta
          (backwardField beta (fun j => h (j + 1)) n i)) n (x 0) (Fin.tail x) = _
    rw [ih, ← normalized_head]
    have ht := (tailPartition_pos beta (fun i => h (i + 1)) n (x 0)).ne'
    have ht' := (tailPartition_pos beta h (n + 1) a).ne'
    change (rawKernel beta h 0 a (x 0) *
        tailPartition beta (fun i => h (i + 1)) n (x 0) /
        tailPartition beta h (n + 1) a) *
      (InhomogeneousChain.weight (rawKernel beta (fun i => h (i + 1))) n
        (x 0) (Fin.tail x) / tailPartition beta (fun i => h (i + 1)) n (x 0)) = _
    field_simp [ht, ht']
    rfl

theorem half_log_transmitted (beta : ℝ) (w : IsingSpin → ℝ)
    (hw : ∀ a, 0 < w a) :
    (Real.log (∑ b, Real.exp (beta * spinSign b) * w b) -
      Real.log (∑ b, Real.exp (-beta * spinSign b) * w b)) / 2 =
    cavityMessage (Real.tanh beta)
      ((Real.log (w .pos) - Real.log (w .neg)) / 2) := by
  have hwp := hw .pos
  have hwn := hw .neg
  have hp : 0 < ∑ b, Real.exp (beta * spinSign b) * w b := by
    rw [sum_isingSpin]
    positivity
  have hm : 0 < ∑ b, Real.exp (-beta * spinSign b) * w b := by
    rw [sum_isingSpin]
    positivity
  apply Real.tanh_injective
  rw [← binary_mean_eq_tanh_half_log hp hm,
    cavityMessage, Real.tanh_artanh
      (cavityMessage_argument_mem (Real.tanh_sq_lt_one beta).le _),
    ← binary_mean_eq_tanh_half_log (hw .pos) (hw .neg), Real.tanh_eq beta]
  simp only [sum_isingSpin, spinSign_neg, spinSign_pos, mul_neg_one, mul_one, neg_neg]
  have hsum : Real.exp beta + Real.exp (-beta) ≠ 0 := by positivity
  have hwSum : w .pos + w .neg ≠ 0 := (add_pos (hw .pos) (hw .neg)).ne'
  have hden : Real.exp (-beta) * w .neg + Real.exp beta * w .pos +
      (Real.exp beta * w .neg + Real.exp (-beta) * w .pos) ≠ 0 := by positivity
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hden (mul_ne_zero hsum hwSum)).2
  ring

theorem tailPartition_half_log (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    (Real.log (tailPartition beta h (n + 1) .pos) -
      Real.log (tailPartition beta h (n + 1) .neg)) / 2 =
    cavityMessage (Real.tanh beta) (backwardField beta h (n + 1) 0) := by
  let w : IsingSpin → ℝ := fun b =>
    Real.exp (h 0 * spinSign b) *
      tailPartition beta (fun i => h (i + 1)) n b
  have hw : ∀ b, 0 < w b := fun b =>
    mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _)
  have heq (a : IsingSpin) : tailPartition beta h (n + 1) a =
      ∑ b, Real.exp (beta * spinSign a * spinSign b) * w b := by
    rw [tailPartition_succ]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [rawKernel, w]
    rw [add_mul, Real.exp_add]
    ring
  rw [heq .pos, heq .neg]
  simp only [spinSign_pos, spinSign_neg, mul_one, mul_neg_one]
  rw [half_log_transmitted beta w hw]
  congr 1
  dsimp [w, backwardField]
  rw [Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
    Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
    Real.log_exp, Real.log_exp]
  ring

theorem backwardField_cavity (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    backwardField beta h (n + 2) 0 = h 0 +
      cavityMessage (Real.tanh beta)
        (backwardField beta (fun i => h (i + 1)) (n + 1) 0) := by
  change h 0 + (Real.log (tailPartition beta (fun i => h (i + 1)) (n + 1) .pos) -
    Real.log (tailPartition beta (fun i => h (i + 1)) (n + 1) .neg)) / 2 = _
  rw [tailPartition_half_log]

def partition (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a, Real.exp (root * spinSign a) * tailPartition beta h n a

theorem partition_pos (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    0 < partition beta root h n := by
  rw [partition, sum_isingSpin]
  exact add_pos (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))
    (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))

def rootLaw (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) : ℝ :=
  Real.exp (root * spinSign a) * tailPartition beta h n a / partition beta root h n

theorem rootLaw_pos (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    0 < rootLaw beta root h n a :=
  div_pos (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))
    (partition_pos _ _ _ _)

@[simp] theorem sum_rootLaw (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    ∑ a, rootLaw beta root h n a = 1 := by
  simp only [rootLaw, ← Finset.sum_div]
  exact div_self (partition_pos beta root h n).ne'

def mass (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) : ℝ :=
  InhomogeneousChain.jointWeight (rawKernel beta h)
    (fun a => Real.exp (root * spinSign a)) n x / partition beta root h n

theorem mass_eq_jointWeight (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) :
    mass beta root h n x =
    InhomogeneousChain.jointWeight
      (fun i => PosteriorChain.transition beta (backwardField beta h n i))
      (rootLaw beta root h n) n x := by
  obtain ⟨a, x, rfl⟩ := Fin.exists_cons x
  rw [mass, InhomogeneousChain.jointWeight_cons,
    InhomogeneousChain.jointWeight_cons, normalized_path]
  unfold rootLaw
  field_simp [(partition_pos beta root h n).ne', (tailPartition_pos beta h n a).ne']

def energy (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) : ℝ :=
  root * spinSign (x 0) + ∑ i : Fin n,
    (h i + beta * spinSign (x i.castSucc)) * spinSign (x i.succ)

theorem mass_eq_exp_energy (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) :
    mass beta root h n x = Real.exp (energy beta root h n x) /
      partition beta root h n := by
  simp only [mass, InhomogeneousChain.jointWeight, rawKernel,
    energy, Real.exp_add, Real.exp_sum]

theorem mass_nonneg (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) : 0 ≤ mass beta root h n x := by
  rw [mass_eq_exp_energy]
  exact (div_pos (Real.exp_pos _) (partition_pos _ _ _ _)).le

@[simp] theorem sum_mass (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    ∑ x, mass beta root h n x = 1 := by
  simp_rw [mass_eq_jointWeight]
  exact InhomogeneousChain.sum_jointWeight _ _
    (fun i => PosteriorChain.transition_sum beta (backwardField beta h n i))
    (sum_rootLaw beta root h n) n

theorem partition_eq_sum_exp (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    partition beta root h n =
      ∑ x : Fin (n + 1) → IsingSpin, Real.exp (energy beta root h n x) := by
  have hm := sum_mass beta root h n
  simp_rw [mass_eq_exp_energy] at hm
  rw [← Finset.sum_div, div_eq_one_iff_eq (partition_pos beta root h n).ne'] at hm
  exact hm.symm

def mean (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) : ℝ :=
  ∑ x, mass beta root h n x * f x

theorem mean_endpoints (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f g : IsingSpin → ℝ) :
    mean beta root h n (fun x => f (x 0) * g (x (Fin.last n))) =
      ∑ a, rootLaw beta root h n a * f a *
        InhomogeneousChain.expectation
          (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n g a := by
  unfold mean
  simp_rw [mass_eq_jointWeight, ← mul_assoc]
  exact InhomogeneousChain.sum_jointWeight_endpoints _ _ _ _ _

theorem mean_first (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x 0)) =
      ∑ a, rootLaw beta root h n a * spinSign a := by
  have hm := mean_endpoints beta root h n spinSign (fun _ => 1)
  simp only [mul_one, InhomogeneousChain.expectation] at hm
  simp only [InhomogeneousChain.sum_weight _
    (fun i => PosteriorChain.transition_sum beta (backwardField beta h n i)), mul_one] at hm
  exact hm

theorem mean_last (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x (Fin.last n))) =
      ∑ a, rootLaw beta root h n a *
        InhomogeneousChain.expectation
          (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n spinSign a := by
  simpa only [one_mul, mul_one] using
    mean_endpoints beta root h n (fun _ => 1) spinSign

def endpointCovariance (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  mean beta root h n (fun x => spinSign (x 0) * spinSign (x (Fin.last n))) -
    mean beta root h n (fun x => spinSign (x 0)) *
      mean beta root h n (fun x => spinSign (x (Fin.last n)))

theorem endpointCovariance_eq (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    endpointCovariance beta root h n =
      (1 - mean beta root h n (fun x => spinSign (x 0)) ^ 2) * Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta) (backwardField beta h n i)) := by
  unfold endpointCovariance
  rw [mean_endpoints, mean_first, mean_last]
  exact PosteriorChain.covariance_eq_response_product beta (backwardField beta h n)
    (rootLaw beta root h n) (sum_rootLaw beta root h n) n

def rootField (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  root + (Real.log (tailPartition beta h n .pos) -
    Real.log (tailPartition beta h n .neg)) / 2

@[simp] theorem rootField_zero (beta root : ℝ) (h : ℕ → ℝ) :
    rootField beta root h 0 = root := by
  simp [rootField]

theorem rootField_succ (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    rootField beta root h (n + 1) = root +
      cavityMessage (Real.tanh beta) (backwardField beta h (n + 1) 0) := by
  rw [rootField, tailPartition_half_log]

theorem rootLaw_eq_tanh (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    rootLaw beta root h n a =
      (1 + spinSign a * Real.tanh (rootField beta root h n)) / 2 := by
  let w : IsingSpin → ℝ := fun a =>
    Real.exp (root * spinSign a) * tailPartition beta h n a
  have hw : ∀ a, 0 < w a := fun a =>
    mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _)
  change w a / (∑ b, w b) = _
  rw [normalize_binary w hw]
  have hlog : (Real.log (w .pos) - Real.log (w .neg)) / 2 =
      rootField beta root h n := by
    dsimp [w, rootField]
    rw [Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_exp, Real.log_exp]
    ring
  rw [hlog]

theorem mean_first_eq_tanh (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x 0)) =
      Real.tanh (rootField beta root h n) := by
  rw [mean_first, sum_isingSpin, rootLaw_eq_tanh, rootLaw_eq_tanh]
  simp only [spinSign_neg, spinSign_pos]
  ring

theorem artanh_mean_first (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    Real.artanh (mean beta root h n (fun x => spinSign (x 0))) =
      rootField beta root h n := by
  rw [mean_first_eq_tanh, Real.artanh_tanh]

theorem rootField_sub_bound {beta : ℝ} (hbeta : 0 ≤ beta)
    (root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    |rootField beta root h n - root| ≤ beta := by
  cases n with
  | zero => simpa using hbeta
  | succ n =>
    rw [rootField_succ, add_sub_cancel_left]
    exact abs_cavityMessage_tanh_le hbeta _

theorem artanh_mean_first_sub_bound {beta : ℝ} (hbeta : 0 ≤ beta)
    (root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    |Real.artanh (mean beta root h n (fun x => spinSign (x 0))) - root| ≤ beta := by
  rw [artanh_mean_first]
  exact rootField_sub_bound hbeta root h n

theorem endpointCovariance_mem_Icc {beta : ℝ} (hbeta : 0 ≤ beta)
    (root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    endpointCovariance beta root h n ∈ Set.Icc 0 (Real.tanh beta ^ n) := by
  unfold endpointCovariance
  rw [mean_endpoints, mean_first, mean_last]
  exact PosteriorChain.covariance_mem_Icc hbeta (backwardField beta h n)
    (rootLaw beta root h n) (fun a => (rootLaw_pos beta root h n a).le)
    (sum_rootLaw beta root h n) n

end Problem367.FinitePathGibbs

end

end OAI
