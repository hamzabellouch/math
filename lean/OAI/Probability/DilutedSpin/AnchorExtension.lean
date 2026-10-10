import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type} [Fintype Ω]

/-- A parameter-dependent old test can be differentiated without changing
any of the actual tree sampling kernels. -/
theorem hasDerivAt_protected_expect_varying {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (C : Finset (Leaf S)) {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ}
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u)
    (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G t x * Real.exp (-protectedLog S C (f t) x)))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => G' x * Real.exp (-protectedLog S C (f u) x)) +
       (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => (G u x * Real.exp (-protectedLog S C (f u) x)) *
          (vertexScore S T m (f u) f' x - protectedLog S C f' x))) u := by
  have hg := fun x => (hG x).mul ((hasDerivAt_protectedLog S C hf x).neg.exp)
  have hd := hasDerivAt_sampleLaw_tilt_expect S T m hm hroot hf hg
  apply hd.congr_deriv
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_congr
  intro x
  change G' x * Real.exp (-protectedLog S C (f u) x) +
    G u x * (Real.exp (-protectedLog S C (f u) x) * -protectedLog S C f' x) +
    G u x * Real.exp (-protectedLog S C (f u) x) * vertexScore S T m (f u) f' x = _
  ring

/-- The full cancellation calculus, with a moving test. Fresh branches are
sampled genuinely, not defined by their expectation. -/
theorem hasDerivAt_fullyProtected_varying {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ} (u : ℝ)
    (hu : ∀ y, 0 < 1+u*D y) (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => fullyProtected S T m D (G t) t)
      (fullyProtected S T m D G' u +
       ∑ v : Internal S, gamma S m v *
        fullyProtected (grow S v) T m D (fun x => G u (oldSample S v x) * D (newPath S v x)) u) u := by
  classical
  let f (t : ℝ) (y : FinitePath Ω n) := Real.log (1+t*D y)
  let DL (y : FinitePath Ω n) := D y / (1+u*D y)
  have hf (y : FinitePath Ω n) : HasDerivAt (fun t => f t y) (DL y) u :=
    hasDerivAt_log_affine (ne_of_gt (hu y))
  have hproto := hasDerivAt_protected_expect S T m hm hroot Finset.univ (G u) hf
  have hvar := hasDerivAt_protected_expect_varying S T m hm hroot Finset.univ hf hG
  have hfull := hasDerivAt_fullyProtected S T m hm hroot hend D (G u) u hu
  have heq (H : Sample Ω S → ℝ) (t : ℝ) :
      (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
        (fun x => H x * Real.exp (-protectedLog S Finset.univ (f t) x)) =
        fullyProtected S T m D H t := by
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    rfl
  simp_rw [heq] at hproto hvar
  have hconst := hproto.unique hfull
  rw [hconst] at hvar
  exact hvar

/-- Unused old positions are a finite family of genuine path projections.
In a canceled-anchor application these are all old leaves except the anchor.
Every already selected color is canceled. -/
noncomputable def anchorEval {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    {ι : Type} (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) (t : ℝ) : ℝ :=
  fullyProtected S T m D (fun x => G x * ∏ i ∈ A, (1+t*D (U i x))) t

theorem fullyProtected_sum {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    {ι : Type} (A : Finset ι) (G : ι → Sample Ω S → ℝ) (t : ℝ) :
    fullyProtected S T m D (fun x => ∑ i ∈ A, G i x) t =
      ∑ i ∈ A, fullyProtected S T m D (G i) t := by
  unfold fullyProtected
  simp only [Finset.sum_mul, FiniteLaw.expect_sum]

 
theorem hasDerivAt_anchorEval {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) (u : ℝ) (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (anchorEval S T m D A U G)
      ((∑ i ∈ A, anchorEval S T m D (A.erase i) U (fun x => G x * D (U i x)) u) +
       ∑ v : Internal S, gamma S m v * anchorEval (grow S v) T m D A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) u) u := by
  have hprod (x : Sample Ω S) :
      HasDerivAt (fun t : ℝ => G x * ∏ i ∈ A, (1+t*D (U i x)))
        (∑ i ∈ A, (G x * D (U i x)) * ∏ j ∈ A.erase i, (1+u*D (U j x))) u := by
    have hh := (HasDerivAt.fun_finsetProd (u := A) (fun i _ =>
      (((hasDerivAt_id u).mul_const (D (U i x))).const_add 1))).const_mul (G x)
    apply hh.congr_deriv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul, id_eq, one_mul]
    ring
  have hd := hasDerivAt_fullyProtected_varying S T m hm hroot hend D u hu hprod
  apply hd.congr_deriv
  rw [fullyProtected_sum]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro v _
    apply congrArg (gamma S m v * ·)
    apply FiniteLaw.expect_congr
    intro x
    change ((G (oldSample S v x) * ∏ i ∈ A, (1+u*D (U i (oldSample S v x)))) *
      D (newPath S v x)) * _ = _
    ring

/-- Ordered histories for all orders of the canceled-anchor expansion. The
state records precisely which OLD positions remain eligible. -/
noncomputable def anchorIterate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι] :
    ℕ → (S : PrescribedTree n) → (A : Finset ι) →
      (ι → Sample Ω S → FinitePath Ω n) → (Sample Ω S → ℝ) → ℝ → ℝ
  | 0, S, A, U, G, t => anchorEval S T m D A U G t
  | k+1, S, A, U, G, t =>
      (∑ i ∈ A, anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t) +
      ∑ v : Internal S, gamma S m v * anchorIterate T m D k (grow S v) A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) t

/-- Every derivative order of the actual finite-kernel canceled-anchor
expectation is the ordered old-or-fresh extension sum. -/
theorem hasDerivAt_anchorIterate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    (u : ℝ) (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (anchorIterate T m D k S A U G)
      (anchorIterate T m D (k+1) S A U G u) u := by
  induction k generalizing S A with
  | zero => exact hasDerivAt_anchorEval S T m hm hroot hend D A U G u hu
  | succ k ih =>
    have h₁ := HasDerivAt.sum (u := A) (fun i (_ : i ∈ A) =>
      ih S (A.erase i) U (fun x => G x * D (U i x)))
    have h₂ := HasDerivAt.sum (u := Finset.univ) (fun v (_ : v ∈ (Finset.univ : Finset (Internal S))) =>
      (ih (grow S v) A (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x))).const_mul (gamma S m v))
    apply (h₁.add h₂).congr_of_eventuallyEq
    filter_upwards [] with t
    simp only [Pi.add_apply, Finset.sum_apply]
    rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (P : FiniteLaw Ω) (m c : ℝ) :
    P.tilt m (fun _ => c) = P := by
  apply weights_ext
  intro x
  simp [tilt, expMoment, expect_const, Real.exp_ne_zero]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem leafSum_mono {n : ℕ} (S : PrescribedTree n) {f g : FinitePath Ω n → ℝ}
    (h : ∀ y, f y ≤ g y) (x : Sample Ω S) : leafSum S f x ≤ leafSum S g x := by
  simp only [leafSum_eq_sum]
  exact Finset.sum_le_sum (fun a _ => h _)

theorem fullyProtected_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) :
    fullyProtected S T m D G 0 = (sampleLaw S T).expect G := by
  simp [fullyProtected, KernelTower.tilt_const n T _ hm, leafSum_const]

theorem anchorEval_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) {ι : Type} (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) :
    anchorEval S T m D A U G 0 = (sampleLaw S T).expect G := by
  simp [anchorEval, fullyProtected_zero S T m hm]

omit [Fintype Ω] in
/-- The denominator in the protected tree rule is uniformly bounded on a
fixed real neighborhood of zero, independently of all kernels and depth. -/
theorem protected_density_bound {n : ℕ} (S : PrescribedTree n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {t : ℝ} (ht : |t| ≤ 1/2) (x : Sample Ω S) :
    Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x) ≤ (2:ℝ) ^ leaves S := by
  have hlow (y : FinitePath Ω n) : (1:ℝ)/2 ≤ 1+t*D y := by
    have ha : |t * D y| ≤ 1/2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)).trans (by simpa using ht)
    have := (abs_le.mp ha).1
    linarith
  have hh := leafSum_mono S (f := fun _ => -Real.log 2)
    (g := fun y => Real.log (1+t*D y)) (fun y => by
      have h := Real.strictMonoOn_log.monotoneOn (show (1:ℝ)/2 ∈ Set.Ioi 0 by norm_num)
        (show 1+t*D y ∈ Set.Ioi 0 by change 0 < 1+t*D y; linarith [hlow y]) (hlow y)
      simpa [Real.log_div] using h) x
  rw [leafSum_const] at hh
  calc
    Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x) ≤
        Real.exp ((leaves S : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = (2:ℝ) ^ leaves S := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]

theorem abs_fullyProtected_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (G : Sample Ω S → ℝ) {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (ht : |t| ≤ 1/2) : |fullyProtected S T m D G t| ≤ B * (2:ℝ) ^ leaves S := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (hG x) (protected_density_bound S D hD ht x) (Real.exp_pos _).le hB

theorem abs_anchorEval_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {ι : Type} (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (ht : |t| ≤ 1/2) : |anchorEval S T m D A U G t| ≤ B * (2:ℝ) ^ (leaves S + A.card) := by
  have hprod (x : Sample Ω S) : |∏ i ∈ A, (1+t*D (U i x))| ≤ (2:ℝ)^A.card := by
    rw [Finset.abs_prod]
    calc
      (∏ i ∈ A, |1+t*D (U i x)|) ≤ ∏ _i ∈ A, (2:ℝ) := Finset.prod_le_prod₀
        (fun i _ => abs_nonneg _) (fun i _ => by
          have hterm := abs_add_le (1:ℝ) (t*D (U i x))
          have ha := mul_le_mul_of_nonneg_left (hD (U i x)) (abs_nonneg t)
          rw [← abs_mul, mul_one] at ha
          simp only [abs_one] at hterm
          linarith)
      _ = (2:ℝ)^A.card := by simp
  have hh := abs_fullyProtected_le S T m D hD (fun x => G x * ∏ i ∈ A, (1+t*D (U i x)))
    (B := B * (2:ℝ)^A.card) (by positivity) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hG x) (hprod x) (abs_nonneg _) hB) ht
  simpa only [anchorEval, pow_add, mul_assoc, mul_comm, mul_left_comm] using hh

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

/-- A depth-independent bound on derivative order `k`; the total absolute
one-step extension coefficient is the count of eligible old positions plus
all sampled leaves. -/
noncomputable def derivativeBound : ℕ → ℕ → ℝ
  | q, 0 => (2:ℝ)^q
  | q, k+1 => (q:ℝ) * derivativeBound (q+1) k

theorem derivativeBound_nonneg (q k : ℕ) : 0 ≤ derivativeBound q k := by
  induction k generalizing q with
  | zero => exact pow_nonneg (by norm_num) _
  | succ k ih => exact mul_nonneg (Nat.cast_nonneg _) (ih _)

theorem derivativeBound_mono (k : ℕ) : Monotone (fun q => derivativeBound q k) := by
  induction k with
  | zero => exact fun a b hab => pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hab
  | succ k ih =>
    intro a b hab
    exact mul_le_mul (by exact_mod_cast hab) (ih (Nat.add_le_add_right hab 1))
      (derivativeBound_nonneg _ _) (Nat.cast_nonneg _)

variable {Ω : Type} [Fintype Ω]

/-- Uniform real control of the full OLD-or-FRESH derivative expansion.
No depth, number of kernel states, or base-disorder law enters the bound. -/
theorem abs_anchorIterate_le {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0 = 0)
    (hend : m (Fin.last n) = 1) (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {ι : Type} [DecidableEq ι] (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B) (ht : |t| ≤ 1/2) :
    |anchorIterate T m D k S A U G t| ≤ B * derivativeBound (leaves S + A.card) k := by
  induction k generalizing S A with
  | zero => exact abs_anchorEval_le S T m D hD A U G hB hG ht
  | succ k ih =>
    let q := leaves S + A.card
    let C := derivativeBound (q+1) k
    have hold (i : ι) :
        |anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t| ≤ B*C := by
      apply (ih S (A.erase i) U _ (fun x => by
        rw [abs_mul]
        exact (mul_le_mul (hG x) (hD _) (abs_nonneg _) hB).trans (by simp))).trans
      apply mul_le_mul_of_nonneg_left _ hB
      exact derivativeBound_mono k (by
        have hc := Finset.card_le_card (Finset.erase_subset i A)
        dsimp [q]
        omega)
    have hfresh (v : Internal S) :
        |anchorIterate T m D k (grow S v) A (fun i x => U i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x)) t| ≤ B*C := by
      have hh := ih (grow S v) A (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) (fun x => by
        rw [abs_mul]
        exact (mul_le_mul (hG _) (hD _) (abs_nonneg _) hB).trans (by simp))
      simpa only [C, q, leaves_grow, Nat.add_right_comm, Nat.add_assoc] using hh
    have h₁ : |∑ i ∈ A, anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t| ≤
        (A.card:ℝ)*(B*C) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ i ∈ A, |anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t|)
          ≤ ∑ _i ∈ A, B*C := Finset.sum_le_sum (fun i _ => hold i)
        _ = _ := by simp
    have h₂ : |∑ v : Internal S, gamma S m v * anchorIterate T m D k (grow S v) A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) t| ≤
        (leaves S:ℝ)*(B*C) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ v : Internal S, |gamma S m v * anchorIterate T m D k (grow S v) A
          (fun i x => U i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x)) t|)
          ≤ ∑ v : Internal S, |gamma S m v| * (B*C) := by
            apply Finset.sum_le_sum
            intro v _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hfresh v) (abs_nonneg _)
        _ = _ := by rw [← Finset.sum_mul, sum_abs_gamma S m hm hpos hroot hend]
    exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by
      dsimp [C, q, derivativeBound]
      push_cast
      ring)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

@[simp] theorem card_leaf {n : ℕ} (S : PrescribedTree n) : Fintype.card (Leaf S) = leaves S := by
  induction S with
  | leaf =>
    change Fintype.card Unit = 1
    exact Fintype.card_unit
  | @node n k C ih =>
    change Fintype.card ((i : Fin k) × Leaf (C i)) = leaves (.node k C)
    simp [Fintype.card_sigma, leaves, ih]

noncomputable instance leafDecidableEq {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) :=
  Classical.decEq _

variable {Ω : Type} [Fintype Ω]

theorem abs_freshEval_le {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (v : Internal S) (D : FinitePath Ω n → ℝ) {B : ℝ} (hD : ∀ y, |D y| ≤ B)
    (x : Sample Ω S) : |freshEval S T v D x| ≤ B := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact (KernelTower.law (n+1) T).abs_expect_le hD
    | some v => exact ih v.1 (T.2 (x v.1).1) v.2 _ (fun y => hD _) (x v.1).2

theorem abs_vertexScore_le {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (f D : FinitePath Ω n → ℝ) {B : ℝ} (hD : ∀ y, |D y| ≤ B)
    (x : Sample Ω S) : |vertexScore S T m f D x| ≤ 2 * (leaves S:ℝ) * B := by
  rw [vertexScore_decomposition, hend, one_mul]
  apply (abs_add_le _ _).trans
  have hleaf : |∑ a : Leaf S, D (pathAt S a x)| ≤ (leaves S:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ a : Leaf S, |D (pathAt S a x)|) ≤ ∑ _a : Leaf S, B :=
        Finset.sum_le_sum (fun a _ => hD _)
      _ = _ := by simp
  have hfresh : |∑ v : Internal S, gamma S m v *
      freshEval S (KernelTower.tilt n T (fun j => m j.succ) f) v D x| ≤ (leaves S:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ v : Internal S, |gamma S m v * freshEval S (KernelTower.tilt n T (fun j => m j.succ) f) v D x|)
        ≤ ∑ v : Internal S, |gamma S m v| * B := by
          apply Finset.sum_le_sum
          intro v _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_freshEval_le S _ v D hD x) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, sum_abs_gamma S m hm hpos hroot hend]
  linarith

omit [Fintype Ω] in
theorem exp_neg_leafSum_log {n : ℕ} (S : PrescribedTree n)
    (A : FinitePath Ω n → ℝ) (hA : ∀ y, 0 < A y) (x : Sample Ω S) :
    Real.exp (-leafSum S (fun y => Real.log (A y)) x) =
      (∏ a : Leaf S, A (pathAt S a x))⁻¹ := by
  rw [leafSum_eq_sum, Real.exp_neg, Real.exp_sum]
  congr 1
  exact Finset.prod_congr rfl (fun a _ => Real.exp_log (hA _))

/-- The actual anchor expectation in pert:palm-expression, with the prior
kernels updated by the new insertion. `G` includes the numerator score mark. -/
noncomputable def anchorInsertion {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (a : Leaf S)
    (G : Sample Ω S → ℝ) (A : FinitePath Ω n → ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (fun y => Real.log (A y)))).expect
    (fun x => G x / A (pathAt S a x))

/-- Links the proved ordered history derivative rule to the single canceled
anchor of the manuscript, not a different protected-leaf functional. -/
theorem anchorEval_eq_anchorInsertion {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    (a : Leaf S) (G : Sample Ω S → ℝ) (t : ℝ) (ht : ∀ y, 0 < 1+t*D y) :
    anchorEval S T m D (Finset.univ.erase a) (pathAt S) G t =
      anchorInsertion S T m a G (fun y => 1+t*D y) := by
  classical
  apply FiniteLaw.expect_congr
  intro x
  rw [exp_neg_leafSum_log S _ ht]
  have hp := Finset.mul_prod_erase (Finset.univ : Finset (Leaf S))
    (fun b => 1+t*D (pathAt S b x)) (Finset.mem_univ a)
  have hn : ∏ b ∈ (Finset.univ : Finset (Leaf S)).erase a, (1+t*D (pathAt S b x)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => ne_of_gt (ht _))
  rw [← hp]
  field_simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The derivative of a canceled-anchor insertion, retaining the actual tree
score and the correction from the canceled denominator. -/
noncomputable def anchorDerivative {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (a : Leaf S)
    (G : Sample Ω S → ℝ) (A E : FinitePath Ω n → ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (fun y => Real.log (A y)))).expect
    (fun x => G x / A (pathAt S a x) *
      (vertexScore S T m (fun y => Real.log (A y)) (fun y => E y / A y) x -
        E (pathAt S a x) / A (pathAt S a x)))

theorem hasDerivAt_anchorInsertion {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (a : Leaf S) (G : Sample Ω S → ℝ)
    {A : ℝ → FinitePath Ω n → ℝ} {E : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, HasDerivAt (fun t => A t y) (E y) u)
    (hp : ∀ y, 0 < A u y) :
    HasDerivAt (fun t => anchorInsertion S T m a G (A t))
      (anchorDerivative S T m a G (A u) E) u := by
  have hf (y : FinitePath Ω n) := (hA y).log (ne_of_gt (hp y))
  have hg (x : Sample Ω S) := (hasDerivAt_const u (G x)).div
    (hA (pathAt S a x)) (ne_of_gt (hp (pathAt S a x)))
  have hd := hasDerivAt_sampleLaw_tilt_expect S T m hm hroot hf hg
  apply hd.congr_deriv
  apply FiniteLaw.expect_congr
  intro x
  change (0 * A u (pathAt S a x) - G x * E (pathAt S a x)) / A u (pathAt S a x)^2 +
    G x / A u (pathAt S a x) * vertexScore S T m (fun y => Real.log (A u y))
      (fun y => E y / A u y) x = _
  ring

private theorem abs_div_bound {x y B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B)
    (hy : (1:ℝ)/2 ≤ y) : |x/y| ≤ 2*B := by
  have hyp : 0 < y := by linarith
  rw [abs_div, abs_of_pos hyp, div_le_iff₀ hyp]
  nlinarith

/-- Uniform bound in the auxiliary `u` direction. It uses only probability
normalization and the telescoping absolute tree coefficients. -/
theorem abs_anchorDerivative_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0 = 0)
    (hend : m (Fin.last n) = 1) (a : Leaf S) (G : Sample Ω S → ℝ)
    (A E : FinitePath Ω n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ x, |G x| ≤ B) (hA : ∀ y, (1:ℝ)/2 ≤ A y) (hE : ∀ y, |E y| ≤ 1) :
    |anchorDerivative S T m a G A E| ≤ (4+8*(leaves S:ℝ))*B := by
  have hEA (y : FinitePath Ω n) : |E y / A y| ≤ 2 := by
    simpa using abs_div_bound (by norm_num : (0:ℝ)≤1) (hE y) (hA y)
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul]
  have hs := abs_vertexScore_le S T m hm hpos hroot hend (fun y => Real.log (A y))
    (fun y => E y/A y) hEA x
  have hdiff := (abs_sub _ _).trans (add_le_add hs (hEA (pathAt S a x)))
  have hG' := abs_div_bound hB (hG x) (hA (pathAt S a x))
  apply (mul_le_mul hG' hdiff (abs_nonneg _) (by positivity)).trans_eq
  ring

omit [Fintype Ω] in
private theorem affine_two_lower_half {n : ℕ} (D E : FinitePath Ω n → ℝ)
    (hD : ∀ y, |D y| ≤ 1) (hE : ∀ y, |E y| ≤ 1) {t u : ℝ}
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω n) :
    (1:ℝ)/2 ≤ 1+t*D y+u*E y := by
  have ht' : |t*D y| ≤ 1/4 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)).trans (by simpa using ht)
  have hu' : |u*E y| ≤ 1/4 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hE y) (abs_nonneg u)).trans (by simpa using hu)
  linarith [(abs_le.mp ht').1, (abs_le.mp hu').1]

/-- The `u`-error in pert:analytic is uniformly linear, before any root
averaging. No analyticity or enlargement of computational limits is needed. -/
theorem anchorInsertion_sub_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (a : Leaf S) (G : Sample Ω S → ℝ) (D E : FinitePath Ω n → ℝ)
    {B t u : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (hD : ∀ y, |D y| ≤ 1) (hE : ∀ y, |E y| ≤ 1)
    (ht : |t| ≤ 1/4) (huz : 0 ≤ u) (hu : u ≤ 1/4) :
    |anchorInsertion S T m a G (fun y => 1+t*D y+u*E y) -
      anchorInsertion S T m a G (fun y => 1+t*D y)| ≤ (4+8*(leaves S:ℝ))*B*u := by
  let F (v : ℝ) := anchorInsertion S T m a G (fun y => 1+t*D y+v*E y)
  let F' (v : ℝ) := anchorDerivative S T m a G (fun y => 1+t*D y+v*E y) E
  have hlow (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) u) (y : FinitePath Ω n) :
      (1:ℝ)/2 ≤ 1+t*D y+v*E y :=
    affine_two_lower_half D E hD hE ht (by rw [abs_of_nonneg hv.1]; exact hv.2.trans hu) y
  have hd (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) u) : HasDerivAt F (F' v) v := by
    apply hasDerivAt_anchorInsertion S T m hm hroot a G
    · intro y
      simpa using ((hasDerivAt_id v).mul_const (E y)).const_add (1+t*D y)
    · intro y
      linarith [hlow v hv y]
  have hb (v : ℝ) (hv : v ∈ Set.Ico (0:ℝ) u) : ‖F' v‖ ≤ (4+8*(leaves S:ℝ))*B := by
    rw [Real.norm_eq_abs]
    exact abs_anchorDerivative_le S T m hmono hpos hroot hend a G _ E hB hG
      (hlow v ⟨hv.1,hv.2.le⟩) hE
  have hx := norm_image_sub_le_of_norm_deriv_le_segment' (fun v hv => (hd v hv).hasDerivWithinAt)
    hb u (show u ∈ Set.Icc (0:ℝ) u from ⟨huz,le_rfl⟩)
  simpa only [F, zero_mul, add_zero, sub_zero, Real.norm_eq_abs] using hx

end DilutedSpinGlass.PrescribedTree

open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

/-- Identifies an explicitly constructed differential jet with Mathlib's
iterated derivatives, without any analytic or compactness assumption. -/
theorem jet_iteratedDerivWithin {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s)
    (hF : ∀ k x, x ∈ s → HasDerivAt (F k) (F (k+1) x) x)
    (k : ℕ) : EqOn (iteratedDerivWithin k (F 0) s) (F k) s := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hx)]
    exact (hF k x hx).hasDerivWithinAt.derivWithin (hs x hx)

theorem jet_contDiffOn {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s)
    (hF : ∀ k x, x ∈ s → HasDerivAt (F k) (F (k+1) x) x)
    (k : ℕ) : ContDiffOn ℝ k (F 0) s := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs).mpr
  have hd (j : ℕ) : DifferentiableOn ℝ (F j) s :=
    fun x hx => (hF j x hx).differentiableAt.differentiableWithinAt
  constructor
  · intro j _
    exact (hd j).continuousOn.congr (jet_iteratedDerivWithin hs hF j)
  · intro j _
    exact (hd j).congr (jet_iteratedDerivWithin hs hF j)

/-- Uniform finite Taylor remainder for the explicit jet used in the
canceled-anchor identities. Only a bound on the required derivative enters. -/
theorem jet_taylor_bound {F : ℕ → ℝ → ℝ} {a b t C : ℝ} (hab : a < b)
    (hF : ∀ k x, x ∈ Icc a b → HasDerivAt (F k) (F (k+1) x) x)
    (k : ℕ) (ht : t ∈ Icc a b)
    (hC : ∀ x ∈ Icc a b, |F (k+1) x| ≤ C) :
    |F 0 t - ∑ j ∈ Finset.range (k+1), F j a / (j.factorial:ℝ) * (t-a)^j| ≤
      C * (t-a)^(k+1) / (k.factorial:ℝ) := by
  have hs := uniqueDiffOn_Icc hab
  have hbound := taylor_mean_remainder_bound hab.le (jet_contDiffOn hs hF (k+1)) ht
    (by
      intro x hx
      rw [Real.norm_eq_abs, jet_iteratedDerivWithin hs hF (k+1) hx]
      exact hC x hx)
  rw [taylor_within_apply] at hbound
  simp only [Real.norm_eq_abs] at hbound
  convert hbound using 2
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [jet_iteratedDerivWithin hs hF j (left_mem_Icc.mpr hab.le)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The literal ordered-history Taylor coefficient of the single anchor.
Only the anchor is initially protected. -/
noncomputable def anchorCoefficient {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    (a : Leaf S) (G : Sample Ω S → ℝ) (k : ℕ) : ℝ :=
  anchorIterate T m D k S (Finset.univ.erase a) (pathAt S) G 0 / (k.factorial:ℝ)

/-- Quantitative real Taylor expansion of the actual canceled-anchor
insertion. This is uniform in every probability kernel and can therefore
be root-averaged before selecting any subsequence. -/
theorem anchorInsertion_taylor_bound {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (a : Leaf S) (G : Sample Ω S → ℝ) {B t : ℝ}
    (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) (k : ℕ) :
    |anchorInsertion S T m a G (fun y => 1+t*D y) -
      ∑ j ∈ Finset.range (k+1), anchorCoefficient S T m D a G j * t^j| ≤
        (B * derivativeBound (leaves S + (Finset.univ.erase a).card) (k+1) /
          (k.factorial:ℝ)) * t^(k+1) := by
  let F (j : ℕ) := anchorIterate T m D j S (Finset.univ.erase a) (pathAt S) G
  have hd (j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) :
      HasDerivAt (F j) (F (j+1) x) x := by
    apply hasDerivAt_anchorIterate T m hm hroot hend D j S _ _ _
    intro y
    have hx' : |x| ≤ 1/2 := by simpa only [abs_of_nonneg hx.1] using hx.2
    have hh := mul_le_mul_of_nonneg_left (hD y) (abs_nonneg x)
    rw [← abs_mul, mul_one] at hh
    have := (abs_le.mp (hh.trans hx')).1
    linarith
  have hb (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) :
      |F (k+1) x| ≤ B*derivativeBound (leaves S+(Finset.univ.erase a).card) (k+1) := by
    apply abs_anchorIterate_le T m hmono hpos hroot hend D hD (k+1) S _ _ _ hB hG
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hr := jet_taylor_bound (by norm_num : (0:ℝ)<1/2) hd k ht hb
  have ha : F 0 t = anchorInsertion S T m a G (fun y => 1+t*D y) := by
    apply anchorEval_eq_anchorInsertion
    intro y
    have hh := mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)
    rw [← abs_mul, mul_one, abs_of_nonneg ht.1] at hh
    have := (abs_le.mp (hh.trans ht.2)).1
    linarith
  rw [ha] at hr
  simpa only [F, anchorCoefficient, sub_zero, div_mul_eq_mul_div] using hr

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ : Type}

def sampleFst : {n : ℕ} → (S : PrescribedTree n) → Sample (Ω × Λ) S → Sample Ω S
  | 0, .leaf, _ => ()
  | _+1, .node _ C, x => fun i => ((x i).1.1, sampleFst (C i) (x i).2)

def sampleSnd : {n : ℕ} → (S : PrescribedTree n) → Sample (Ω × Λ) S → Sample Λ S
  | 0, .leaf, _ => ()
  | _+1, .node _ C, x => fun i => ((x i).1.2, sampleSnd (C i) (x i).2)

def samplePair : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S → Sample Λ S → Sample (Ω × Λ) S
  | 0, .leaf, _, _ => ()
  | _+1, .node _ C, x, y => fun i => (((x i).1,(y i).1), samplePair (C i) (x i).2 (y i).2)

@[simp] lemma sampleFst_pair {n : ℕ} (S : PrescribedTree n) (x : Sample Ω S) (y : Sample Λ S) :
    sampleFst S (samplePair S x y) = x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change ((x i).1, sampleFst (C i) (samplePair (C i) (x i).2 (y i).2)) = x i
    rw [ih]

@[simp] lemma sampleSnd_pair {n : ℕ} (S : PrescribedTree n) (x : Sample Ω S) (y : Sample Λ S) :
    sampleSnd S (samplePair S x y) = y := by
  induction S with
  | leaf => change () = y; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change ((y i).1, sampleSnd (C i) (samplePair (C i) (x i).2 (y i).2)) = y i
    rw [ih]

@[simp] lemma samplePair_projections {n : ℕ} (S : PrescribedTree n) (x : Sample (Ω × Λ) S) :
    samplePair S (sampleFst S x) (sampleSnd S x) = x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change (((x i).1.1,(x i).1.2), samplePair (C i) (sampleFst (C i) (x i).2)
      (sampleSnd (C i) (x i).2)) = x i
    rw [ih]

def sampleProdEquiv {n : ℕ} (S : PrescribedTree n) : Sample (Ω × Λ) S ≃ Sample Ω S × Sample Λ S where
  toFun x := (sampleFst S x, sampleSnd S x)
  invFun x := samplePair S x.1 x.2
  left_inv := samplePair_projections S
  right_inv x := by simp

@[simp] lemma pathAt_sampleFst {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (x : Sample (Ω × Λ) S) : S.pathAt a (sampleFst S x) = KernelTower.pathFst n (S.pathAt a x) := by
  induction S with
  | leaf => rfl
  | node k C ih => exact congrArg (Prod.mk _) (ih a.1 a.2 (x a.1).2)

@[simp] lemma pathAt_sampleSnd {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (x : Sample (Ω × Λ) S) : S.pathAt a (sampleSnd S x) = KernelTower.pathSnd n (S.pathAt a x) := by
  induction S with
  | leaf => rfl
  | node k C ih => exact congrArg (Prod.mk _) (ih a.1 a.2 (x a.1).2)

variable [Fintype Ω] [Fintype Λ]

lemma sampleLaw_prod_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (U : KernelTower Λ n) (x : Sample (Ω × Λ) S) :
    (S.sampleLaw (KernelTower.prod n T U)).weight x =
      (S.sampleLaw T).weight (sampleFst S x) * (S.sampleLaw U).weight (sampleSnd S x) := by
  induction S with
  | leaf => simp [sampleLaw,KernelTower.unitLaw]
  | @node n k C ih =>
    change (∏ i, (T.1.weight (x i).1.1 * U.1.weight (x i).1.2) *
        ((C i).sampleLaw (KernelTower.prod n (T.2 (x i).1.1) (U.2 (x i).1.2))).weight (x i).2) =
      (∏ i, T.1.weight (x i).1.1 * ((C i).sampleLaw (T.2 (x i).1.1)).weight (sampleFst (C i) (x i).2)) *
      (∏ i, U.1.weight (x i).1.2 * ((C i).sampleLaw (U.2 (x i).1.2)).weight (sampleSnd (C i) (x i).2))
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [ih]
    ring

/-- Fresh mark samples are genuinely independent of every old physical/mark
sample in a prescribed tree, not merely of a single replica. -/
lemma sampleExpect_prod {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (U : KernelTower Λ n) (f : Sample (Ω × Λ) S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T U)).expect f =
      (S.sampleLaw T).expect (fun x => (S.sampleLaw U).expect (fun y => f (samplePair S x y))) := by
  unfold FiniteLaw.expect
  rw [show (∑ x, (S.sampleLaw (KernelTower.prod n T U)).weight x * f x) =
      ∑ z : Sample Ω S × Sample Λ S,
        (S.sampleLaw T).weight z.1 * (S.sampleLaw U).weight z.2 * f (samplePair S z.1 z.2) from
    Fintype.sum_equiv (sampleProdEquiv S) _ _ (fun x => by
      simp only [sampleProdEquiv,Equiv.coe_fn_mk,samplePair_projections,sampleLaw_prod_weight])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma expect_prod_separated {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (U : KernelTower Λ n)
    (f : Sample Ω S → ℝ) (g : Sample Λ S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T U)).expect
      (fun x => f (sampleFst S x) * g (sampleSnd S x)) =
        (S.sampleLaw T).expect f * (S.sampleLaw U).expect g := by
  rw [sampleExpect_prod]
  simp only [sampleFst_pair,sampleSnd_pair,FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_right]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
