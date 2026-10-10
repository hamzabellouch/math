import OAI.NumberTheory.JointDickman.Arithmetic.PrimeResidueChannel
import OAI.NumberTheory.JointDickman.Probability.CoarseChannel

namespace OAI

/-!
# Coarse approximation of the actual fair-prime channel

Normalized high-exclusive cell probabilities are compared directly with
bounded Lipschitz profiles. Their product yields the smooth mixture kernel;
the actual two-split comparison and the low-union estimate then transfer
the coarse approximation to the original fair-prime channel.
-/

namespace JointDickman

open scoped BigOperators NNReal

/-- The approximating factors are bounded; the actual factors acquire
their bounds from the local errors. -/
theorem product_error_of_bounded_profile {a b u v M η : ℝ}
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hu : |u| ≤ M) (hv : |v| ≤ M)
    (ha : |a - u| ≤ η) (hb : |b - v| ≤ η) :
    |a * b - u * v| ≤ 2 * M * η + η ^ 2 := by
  have hbabs : |b| ≤ M + η := by
    calc
      |b| = |v + (b - v)| := by congr 1; ring
      _ ≤ |v| + |b - v| := abs_add_le _ _
      _ ≤ M + η := add_le_add hv hb
  calc
    |a * b - u * v| = |(a - u) * b + u * (b - v)| := by congr 1; ring
    _ ≤ |(a - u) * b| + |u * (b - v)| := abs_add_le _ _
    _ = |a - u| * |b| + |u| * |b - v| := by rw [abs_mul, abs_mul]
    _ ≤ η * (M + η) + M * η := add_le_add
      (mul_le_mul ha hbabs (abs_nonneg _) hη)
      (mul_le_mul hu hb (abs_nonneg _) hM)
    _ = _ := by ring

/-- Dividing the cell probabilities before taking their product gives
exactly the normalized exclusive-product kernel. -/
theorem exclusiveProductKernel_eq_normalized {C D R : Type*} [Fintype C]
    (w : C → ℝ) (p : C → D × R → ℝ) {m : ℝ} (hm : m ≠ 0) (a b : D × R) :
    exclusiveProductKernel w (fun _ => m) p a b =
      ∑ c, w c * (p c a / m) * (p c b / m) := by
  unfold exclusiveProductKernel
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  field_simp

/-- The smooth mixture follows from the normalized cellwise local law;
no kernel-approximation premise is needed. -/
theorem exclusiveProductKernel_smooth_error {C D R : Type*} [Fintype C]
    (w : C → ℝ) (p : C → D × R → ℝ) (f : C → ℝ → ℝ)
    (location : D × R → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {m M η : ℝ} (hm : m ≠ 0) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hf : ∀ c x, |f c x| ≤ M)
    (hlocal : ∀ c a, |p c a / m - f c (location a)| ≤ η) (a b : D × R) :
    |exclusiveProductKernel w (fun _ => m) p a b - smoothMixtureKernel w f location a b| ≤
      2 * M * η + η ^ 2 := by
  rw [exclusiveProductKernel_eq_normalized w p hm]
  unfold smoothMixtureKernel
  calc
    _ = |∑ c, w c * ((p c a / m) * (p c b / m) - f c (location a) * f c (location b))| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c, |w c * ((p c a / m) * (p c b / m) - f c (location a) * f c (location b))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, w c * |(p c a / m) * (p c b / m) - f c (location a) * f c (location b)| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ c, w c * (2 * M * η + η ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (product_error_of_bounded_profile hM hη (hf c _) (hf c _)
          (hlocal c a) (hlocal c b)) (hw c)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Remove the actual independent low union from the original channel
kernel. The remaining smooth-mixture error is derived from the local
probabilities and the proved actual-to-independent cell comparison. -/
theorem fairPrimeKernel_discarded_smooth_error {D R : Type*}
    [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → D × R)
    (low : (Q → Bool) → Prop) [DecidablePred low]
    (f : (Q → Bool) → ℝ → ℝ) (location : D × R → ℝ)
    {m M η : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hf : ∀ c x, |f c x| ≤ M)
    (hlocal : ∀ c a, |primeHighExclusiveCell Q cell low c a / m - f c (location a)| ≤ η)
    (a b : D × R) :
    |(finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) a b -
        primeLowUnionKernel Q cell low m a b) -
      smoothMixtureKernel (quarterPrimeMass Q) f location a b| ≤
        2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) := by
  have hind := independentPairKernel_cutoff (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeOutputCell Q cell) low (fun _ : D => m) a b
  change independentPairMass _ _ _ _ _ / (m * m) =
    primeLowUnionKernel Q cell low m a b +
      exclusiveProductKernel (quarterPrimeMass Q) (fun _ : D => m)
        (primeHighExclusiveCell Q cell low) a b at hind
  have herr := fairPrimeKernel_independent_error Q hQ hN hcut cell hm a b
  rw [hind] at herr
  have hhigh := exclusiveProductKernel_smooth_error (quarterPrimeMass Q)
    (primeHighExclusiveCell Q cell low) f location (quarterPrimeMass_nonneg Q hQ)
    (quarterPrimeMass_sum Q) hm.ne' hM hη hf hlocal a b
  have heq : (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) a b -
        primeLowUnionKernel Q cell low m a b) - smoothMixtureKernel (quarterPrimeMass Q) f location a b =
      (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) a b -
        (primeLowUnionKernel Q cell low m a b +
          exclusiveProductKernel (quarterPrimeMass Q) (fun _ : D => m)
            (primeHighExclusiveCell Q cell low) a b)) +
      (exclusiveProductKernel (quarterPrimeMass Q) (fun _ : D => m)
        (primeHighExclusiveCell Q cell low) a b -
          smoothMixtureKernel (quarterPrimeMass Q) f location a b) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add herr hhigh).trans_eq (add_comm _ _))

/-- Coarse compactness for the actual fair-prime channel, uniformly over
every real input. The only arithmetic premises are the two low-event
local mass bounds and the normalized high-exclusive local law. -/
theorem fairPrimeCoarseChannel_square_bound {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → D × R)
    (low : (Q → Bool) → Prop) [DecidablePred low]
    (f : (Q → Bool) → ℝ → ℝ) (location : D × R → ℝ)
    {m H M η mesh : ℝ} {L₀ : ℝ≥0}
    (hm : 0 < m) (hH : 0 ≤ H) (hM : 0 ≤ M) (hη : 0 ≤ η) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (hmarginal : ∀ a, independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeOutputCell Q cell) a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ a,
      optionCellMass (quarterPrimeMass Q) (fun c => primeOutputCell Q cell c e) a ≤ H * m)
    (hlocal : ∀ c a, |primeHighExclusiveCell Q cell low c a / m - f c (location a)| ≤ η)
    (g : (Q → Bool) → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) g a -
        finiteResidueAverage (fun r =>
          finiteChannel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) g (a.1, r))) ^ 2) ≤
      (8 * lowExclusiveProbability (quarterPrimeMass Q) low * H +
        4 * (2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) +
          2 * M * (L₀ : ℝ) * mesh) * ∑ _a : D × R, m) *
            ∑ x, fullPrimeMass Q x * g x ^ 2 := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hσ := lowExclusiveProbability_nonneg (quarterPrimeMass Q) low hquarter
  let K := finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell)
  let L := primeLowUnionKernel Q cell low m
  have hL (a b : D × R) : 0 ≤ L a b :=
    lowUnionExclusiveKernel_nonneg _ _ _ _ _ hquarter hquarter (fun _ => hm.le) a b
  have hrows (a : D × R) : (∑ b : D × R, m * L a b) ≤
      2 * lowExclusiveProbability (quarterPrimeMass Q) low * H :=
    lowUnionExclusiveKernel_weighted_rows _ _ _ _ hquarter hquarter
      (quarterPrimeMass_sum Q) hm hmarginal hcommon a
  have hsmooth := fairPrimeKernel_discarded_smooth_error Q hQ hN hcut cell low f location
    hm hM hη hf hlocal
  have hε : 0 ≤ 2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) := by positivity
  have hbound := coarseChannel_square_bound (fullPrimeMass Q) (fairPrimeTransition Q cell)
    (quarterPrimeMass Q) f location L (fun a b => K a b - L a b)
    (fullPrimeMass_nonneg Q hQ) hquarter (quarterPrimeMass_sum Q)
    hm (mul_nonneg (mul_nonneg (by norm_num) hσ) hH) hε hM hmesh hf hLip hdiam hL hrows
    (fun a b => by dsimp [K]; ring) hsmooth g
  convert hbound using 1
  ring

end JointDickman

end OAI
