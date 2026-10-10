import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace OAI

/-!
# Analytic theta products, zeros, and marked products
-/

section

namespace Nagata.W21

open Filter Topology
open scoped BigOperators

noncomputable def thetaPositive (τ z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - τ ^ n * z)

/-- The negative-index product is written with index `n+1`, starting at zero. -/
noncomputable def thetaProduct (τ z : ℂ) : ℂ :=
  thetaPositive τ z * thetaPositive τ (τ * z⁻¹)

/-- Convergence of the positive half, valid at its zeros as well. -/
theorem thetaPositive_multipliable {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    Multipliable (fun n : ℕ ↦ 1 - τ ^ n * z) := by
  simpa only [mul_neg, sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable
      ((summable_geometric_of_norm_lt_one hτ).mul_right (-z))

/-- Convergence of the second product as indexed in the manuscript. -/
theorem thetaNegative_multipliable {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    Multipliable (fun n : ℕ ↦ 1 - τ ^ (n + 1) / z) := by
  simpa only [div_eq_mul_inv, pow_succ, mul_assoc] using
    thetaPositive_multipliable hτ (τ * z⁻¹)

/-- The genuine product definition agrees with the two products in the source. -/
theorem thetaProduct_eq_source (τ z : ℂ) :
    thetaProduct τ z = (∏' n : ℕ, (1 - τ ^ n * z)) *
      ∏' n : ℕ, (1 - τ ^ (n + 1) / z) := by
  simp only [thetaProduct, thetaPositive, div_eq_mul_inv, pow_succ, mul_assoc]

/-- Removing the first factor from a convergent product, without dividing by it. -/
theorem thetaPositive_shift {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    thetaPositive τ z = (1 - z) * thetaPositive τ (τ * z) := by
  have hm : Multipliable (fun n : ℕ ↦ 1 - τ ^ (n + 1) * z) := by
    simpa only [pow_succ, mul_assoc] using thetaPositive_multipliable hτ (τ * z)
  simpa only [thetaPositive, pow_zero, one_mul, pow_succ, mul_assoc] using
    tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - τ ^ n * z) hm

/-- Theta automorphy on `ℂ*`, proved from convergent products. -/
theorem thetaProduct_automorphy {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ (τ * z) = -z⁻¹ * thetaProduct τ z := by
  have hc : τ * (τ * z)⁻¹ = z⁻¹ := by
    rw [mul_inv_rev]
    calc
      τ * (z⁻¹ * τ⁻¹) = (τ * τ⁻¹) * z⁻¹ := by ac_rfl
      _ = z⁻¹ := by rw [mul_inv_cancel₀ hτ0, one_mul]
  have hb : 1 - z⁻¹ = -z⁻¹ * (1 - z) := by
    symm
    rw [mul_sub, mul_one, neg_mul, sub_neg_eq_add, inv_mul_cancel₀ hz, add_comm]
    exact (sub_eq_add_neg 1 z⁻¹).symm
  unfold thetaProduct
  rw [hc, thetaPositive_shift hτ z⁻¹, hb]
  calc
    thetaPositive τ (τ * z) * ((-z⁻¹ * (1 - z)) * thetaPositive τ (τ * z⁻¹)) =
        -z⁻¹ * (((1 - z) * thetaPositive τ (τ * z)) *
          thetaPositive τ (τ * z⁻¹)) := by ac_rfl
    _ = -z⁻¹ * (thetaPositive τ z * thetaPositive τ (τ * z⁻¹)) := by
      rw [← thetaPositive_shift hτ z]

/-- The automorphy equation with the manuscript's real parameter hypotheses. -/
theorem thetaProduct_automorphy_real {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ≠ 0) :
    thetaProduct (τ : ℂ) ((τ : ℂ) * z) = -z⁻¹ * thetaProduct (τ : ℂ) z := by
  apply thetaProduct_automorphy
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0] using hτ1
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt hτ0)
  · exact hz

/-- A theta factor with zero represented by `a` has multiplier `-a`.
This is the covering-space equation used for `D(1,-a)` in the manuscript. -/
theorem thetaProduct_scaled_automorphy {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ ((τ * z) / a) = (-a) * z⁻¹ * thetaProduct τ (z / a) := by
  simpa only [div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv, neg_mul] using
    thetaProduct_automorphy hτ hτ0 (div_ne_zero hz ha)

/-- Away from zeros of its factors the positive product is nonzero. -/
theorem thetaPositive_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ)
    (hz : ∀ n : ℕ, 1 - τ ^ n * z ≠ 0) : thetaPositive τ z ≠ 0 := by
  have hn : Summable (fun n : ℕ ↦ ‖-(τ ^ n * z)‖) := by
    simpa only [norm_neg, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg τ) hτ).mul_right ‖z‖
  have hf : ∀ n : ℕ, 1 + -(τ ^ n * z) ≠ 0 := by
    simpa only [sub_eq_add_neg] using hz
  simpa only [thetaPositive, sub_eq_add_neg] using
    tprod_one_add_ne_zero_of_summable hf hn

/-- No extra zeros are introduced by passage to the infinite positive product. -/
theorem thetaPositive_eq_zero_iff {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    thetaPositive τ z = 0 ↔ ∃ n : ℕ, τ ^ n * z = 1 := by
  classical
  constructor
  · intro hp
    by_contra hf
    have hn : ∀ n : ℕ, 1 - τ ^ n * z ≠ 0 := by
      intro n hn
      apply hf
      exact ⟨n, (sub_eq_zero.mp hn).symm⟩
    exact thetaPositive_ne_zero hτ z hn hp
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero (f := fun n : ℕ ↦ 1 - τ ^ n * z)
      ⟨n, by change 1 - τ ^ n * z = 0; rw [hn, sub_self]⟩

/-- Exact factor-zero description of the full product, before identifying the
index set with the integer powers of a nonzero parameter. -/
theorem thetaProduct_eq_zero_iff_factors {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    thetaProduct τ z = 0 ↔
      (∃ n : ℕ, τ ^ n * z = 1) ∨ (∃ n : ℕ, τ ^ n * (τ * z⁻¹) = 1) := by
  rw [thetaProduct, mul_eq_zero, thetaPositive_eq_zero_iff hτ z,
    thetaPositive_eq_zero_iff hτ (τ * z⁻¹)]

end Nagata.W21

end

section

/-! Local uniform convergence and holomorphy of the genuine theta product. -/
namespace Nagata.W21

open Filter Topology
open scoped BigOperators

/-- Compact uniform convergence after any continuous bounded substitution. -/
theorem thetaPositive_hasProdUniformlyOn_comp {α : Type*} [TopologicalSpace α]
    {τ : ℂ} (hτ : ‖τ‖ < 1) {K : Set α} (hK : IsCompact K)
    (g : α → ℂ) (hg : ContinuousOn g K) (R : ℝ)
    (hR : ∀ x ∈ K, ‖g x‖ ≤ R) :
    HasProdUniformlyOn (fun (n : ℕ) x ↦ 1 - τ ^ n * g x)
      (fun x ↦ thetaPositive τ (g x)) K := by
  have hu : Summable (fun n : ℕ ↦ ‖τ‖ ^ n * R) :=
    (summable_geometric_of_lt_one (norm_nonneg τ) hτ).mul_right R
  have hb : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, ‖-(τ ^ n * g x)‖ ≤ ‖τ‖ ^ n * R := by
    exact Eventually.of_forall fun n x hx ↦ by
      rw [norm_neg, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hR x hx) (pow_nonneg (norm_nonneg τ) n)
  have hc : ∀ n : ℕ, ContinuousOn (fun x ↦ -(τ ^ n * g x)) K :=
    fun n ↦ (continuousOn_const.mul hg).neg
  simpa only [sub_eq_add_neg, thetaPositive] using
    Summable.hasProdUniformlyOn_nat_one_add hK hu hb hc

/-- The second source product converges uniformly on every compact subset of
`ℂ*`; compactness supplies a bound for inversion. -/
theorem thetaNegative_hasProdUniformlyOn {τ : ℂ} (hτ : ‖τ‖ < 1)
    {K : Set ℂ} (hK : IsCompact K) (hz : ∀ z ∈ K, z ≠ 0) :
    HasProdUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ (n + 1) / z)
      (fun z ↦ thetaPositive τ (τ * z⁻¹)) K := by
  have hg : ContinuousOn (fun z : ℂ ↦ τ * z⁻¹) K :=
    continuousOn_const.mul (continuousOn_id.inv₀ hz)
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn hg).isBounded.exists_norm_le
  have hu := thetaPositive_hasProdUniformlyOn_comp hτ hK
    (fun z : ℂ ↦ τ * z⁻¹) hg R (fun z hz ↦ hR _ ⟨z, hz, rfl⟩)
  simpa only [pow_succ, div_eq_mul_inv, mul_assoc] using hu

/-- The negative half converges locally uniformly on the punctured plane. -/
theorem thetaNegative_hasProdLocallyUniformlyOn {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ (n + 1) / z)
      (fun z ↦ thetaPositive τ (τ * z⁻¹)) {z : ℂ | z ≠ 0} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ne
  intro K hKs hK
  exact thetaNegative_hasProdUniformlyOn hτ hK (fun z hz ↦ hKs hz)

/-- The positive product converges locally uniformly on the whole complex plane. -/
theorem thetaPositive_hasProdLocallyUniformlyOn {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ n * z)
      (thetaPositive τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact thetaPositive_hasProdUniformlyOn_comp hτ hK (fun z ↦ z)
    continuousOn_id R hR

/-- The positive product is entire, by local uniform convergence of polynomials. -/
theorem thetaPositive_differentiable {τ : ℂ} (hτ : ‖τ‖ < 1) :
    Differentiable ℂ (thetaPositive τ) := by
  have hlim := (thetaPositive_hasProdLocallyUniformlyOn hτ).tendstoLocallyUniformlyOn_finsetRange
  have hd : ∀ N : ℕ, DifferentiableOn ℂ
      (fun z ↦ ∏ n ∈ Finset.range N, (1 - τ ^ n * z)) Set.univ := by
    intro N
    exact DifferentiableOn.fun_finsetProd fun n _ ↦
      (differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const (τ ^ n)).mul differentiableOn_id)
  exact differentiableOn_univ.mp
    (hlim.differentiableOn (Eventually.of_forall hd) isOpen_univ)

/-- The source theta product is holomorphic on the punctured complex plane. -/
theorem thetaProduct_differentiableAt {τ z : ℂ} (hτ : ‖τ‖ < 1) (hz : z ≠ 0) :
    DifferentiableAt ℂ (thetaProduct τ) z := by
  have hp := thetaPositive_differentiable hτ
  exact (hp z).mul ((hp (τ * z⁻¹)).fun_comp' z
    ((differentiableAt_const τ).mul (differentiableAt_inv hz)))

theorem thetaPositive_parameter_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) :
    thetaPositive τ τ ≠ 0 := by
  apply thetaPositive_ne_zero hτ τ
  intro n hn
  have he : τ ^ (n + 1) = 1 := by
    simpa only [pow_succ] using (sub_eq_zero.mp hn).symm
  have hlt : ‖τ ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg τ) hτ (Nat.succ_ne_zero n)
  rw [he, norm_one] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

/-- The theta product vanishes at the representative `1`. -/
theorem thetaProduct_one {τ : ℂ} (hτ : ‖τ‖ < 1) : thetaProduct τ 1 = 0 := by
  rw [thetaProduct, thetaPositive_shift hτ 1]
  simp

/-- The derivative at `1` comes from its single zero factor. -/
theorem thetaProduct_hasDerivAt_one {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasDerivAt (thetaProduct τ) (-(thetaPositive τ τ) ^ 2) 1 := by
  have hp := thetaPositive_differentiable hτ
  have hg : DifferentiableAt ℂ
      (fun z : ℂ ↦ thetaPositive τ (τ * z) * thetaPositive τ (τ * z⁻¹)) 1 :=
    ((hp (τ * 1)).fun_comp' 1 ((differentiableAt_const τ).mul differentiableAt_id)).mul
      ((hp (τ * (1 : ℂ)⁻¹)).fun_comp' 1
        ((differentiableAt_const τ).mul (differentiableAt_inv one_ne_zero)))
  have heq : thetaProduct τ = fun z : ℂ ↦
      (1 - z) * (thetaPositive τ (τ * z) * thetaPositive τ (τ * z⁻¹)) := by
    funext z
    rw [thetaProduct, thetaPositive_shift hτ z]
    exact mul_assoc _ _ _
  rw [heq]
  convert ((hasDerivAt_id' (x := (1 : ℂ))).const_sub 1).mul hg.hasDerivAt using 1
  simp [pow_two]

/-- Nonzero derivative certifies that the theta zero at `1` is simple. -/
theorem thetaProduct_deriv_one_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) :
    deriv (thetaProduct τ) 1 ≠ 0 := by
  rw [(thetaProduct_hasDerivAt_one hτ).deriv]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (thetaPositive_parameter_ne_zero hτ))

end Nagata.W21

end

section

namespace Nagata.W21

/-- Separate the inverse natural powers from the strictly positive powers. -/
theorem thetaProduct_eq_zero_iff_nat_powers {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ z = 0 ↔
      (∃ n : ℕ, z = (τ ^ n)⁻¹) ∨ (∃ n : ℕ, z = τ ^ (n + 1)) := by
  rw [thetaProduct_eq_zero_iff_factors hτ z]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, ((mul_eq_one_iff_inv_eq₀ (pow_ne_zero n hτ0)).mp hn).symm⟩
    · have he : τ ^ (n + 1) * z⁻¹ = 1 := by
        simpa only [pow_succ, mul_assoc] using hn
      exact Or.inr ⟨n, ((mul_inv_eq_one₀ hz).mp he).symm⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, (mul_eq_one_iff_inv_eq₀ (pow_ne_zero n hτ0)).mpr hn.symm⟩
    · right
      refine ⟨n, ?_⟩
      have he : τ ^ (n + 1) * z⁻¹ = 1 := (mul_inv_eq_one₀ hz).mpr hn.symm
      simpa only [pow_succ, mul_assoc] using he

/-- The source theta product has precisely the zeros `τ^ℤ` on `ℂ*`. -/
theorem thetaProduct_eq_zero_iff_zpow {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ z = 0 ↔ ∃ k : ℤ, z = τ ^ k := by
  rw [thetaProduct_eq_zero_iff_nat_powers hτ hτ0 hz]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨-(n : ℤ), by simpa only [zpow_neg, zpow_natCast] using hn⟩
    · exact ⟨((n + 1 : ℕ) : ℤ), by simpa only [zpow_natCast] using hn⟩
  · rintro ⟨k, rfl⟩
    cases k with
    | ofNat n =>
      cases n with
      | zero => exact Or.inl ⟨0, by simp⟩
      | succ n => exact Or.inr ⟨n, zpow_natCast τ (n + 1)⟩
    | negSucc n => exact Or.inl ⟨n + 1, by simp only [zpow_negSucc]⟩

/-- The zeros of the theta factor `Θ(z/a)` are exactly the lifts of `a`
in the multiplicative quotient. The quotient itself is not assumed here. -/
theorem thetaProduct_scaled_eq_zero_iff {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ (z / a) = 0 ↔ ∃ k : ℤ, z = a * τ ^ k := by
  rw [thetaProduct_eq_zero_iff_zpow hτ hτ0 (div_ne_zero hz ha)]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [mul_comm] using (div_eq_iff ha).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (div_eq_iff ha).mpr (by simpa only [mul_comm] using hk)⟩

end Nagata.W21

end

section

/-! Transport of the nonzero derivative at `1` along the theta period orbit. -/
namespace Nagata.W21

open Filter Topology

theorem thetaProduct_zpow_eq_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (k : ℤ) : thetaProduct τ (τ ^ k) = 0 :=
  (thetaProduct_eq_zero_iff_zpow hτ hτ0 (zpow_ne_zero k hτ0)).mpr ⟨k, rfl⟩

/-- Differentiate the automorphy equation at a zero. -/
theorem thetaProduct_deriv_mul_at_zero {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : thetaProduct τ z = 0) :
    deriv (thetaProduct τ) (τ * z) * τ = -z⁻¹ * deriv (thetaProduct τ) z := by
  have hl := (thetaProduct_differentiableAt hτ (mul_ne_zero hτ0 hz)).hasDerivAt.comp z
    (hasDerivAt_const_mul τ (x := z))
  have hr := (hasDerivAt_inv hz).neg.mul
    (thetaProduct_differentiableAt hτ hz).hasDerivAt
  have heq : (fun w : ℂ ↦ thetaProduct τ (τ * w)) =ᶠ[𝓝 z]
      (fun w : ℂ ↦ -w⁻¹ * thetaProduct τ w) :=
    Filter.Eventually.mono (isOpen_ne.mem_nhds hz) fun w hw ↦
      thetaProduct_automorphy hτ hτ0 hw
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa only [hzero, mul_zero, zero_add, Pi.neg_apply] using he

/-- At zeros, multiplying the argument by the nonzero period preserves a
nonzero first derivative. -/
theorem thetaProduct_deriv_mul_ne_zero_iff {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : thetaProduct τ z = 0) :
    deriv (thetaProduct τ) (τ * z) ≠ 0 ↔ deriv (thetaProduct τ) z ≠ 0 := by
  have he := thetaProduct_deriv_mul_at_zero hτ hτ0 hz hzero
  constructor
  · intro hmul hd
    have hbad : deriv (thetaProduct τ) (τ * z) * τ = 0 := by
      rw [he, hd, mul_zero]
    exact (mul_ne_zero hmul hτ0) hbad
  · intro hd hmul
    have hbad : -z⁻¹ * deriv (thetaProduct τ) z = 0 := by
      rw [← he, hmul, zero_mul]
    exact (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hz)) hd) hbad

/-- The derivative is nonzero at every nonnegative power. -/
theorem thetaProduct_deriv_pow_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (n : ℕ) : deriv (thetaProduct τ) (τ ^ n) ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero] using thetaProduct_deriv_one_ne_zero hτ
  | succ n ih =>
    have hz : thetaProduct τ (τ ^ n) = 0 := by
      simpa only [zpow_natCast] using thetaProduct_zpow_eq_zero hτ hτ0 (n : ℤ)
    have hd := (thetaProduct_deriv_mul_ne_zero_iff hτ hτ0 (pow_ne_zero n hτ0) hz).mpr ih
    simpa only [pow_succ', Nat.succ_eq_add_one] using hd

/-- The derivative is nonzero at every inverse natural power. -/
theorem thetaProduct_deriv_inv_pow_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (n : ℕ) : deriv (thetaProduct τ) ((τ ^ n)⁻¹) ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero, inv_one] using thetaProduct_deriv_one_ne_zero hτ
  | succ n ih =>
    have hz : thetaProduct τ ((τ ^ (n + 1))⁻¹) = 0 := by
      simpa only [zpow_neg, zpow_natCast] using
        thetaProduct_zpow_eq_zero hτ hτ0 (-((n + 1 : ℕ) : ℤ))
    have hm : τ * (τ ^ (n + 1))⁻¹ = (τ ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
    have hd : deriv (thetaProduct τ) (τ * (τ ^ (n + 1))⁻¹) ≠ 0 := by
      rwa [hm]
    exact (thetaProduct_deriv_mul_ne_zero_iff hτ hτ0
      (inv_ne_zero (pow_ne_zero (n + 1) hτ0)) hz).mp hd

/-- Every theta zero on `ℂ*` has nonzero first derivative. -/
theorem thetaProduct_zero_has_nonzero_deriv {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : thetaProduct τ z = 0) :
    deriv (thetaProduct τ) z ≠ 0 := by
  obtain ⟨k, rfl⟩ := (thetaProduct_eq_zero_iff_zpow hτ hτ0 hz).mp hzero
  cases k with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using thetaProduct_deriv_pow_ne_zero hτ hτ0 n
  | negSucc n =>
    simpa only [zpow_negSucc] using thetaProduct_deriv_inv_pow_ne_zero hτ hτ0 (n + 1)

end Nagata.W21

end

section

/-! The actual finite product of shifted theta factors used for the marked divisor. -/
namespace Nagata.W21
open scoped BigOperators

noncomputable def markedThetaProduct {ι : Type*} [Fintype ι] (τ : ℂ) (a : ι → ℂ)
    (z : ℂ) : ℂ := ∏ i, thetaProduct τ (z / a i)

theorem thetaProduct_scaled_differentiableAt {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (ha : a ≠ 0) (hz : z ≠ 0) : DifferentiableAt ℂ (fun w ↦ thetaProduct τ (w / a)) z :=
  (thetaProduct_differentiableAt (τ := τ) (z := z / a) hτ (div_ne_zero hz ha)).fun_comp' z
    ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const a)

theorem markedThetaProduct_differentiableAt {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (ha : ∀ i, a i ≠ 0)
    (hz : z ≠ 0) : DifferentiableAt ℂ (markedThetaProduct τ a) z := by
  classical
  exact DifferentiableAt.fun_finsetProd fun i _ ↦
    thetaProduct_scaled_differentiableAt hτ (ha i) hz

theorem markedThetaProduct_analyticOnNhd {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} (hτ : ‖τ‖ < 1) (ha : ∀ i, a i ≠ 0) :
    AnalyticOnNhd ℂ (markedThetaProduct τ a) {z : ℂ | z ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ne
  intro z hz
  exact (markedThetaProduct_differentiableAt hτ ha hz).differentiableWithinAt

theorem markedThetaProduct_eq_zero_iff {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hz : z ≠ 0) :
    markedThetaProduct τ a z = 0 ↔ ∃ i, ∃ k : ℤ, z = a i * τ ^ k := by
  classical
  simp only [markedThetaProduct, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    thetaProduct_scaled_eq_zero_iff hτ hτ0 (ha _) hz]

/-- The actual rescaling preserves simplicity of every theta zero. -/
theorem thetaProduct_scaled_zero_has_nonzero_deriv {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0)
    (hf : thetaProduct τ (z / a) = 0) :
    deriv (fun w ↦ thetaProduct τ (w / a)) z ≠ 0 := by
  have hd := (thetaProduct_differentiableAt hτ (div_ne_zero hz ha)).hasDerivAt.comp z
    ((hasDerivAt_id z).div_const a)
  change HasDerivAt (fun w ↦ thetaProduct τ (w / a))
    (deriv (thetaProduct τ) (z / a) * (1 / a)) z at hd
  rw [hd.deriv]
  exact mul_ne_zero (thetaProduct_zero_has_nonzero_deriv hτ hτ0 (div_ne_zero hz ha) hf)
    (div_ne_zero one_ne_zero ha)

/-- An elementary finite-product simple-zero theorem used below. -/
theorem finiteProduct_zero_has_nonzero_deriv {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (z : ℂ) (hf : ∀ i, DifferentiableAt ℂ (f i) z)
    (i : ι) (hi : f i z = 0) (hdi : deriv (f i) z ≠ 0)
    (hother : ∀ j, j ≠ i → f j z ≠ 0) :
    deriv (fun w ↦ ∏ j, f j w) z ≠ 0 := by
  classical
  let g : ℂ → ℂ := fun w ↦ ∏ j ∈ Finset.univ.erase i, f j w
  have hg : DifferentiableAt ℂ g z :=
    DifferentiableAt.fun_finsetProd fun j _ ↦ hf j
  have hgz : g z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj ↦
    hother j (Finset.mem_erase.mp hj).1
  have heq : (fun w ↦ ∏ j, f j w) = (fun w ↦ f i w * g w) := by
    funext w
    exact (Finset.mul_prod_erase Finset.univ (fun j ↦ f j w) (Finset.mem_univ i)).symm
  rw [heq, deriv_fun_mul (hf i) hg, hi, zero_mul, add_zero]
  exact mul_ne_zero hdi hgz

/-- Distinct marked period orbits imply that no two shifted theta factors vanish
at the same point. -/
theorem markedThetaFactors_unique_zero {ι : Type*} {τ : ℂ} {a : ι → ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k))
    {z : ℂ} (hz : z ≠ 0) {i j : ι} (hij : i ≠ j)
    (hi : thetaProduct τ (z / a i) = 0) : thetaProduct τ (z / a j) ≠ 0 := by
  intro hj
  obtain ⟨k, hk⟩ := (thetaProduct_scaled_eq_zero_iff hτ hτ0 (ha i) hz).mp hi
  obtain ⟨l, hl⟩ := (thetaProduct_scaled_eq_zero_iff hτ hτ0 (ha j) hz).mp hj
  apply hdisjoint hij (l - k)
  apply mul_right_cancel₀ (zpow_ne_zero k hτ0)
  rw [← hk, mul_assoc, ← zpow_add₀ hτ0, sub_add_cancel, ← hl]

/-- The marked product has simple zeros when the marks represent distinct
points in the period quotient. -/
theorem markedThetaProduct_zero_has_nonzero_deriv {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k))
    {z : ℂ} (hz : z ≠ 0) (hzero : markedThetaProduct τ a z = 0) :
    deriv (markedThetaProduct τ a) z ≠ 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact finiteProduct_zero_has_nonzero_deriv (fun j w ↦ thetaProduct τ (w / a j)) z
    (fun j ↦ thetaProduct_scaled_differentiableAt hτ (ha j) hz) i hi
    (thetaProduct_scaled_zero_has_nonzero_deriv hτ hτ0 (ha i) hz hi)
    (fun j hj ↦ markedThetaFactors_unique_zero hτ hτ0 ha hdisjoint hz hj.symm hi)

end Nagata.W21

end

end OAI
