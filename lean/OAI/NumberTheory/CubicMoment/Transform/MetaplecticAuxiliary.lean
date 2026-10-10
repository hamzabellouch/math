import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPartialSums
import OAI.NumberTheory.CubicGram.FrequencyGauss

namespace OAI

/-! The auxiliary functions in Heath-Brown (2000), §3, equations (14)
and (19), and the finite-divisor estimate on author-manuscript p.14.
Only fixed-level strip growth is needed here, so the finite-divisor
estimate drops its factors at most one. All polynomial estimates below
are derived from the stated auxiliary bound and convergent Euler inverse. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPsiSeries (q : Eisenstein) (z : ℂ) : ℂ :=
  normDirichletSeries (fun c : PrimaryArgument =>
    (Real.sqrt (norm c):ℂ)*frequencyGauss c q) (fun c => norm c) z

def metaplecticZetaInverse (z : ℂ) : ℂ :=
  normDirichletSeries (fun c : PrimaryArgument => (idealMoebius c:ℂ))
    (fun c => norm c) (3*z-2)

def metaplecticPrimaryDivisors (r : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall (norm r)).filter (fun q => q ∣ r)

/-- HB §3 (19), at large height only. The parameter `e` is retained
literally; the application below uses just `e = 1/10`. -/
def HeathBrownZBound (Z : Eisenstein → ℂ → ℂ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Eisenstein, primary q → Squarefree q →
    ∀ α ∈ Icc (1/2:ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
      ‖Z q ((α:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        C*norm q^((3/2+e-α)/2)*(1+t^2)^(3/2+e-α)

/-- Equation (14), after division by its absolutely convergent Euler
factor. The reciprocal is the literal primary Möbius series above. -/
def HeathBrownZFactorization (Ψ Z : Eisenstein → ℂ → ℂ) : Prop :=
  (∀ q : Eisenstein, primary q → Squarefree q → ∀ z : ℂ, (3/2:ℝ) < z.re →
    Ψ q z = metaplecticPsiSeries q z) ∧
  ∀ q : Eisenstein, primary q → Squarefree q → ∀ z : ℂ, 1 < z.re →
    Ψ q z = Z q z*metaplecticZetaInverse z

/-- The finite-divisor inequality following the exact identity on HB
p.14. Since `Nr, Nd ≥ 1`, its factors `(Nr)^(-1/2)` and `(Nd)^(-1/2)`
are discarded, and complementary divisors are reindexed. This weaker
fixed-level version suffices solely to justify a contour shift. -/
def HeathBrownFiniteDivisor (F Ψ : Eisenstein → ℂ → ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 ≤ A ∧
    ∀ r : Eisenstein, primary r → Squarefree r →
    ∀ s : ℂ, 1/2+δ ≤ s.re →
      ‖F r s‖ ≤ A*norm r^s.re*
        ∑ q ∈ metaplecticPrimaryDivisors r, ‖Ψ q (s+1/2)‖

private lemma norm_idealMoebius_le_one (c : Eisenstein) : ‖(idealMoebius c:ℂ)‖ ≤ 1 := by
  have hsq : ‖(idealMoebius c:ℂ)‖^2 ≤ 1 := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      idealMoebius_sq]
    split_ifs <;> norm_num
  nlinarith [_root_.norm_nonneg (idealMoebius c:ℂ)]

lemma metaplecticZetaInverse_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ z : ℂ, 1+δ ≤ z.re → ‖metaplecticZetaInverse z‖ ≤ E := by
  let E := ∑' c : PrimaryArgument, norm c^(-(1+3*δ))
  have hsum : Summable (fun c : PrimaryArgument => norm c^(-(1+3*δ))) :=
    primary_norm_rpow_summable (by linarith)
  refine ⟨E,tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg _) _),?_⟩
  intro z hz
  have hpoint (c : PrimaryArgument) :
      ‖(idealMoebius c:ℂ)*(norm c:ℂ)^(-(3*z-2))‖ ≤ norm c^(-(1+3*δ)) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (norm_pos_of_ne_zero (primary_ne_zero c.property))]
    have hp : (-(3*z-2)).re ≤ -(1+3*δ) := by simp; linarith
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _)
      (norm_idealMoebius_le_one c)).trans
      (Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero c.property)) hp)
  have habs := hsum.of_nonneg_of_le (fun c => _root_.norm_nonneg _) hpoint
  unfold metaplecticZetaInverse normDirichletSeries
  exact (norm_tsum_le_tsum_norm habs).trans (Summable.tsum_le_tsum hpoint habs hsum)

lemma heathBrown_Z_polynomial {Z : Eisenstein → ℂ → ℂ} (hZ : HeathBrownZBound Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Eisenstein, primary q → Squarefree q →
      ∀ α ∈ Icc (1/2:ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
        ‖Z q ((α:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C*norm q*(1+|t|)^4 := by
  obtain ⟨C,hC,hZ⟩ := hZ (1/10) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro q hq hsq α hα t ht
  have hN : 1 ≤ norm q := one_le_norm (primary_ne_zero hq)
  have hp : norm q^((3/2+(1/10:ℝ)-α)/2) ≤ norm q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN
      (show (3/2+(1/10:ℝ)-α)/2 ≤ 1 by linarith [hα.1])
  have hT : (1+t^2)^(3/2+(1/10:ℝ)-α) ≤ (1+|t|)^4 := by
    calc
      _ ≤ (1+t^2)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by nlinarith [sq_nonneg t]) (by linarith [hα.1])
      _ = (1+t^2)^2 := Real.rpow_ofNat _ _
      _ ≤ ((1+|t|)^2)^2 := pow_le_pow_left₀ (by positivity)
        (by nlinarith [abs_nonneg t,sq_abs t]) _
      _ = _ := by ring
  exact (hZ q hq hsq α hα t ht).trans (by gcongr)

lemma heathBrown_psi_polynomial {Ψ Z : Eisenstein → ℂ → ℂ}
    (hZ : HeathBrownZBound Z) (hfac : HeathBrownZFactorization Ψ Z)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Eisenstein, primary q → Squarefree q →
      ∀ α ∈ Icc (1+δ) (3/2:ℝ), ∀ t : ℝ, 1 ≤ |t| →
        ‖Ψ q ((α:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C*norm q*(1+|t|)^4 := by
  obtain ⟨C,hC,hbound⟩ := heathBrown_Z_polynomial hZ
  obtain ⟨E,hE,hEinv⟩ := metaplecticZetaInverse_uniform hδ
  refine ⟨C*E,mul_nonneg hC hE,?_⟩
  intro q hq hsq α hα t ht
  rw [hfac.2 q hq hsq _ (by simp; linarith [hα.1]),norm_mul]
  have hleft := hbound q hq hsq α ⟨by linarith [hα.1],hα.2⟩ t ht
  have hright := hEinv ((α:ℂ)+(t:ℂ)*Complex.I) (by simpa using hα.1)
  have hqn := norm_nonneg q
  calc
    _ ≤ (C*norm q*(1+|t|)^4)*E := mul_le_mul hleft hright
      (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Fixed-level growth on the left part of the contour strip, derived
from HB's auxiliary bound rather than assumed for the original series. -/
lemma heathBrown_left_strip_polynomial {F Ψ Z : Eisenstein → ℂ → ℂ}
    (hZ : HeathBrownZBound Z) (hfac : HeathBrownZFactorization Ψ Z)
    (hdiv : HeathBrownFiniteDivisor F Ψ) {δ : ℝ} (hδ : 0 < δ)
    {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    MetaplecticStripPolynomial (F r) (1/2+δ) (9/10) := by
  obtain ⟨C,hC,hΨ⟩ := heathBrown_psi_polynomial hZ hfac hδ
  obtain ⟨A,hA,hF⟩ := hdiv δ hδ
  let Q := ∑ q ∈ metaplecticPrimaryDivisors r, norm q
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun q _ => norm_nonneg q)
  have hrn := norm_nonneg r
  refine ⟨A*norm r*C*Q,by positivity,4,?_⟩
  intro σ hσ t ht
  have hR : 1 ≤ norm r := one_le_norm (primary_ne_zero hr)
  have hp : norm r^σ ≤ norm r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
      (show σ ≤ (1:ℝ) by linarith [hσ.2])
  have hsum : (∑ q ∈ metaplecticPrimaryDivisors r,
      ‖Ψ q ((σ:ℂ)+(t:ℂ)*Complex.I+1/2)‖) ≤ C*Q*(1+|t|)^4 := by
    calc
      _ ≤ ∑ q ∈ metaplecticPrimaryDivisors r, C*norm q*(1+|t|)^4 := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' : primary q := (mem_primaryElementBall.mp (Finset.mem_filter.mp hq).1).1
        have he : (σ:ℂ)+(t:ℂ)*Complex.I+1/2 =
            ((σ+1/2:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
        rw [he]
        have hqs : Squarefree q := fun x hx => hs x (hx.trans (Finset.mem_filter.mp hq).2)
        apply hΨ q hq' hqs (σ+1/2) ⟨by linarith [hσ.1],by linarith [hσ.2]⟩ t ht
      _ = _ := by simp only [Q,← Finset.sum_mul,← Finset.mul_sum]
  have hf := hF r hr hs ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ.1)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hf
  calc
    _ ≤ A*norm r^σ*(C*Q*(1+|t|)^4) := hf.trans (by gcongr)
    _ ≤ A*norm r*(C*Q*(1+|t|)^4) := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
