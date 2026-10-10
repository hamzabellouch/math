import OAI.NumberTheory.CubicMoment.Estimates.MellinDualTail

namespace OAI

/-! Moving finite dual polynomials back to the symmetry line. The only
new conditional analytic input is the bounded-strip polynomial estimate
for the classical Gamma quotient, a specialization of NIST DLMF 5.11.9
(uniformly for bounded real parts). The half-integer-line estimate needed
for the discarded tail was proved directly in GammaLeftLine. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

/-- The elementary quotient in the trivial infinity-type equation. -/
def gammaFEQuotient (s : ℂ) : ℂ := Complex.Gamma (1-s)/Complex.Gamma s

/-- Small bounded-strip consequence of the uniform vertical Stirling
formula, NIST DLMF (5.11.9), https://dlmf.nist.gov/5.11.E9.
This concerns only the classical Gamma function, not an arithmetic sum. -/
def GammaQuotientStripBound (a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ u : ℝ,
    ‖gammaFEQuotient (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^N

lemma differentiableOn_gammaFEQuotient :
    DifferentiableOn ℂ gammaFEQuotient {s : ℂ | s.re < 1} := by
  intro s hs
  have hreg : ∀ n : ℕ, 1-s ≠ -(n:ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.sub_re,Complex.one_re,Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    change s.re < 1 at hs
    linarith
  have hu : DifferentiableAt ℂ (fun z : ℂ => 1-z) s := by fun_prop
  have htop := (Complex.differentiableAt_Gamma (1-s) hreg).comp s hu
  exact (htop.mul (Complex.differentiable_one_div_Gamma s)).differentiableWithinAt

lemma norm_conductor_power_strip {A a σ u : ℝ} (hA : 0 < A)
    (hσ : σ ∈ Icc a (1/2:ℝ)) :
    ‖(A:ℂ)^(1-2*(σ+(u:ℂ)*Complex.I))‖ ≤ max 1 (A^(1-2*a)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
  have hre : (1-2*((σ:ℂ)+(u:ℂ)*Complex.I)).re = 1-2*σ := by simp
  rw [hre]
  by_cases hA1 : 1 ≤ A
  · exact (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith [hσ.1])).trans (le_max_right _ _)
  · exact (Real.rpow_le_one hA.le (le_of_not_ge hA1) (by linarith [hσ.2])).trans
      (le_max_left _ _)

def finiteNormDirichlet {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) (s : ℂ) : ℂ := ∑ i ∈ S, a i*(N i:ℂ)^(-s)

lemma differentiable_finiteNormDirichlet {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i) :
    Differentiable ℂ (finiteNormDirichlet S a N) := by
  apply Differentiable.fun_sum
  intro i hi
  have : NeZero (N i:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (hN i hi).ne'⟩
  exact ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg).const_mul _

lemma norm_finiteNormDirichlet_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖finiteNormDirichlet S a N s‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le zero_lt_one (hN i hi)),
    Complex.neg_re]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos
    (hN i hi) (by linarith))

def finiteHeckeDual {ι : Type*} (S : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (ε : ℂ) (A : ℝ) (s : ℂ) : ℂ :=
  ε*(A:ℂ)^(1-2*s)*gammaFEQuotient s*finiteNormDirichlet S a N (1-s)

lemma differentiableOn_finiteHeckeDual {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i)
    (ε : ℂ) {A : ℝ} (hA : 0 < A) :
    DifferentiableOn ℂ (finiteHeckeDual S a N ε A) {s : ℂ | s.re < 1} := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  have hp : Differentiable ℂ (fun s : ℂ => (A:ℂ)^(1-2*s)) :=
    (differentiable_const_cpow_of_neZero _).comp (by fun_prop)
  have hd : Differentiable ℂ (fun s : ℂ => finiteNormDirichlet S a N (1-s)) :=
    (differentiable_finiteNormDirichlet S a N hN).comp (by fun_prop)
  exact ((hp.const_mul ε).differentiableOn.mul
    differentiableOn_gammaFEQuotient).mul hd.differentiableOn

/-- The finite retained dual polynomial admits the actual contour move.
Its coefficients are unchanged during the move. -/
theorem finite_hecke_dual_contour_shift {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {A Z b : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (hb : b ≤ 1/2)
    (hGamma : GammaQuotientStripBound b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    (∫ τ : ℝ, mellin W (b+(τ:ℂ)*Complex.I)*(Z:ℂ)^(b+(τ:ℂ)*Complex.I)*
      finiteHeckeDual S a N ε A (b+((τ-t:ℝ):ℂ)*Complex.I)) =
    ∫ τ : ℝ, mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual S a N ε A ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) := by
  obtain ⟨Cg,n,hCg,hg⟩ := hGamma
  let B := ‖ε‖*max 1 (A^(1-2*b))*Cg*(∑ i ∈ S, ‖a i‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoly (σ : ℝ) (hσ : σ ∈ Icc b (1/2:ℝ)) (τ : ℝ) :
      ‖finiteHeckeDual S a N ε A (σ+((τ-t:ℝ):ℂ)*Complex.I)‖ ≤ B*(1+|τ-t|)^n := by
    have hn := norm_finiteNormDirichlet_le S a N hN
      (1-(σ+((τ-t:ℝ):ℂ)*Complex.I)) (by simp; linarith [hσ.2])
    have hpow := norm_conductor_power_strip (u := τ-t) hA hσ
    have hgam := hg σ hσ (τ-t)
    unfold finiteHeckeDual
    simp only [norm_mul]
    calc
      _ ≤ ‖ε‖*max 1 (A^(1-2*b))*(Cg*(1+|τ-t|)^n)*(∑ i ∈ S, ‖a i‖) := by gcongr
      _ = _ := by dsimp [B]; ring
  let f : ℂ → ℂ := fun s => mellin W s*(Z:ℂ)^s*
    finiteHeckeDual S a N ε A (s-(t:ℂ)*Complex.I)
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hZ).ne'⟩
  have hshift : DifferentiableOn ℂ (fun s : ℂ =>
      finiteHeckeDual S a N ε A (s-(t:ℂ)*Complex.I)) (closedVerticalStrip b (1/2)) := by
    apply (differentiableOn_finiteHeckeDual S a N
      (fun i hi => lt_of_lt_of_le zero_lt_one (hN i hi)) ε hA).comp
      (differentiable_id.sub_const _).differentiableOn
    intro s hs
    change (s-(t:ℂ)*Complex.I).re < 1
    have hsr := hs.2
    simpa using lt_of_le_of_lt hsr (by norm_num : (1/2:ℝ) < 1)
  have hf : DifferentiableOn ℂ f (closedVerticalStrip b (1/2)) :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).mul
      (differentiable_const_cpow_of_neZero _)).differentiableOn.mul hshift
  obtain ⟨K,_,hK⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t
    (finiteHeckeDual S a N ε A) hB n hpoly
  have he (σ τ : ℝ) : f (σ+(τ:ℂ)*Complex.I) =
      mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        finiteHeckeDual S a N ε A (σ+((τ-t:ℝ):ℂ)*Complex.I) := by
    dsimp [f]
    congr 2
    push_cast
    ring
  have hc := mellin_contour_shift_of_majorant hb f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 (by intro σ hσ τ; rw [he]; exact hK σ hσ τ)
  simp_rw [he] at hc
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hc

lemma finite_hecke_dual_strip_growth {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {A b : ℝ} (hA : 0 < A) (hGamma : GammaQuotientStripBound b) :
    ∃ (B : ℝ) (n : ℕ), 0 ≤ B ∧ ∀ σ ∈ Icc b (1/2:ℝ), ∀ u : ℝ,
      ‖finiteHeckeDual S a N ε A (σ+(u:ℂ)*Complex.I)‖ ≤ B*(1+|u|)^n := by
  obtain ⟨Cg,n,hCg,hg⟩ := hGamma
  let B := ‖ε‖*max 1 (A^(1-2*b))*Cg*(∑ i ∈ S, ‖a i‖)
  refine ⟨B,n,by dsimp [B]; positivity,?_⟩
  intro σ hσ u
  have hn := norm_finiteNormDirichlet_le S a N hN (1-(σ+(u:ℂ)*Complex.I))
    (by simp; linarith [hσ.2])
  have hpow := norm_conductor_power_strip (u := u) hA hσ
  have hgam := hg σ hσ u
  unfold finiteHeckeDual
  simp only [norm_mul]
  calc
    _ ≤ ‖ε‖*max 1 (A^(1-2*b))*(Cg*(1+|u|)^n)*(∑ i ∈ S, ‖a i‖) := by gcongr
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
