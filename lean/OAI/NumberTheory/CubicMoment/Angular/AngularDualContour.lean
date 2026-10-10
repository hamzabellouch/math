import OAI.NumberTheory.CubicMoment.Angular.AngularDualTail
import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualContour

namespace OAI

/-! Retained finite dual polynomials for fixed infinity type. The sole
Gamma strip input is the bounded-strip consequence of NIST DLMF 5.11.9;
there is no arithmetic moment or smooth-duality conclusion in that input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def angularGammaFEQuotient (k : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))

/-- The fixed-shift specialization of the uniform vertical Stirling
formula, DLMF 5.11.9. -/
def AngularGammaQuotientStripBound (k a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ u : ℝ,
    ‖angularGammaFEQuotient k (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^N

lemma differentiableOn_angularGammaFEQuotient {k : ℝ} (hk : 0 ≤ k) :
    DifferentiableOn ℂ (angularGammaFEQuotient k) {s : ℂ | s.re < 1} := by
  intro s hs
  have hreg : ∀ n : ℕ, 1-s+(k:ℂ) ≠ -(n:ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,
      Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    change s.re < 1 at hs
    linarith
  have hu : DifferentiableAt ℂ (fun z : ℂ => 1-z+(k:ℂ)) s := by fun_prop
  have htop := (Complex.differentiableAt_Gamma (1-s+(k:ℂ)) hreg).comp s hu
  have hbot := (Complex.differentiable_one_div_Gamma (s+(k:ℂ))).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(k:ℂ)) s by fun_prop)
  exact (htop.mul hbot).differentiableWithinAt

def angularFiniteHeckeDual {ι : Type*} (S : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (ε : ℂ) (A k : ℝ) (s : ℂ) : ℂ :=
  ε*(A:ℂ)^(1-2*s)*angularGammaFEQuotient k s*finiteNormDirichlet S a N (1-s)

lemma differentiableOn_angularFiniteHeckeDual {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i)
    (ε : ℂ) {k : ℝ} (hk : 0 ≤ k) {A : ℝ} (hA : 0 < A) :
    DifferentiableOn ℂ (angularFiniteHeckeDual S a N ε A k) {s : ℂ | s.re < 1} := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  have hp : Differentiable ℂ (fun s : ℂ => (A:ℂ)^(1-2*s)) :=
    (differentiable_const_cpow_of_neZero _).comp (by fun_prop)
  have hd : Differentiable ℂ (fun s : ℂ => finiteNormDirichlet S a N (1-s)) :=
    (differentiable_finiteNormDirichlet S a N hN).comp (by fun_prop)
  exact ((hp.const_mul ε).differentiableOn.mul
    (differentiableOn_angularGammaFEQuotient hk)).mul hd.differentiableOn

/-- The finite retained dual polynomial admits the actual contour move.
Its coefficients are unchanged during the move. -/
theorem angular_finite_dual_contour_shift {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {k : ℝ} (hk : 0 ≤ k) {A Z b : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (hb : b ≤ 1/2)
    (hGamma : AngularGammaQuotientStripBound k b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    (∫ τ : ℝ, mellin W (b+(τ:ℂ)*Complex.I)*(Z:ℂ)^(b+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S a N ε A k (b+((τ-t:ℝ):ℂ)*Complex.I)) =
    ∫ τ : ℝ, mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S a N ε A k ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) := by
  obtain ⟨Cg,n,hCg,hg⟩ := hGamma
  let B := ‖ε‖*max 1 (A^(1-2*b))*Cg*(∑ i ∈ S, ‖a i‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoly (σ : ℝ) (hσ : σ ∈ Icc b (1/2:ℝ)) (τ : ℝ) :
      ‖angularFiniteHeckeDual S a N ε A k (σ+((τ-t:ℝ):ℂ)*Complex.I)‖ ≤ B*(1+|τ-t|)^n := by
    have hn := norm_finiteNormDirichlet_le S a N hN
      (1-(σ+((τ-t:ℝ):ℂ)*Complex.I)) (by simp; linarith [hσ.2])
    have hpow := norm_conductor_power_strip (u := τ-t) hA hσ
    have hgam := hg σ hσ (τ-t)
    unfold angularFiniteHeckeDual
    simp only [norm_mul]
    calc
      _ ≤ ‖ε‖*max 1 (A^(1-2*b))*(Cg*(1+|τ-t|)^n)*(∑ i ∈ S, ‖a i‖) := by gcongr
      _ = _ := by dsimp [B]; ring
  let f : ℂ → ℂ := fun s => mellin W s*(Z:ℂ)^s*
    angularFiniteHeckeDual S a N ε A k (s-(t:ℂ)*Complex.I)
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hZ).ne'⟩
  have hshift : DifferentiableOn ℂ (fun s : ℂ =>
      angularFiniteHeckeDual S a N ε A k (s-(t:ℂ)*Complex.I)) (closedVerticalStrip b (1/2)) := by
    apply (differentiableOn_angularFiniteHeckeDual S a N
      (fun i hi => lt_of_lt_of_le zero_lt_one (hN i hi)) ε hk hA).comp
      (differentiable_id.sub_const _).differentiableOn
    intro s hs
    change (s-(t:ℂ)*Complex.I).re < 1
    have hsr := hs.2
    simpa using lt_of_le_of_lt hsr (by norm_num : (1/2:ℝ) < 1)
  have hf : DifferentiableOn ℂ f (closedVerticalStrip b (1/2)) :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).mul
      (differentiable_const_cpow_of_neZero _)).differentiableOn.mul hshift
  obtain ⟨K,_,hK⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t
    (angularFiniteHeckeDual S a N ε A k) hB n hpoly
  have he (σ τ : ℝ) : f (σ+(τ:ℂ)*Complex.I) =
      mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        angularFiniteHeckeDual S a N ε A k (σ+((τ-t:ℝ):ℂ)*Complex.I) := by
    dsimp [f]
    congr 2
    push_cast
    ring
  have hc := mellin_contour_shift_of_majorant hb f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 (by intro σ hσ τ; rw [he]; exact hK σ hσ τ)
  simp_rw [he] at hc
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hc

lemma angular_finite_dual_strip_growth {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {k : ℝ} (_hk : 0 ≤ k) {A b : ℝ} (hA : 0 < A) (hGamma : AngularGammaQuotientStripBound k b) :
    ∃ (B : ℝ) (n : ℕ), 0 ≤ B ∧ ∀ σ ∈ Icc b (1/2:ℝ), ∀ u : ℝ,
      ‖angularFiniteHeckeDual S a N ε A k (σ+(u:ℂ)*Complex.I)‖ ≤ B*(1+|u|)^n := by
  obtain ⟨Cg,n,hCg,hg⟩ := hGamma
  let B := ‖ε‖*max 1 (A^(1-2*b))*Cg*(∑ i ∈ S, ‖a i‖)
  refine ⟨B,n,by dsimp [B]; positivity,?_⟩
  intro σ hσ u
  have hn := norm_finiteNormDirichlet_le S a N hN (1-(σ+(u:ℂ)*Complex.I))
    (by simp; linarith [hσ.2])
  have hpow := norm_conductor_power_strip (u := u) hA hσ
  have hgam := hg σ hσ u
  unfold angularFiniteHeckeDual
  simp only [norm_mul]
  calc
    _ ≤ ‖ε‖*max 1 (A^(1-2*b))*(Cg*(1+|u|)^n)*(∑ i ∈ S, ‖a i‖) := by gcongr
    _ = _ := by dsimp [B]; ring


end CubicFirstMoment

end

end OAI
