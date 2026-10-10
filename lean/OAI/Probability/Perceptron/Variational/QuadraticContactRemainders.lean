import Mathlib
import OAI.Probability.Perceptron.Interpolation.TiltReplicaCoordinate

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
lemma quadratic_contact_remainders {A : ℝ → ℝ} {u a c s dA : ℝ}
    (hd : HasDerivAt A dA u)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-A t) u)
    (hp : c*(u-a)^2-A u ≤ c*(u+s-a)^2-A (u+s))
    (hm : c*(u-a)^2-A u ≤ c*(u-s-a)^2-A (u-s)) :
    A (u+s)-A u-s*dA ≤ c*s^2 ∧ A (u-s)-A u+s*dA ≤ c*s^2 := by
  have he := hmin.hasDerivAt_eq_zero
    (((((hasDerivAt_id u).sub_const a).pow 2).const_mul c).sub hd)
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at he
  constructor <;> nlinarith [congrArg (fun t : ℝ => t*s) he]

lemma integral_convex_contact_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ → ℝ} {A : ℝ → ℝ}
    {d : Ω → ℝ} {u s dA C δ : ℝ} (hs : 0 < s)
    (hdm : AEStronglyMeasurable d P)
    (hf : ∀ᵐ ω ∂P, ConvexOn ℝ univ (f ω) ∧ HasDerivAt (f ω) (d ω) u)
    (hp : A (u+s)-A u-s*dA ≤ C*s^2) (hm : A (u-s)-A u+s*dA ≤ C*s^2)
    (hip : Integrable (fun ω => f ω (u+s)) P)
    (hi0 : Integrable (fun ω => f ω u) P)
    (him : Integrable (fun ω => f ω (u-s)) P)
    (hbp : (∫ ω, |f ω (u+s)-A (u+s)| ∂P) ≤ δ)
    (hb0 : (∫ ω, |f ω u-A u| ∂P) ≤ δ)
    (hbm : (∫ ω, |f ω (u-s)-A (u-s)| ∂P) ≤ δ) :
    (∫ ω, |d ω-dA| ∂P) ≤ C*s+4*δ/s := by
  have ip := (hip.sub (integrable_const (A (u+s)))).abs
  have i0 := (hi0.sub (integrable_const (A u))).abs
  have im := (him.sub (integrable_const (A (u-s)))).abs
  let B := fun ω => C*s+(|f ω (u+s)-A (u+s)|+2*|f ω u-A u|+|f ω (u-s)-A (u-s)|)/s
  have hB : Integrable B P := (integrable_const (C*s)).add ((ip.add (i0.const_mul 2) |>.add im).div_const s)
  have hbound : ∀ᵐ ω ∂P, |d ω-dA| ≤ B ω := hf.mono fun ω hω =>
    convex_contact_derivative_bound hs hω.1 hω.2 hp hm
  have hi : Integrable (fun ω => |d ω-dA|) P := hB.mono'
    (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hdm.sub aestronglyMeasurable_const).norm) (hbound.mono fun ω hω => by simpa using hω)
  calc
    _ ≤ ∫ ω, B ω ∂P := integral_mono_ae hi hB hbound
    _ = C*s+((∫ ω, |f ω (u+s)-A (u+s)| ∂P)+
        2*(∫ ω, |f ω u-A u| ∂P)+(∫ ω, |f ω (u-s)-A (u-s)| ∂P))/s := by
      have he := integral_add (integrable_const (C*s)) ((ip.add (i0.const_mul 2) |>.add im).div_const s)
      have he' := integral_add (ip.add (i0.const_mul 2)) im
      have he'' := integral_add ip (i0.const_mul 2)
      simp only [Pi.add_apply,Pi.sub_apply] at he he' he''
      dsimp only [B]
      rw [he,integral_div,he',he'']
      simp [integral_const_mul]
    _ ≤ _ := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hs.le
      linarith

lemma integral_centered_abs_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω-∫ η, X η ∂P| ∂P) ≤ Real.sqrt (variance X P) := by
  have hC : MemLp (fun ω => X ω-∫ η, X η ∂P) 2 P := hX.sub (memLp_const _)
  have hA := hC.norm
  have hv := variance_nonneg (fun ω => |X ω-∫ η, X η ∂P|) P
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs] using hA)] at hv
  simp only [Pi.pow_apply,sq_abs] at hv
  rw [← variance_eq_integral hX.aestronglyMeasurable.aemeasurable] at hv
  apply (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) (variance_nonneg X P)).mpr
  linarith

end SphericalPerceptronFreeEnergy

end

end OAI
