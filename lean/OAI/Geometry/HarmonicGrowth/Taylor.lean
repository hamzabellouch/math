import Mathlib

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.PulseTaylor

/-- Two applications of the mean value theorem, retaining the derivative
remainder needed for C1 control of a slow pulse. -/
theorem quadratic_remainder {f f' f'' : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ x ∈ Icc (1/2:ℝ) (3/2),HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (1/2:ℝ) (3/2),HasDerivAt f' (f'' x) x)
    (hb : ∀ x ∈ Icc (1/2:ℝ) (3/2),|f'' x| ≤ C) :
    ∀ q ∈ Icc (1/2:ℝ) (3/2),
      |f q-f 1-(q-1)*f' 1| ≤ C*(q-1)^2 ∧ |f' q-f' 1| ≤ C*|q-1| := by
  intro q hq
  have h1 : (1:ℝ) ∈ Icc (1/2:ℝ) (3/2) := by norm_num
  have hder (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) (3/2)) :
      |f' x-f' 1| ≤ C*|x-1| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (1/2:ℝ) (3/2)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy => (hf' y hy).hasDerivWithinAt)
        (fun y hy => by simpa only [Real.norm_eq_abs] using hb y hy) h1 hx
  refine ⟨?_,hder q hq⟩
  let g : ℝ → ℝ := fun x => f x-f 1-(x-1)*f' 1
  have hsub : uIcc (1:ℝ) q ⊆ Icc (1/2:ℝ) (3/2) := uIcc_subset_Icc h1 hq
  have hd (x : ℝ) (hx : x ∈ uIcc (1:ℝ) q) : HasDerivAt g (f' x-f' 1) x := by
    simpa only [g,Pi.sub_apply,id_eq,one_mul] using
      ((hf x (hsub hx)).sub_const (f 1)).fun_sub (((hasDerivAt_id x).sub_const 1).mul_const (f' 1))
  have hdist (x : ℝ) (hx : x ∈ uIcc (1:ℝ) q) : |x-1| ≤ |q-1| := by
    rw [mem_uIcc] at hx
    rcases hx with hx|hx
    · rw [abs_of_nonneg (by linarith : 0 ≤ x-1),abs_of_nonneg (by linarith : 0 ≤ q-1)]
      linarith
    · rw [abs_of_nonpos (by linarith : x-1 ≤ 0),abs_of_nonpos (by linarith : q-1 ≤ 0)]
      linarith
  have hh := (convex_uIcc (1:ℝ) q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt)
    (fun x hx => show ‖f' x-f' 1‖ ≤ C*|q-1| from
      (hder x (hsub hx)).trans (mul_le_mul_of_nonneg_left (hdist x hx) hC))
    (left_mem_uIcc) (right_mem_uIcc)
  have habs : |q-1| * |q-1|=(q-1)^2 := by rw [← sq, sq_abs]
  simpa only [g,sub_self,zero_mul,sub_zero,Real.norm_eq_abs,mul_assoc,habs] using hh

/-- The scalar power appearing in the genuine Berger angular operator has a
uniform quadratic value remainder AND a uniform linear derivative remainder. -/
theorem rpow_remainder (r : ℝ) : ∃ C : ℝ,0 ≤ C ∧
    ∀ q ∈ Icc (1/2:ℝ) (3/2),
      |q^r-1-r*(q-1)| ≤ C*(q-1)^2 ∧
      |r*q^(r-1)-r| ≤ C*|q-1| := by
  have hc : ContinuousOn (fun x : ℝ => r*(r-1)*x^(r-2)) (Icc (1/2:ℝ) (3/2)) := by
    apply continuousOn_const.mul
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (by change x ≠ 0; linarith [hx.1]))
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hf (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) (3/2)) :
      HasDerivAt (fun q : ℝ => q^r) (r*x^(r-1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))
  have hd (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) (3/2)) :
      HasDerivAt (fun q : ℝ => r*q^(r-1)) (r*(r-1)*x^(r-2)) x := by
    have hh := (Real.hasDerivAt_rpow_const (p := r-1) (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul r
    simpa only [sub_sub,show (1+1:ℝ)=2 by norm_num,mul_assoc] using hh
  have hh := quadratic_remainder hC hf hd
    (fun x hx => (hB x hx).trans (le_max_left _ _))
  refine ⟨C,hC,fun q hq => ?_⟩
  simpa only [Real.one_rpow,mul_one,mul_comm (q-1) r] using hh q hq

end HarmonicCounterexample.PulseTaylor

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.PulseTaylor
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact Berger angular coefficient, with b=B_l Id and D=D_J².
Here r=1/m, and the outer scalar a^{-2} is applied separately. -/
def angular (r : ℝ) (b D : E) (q : ℝ) : E :=
  q^r • b+(q^r-q^(r-1)) • D

def angularD (r : ℝ) (b D : E) (q : ℝ) : E :=
  (r*q^(r-1)) • b+(r*q^(r-1)-(r-1)*q^(r-2)) • D

lemma angular_eq_berger (r : ℝ) (b D : E) {q : ℝ} (hq : 0 < q) :
    angular r b D q=q^r • (b+(1-q⁻¹) • D) := by
  rw [angular,Real.rpow_sub hq,Real.rpow_one]
  simp only [smul_add,smul_smul,div_eq_mul_inv]
  congr 1
  congr 1
  ring

lemma angular_hasDerivAt (r : ℝ) (b D : E) {q : ℝ} (hq : q ≠ 0) :
    HasDerivAt (angular r b D) (angularD r b D q) q := by
  have h1 := Real.hasDerivAt_rpow_const (p := r) (Or.inl hq)
  have h2 := Real.hasDerivAt_rpow_const (p := r-1) (Or.inl hq)
  have hh := (h1.smul_const b).fun_add ((h1.fun_sub h2).smul_const D)
  change HasDerivAt (fun y : ℝ => y^r • b+(y^r-y^(r-1)) • D) _ q
  simpa only [angularD,sub_sub,show (1+1:ℝ)=2 by norm_num] using hh

lemma angular_one (r : ℝ) (b D : E) : angular r b D 1=b := by simp [angular]
lemma angularD_one (r : ℝ) (b D : E) : angularD r b D 1=r • b+D := by
  simp only [angularD,Real.one_rpow,mul_one,sub_sub_cancel,one_smul]

/-- Genuine uniform C1 Taylor control of the angular operator, rather than
an endpoint assertion or a formal Taylor expansion taken as an axiom. -/
theorem angular_remainder (r : ℝ) (b D : E) : ∃ C : ℝ,0 ≤ C ∧
    ∀ q ∈ Icc (1/2:ℝ) (3/2),
      ‖angular r b D q-b-(q-1) • (r • b+D)‖ ≤ C*(q-1)^2 ∧
      ‖angularD r b D q-(r • b+D)‖ ≤ C*|q-1| := by
  obtain ⟨C₁,hC₁,h₁⟩ := rpow_remainder r
  obtain ⟨C₂,hC₂,h₂⟩ := rpow_remainder (r-1)
  let C := C₁*‖b‖+(C₁+C₂)*‖D‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq
  have hv1 := (h₁ q hq).1
  have hv2 := (h₂ q hq).1
  have hd1 := (h₁ q hq).2
  have hd2 := (h₂ q hq).2
  have value_eq : angular r b D q-b-(q-1) • (r • b+D) =
      (q^r-1-r*(q-1)) • b+
        ((q^r-1-r*(q-1))-(q^(r-1)-1-(r-1)*(q-1))) • D := by
    dsimp [angular]
    module
  have deriv_eq : angularD r b D q-(r • b+D) =
      (r*q^(r-1)-r) • b+
        ((r*q^(r-1)-r)-((r-1)*q^((r-1)-1)-(r-1))) • D := by
    rw [show (r-1)-1=r-2 by ring]
    dsimp [angularD]
    module
  constructor
  · rw [value_eq]
    calc
      _ ≤ ‖(q^r-1-r*(q-1)) • b‖+
          ‖((q^r-1-r*(q-1))-(q^(r-1)-1-(r-1)*(q-1))) • D‖ := norm_add_le _ _
      _ ≤ (C₁*(q-1)^2)*‖b‖+((C₁+C₂)*(q-1)^2)*‖D‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
        have hs := (abs_sub _ _).trans (add_le_add hv1 hv2)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hv1 (norm_nonneg b)
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg D)
          nlinarith
      _ = C*(q-1)^2 := by dsimp [C]; ring
  · rw [deriv_eq]
    calc
      _ ≤ ‖(r*q^(r-1)-r) • b‖+
          ‖((r*q^(r-1)-r)-((r-1)*q^((r-1)-1)-(r-1))) • D‖ := norm_add_le _ _
      _ ≤ (C₁*|q-1|)*‖b‖+((C₁+C₂)*|q-1|)*‖D‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
        have hs := (abs_sub _ _).trans (add_le_add hd1 hd2)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hd1 (norm_nonneg b)
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg D)
          nlinarith
      _ = C*|q-1| := by dsimp [C]; ring

/-- Separation of the slowly varying scale from the small pulse. In the source
α=a(t)^{-2}, β=a_*^{-2}, δ=z/T. -/
lemma scaled_value_error {F b L : E} {α β δ C : ℝ}
    (hF : ‖F-b-δ • L‖ ≤ C*δ^2) :
    ‖α • F-α • b-(β*δ) • L‖ ≤
      |α| *C*δ^2+|α-β| *|δ| *‖L‖ := by
  have he : α • F-α • b-(β*δ) • L =
      α • (F-b-δ • L)+((α-β)*δ) • L := by module
  rw [he]
  calc
    _ ≤ ‖α • (F-b-δ • L)‖+‖((α-β)*δ) • L‖ := norm_add_le _ _
    _ = |α| *‖F-b-δ • L‖+|α-β| *|δ| *‖L‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,mul_assoc]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hF (abs_nonneg α)]

lemma scaled_deriv_error {F L : E} {α β δ C : ℝ}
    (hF : ‖F-L‖ ≤ C*|δ|) :
    ‖α • F-β • L‖ ≤ |α| *C*|δ|+|α-β| *‖L‖ := by
  have he : α • F-β • L=α • (F-L)+(α-β) • L := by module
  rw [he]
  calc
    _ ≤ ‖α • (F-L)‖+‖(α-β) • L‖ := norm_add_le _ _
    _ = |α| *‖F-L‖+|α-β| *‖L‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hF (abs_nonneg α)]

end HarmonicCounterexample.PulseTaylor

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.PulseTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform value AND parameter-direction remainders for the exact slowly
scaled Berger operator. No coefficient approximation is a hypothesis. -/
theorem berger_slow_pulse_remainders (r : ℝ) (b D : E) {M Z : ℝ}
    (hM : 0 ≤ M) (hZ : 0 ≤ Z) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ α β δ τ z zh : ℝ,
      0 ≤ δ → 0 ≤ τ → |α| ≤ M → |α-β| ≤ δ → |z| ≤ Z → |zh| ≤ Z →
      1+τ*z ∈ Set.Icc (1/2:ℝ) (3/2) →
      ‖α • angular r b D (1+τ*z)-α • b-(β*τ*z) • (r • b+D)‖ ≤ C*(δ*τ+τ^2) ∧
      ‖(τ*zh) • (α • angularD r b D (1+τ*z)-β • (r • b+D))‖ ≤ C*(δ*τ+τ^2) := by
  obtain ⟨C₀,hC₀,hrem⟩ := angular_remainder r b D
  let L := r • b+D
  let C := M*C₀*Z^2+Z*‖L‖
  have hC : 0 ≤ C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro α β δ τ z zh hδ hτ hα hscale hz hzh hq
  obtain ⟨hval,hder⟩ := hrem (1+τ*z) hq
  have he : 1+τ*z-1=τ*z := by ring
  rw [he] at hval hder
  have hp : |τ*z| ≤ τ*Z := by rw [abs_mul,abs_of_nonneg hτ];gcongr
  have hsq : (τ*z)^2 ≤ τ^2*Z^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg (τ*z)) hp
    simpa only [← sq,sq_abs,mul_pow] using hh
  have hcτ : 0 ≤ δ*τ := mul_nonneg hδ hτ
  have hC₁ : M*C₀*Z^2 ≤ C := by dsimp [C];exact le_add_of_nonneg_right (by positivity)
  have hC₂ : Z*‖L‖ ≤ C := by dsimp [C];exact le_add_of_nonneg_left (by positivity)
  have htarget : M*C₀*τ^2*Z^2+δ*τ*Z*‖L‖ ≤ C*(δ*τ+τ^2) := by
    have h₁ := mul_le_mul_of_nonneg_right hC₁ (sq_nonneg τ)
    have h₂ := mul_le_mul_of_nonneg_right hC₂ hcτ
    nlinarith
  constructor
  · have hv := scaled_value_error (α := α) (β := β) hval
    rw [show β*(τ*z)=β*τ*z by ring] at hv
    apply hv.trans
    calc
      |α| *C₀*(τ*z)^2+|α-β| *|τ*z| *‖r • b+D‖ ≤
          M*C₀*(τ^2*Z^2)+δ*(τ*Z)*‖L‖ := by
            dsimp only [L]
            gcongr
      _ ≤ _ := by nlinarith [htarget]
  · have hd := scaled_deriv_error (α := α) (β := β) hder
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hτ]
    calc
      τ*|zh| *‖α • angularD r b D (1+τ*z)-β • (r • b+D)‖ ≤
          τ*Z*(M*C₀*(τ*Z)+δ*‖L‖) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hzh hτ) _ (norm_nonneg _) (by positivity)
            apply hd.trans
            dsimp only [L]
            gcongr
      _ ≤ _ := by nlinarith [htarget]

end HarmonicCounterexample.PulseTaylor

end

end OAI
