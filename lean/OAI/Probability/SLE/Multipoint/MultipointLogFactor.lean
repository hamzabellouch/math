import OAI.Probability.SLE.ClippedCoordinates

namespace OAI

/-! Smooth logarithmic-coordinate monomials for the multipoint factors.
The three monomials in each regularized factor have this form. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge.Multipoint

def logFactor (κ c r : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp ((c*κ/4)*q.2+(r-c*κ/4)*q.1.im-(r/2)*Real.log (greenLogNormSq κ q x))

lemma logFactor_pos (κ c r : ℝ) (q : ℂ × ℝ) (x : ℝ) : 0 < logFactor κ c r q x :=
  Real.exp_pos _

lemma logFactor_contDiff (κ c r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => logFactor κ c r p.1 p.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) :=
    ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add
      ((contDiff_const.mul him).exp)
  have hlog := hN.log (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')
  unfold logFactor
  exact ((contDiff_const.mul contDiff_fst.snd).add
    (contDiff_const.mul him) |>.sub (contDiff_const.mul hlog)).exp

lemma logFactor_spatial_derivative (κ c r : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (logFactor κ c r q)
      (logFactor κ c r q x * (r*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x)) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  have hlog := hN.log (greenLogNormSq_pos κ q x).ne'
  have hd := ((hasDerivAt_const x ((c*κ/4)*q.2+(r-c*κ/4)*q.1.im)).sub
    (hlog.const_mul (r/2))).exp
  convert hd using 1 <;> try rfl
  dsimp only [logFactor, Pi.sub_apply, Pi.mul_apply, Function.comp_def]
  ring

lemma logFactor_spatial_second (κ c r : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (logFactor κ c r q) x =
      logFactor κ c r q x * κ*r*((r+1)*(q.1.re-Real.sqrt κ*x)^2-Real.exp (2*q.1.im)) /
        (greenLogNormSq κ q x)^2 := by
  have hd : deriv (logFactor κ c r q) = fun x =>
      logFactor κ c r q x*(r*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x) :=
    funext (fun x => (logFactor_spatial_derivative κ c r q x).deriv)
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  have hcoef := (hX.const_mul (r*Real.sqrt κ)).div hN (greenLogNormSq_pos κ q x).ne'
  have hsecond := (logFactor_spatial_derivative κ c r q x).mul hcoef
  rw [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq] at hsecond
  change HasDerivAt (fun y => logFactor κ c r q y *
    (r*Real.sqrt κ*(q.1.re-Real.sqrt κ*y)/greenLogNormSq κ q y)) _ x at hsecond
  rw [hsecond.deriv]
  dsimp only [greenLogNormSq]
  generalize logFactor κ c r q x = f
  generalize q.1.re-Real.sqrt κ*x = X
  generalize Real.exp (2*q.1.im) = Y
  have hs := Real.sq_sqrt hκ
  generalize Real.sqrt κ = v at *
  rw [← hs]
  field_simp
  ring

lemma logFactor_directional (κ c r : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun q => logFactor κ c r q x) q) v =
      logFactor κ c r q x*((c*κ/4)*v.2+(r-c*κ/4)*v.1.im-(r/2)*
        ((2*(q.1.re-Real.sqrt κ*x)*v.1.re+2*Real.exp (2*q.1.im)*v.1.im)/
          greenLogNormSq κ q x)) := by
  have hzre : HasDerivAt (fun t : ℝ => (q+t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_re, Complex.smul_re, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.re).const_add q.1.re
  have hzim : HasDerivAt (fun t : ℝ => (q+t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hj : HasDerivAt (fun t : ℝ => (q+t • v).2) v.2 0 := by
    simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, id_eq, one_mul]
      using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q+t • v) x)
      (2*(q.1.re-Real.sqrt κ*x)*v.1.re+2*Real.exp (2*q.1.im)*v.1.im) 0 := by
    convert ((hzre.sub_const (Real.sqrt κ*x)).pow 2).add ((hzim.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul, add_zero, Nat.cast_ofNat]
    ring
  have hlog := hN.log (by simpa only [zero_smul, add_zero] using (greenLogNormSq_pos κ q x).ne')
  have hcalc := ((hj.const_mul (c*κ/4)).add (hzim.const_mul (r-c*κ/4))).sub
    (hlog.const_mul (r/2))
  have hline : HasDerivAt (fun t : ℝ => logFactor κ c r (q+t • v) x)
      (logFactor κ c r q x*((c*κ/4)*v.2+(r-c*κ/4)*v.1.im-(r/2)*
        ((2*(q.1.re-Real.sqrt κ*x)*v.1.re+2*Real.exp (2*q.1.im)*v.1.im)/
          greenLogNormSq κ q x))) 0 := by
    convert hcalc.exp using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.add_apply, zero_smul, add_zero, logFactor]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun q => logFactor κ c r q x) :=
    (logFactor_contDiff κ c r).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun q => logFactor κ c r q x)
      (fderiv ℝ (fun q => logFactor κ c r q x) q) (q+(0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

/-- The source angular generator in actual capacity-two coordinates. -/
theorem logFactor_physical_generator (κ c r : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun q => logFactor κ c r q x) q)
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2 : ℝ)*iteratedDeriv 2 (logFactor κ c r q) x =
    logFactor κ c r q x * κ *
      ((r*(r-greenExponent κ)/2)*(q.1.re-Real.sqrt κ*x)^2+
        (c-r/2)*Real.exp (2*q.1.im)) / (greenLogNormSq κ q x)^2 := by
  rw [logFactor_directional, logFactor_spatial_second κ c r hκ.le]
  obtain ⟨hr, hi, hj⟩ := physicalLogLoewnerField_components κ q x
  rw [hr, hi, hj]
  have hp : κ*(greenExponent κ+1) = 8 := by
    simp only [greenExponent, sub_add_cancel]
    field_simp
  have hn := (greenLogNormSq_pos κ q x).ne'
  field_simp [hn]
  dsimp only [greenLogNormSq]
  linear_combination 4*logFactor κ c r q x*r*(q.1.re-Real.sqrt κ*x)^2*hp

end SLEExactGauge.Multipoint

end

end OAI
