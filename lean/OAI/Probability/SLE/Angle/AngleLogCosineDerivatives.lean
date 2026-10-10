import OAI.Probability.SLE.Angle.AngleLogCosine

namespace OAI

/-! Brownian second derivative and physical Loewner directional derivative
of the actual cosine coordinate. -/
noncomputable section

namespace SLEExactGauge

lemma logCosine_spatial_second {κ : ℝ} (hκ : 0≤κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (logCosine κ q) x=
      -3*κ*(q.1.re-Real.sqrt κ*x)*Real.exp (2*q.1.im)*logInverseNorm κ q x/
        greenLogNormSq κ q x^2 := by
  have hd : deriv (logCosine κ q)=fun y =>
      -Real.sqrt κ*Real.exp (2*q.1.im)*logInverseNorm κ q y/greenLogNormSq κ q y :=
    funext (fun y => (logCosine_spatial κ q y).deriv)
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  have hcalc := ((logInverseNorm_spatial κ q x).const_mul
    (-Real.sqrt κ*Real.exp (2*q.1.im))).div hN (greenLogNormSq_pos κ q x).ne'
  conv_lhs => rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [hd]
  change HasDerivAt (fun y => -Real.sqrt κ*Real.exp (2*q.1.im)*
    logInverseNorm κ q y/greenLogNormSq κ q y) _ x at hcalc
  rw [hcalc.deriv]
  have hsq := Real.sq_sqrt hκ
  have hn := (greenLogNormSq_pos κ q x).ne'
  generalize Real.sqrt κ = r at *
  field_simp
  rw [← hsq]
  ring

lemma logInverseNorm_directional (κ : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logInverseNorm κ r x) q v =
      -logInverseNorm κ q x*((q.1.re-Real.sqrt κ*x)*v.1.re+
        Real.exp (2*q.1.im)*v.1.im)/greenLogNormSq κ q x := by
  have hr : HasDerivAt (fun t : ℝ => (q+t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add,Prod.smul_fst,Complex.add_re,Complex.smul_re,smul_eq_mul,
      id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const v.1.re).const_add q.1.re
  have hi : HasDerivAt (fun t : ℝ => (q+t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add,Prod.smul_fst,Complex.add_im,Complex.smul_im,smul_eq_mul,
      id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const v.1.im).const_add q.1.im
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q+t • v) x)
      (2*(q.1.re-Real.sqrt κ*x)*v.1.re+2*Real.exp (2*q.1.im)*v.1.im) 0 := by
    convert ((hr.sub_const (Real.sqrt κ*x)).pow 2).add ((hi.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul,add_zero,Nat.cast_ofNat]
    ring
  have hcalc := ((hN.log (by simpa only [zero_smul,add_zero] using
    (greenLogNormSq_pos κ q x).ne')).neg.div_const 2).exp
  have hline : HasDerivAt (fun t : ℝ => logInverseNorm κ (q+t • v) x)
      (-logInverseNorm κ q x*((q.1.re-Real.sqrt κ*x)*v.1.re+
        Real.exp (2*q.1.im)*v.1.im)/greenLogNormSq κ q x) 0 := by
    simp only [logInverseNorm_eq]
    apply hcalc.congr_deriv
    simp only [Pi.neg_apply,zero_smul,add_zero]
    ring
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun r : ℂ × ℝ => logInverseNorm κ r x) :=
    (logInverseNorm_contDiff κ).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => logInverseNorm κ r x)
      (fderiv ℝ (fun r : ℂ × ℝ => logInverseNorm κ r x) q) (q+(0:ℝ) • v) := by
    simpa only [zero_smul,add_zero] using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

lemma logCosine_directional (κ : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logCosine κ r x) q v =
      v.1.re*logInverseNorm κ q x-(q.1.re-Real.sqrt κ*x)*logInverseNorm κ q x*
        ((q.1.re-Real.sqrt κ*x)*v.1.re+Real.exp (2*q.1.im)*v.1.im)/greenLogNormSq κ q x := by
  let X : (ℂ × ℝ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)
  have hx := (X.hasFDerivAt (x := q)).sub_const (Real.sqrt κ*x)
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun r : ℂ × ℝ => logInverseNorm κ r x) :=
    (logInverseNorm_contDiff κ).comp (contDiff_id.prodMk contDiff_const)
  have he := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℝ => L v)
    (hx.mul ((hcd.differentiable (by simp)) q).hasFDerivAt).fderiv
  change fderiv ℝ (fun r : ℂ × ℝ => logCosine κ r x) q v = _ at he
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,
    X,ContinuousLinearMap.comp_apply,Complex.reCLM_apply,
    logInverseNorm_directional]
  change (q.1.re-Real.sqrt κ*x)*(-logInverseNorm κ q x*((q.1.re-Real.sqrt κ*x)*v.1.re+
    Real.exp (2*q.1.im)*v.1.im)/greenLogNormSq κ q x)+logInverseNorm κ q x*v.1.re = _
  ring

lemma logCosine_physical_direction (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logCosine κ r x) q
      (physicalLogLoewnerField (Real.sqrt κ*x) q)=
      4*(q.1.re-Real.sqrt κ*x)*Real.exp (2*q.1.im)*logInverseNorm κ q x/
        greenLogNormSq κ q x^2 := by
  rw [logCosine_directional]
  obtain ⟨hr,hi,_⟩ := physicalLogLoewnerField_components κ q x
  rw [hr,hi]
  have hn := (greenLogNormSq_pos κ q x).ne'
  field_simp
  unfold greenLogNormSq
  ring

end SLEExactGauge

end

end OAI
