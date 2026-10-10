import OAI.NumberTheory.DirichletL.PrimeRows.ZContour
import OAI.NumberTheory.DirichletL.PrimeRows.ZGrowth

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

private lemma norm_mul_seven_le {a b c d e f g : ℂ} {A B C D E F G : ℝ}
    (ha : ‖a‖≤A) (hb : ‖b‖≤B) (hc : ‖c‖≤C) (hd : ‖d‖≤D)
    (he : ‖e‖≤E) (hf : ‖f‖≤F) (hg : ‖g‖≤G) :
    ‖a*b*c*d*e*f*g‖≤A*B*C*D*E*F*G := by
  have hA := (norm_nonneg a).trans ha
  have hB := (norm_nonneg b).trans hb
  have hC := (norm_nonneg c).trans hc
  have hD := (norm_nonneg d).trans hd
  have hE := (norm_nonneg e).trans he
  have hF := (norm_nonneg f).trans hf
  simp only [norm_mul]
  gcongr

def zRowScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_z_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      zRowScalar P u W1 X Y Z x w z*mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel zRowScalar sourceMellinWeight
  ring

lemma zRowScalar_bounded {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (x w : ℂ) (l r : ℝ) (hl : 0<l) :
    ∃A : ℝ,0≤A ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖zRowScalar P u W1 X Y Z x w ((v:ℂ)+t*I)‖≤A := by
  let B : Fin K→ℝ := fun i=>scaleBound (elementNorm (CompletedGauss.primaryGenerator (P i).val)) (l-1) (r-1)
  let A := scaleBound X (1/2-r) (1/2-l)*scaleBound Z (x.re+l-1) (x.re+r-1)*
    ‖(Y:ℂ)^(w-1)‖*Real.exp ((|x.re|+r+1)^2)*‖mellin W1 w‖*
    (∏i,B i)*scaleBound (elementNorm u.val) (-r) (-l)
  have hB (i : Fin K) : 0≤B i := (scaleBound_pos _ _ _).le
  have hBP : 0≤∏i,B i := Finset.prod_nonneg (fun i _=>hB i)
  have hscale (a b c : ℝ) : 0≤scaleBound a b c := (scaleBound_pos _ _ _).le
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro v hv t
  have hXb := cpow_le_scaleBound hX (1/2-((v:ℂ)+t*I))
    (show (1/2-((v:ℂ)+t*I)).re∈Icc (1/2-r) (1/2-l) by
      simpa using And.intro (sub_le_sub_left hv.2 (1/2)) (sub_le_sub_left hv.1 (1/2)))
  have hZb := cpow_le_scaleBound hZ (x+((v:ℂ)+t*I)-1)
    (show (x+((v:ℂ)+t*I)-1).re∈Icc (x.re+l-1) (x.re+r-1) by
      simpa using And.intro (by linarith [hv.1] : x.re+l-1≤x.re+v-1)
        (by linarith [hv.2] : x.re+v-1≤x.re+r-1))
  have hGb := gaussian_strip_norm_le x hl hv t
  have hPb : ‖∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((v:ℂ)+t*I)-1)‖≤∏i,B i := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro i hi
    apply cpow_le_scaleBound
      (elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)
    simpa using And.intro (sub_le_sub_right hv.1 1) (sub_le_sub_right hv.2 1)
  have hFb : ‖frequencyWeight (((v:ℂ)+t*I)) ⟨u.val,u.property.1⟩‖≤scaleBound (elementNorm u.val) (-r) (-l) := by
    apply cpow_le_scaleBound (elementNorm_pos _ u.property.1)
    simpa using And.intro (neg_le_neg hv.2) (neg_le_neg hv.1)
  exact (norm_mul_seven_le hXb hZb le_rfl hGb le_rfl hPb hFb).trans (le_max_left A 0)

theorem continuedPhysicalRowKernel_z_cauchy {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((v:ℂ)+t*I)‖≤B*cauchy t := by
  obtain ⟨A,hA,hscalar⟩ := zRowScalar_bounded S hS P hPS u W1 X Y Z hX hZ x w l r (by linarith)
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_z_bounded eps S hS hfirst _
    (contourTupleOutside S P hPS) η u x w hx hw hxw
  obtain ⟨D,hD,hm⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a b ha hW l r (by linarith) 2
  refine ⟨A*D*C,mul_nonneg (mul_nonneg hA hD.le) hC,?_⟩
  intro v hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w ((v:ℂ)+t*I)‖≤C := by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans (hrow _ (by simpa using hl.trans hv.1))
  have hm' : ‖mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) ((v:ℂ)+t*I)‖≤D*cauchy t :=
    CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm v hv t)
  rw [continuedPhysicalRowKernel_z_factor,norm_mul,norm_mul]
  calc
    _ ≤ A*(D*cauchy t)*C := mul_le_mul (mul_le_mul (hscalar v hv t) hm' (norm_nonneg _) hA)
      hr (norm_nonneg _) (mul_nonneg hA (mul_nonneg hD.le (cauchy_nonneg t)))
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
