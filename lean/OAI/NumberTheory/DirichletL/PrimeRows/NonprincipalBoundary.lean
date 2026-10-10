import OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalContour

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowKernelScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (x z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_w_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      rowKernelScalar P u W0 X Z x z*(Y:ℂ)^(w-1)*mellin W1 w*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel rowKernelScalar sourceMellinWeight
  ring

theorem continuedPhysicalRowKernel_cauchy {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤C)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((v:ℂ)+t*I) z‖≤B*cauchy t := by
  obtain ⟨D,hD,hm⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a b ha hW
    (W1.smooth ⊤) l r (N+2)
  have hscale := (scaleBound_pos Y (l-1) (r-1)).le
  let A := ‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*C
  refine ⟨A*D,by dsimp [A]; positivity,?_⟩
  intro v hv t
  have hYbd := cpow_le_scaleBound hY (((v:ℂ)+t*I)-1)
    (show (((v:ℂ)+t*I)-1).re∈Icc (l-1) (r-1) by simpa using hv)
  have hm' : height t^2*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖)≤D := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using hm v hv t
  have hmc : height t^N*‖mellin W1 ((v:ℂ)+t*I)‖≤D*cauchy t :=
    CubicReflectionKernel.weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le N) (norm_nonneg _)) t hm'
  rw [continuedPhysicalRowKernel_w_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*
        ‖mellin W1 ((v:ℂ)+t*I)‖)*(C*height t^N) := by
      apply mul_le_mul _ (hpoly v hv t) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYbd (norm_nonneg _)) (norm_nonneg _)
    _ = A*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖) := by dsimp [A]; ring
    _ ≤ A*(D*cauchy t) := mul_le_mul_of_nonneg_left hmc (by dsimp [A]; positivity)
    _ = _ := by ring

theorem nonprincipal_w_integral_eq_of_polynomial {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤C)
    (hlr : l≤r) (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l)
    (hz : (17/50:ℝ)≤z.re) (hxl : 1+eps≤x.re+l)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW
    X Y Z hY x z l r C N hC hpoly
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro w hw
  exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x w z hx (hl.trans hw.1) hz (by linarith [hw.1])).differentiableWithinAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
