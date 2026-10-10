import OAI.NumberTheory.DirichletL.PrimeRows.ZBoundary

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem first_z_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hx hw (by linarith) hl
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro z hz
  exact (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hX hZ x w z hx hw (hl.trans hz.1) hxw).differentiableWithinAt

lemma first_z_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    Integrable (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I)) := by
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l l hx hw (by linarith) hl
  have hc : Continuous (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hX hZ x w ((l:ℂ)+t*I) hx hw (by simpa using hl) hxw).continuousAt.comp
        (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_z_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (F : Finset FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  rw [integral_finsetSum F (fun u hu=>first_z_vertical_integrable eps heps S hS hfirst hmax P hPS η u
      W0 W1 a b ha hW X Y Z hX hZ x w l hx hw hxw hl),
    integral_finsetSum F (fun u hu=>first_z_vertical_integrable eps heps S hS hfirst hmax P hPS η u
      W0 W1 a b ha hW X Y Z hX hZ x w r hx hw hxw (hl.trans hlr))]
  exact Finset.sum_congr rfl (fun u hu=>first_z_integral_eq eps heps S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hlr hx hw hxw hl)

end SevenEighths.ProbeHighRowFamily

end

end OAI
