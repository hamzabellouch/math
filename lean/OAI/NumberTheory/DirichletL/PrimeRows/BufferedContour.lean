import OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalContour

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma reciprocal_differentiableAt_of_nonzero (χ : Character) (s : ℂ) (h0 : s≠0)
    (hnz : ¬(χ.residue=1 ∧ s=1) → LFunction χ s≠0) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal χ) s := by
  by_cases hχ : χ.residue=1
  · have hr : HeckeReciprocal.regularizedL χ s≠0 := by
      by_cases hs : s=1
      · subst s
        exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ
      · rw [HeckeReciprocal.regularizedL_eq χ h0 hs]
        exact mul_ne_zero (sub_ne_zero.mpr hs) (hnz (by simp [hs]))
    have he : HeckeReciprocal.reciprocal χ=(fun z=>(z-1)/HeckeReciprocal.regularizedL χ z) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_left hχ]
    rw [he]
    exact (differentiableAt_id.sub_const 1).div
      (HeckeReciprocal.regularizedL_differentiableAt χ h0) hr
  · have he : HeckeReciprocal.reciprocal χ=(fun z=>(LFunction χ z)⁻¹) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_right hχ]
    rw [he]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv (hnz (by simp [hχ]))

theorem physicalCompensatedRow_buffered_differentiableAt_x
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  have hx0 : x≠0 := by intro h;norm_num [h] at hx
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (reciprocal_differentiableAt_of_nonzero _ x hx0 hnz).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) :
    Differentiable ℂ (fun x=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hz)

theorem continuedPhysicalRowKernel_buffered_differentiableAt_x {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x :=
  (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    ((physicalCompensatedRow_buffered_differentiableAt_x eps heps S hS hfirst _
      (contourTupleOutside S P hPS) η u x w z hx hw hz hxw hnz).const_mul _)

theorem buffered_x_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r T : ℝ)
    (hl : (51/100:ℝ)≤l) (hr : (51/100:ℝ)≤r) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hlw : 1+eps≤l+w.re) (hrw : 1+eps≤r+w.re)
    (hnz : ∀x∈(uIcc l r ×ℂ uIcc (-T) T),
      ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
        LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro x hx
    have hxlo : min l r≤x.re := hx.1.1
    have hx' : (51/100:ℝ)≤x.re := (le_min hl hr).trans hxlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-w.re≤l) (by linarith : 1+eps-w.re≤r)).trans hxlo
      linarith
    exact (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hZ x w z hx' hw hz hxw (hnz x hx)).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end SevenEighths.ProbeHighRowFamily

end

end OAI
