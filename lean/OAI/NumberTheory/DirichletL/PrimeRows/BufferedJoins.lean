import OAI.NumberTheory.DirichletL.PrimeRows.HorizontalIntegral

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem buffered_horizontal_join_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := buffered_x_slice_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr
  refine ⟨2*C,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  let A : ℝ := C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (mul_nonneg hC (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
