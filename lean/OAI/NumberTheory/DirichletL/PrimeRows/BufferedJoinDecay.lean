import OAI.NumberTheory.DirichletL.PrimeRows.BufferedHeightGrowth
import OAI.NumberTheory.DirichletL.PrimeRows.BufferedSlices

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_height_uniform {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_height_growth e he he' S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro a B H i ha haTop hB hH hbin σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound a B H i ha haTop hB hH hbin ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem buffered_x_slice_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_height_uniform e he he' S hS hmax hfirst P hPS η u hu ψ r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A*D,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow a B H i ha haTop hB hH hbin σ hσ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
