import OAI.NumberTheory.DirichletL.Detector.CentralAllSlots
import OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralPrimeSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralAllSlots
local notation "O" => HeckeFamily.O

theorem actual_central_prime_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset PrimeIdeal) (hPS : ∀j P,P∈T j→P.val∉S),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      |x.im|≤(3*i+2:ℕ)*T0 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
        (fun j=>hPS j (P j).val (P j).property) W Y x w z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Ca,hCa,hall⟩ := actual_three_branch_slots N e eps c d B he he1 heps hc hd hB
  obtain ⟨Cb,hCb,hcost⟩ := central_remaining_rowCost_bound e eps he he1 heps S hS hfirst
  refine ⟨Ca*Cb,mul_pos hCa hCb,?_⟩
  intro u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hPS hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hxi hwi p hp hphase
  let hs : ∀j P,P∈T j→Supported P.val := fun j P hP=>outside_prime_supported S hS.bad P (hPS j P hP)
  have hinj (P : ∀j,T j) : Function.Injective (fun j=>(P j).val) := by
    intro j l hh
    change (P j).val=(P l).val at hh
    by_contra hne
    exact Finset.disjoint_left.mp (hdis j l hne) (P j).property (by rw [hh];exact (P l).property)
  have ha' := hall S hS.prime hmax hS.bad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
    W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  have hc' := hcost η u twists T0 a ((3*i+2:ℕ)*T0) i hT0 ha ha1 le_rfl hbin x w z hx hw hz hxi
  have hN : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hy : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (zero_le_one.trans (hY j)) _)
  have hpp : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hinj W Y a e x w z
    hfirst ha ha1 he he1.le hx hw hz hQ hη hsmall,centralRowScalar_split,norm_mul,norm_mul]
  have hn := mul_le_mul_of_nonneg_left ha' (norm_nonneg (centralRemainingScalar S hS η u x w z))
  have hc'' := mul_le_mul_of_nonneg_right hc'
    (show 0≤Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) by positivity)
  have hpow : rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1))=
      rowNorm u^(a-1/2+12*e+eps*(N+8)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = ‖centralRemainingScalar S hS η u x w z‖*
      (‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖) := by ring
    _ ≤ ‖centralRemainingScalar S hS η u x w z‖*
      (Ca*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0)*
        rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hn
    _ = (‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by ring
    _ ≤ (Cb*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+(3*i+2:ℕ)*T0)^(2+4*eps))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hc''
    _ = _ := by
      calc
        _ = Ca*Cb*(η.modulus.absNorm:ℝ)^(2*eps)*(rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1)))*
          (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeCentralPrimeSum

end

end OAI
