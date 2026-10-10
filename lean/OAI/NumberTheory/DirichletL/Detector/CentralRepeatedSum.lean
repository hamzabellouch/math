import OAI.NumberTheory.DirichletL.Detector.CentralRepeatedProduct
import OAI.NumberTheory.DirichletL.Detector.CentralRepeatedChoices

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedChoices
open ProbeSelectedPrimeSums
local notation "O" => HeckeFamily.O

theorem actual_repeated_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(k : ℕ),k≤N → ∀(T : Fin k→Finset PrimeIdeal)
      (hs : ∀j P,P∈T j→Supported P.val),
      (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j,(Y j)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hprod⟩ := selected_repeated_product e eps he he1 heps
  obtain ⟨D,hD,hcount⟩ := active_card_subpower N eps heps
  let A := annularPower c d (-(4/25:ℝ))
  let E := (max 1 (812*B*A))^N
  have hA : 0≤A := annularPower_nonneg c d _ hc
  have hE : 0<E := by dsimp [E];positivity
  refine ⟨D*C*E,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin k hk T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi
  let R := rowCost S hS u a e eps ((3*i+2:ℕ)*T0)
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  have hR : 0≤R := rowCost_nonneg _ _ _ _ _ _ _
  have hY0 (j : Fin k) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hYY : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hY0 j).le _)
  have hterm (P : ∀j,T j) (hP : P∈activeChoices u T W Y) :
      L*(∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
        centralRepeatedTerm η u (P j).val (hs j (P j).val (P j).property) x w z‖)≤
      C*E*R*∏j,(Y j)^(-(4/25:ℝ)) := by
    have hp := (Finset.mem_filter.mp hP).2
    have hb := hprod S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k
      (fun j=>(P j).val) (fun j=>hs j (P j).val (P j).property) (hdis P)
      (fun j=>hη j (P j).val (P j).property) (fun j=>hQ j (P j).val (P j).property)
      (fun j=>hsmall j (P j).val (P j).property) (fun j=>(hp j).1)
      B W Y hB hW x w z hx hw hz hwi
    have hpow : (∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2))≤A^k*∏j,(Y j)^(-(4/25:ℝ)) := by
      have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j _=>Real.rpow_nonneg (show (0:ℝ)≤(P j).val.val.absNorm by positivity) (-(4/25:ℝ)))
        (fun j (_:j∈Finset.univ)=>annular_rpow c d (Y j) ((P j).val.val.absNorm:ℝ) (-(4/25:ℝ)) hc hd (hY0 j)
          ((le_div_iff₀ (hY0 j)).mp (hWS j (hp j).2).1)
          ((div_le_iff₀ (hY0 j)).mp (hWS j (hp j).2).2))
      norm_num only [hz,show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num] at ⊢
      simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
    have hEbound : (812*B)^k*A^k≤E := by
      rw [←mul_pow]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (812*B*A)) k).trans
        (pow_le_pow_right₀ (le_max_left 1 _) hk)
    calc
      _ ≤ C*(812*B)^k*R*∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2) := hb
      _ ≤ C*(812*B)^k*R*(A^k*∏j,(Y j)^(-(4/25:ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C*((812*B)^k*A^k)*R*∏j,(Y j)^(-(4/25:ℝ)) := by ring
      _ ≤ _ := by gcongr
  rw [sum_products_restrict η u T hs W Y x w z,Finset.mul_sum]
  have hh := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply hh.trans
  calc
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps)*(C*E*R*∏j,(Y j)^(-(4/25:ℝ))) :=
      mul_le_mul_of_nonneg_right (hcount k hk u T W Y) (by positivity)
    _ = _ := by dsimp [R];ring
end SevenEighths.ProbeCentralRepeatedSum

end

end OAI
