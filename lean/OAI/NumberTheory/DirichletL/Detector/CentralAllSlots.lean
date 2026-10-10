import OAI.NumberTheory.DirichletL.Detector.CentralBranchProduct
import OAI.NumberTheory.DirichletL.Detector.CentralRepeatedSubset
import OAI.NumberTheory.DirichletL.PrimeRows.CentralSlotSum

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeCentralRepeatedProduct
open ProbeCentralRepeatedSubset ProbeCentralBranchProduct
local notation "O" => HeckeFamily.O

def phaseSlot (u : FreeRow) (T : Finset PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑P:T,W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val.val))

theorem actual_three_branch_slots (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖ ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Cr,hCr,hregular⟩ := central_regular_slot_sum eps c d B heps hc hd hB
  obtain ⟨Ct,hCt,hrepeated⟩ := actual_repeated_subset N e eps c d B he he1 heps hc hd hB
  refine ⟨Ct*(Cr+2)^N,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  let R := Ct*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*U^eps
  let A : Fin N→ℂ := fun j=>phaseSlot u (T j) (W j) (Y j) z
  let E : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRegularError η u P.val (hs j P.val P.property) x w z
  let F : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRepeatedTerm η u P.val (hs j P.val P.property) x w z
  let yy : Fin N→ℝ := fun j=>(Y j)^(-(4/25:ℝ))
  have hU : 1≤U := by dsimp [U];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hUp : 1≤U^eps := Real.one_le_rpow hU heps.le
  have hR : 0≤R := by dsimp [R];exact mul_nonneg (mul_nonneg hCt.le (rowCost_nonneg _ _ _ _ _ _ _)) (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have hyy (j : Fin N) : 0≤yy j := Real.rpow_nonneg (zero_le_one.trans (hY j)) _
  have hE (j : Fin N) : ‖E j‖≤yy j*(Cr*U^eps) := by
    have hb := hregular η u (T j) (fun P hP=>⟨hs j P hP,hQ j P hP,hη j P hP⟩)
      (Y j) (hY j) (W j) (hWS j) (hW j) a e x w z ha ha1 he he1.le hx hw hz (hsmall j)
    exact (norm_sum_le _ _).trans (hb.trans_eq (by dsimp [yy,U];ring))
  have hF (J : Finset (Fin N)) : L*(∏j∈J,‖F j‖)≤R*(∏j∈J,yy j) := by
    have hb := hrepeated S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
      W Y hY hWS hW x w z hx hw hz hwi J
    have hp' : (∏j:J,‖F j.val‖)≤∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro j _
      exact norm_sum_le _ _
    have hh := (mul_le_mul_of_nonneg_left hp' (show 0≤L from norm_nonneg _)).trans hb
    rw [Finset.prod_coe_sort J (fun j=>‖F j‖),
      Finset.prod_coe_sort J (fun j=>(Y j)^(-(4/25:ℝ)))] at hh
    exact hh
  have hb := three_branch_bound L R (Cr*U^eps) A E F yy p (norm_nonneg _) hR (by positivity) hyy hp hphase hE hF
  have heq : (∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hs j P.val P.property) x w z)=∏j,(A j+E j+F j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [A,E,F,phaseSlot,centralNormalizedSlot_split,mul_add,Finset.sum_add_distrib]
  rw [heq]
  apply hb.trans
  have hcoef : (Cr*U^eps+2)^N≤(Cr+2)^N*U^(eps*N) := by
    have hh : Cr*U^eps+2≤(Cr+2)*U^eps := by nlinarith
    have hp' := pow_le_pow_left₀ (show 0≤Cr*U^eps+2 by positivity) hh N
    rw [mul_pow] at hp'
    have heq : (U^eps)^N=U^(eps*N) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU)]
    rwa [heq] at hp'
  have hyprod : 0≤∏j,yy j := Finset.prod_nonneg (fun j _=>hyy j)
  have hpprod : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  calc
    _ ≤ R*((Cr+2)^N*U^(eps*N))*(∏j,yy j)*(∏j,p j) := by gcongr
    _ = _ := by
      dsimp [R,yy]
      have hh : U^eps*U^(eps*N)=U^(eps*(N+1)) := by rw [←Real.rpow_add (zero_lt_one.trans_le hU)];congr 1;ring
      calc
        _ = Ct*(Cr+2)^N*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*(U^eps*U^(eps*N))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hh]
end SevenEighths.ProbeCentralAllSlots

end

end OAI
