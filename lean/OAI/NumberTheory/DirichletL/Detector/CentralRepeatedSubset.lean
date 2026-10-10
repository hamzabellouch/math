import OAI.NumberTheory.DirichletL.Detector.CentralRepeatedSum

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSubset
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedSum
local notation "O" => HeckeFamily.O

theorem actual_repeated_subset (N : ℕ) (e eps c d B : ℝ)
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
    ∀J : Finset (Fin N),
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j:J,(Y j.val)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := actual_repeated_sum N e eps c d B he he1 heps hc hd hB
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi J
  let k := Fintype.card J
  let E : J≃Fin k := Fintype.equivFin J
  let idx : Fin k→Fin N := fun j=>(E.symm j).val
  have hi : Function.Injective idx := fun j l h=>E.symm.injective (Subtype.ext h)
  have hk : k≤N := by
    dsimp [k]
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using J.card_le_univ
  have hd' (P : ∀j,T (idx j)) : Function.Injective (fun j=>(P j).val) := by
    intro j l heq
    change (P j).val=(P l).val at heq
    by_contra hne
    have hdiff : idx j≠idx l := fun h=>hne (hi h)
    exact Finset.disjoint_left.mp (hdis _ _ hdiff) (P j).property (by rw [heq];exact (P l).property)
  have hb := hmain S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k hk
    (fun j=>T (idx j)) (fun j P hP=>hs (idx j) P hP) hd'
    (fun j P hP=>hη (idx j) P hP) (fun j P hP=>hQ (idx j) P hP)
    (fun j P hP=>hsmall (idx j) P hP) (fun j=>W (idx j)) (fun j=>Y (idx j))
    (fun j=>hY (idx j)) (fun j=>hWS (idx j)) (fun j=>hW (idx j)) x w z hx hw hz hwi
  have hleft : (∏j:Fin k,∑P:T (idx j),‖W (idx j) ((P.val.val.absNorm:ℝ)/Y (idx j))*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs (idx j) P.val P.property) x w z‖)=
      ∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  have hright : (∏j:Fin k,(Y (idx j))^(-(4/25:ℝ)))=∏j:J,(Y j.val)^(-(4/25:ℝ)) :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  rw [hleft,hright] at hb
  exact hb
end SevenEighths.ProbeCentralRepeatedSubset

end

end OAI
