import OAI.NumberTheory.DirichletL.PrimeRows.RowCount

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physical_row_dyad (K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (U : ℝ),1≤U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r →
      (∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_tuple_sum K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  let A : ℝ := ProbeSelectedPrimeSums.annularPower 1 2 (3/5+δ-r)
  have hA : 0<A := by
    have hh := le_max_left ((1:ℝ)^(3/5+δ-r)) ((2:ℝ)^(3/5+δ-r))
    rw [Real.one_rpow] at hh
    simpa only [A,ProbeSelectedPrimeSums.annularPower,Real.one_rpow] using (lt_of_lt_of_le zero_lt_one hh)
  refine ⟨256*C*A,by positivity,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let F : FreeRow→ℝ := fun u=>∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
    (fun i=>hT i (P i).val (P i).property) W Y x w z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^δ*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈R) : F u≤D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ) := by
    have hh := hmain η u (hR u hu).1 T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
    apply hh.trans_eq
    dsimp [D]
    ring
  have heq (u : FreeRow) :
      (∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)=
      ‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    simp only [norm_mul,Finset.mul_sum,F]
  simp_rw [heq]
  apply (dyadic_weighted_rows (3/5+δ) r D U hD hU R (fun u hu=>(hR u hu).2) F hF z hz).trans_eq
  change 256*D*A*U^(1+(3/5+δ)-r)=_
  rw [show (1:ℝ)+(3/5+δ)-r=8/5+δ-r by ring]
  dsimp [D]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
