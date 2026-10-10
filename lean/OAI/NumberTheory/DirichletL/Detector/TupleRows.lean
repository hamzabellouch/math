import OAI.NumberTheory.DirichletL.Detector.TupleMellin
import OAI.NumberTheory.DirichletL.Detector.TupleProducts

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceRowSummand_summable (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (D : Id) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    Summable (fun u : FreeRow=>star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S D η u.val x w z) := by
  let e : FreeRow×((Id×Id)×(Id×Id))→FullHighIndex := fun p=>(⟨p.1.val,p.1.property.1⟩,p.2)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun t : FullHighIndex=>t.1.val) h
    · exact congrArg (fun t : FullHighIndex=>t.2) h
  have hs := (fullHighSummand_summable S D η x w z hx hw hz
    (fun H=>star (C.residueMonoid H.val))
    (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val)).comp_injective he
  have ht := hs.prod
  apply ht.congr
  intro u
  dsimp only [Function.comp_def,e]
  exact tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩)
    (f:=fun c : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u.val x w z c.1.1 c.1.2 c.2.1 c.2.2)

def tupleIndexedCoefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) (x w : ℂ) : ℂ :=
  (-1:ℂ)^J.card*(∏i∈J,(elementNorm (p i):ℂ)^(-w))*
    (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x)

def indexedCompensatedHigh {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (u : O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
    markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z

lemma tupleSourceSeries_common_scale {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
          sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z := by
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_source_scalar η p hp J x w z
  unfold tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*he*
    sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

theorem tupleSourceSeries_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
          indexedCompensatedHigh η S p u.val x w z := by
  rw [tupleSourceSeries_common_scale η S C p hp]
  congr 1
  let f : Finset (Fin K)→FreeRow→ℂ := fun J u=>tupleIndexedCoefficient η p J x w*
    (star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u.val x w z)
  have hf (J : Finset (Fin K)) : Summable (f J) :=
    (sourceRowSummand_summable η S C _ x w z hx hw hz).mul_left _
  have hsum := Summable.tsum_finsetSum (s:=(Finset.univ:Finset (Fin K)).powerset)
    (f:=f) (fun J _=>hf J)
  unfold sourceRowSeries
  simp only [←tsum_mul_left]
  change (∑J∈(Finset.univ:Finset (Fin K)).powerset,∑'u,f J u)=_
  rw [←hsum]
  apply tsum_congr
  intro u
  unfold indexedCompensatedHigh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [f]
  ring

end SevenEighths.ProbePhysical
end

end OAI
