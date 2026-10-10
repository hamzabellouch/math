import OAI.NumberTheory.DirichletL.Detector.TupleScaling
import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_cpow {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0)
    (J : Finset (Fin K)) (s : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^s=∏i∈J,(elementNorm (p i):ℂ)^s := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,elementNorm_one,Complex.ofReal_one,Complex.one_cpow]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,elementNorm_mul,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (elementNorm_pos _ (hp i)).le (tuple_norm_pos p hp J).le,
      ih,Finset.prod_insert hi]

lemma tuple_target_star {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) :
    star (HeckeFamily.elementCoeff η (∏i∈J,p i))=∏i∈J,star (HeckeFamily.elementCoeff η (p i)) := by
  change star (ProbeRow.targetMonoid η (∏i∈J,p i))=_
  rw [map_prod,star_prod]
  rfl

lemma tuple_source_scalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (x w z : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)=
    (∏i,(elementNorm (p i):ℂ)^(z-1))*
      (∏i∈J,(elementNorm (p i):ℂ)^(-w))*
      (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x) := by
  rw [tuple_norm_cpow p hp J,tuple_norm_cpow p hp (Finset.univ\J),tuple_target_star]
  have he (i : Fin K) : (elementNorm (p i):ℂ)^(z-w-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^(-w) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  have hf (i : Fin K) : (elementNorm (p i):ℂ)^(x+z-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^x := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  simp only [he,hf,Finset.prod_mul_distrib]
  have hc := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i : Fin K=>(elementNorm (p i):ℂ)^(z-1))
  rw [←hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI
