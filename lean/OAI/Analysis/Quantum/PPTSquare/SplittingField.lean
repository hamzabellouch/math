import Mathlib.Analysis.Complex.Polynomial.Basic
import OAI.Analysis.Quantum.PPTSquare.Modular
import OAI.Analysis.Quantum.PPTSquare.GaloisAction
import OAI.Analysis.Quantum.PPTSquare.SplittingSetup
import OAI.Analysis.Quantum.PPTSquare.FieldExtension
import OAI.Analysis.Quantum.PPTSquare.EigenGalois

namespace OAI

noncomputable section
open scoped BigOperators Matrix NumberField
open Matrix Polynomial PencilAlgebra PencilEvaluation NumberField
namespace PencilField
abbrev f : ℤ[X] := PencilAlgebra.N0Num.charpoly
abbrev K := SplittingSetup.Split f
attribute [local instance] GaloisAction.prime41
attribute [local instance] GaloisAction.prime131
attribute [local instance] GaloisAction.prime139
lemma reduction41 : f.map (Int.castRingHom (ZMod 41)) = ModularPencil.P41.f :=
  ModularPencil.P41.charpoly
lemma reduction131 : f.map (Int.castRingHom (ZMod 131)) = ModularPencil.P131.f :=
  ModularPencil.P131.charpoly
lemma reduction139 : f.map (Int.castRingHom (ZMod 139)) = ModularPencil.P139.f :=
  ModularPencil.P139.charpoly
section
attribute [local instance] Classical.propDecidable
lemma gcd_bridge41 (e n : ℕ) (h : ModularPencil.P41.degreeCert e n) :
    (EuclideanDomain.gcd ModularPencil.P41.f (X^e-X)).natDegree = n := by
  unfold ModularPencil.P41.degreeCert at h
  convert h using 2
lemma gcd_bridge131 (e n : ℕ) (h : ModularPencil.P131.degreeCert e n) :
    (EuclideanDomain.gcd ModularPencil.P131.f (X^e-X)).natDegree = n := by
  unfold ModularPencil.P131.degreeCert at h
  convert h using 2
lemma gcd_bridge139 (e n : ℕ) (h : ModularPencil.P139.degreeCert e n) :
    (EuclideanDomain.gcd ModularPencil.P139.f (X^e-X)).natDegree = n := by
  unfold ModularPencil.P139.degreeCert at h
  convert h using 2
lemma reduction_gcd41 (e n : ℕ) (h : ModularPencil.P41.degreeCert e n) :
    (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 41))) (X^e-X)).natDegree = n := by
  rw [reduction41]
  convert gcd_bridge41 e n h using 2

lemma reduction_gcd131 (e n : ℕ) (h : ModularPencil.P131.degreeCert e n) :
    (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 131))) (X^e-X)).natDegree = n := by
  rw [reduction131]
  convert gcd_bridge131 e n h using 2

lemma reduction_gcd139 (e n : ℕ) (h : ModularPencil.P139.degreeCert e n) :
    (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 139))) (X^e-X)).natDegree = n := by
  rw [reduction139]
  convert gcd_bridge139 e n h using 2

end
lemma exists_field_data :
    ∃ (r : Fin 20 → K) (t : Fin 20 → Fin 3 → K),
      Function.Injective r ∧
      ((action (K := K) 0).charpoly = ∏ i, (X-C (r i))) ∧
      IsUnit (evaluation t) ∧
      (∀ a, evaluation t * action a = diagonal (fun i => (denominator : K)*t i a) * evaluation t) ∧
      (∀ i, (denominator : K)*t i 0 = r i) ∧
      (∀ j : Fin 10 → Fin 20, Function.Injective j →
        IsUnit ((evaluation t).submatrix j (fun k : Fin 10 => k.castLE (by decide)))) := by
  classical
  obtain ⟨r,hf⟩ := IntegralRoots.exists_integral_roots (K := K) f
    (Matrix.charpoly_monic _) 20 (by simp [f, Matrix.charpoly_natDegree_eq_dim])
    (SplittingSetup.splits f)
  have hsep41 : (f.map (Int.castRingHom (ZMod 41))).Separable := by
    rw [reduction41]; exact ModularPencil.P41.separable
  have hr : Function.Injective r := IntegralRoots.injective_of_squarefree_reduction r f hf 41 hsep41
  have hall : ∀ π : Equiv.Perm (Fin 20), ∃ σ : K ≃ₐ[ℚ] K,
      ∀ i, σ (r i : K) = (r (π i) : K) := by
    apply GaloisAction.full_action r hr f hf hsep41
    · with_reducible exact reduction_gcd41 (41^4) 0 ModularPencil.P41.gcd_degree4
    · with_reducible exact reduction_gcd41 (41^10) 0 ModularPencil.P41.gcd_degree10
    · with_reducible exact reduction_gcd41 (41^20) 20 ModularPencil.P41.gcd_degree20
    · rw [reduction131]; exact ModularPencil.P131.separable
    · with_reducible exact reduction_gcd131 (131^17) 18 ModularPencil.P131.gcd_degree17
    · rw [reduction139]; exact ModularPencil.P139.separable
    · with_reducible exact reduction_gcd139 (139^1) 1 ModularPencil.P139.gcd_degree1
    · with_reducible exact reduction_gcd139 (139^19) 20 ModularPencil.P139.gcd_degree19
  let roots : Fin 20 → K := fun i => (r i : K)
  have hir : Function.Injective roots := RingOfIntegers.coe_injective.comp hr
  have hprod : f.map (Int.castRingHom K) = ∏ i, (X-C (roots i)) :=
    CertificateGalois.map_product_integer_roots r f hf (algebraMap (𝓞 K) K)
  have hchar : (action (K := K) 0).charpoly = ∏ i, (X-C (roots i)) := by
    calc
      (action (K := K) 0).charpoly = f.map (Int.castRingHom K) := by
        change (N0Num.map (Int.castRingHom K)).charpoly =
          N0Num.charpoly.map (Int.castRingHom K)
        exact Matrix.charpoly_map N0Num (Int.castRingHom K)
      _ = ∏ i, (X-C (roots i)) := hprod
  obtain ⟨t,hu,he,ht⟩ := exists_evaluations roots hir hchar
  refine ⟨roots,t,hir,hchar,hu,he,ht,?_⟩
  have hex : evaluation t * action 0 = diagonal roots * evaluation t := by
    convert he 0 using 1
    congr 2
    ext i
    exact (ht i).symm
  apply EigenGalois.all_minors (action 0) (evaluation t) roots hir hu hex 0
    (fun i => lowMon_zero (t i))
  · intro π
    obtain ⟨σ,hσ⟩ := hall π
    refine ⟨σ.toRingEquiv,?_,hσ⟩
    ext i j
    simp [action]
  · intro i j h
    exact Fin.ext (congrArg (fun k : Fin 20 => k.val) h)

lemma exists_complex_data :
    ∃ (r : Fin 20 → ℂ) (t : Fin 20 → Fin 3 → ℂ),
      Function.Injective r ∧
      ((action (K := ℂ) 0).charpoly = ∏ i, (X-C (r i))) ∧
      IsUnit (evaluation t) ∧
      (∀ a, evaluation t * action a = diagonal (fun i => (denominator : ℂ)*t i a) * evaluation t) ∧
      (∀ i, (denominator : ℂ)*t i 0 = r i) ∧
      (∀ j : Fin 10 → Fin 20, Function.Injective j →
        IsUnit ((evaluation t).submatrix j (fun k : Fin 10 => k.castLE (by decide)))) := by
  let φ : K →ₐ[ℚ] ℂ := Polynomial.SplittingField.lift (f.map (Int.castRingHom ℚ)) (IsAlgClosed.splits _)
  obtain ⟨r,t,hr,hf,hu,he,ht,hm⟩ := exists_field_data
  exact ⟨fun i => φ (r i), fun i a => φ (t i a),
    PencilExtension.data_map φ.toRingHom t r hr hf hu he ht hm⟩
end PencilField

end

end OAI
