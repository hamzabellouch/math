import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.MvPolynomial.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial

section Substitution

variable {k σ τ : Type*} [CommSemiring k]

theorem totalDegree_aeval_le (F : τ → MvPolynomial σ k) (D : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ D) (p : MvPolynomial τ k) :
    (aeval F p).totalDegree ≤ p.totalDegree * D := by
  classical
  have hm (d : τ →₀ ℕ) (c : k) :
      (aeval F (monomial d c)).totalDegree ≤ (d.sum fun _ e => e) * D := by
    rw [aeval_monomial, Finsupp.prod]
    calc
      (algebraMap k (MvPolynomial σ k) c *
          ∏ i ∈ d.support, F i ^ d i).totalDegree
          ≤ (∏ i ∈ d.support, F i ^ d i).totalDegree := by
            simpa only [MvPolynomial.algebraMap_eq, totalDegree_C, zero_add] using
              totalDegree_mul (C c) (∏ i ∈ d.support, F i ^ d i)
      _ ≤ ∑ i ∈ d.support, (F i ^ d i).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ d.support, d i * D :=
        Finset.sum_le_sum fun i _ =>
          (totalDegree_pow (F i) (d i)).trans (Nat.mul_le_mul_left _ (hF i))
      _ = (d.sum fun _ e => e) * D := by rw [Finsupp.sum, Finset.sum_mul]
  have he : aeval F p = ∑ d ∈ p.support, aeval F (monomial d (p.coeff d)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  exact totalDegree_finsetSum_le fun d hd =>
    (hm d (p.coeff d)).trans (Nat.mul_le_mul_right D (le_totalDegree hd))

end Substitution

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientDegreeFiltration (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (restrictTotalDegree σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

noncomputable instance quotientDegreeFiltration_finite (I : Ideal (MvPolynomial σ k))
    (n : ℕ) : Module.Finite k (quotientDegreeFiltration I n) := by
  unfold quotientDegreeFiltration
  infer_instance

omit [Finite σ] in
theorem normalization_mem_quotientDegreeFiltration {τ : Type*}
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (F : τ → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D)
    (n : ℕ) (p : MvPolynomial τ k) (hp : p.totalDegree ≤ n) :
    g p ∈ quotientDegreeFiltration I (n * D) := by
  have he : (Ideal.Quotient.mkₐ k I).comp (aeval F) = g := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact hF i
  refine Submodule.mem_map.mpr ⟨aeval F p,
    (mem_restrictTotalDegree σ _ _).mpr
      ((totalDegree_aeval_le F D hD p).trans (Nat.mul_le_mul_right D hp)), ?_⟩
  exact AlgHom.congr_fun he p

theorem normalization_lower_growth {τ : Type*} [Fintype τ]
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) :
    ∃ D : ℕ, ∀ n : ℕ,
      Module.finrank k (restrictTotalDegree τ k n) ≤
        Module.finrank k (quotientDegreeFiltration I (n * D)) := by
  classical
  choose F hF using fun i : τ => Ideal.Quotient.mk_surjective (g (X i))
  let D := Finset.univ.sup fun i => (F i).totalDegree
  have hD : ∀ i, (F i).totalDegree ≤ D := fun i =>
    Finset.le_sup (f := fun j : τ => (F j).totalDegree) (Finset.mem_univ i)
  refine ⟨D, fun n => ?_⟩
  let L : restrictTotalDegree τ k n →ₗ[k] quotientDegreeFiltration I (n * D) :=
    { toFun := fun p => ⟨g p, normalization_mem_quotientDegreeFiltration I g F hF D hD
        n p ((mem_restrictTotalDegree τ _ _).mp p.property)⟩
      map_add' := fun p q => Subtype.ext (g.map_add p q)
      map_smul' := fun c p => Subtype.ext (g.toLinearMap.map_smul c p) }
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro p q hpq
  exact Subtype.ext (hg (congrArg Subtype.val hpq))

end PiExponentJets.W24

end OAI
