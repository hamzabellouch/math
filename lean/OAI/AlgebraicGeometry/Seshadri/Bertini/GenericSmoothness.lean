import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.SimultaneousHyperplanes
import OAI.AlgebraicGeometry.Seshadri.Bertini.LinearFamilies

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

lemma hyperplane_parameter_polynomial_ne_zero {K σ : Type} [Field K]
    (S : Subfield K) (p : MvPolynomial (Option σ) K) (hp : p ≠ 0)
    (hcoeff : (p.coeffs : Set K) ⊆ S)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) (hf : Function.Injective f) :
    MvPolynomial.aeval ((fun o : Option σ => o.elim (f X) (fun i => f (C (MvPolynomial.X i))))) p ≠ 0 := by
  have hrange : p ∈ Set.range (MvPolynomial.map S.subtype) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, hcoeff hx⟩, rfl⟩
  obtain ⟨p₀, rfl⟩ := hrange
  let t : Option σ → K := (fun o : Option σ => o.elim (f X) (fun i => f (C (MvPolynomial.X i))))
  have he : (MvPolynomial.aeval t : MvPolynomial (Option σ) S →ₐ[S] K) =
      f.comp (MvPolynomial.optionEquivLeft S σ).toAlgHom := by
    ext i
    cases i <;> simp [t]
  have hval : MvPolynomial.aeval t (MvPolynomial.map S.subtype p₀) =
      f (MvPolynomial.optionEquivLeft S σ p₀) := by
    rw [show (MvPolynomial.aeval t (MvPolynomial.map S.subtype p₀)) =
      (MvPolynomial.aeval t : MvPolynomial (Option σ) S →ₐ[S] K) p₀ by
        simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
        rfl]
    rw [he]
    rfl
  change MvPolynomial.aeval t (MvPolynomial.map S.subtype p₀) ≠ 0
  rw [hval]
  intro hz
  have hz₀ : p₀ = 0 := (MvPolynomial.optionEquivLeft S σ).injective (hf (by simpa using hz))
  exact hp (by simp [hz₀])

end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem etale_generic_smooth_integral_hyperplane_section {K A ι : Type} {n : ℕ}
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b))
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) ∧
        Algebra.Smooth K (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  let : Algebra.FormallySmooth K A := Algebra.FormallySmooth.comp K (MvPolynomial ι K) A
  let : Algebra.Smooth K A := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let w : Option (Fin n) → A := fun o => o.elim 1 (fun k => -v k)
  have hw : Ideal.span (Set.range w) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨none, rfl⟩)
  obtain ⟨p, hp, hs⟩ := MaximalSeshadri.LinearBertini.affine_bertini (K := K) w hw
  obtain ⟨S, hS, hcS, hint⟩ := etale_generic_hyperplane_section
    v i j a b hab hvi hvj (c ∪ (p.coeffs : Set K)) (hc.union (show (p.coeffs : Set K).Countable from p.coeffs.countable_toSet))
  refine ⟨S, hS, fun x hx => hcS (Or.inl hx), fun f hf => ⟨hint f hf, ?_⟩⟩
  have hcoeff : (p.coeffs : Set K) ⊆ S := fun _ hx => hcS (Or.inr hx)
  have hn := hyperplane_parameter_polynomial_ne_zero S p hp hcoeff f hf
  let t : Option (Fin n) → K := fun o => o.elim (f X) (fun k => f (C (MvPolynomial.X k)))
  have he : MaximalSeshadri.LinearBertini.specializedSection w t =
      algebraMap K A (f X) - ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k := by
    simp [MaximalSeshadri.LinearBertini.specializedSection, w, t, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  let : Algebra.Smooth K (A ⧸ Ideal.span {MaximalSeshadri.LinearBertini.specializedSection w t}) := hs t hn
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq K
    (congrArg (fun x : A => Ideal.span {x}) he))

end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem simultaneous_etale_smooth_integral_hyperplanes
    {K ι : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable ι] (A σ : ι → Type) [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
    [∀ j, Algebra K (A j)] [∀ j, Algebra.FiniteType K (A j)]
    [∀ j, Algebra (MvPolynomial (σ j) K) (A j)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) (A j)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) (A j)]
    (v : ∀ j, Fin n → A j) (i₁ i₂ : ι → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (b j)))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∃ f : (MvPolynomial (Fin n) T)[X] →ₐ[T] K, Function.Injective f ∧
        ∀ j, IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) (f X) -
          ∑ k, algebraMap K (A j) (f (C (MvPolynomial.X k))) * v j k}) ∧
          Algebra.Smooth K (A j ⧸ Ideal.span {algebraMap K (A j) (f X) -
            ∑ k, algebraMap K (A j) (f (C (MvPolynomial.X k))) * v j k}) := by
  let P (j : ι) (α : Fin n → K) (β : K) : Prop :=
    IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k}) ∧
    Algebra.Smooth K (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k})
  have hP j : ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        P j (fun k => f (C (MvPolynomial.X k))) (f X) := by
    obtain ⟨S, hS, _, h⟩ := etale_generic_smooth_integral_hyperplane_section
      (v j) (i₁ j) (i₂ j) (a j) (b j) (hab j) (hva j) (hvb j)
      (∅ : Set K) Set.countable_empty
    exact ⟨S, hS, h⟩
  obtain ⟨T, hT, hcT, hh⟩ := simultaneous_generic_hyperplane_parameters P hP c hc
  let : Countable T := hT
  obtain ⟨f, hf⟩ := independent_hyperplane_parameters (σ := Fin n) T
  exact ⟨T, hT, hcT, f, hf, hh f hf⟩

end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
variable {K S σ : Type*} [Field K] [CommRing S] [Algebra S K]

def hyperplaneVariable (o : Option σ) : (MvPolynomial σ S)[X] :=
  o.elim X (fun i => C (MvPolynomial.X i))

def permuteHyperplaneHom (e : Option σ ≃ Option σ)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) : (MvPolynomial σ S)[X] →ₐ[S] K :=
  f.comp (((MvPolynomial.optionEquivLeft S σ).symm.trans
    ((MvPolynomial.renameEquiv S e).trans (MvPolynomial.optionEquivLeft S σ))).toAlgHom)

lemma permuteHyperplaneHom_injective (e : Option σ ≃ Option σ)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) (hf : Function.Injective f) :
    Function.Injective (permuteHyperplaneHom e f) :=
  hf.comp (((MvPolynomial.optionEquivLeft S σ).symm.trans
    ((MvPolynomial.renameEquiv S e).trans (MvPolynomial.optionEquivLeft S σ))).injective)

@[simp] lemma permuteHyperplaneHom_variable (e : Option σ ≃ Option σ)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) (o : Option σ) :
    permuteHyperplaneHom e f (hyperplaneVariable o) =
      f (hyperplaneVariable (e o)) := by
  have hv (a : Option σ) : MvPolynomial.optionEquivLeft S σ (MvPolynomial.X a) =
      hyperplaneVariable a := by cases a <;> simp [hyperplaneVariable]
  rw [← hv o]
  simp only [permuteHyperplaneHom, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hv]

end
noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem simultaneous_reindexed_generic_hyperplane_parameters
    {K σ ι : Type} [Field K] [Countable ι]
    (P : ι → (σ → K) → K → Prop)
    (hP : ∀ i, ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial σ S)[X] →ₐ[S] K, Function.Injective f →
        P i (fun k => f (C (MvPolynomial.X k))) (f X))
    (e : ι → (Option σ ≃ Option σ)) (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∀ f : (MvPolynomial σ T)[X] →ₐ[T] K, Function.Injective f →
        ∀ i, P i (fun k => f (hyperplaneVariable (e i (some k))))
          (f (hyperplaneVariable (e i none))) := by
  choose S hS hProp using hP
  obtain ⟨T, hT, hcT, hST⟩ := common_hyperplane_field S hS c hc
  refine ⟨T, hT, hcT, fun f hf i => ?_⟩
  let g := restrictHyperplaneHom (hST i) f
  have hg : Function.Injective g := restrictHyperplaneHom_injective (hST i) f hf
  have he := hProp i (permuteHyperplaneHom (e i) g)
    (permuteHyperplaneHom_injective (e i) g hg)
  have hv (o : Option σ) : permuteHyperplaneHom (e i) g (hyperplaneVariable o) =
      f (hyperplaneVariable (e i o)) := by
    rw [permuteHyperplaneHom_variable]
    cases e i o <;> simp only [hyperplaneVariable, Option.elim_none, Option.elim_some]
    · exact restrictHyperplaneHom_X (hST i) f
    · exact restrictHyperplaneHom_CX (hST i) f _
  have hnone := hv none
  have hsome (k : σ) := hv (some k)
  change permuteHyperplaneHom (e i) g X = _ at hnone
  have hfun : (fun k => permuteHyperplaneHom (e i) g (C (MvPolynomial.X k))) =
      (fun k => f (hyperplaneVariable (e i (some k)))) := funext hsome
  rwa [hfun, hnone] at he
end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem simultaneous_reindexed_smooth_integral_hyperplanes
    {K ι : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable ι] (A σ : ι → Type) [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
    [∀ j, Algebra K (A j)] [∀ j, Algebra.FiniteType K (A j)]
    [∀ j, Algebra (MvPolynomial (σ j) K) (A j)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) (A j)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) (A j)]
    (v : ∀ j, Fin n → A j) (i₁ i₂ : ι → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (b j)))
    (e : ι → (Option (Fin n) ≃ Option (Fin n)))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∃ f : (MvPolynomial (Fin n) T)[X] →ₐ[T] K, Function.Injective f ∧
        ∀ j, IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) (f (hyperplaneVariable (e j none))) -
          ∑ k, algebraMap K (A j) (f (hyperplaneVariable (e j (some k)))) * v j k}) ∧
          Algebra.Smooth K (A j ⧸ Ideal.span {algebraMap K (A j) (f (hyperplaneVariable (e j none))) -
            ∑ k, algebraMap K (A j) (f (hyperplaneVariable (e j (some k)))) * v j k}) := by
  let P (j : ι) (α : Fin n → K) (β : K) : Prop :=
    IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k}) ∧
    Algebra.Smooth K (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k})
  have hP j : ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        P j (fun k => f (C (MvPolynomial.X k))) (f X) := by
    obtain ⟨S, hS, _, h⟩ := etale_generic_smooth_integral_hyperplane_section
      (v j) (i₁ j) (i₂ j) (a j) (b j) (hab j) (hva j) (hvb j)
      (∅ : Set K) Set.countable_empty
    exact ⟨S, hS, h⟩
  obtain ⟨T, hT, hcT, hh⟩ := simultaneous_reindexed_generic_hyperplane_parameters P hP e c hc
  let : Countable T := hT
  obtain ⟨f, hf⟩ := independent_hyperplane_parameters (σ := Fin n) T
  exact ⟨T, hT, hcT, f, hf, hh f hf⟩

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
