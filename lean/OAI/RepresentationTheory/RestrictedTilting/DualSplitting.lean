import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.StandardLifts

namespace OAI

/-! Standard-costandard extension splitting and dual rational representations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section

universe u
variable (k : Type u) [Field k] [Infinite k]

lemma standard_weight_bound (n : ℕ) :
    HasWeightsBetween (standardRepresentation k n) (-(n : ℤ)) n := by
  intro m v hm hv
  apply eigenvector_eq_zero_of_basis k (standardBasis k n)
    (fun i => (n : ℤ) - 2 * i) (standardRepresentation k n)
    (standardBasis_weight k n) m ?_ v hv
  intro i
  have hi := i.isLt
  rcases hm with hm | hm <;> omega

omit [Infinite k] in
lemma hasWeightsBetween_mono {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) {l h l' h' : ℤ}
    (hb : HasWeightsBetween ρ l h) (hl : l' ≤ l) (hh : h ≤ h') :
    HasWeightsBetween ρ l' h' := by
  intro m v hm hv
  exact hb m v (by rcases hm with hm | hm <;> omega) hv

 

theorem standard_costandard_split_of_le {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M]
    (ρ : Representation k (SL2 k) M) (hρ : IsRational k ρ)
    (n m : ℕ) (hmn : m ≤ n)
    (f : MvPolynomial.homogeneousSubmodule (Fin 2) k m →ₗ[k] M)
    (g : M →ₗ[k] Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n))
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.ker g = LinearMap.range f)
    (hfi : ∀ a x, f ((costandard k m).ρ a x) = ρ a (f x))
    (hgi : ∀ a x, g (ρ a x) = standardRepresentation k n a (g x)) :
    ∃ s : Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k] M,
      g.comp s = LinearMap.id ∧
      ∀ a x, s (standardRepresentation k n a x) = ρ a (s x) := by
  have hb : HasWeightsBetween ρ (-(n : ℤ)) n := by
    apply hasWeightsBetween_extension (costandard k m).ρ ρ (standardRepresentation k n)
      f g hf he (fun x a => hfi a x) (fun x a => hgi a x)
    · apply hasWeightsBetween_mono k _ (fun a v hv hw => costandard_weight_bound k m a hv v hw)
      <;> omega
    · exact standard_weight_bound k n
  obtain ⟨v, hgv, hv⟩ := rational_weight_lift k ρ (standardRepresentation k n) hρ g
    hgi hg (integerCharacter k n) (standardHighest k n) (standardHighest_weight k n)
  obtain ⟨s, hsv, hs⟩ := exists_standard_lift k ρ hρ n hb v hv
  refine ⟨s, ?_, hs⟩
  apply standard_lower_orbit_ext k n Set.univ Set.infinite_univ
  intro t ht
  simp only [LinearMap.comp_apply, LinearMap.id_apply, hs, hgi, hsv, hgv]

end

section

universe u
variable (k : Type u) [Field k]

noncomputable def inverseCoordinatePolynomial (ij : Fin 2 × Fin 2) :
    MvPolynomial (Fin 2 × Fin 2) k :=
  !![MvPolynomial.X (1,1), -MvPolynomial.X (0,1);
    -MvPolynomial.X (1,0), MvPolynomial.X (0,0)] ij.1 ij.2

lemma eval_inverseCoordinatePolynomial (g : SL2 k) (ij : Fin 2 × Fin 2) :
    MvPolynomial.eval (fun ij => g ij.1 ij.2) (inverseCoordinatePolynomial k ij) =
      (g⁻¹ : SL2 k) ij.1 ij.2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [inverseCoordinatePolynomial]

 
lemma IsRational.dual {M : Type u} [AddCommGroup M] [Module k M]
    [Module.Finite k M] (ρ : Representation k (SL2 k) M) (hρ : IsRational k ρ) :
    IsRational k (Representation.dual ρ) := by
  intro φ ψ
  obtain ⟨v, rfl⟩ := (Module.evalEquiv k M).surjective ψ
  obtain ⟨P, hP⟩ := hρ v φ
  refine ⟨MvPolynomial.bind₁ (inverseCoordinatePolynomial k) P, fun g => ?_⟩
  change φ (ρ g⁻¹ v) = _
  rw [hP]
  change _ = MvPolynomial.eval₂Hom (RingHom.id k) (fun ij => g ij.1 ij.2)
    (MvPolynomial.bind₁ (inverseCoordinatePolynomial k) P)
  rw [MvPolynomial.eval₂Hom_bind₁]
  change _ = MvPolynomial.eval (fun ij =>
    MvPolynomial.eval (fun ij => g ij.1 ij.2) (inverseCoordinatePolynomial k ij)) P
  simp only [eval_inverseCoordinatePolynomial]

lemma dual_intertwines {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (f : M →ₗ[k] N) (hf : ∀ g x, f (ρ g x) = σ g (f x)) :
    ∀ g φ, f.dualMap (Representation.dual σ g φ) =
      Representation.dual ρ g (f.dualMap φ) := by
  intro g φ
  ext x
  change φ (σ g⁻¹ (f x)) = φ (f (ρ g⁻¹ x))
  rw [hf]

lemma eval_intertwines {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (g : SL2 k) (x : M) :
    Module.Dual.eval k M (ρ g x) =
      Representation.dual (Representation.dual ρ) g (Module.Dual.eval k M x) := by
  ext φ
  change φ (ρ g x) = φ (ρ (g⁻¹)⁻¹ x)
  rw [inv_inv]

end

section

variable {k G A B C : Type*} [Field k] [Group G]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

 
lemma equivariant_section_of_retraction
    (ρA : Representation k G A) (ρB : Representation k G B)
    (ρC : Representation k G C) (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (hg : Function.Surjective g) (he : LinearMap.ker g = LinearMap.range f)
    (hgρ : ∀ a x, g (ρB a x) = ρC a (g x))
    (r : B →ₗ[k] A) (hr : r.comp f = LinearMap.id)
    (hrρ : ∀ a x, r (ρB a x) = ρA a (r x)) :
    ∃ s : C →ₗ[k] B, g.comp s = LinearMap.id ∧
      ∀ a x, s (ρC a x) = ρB a (s x) := by
  obtain ⟨s₀, hs₀⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have hgf (x : A) : g (f x) = 0 := by
    exact LinearMap.mem_ker.mp (he.symm ▸ LinearMap.mem_range_self f x)
  have hrf (x : A) : r (f x) = x := LinearMap.congr_fun hr x
  let s : C →ₗ[k] B := s₀ - f.comp (r.comp s₀)
  have hgs (x : C) : g (s x) = x := by
    dsimp [s]
    rw [map_sub, hgf, sub_zero]
    exact LinearMap.congr_fun hs₀ x
  have hrs (x : C) : r (s x) = 0 := by simp [s, hrf]
  have hext {x y : B} (h₁ : g x = g y) (h₂ : r x = r y) : x = y := by
    have hxy : x - y ∈ LinearMap.range f := by
      rw [← he, LinearMap.mem_ker, map_sub, h₁, sub_self]
    obtain ⟨z, hz⟩ := hxy
    have hz0 : z = 0 := by
      rw [← hrf z, hz, map_sub, h₂, sub_self]
    exact sub_eq_zero.mp (by simpa [hz0] using hz.symm)
  refine ⟨s, LinearMap.ext hgs, fun a x => hext ?_ ?_⟩
  · rw [hgs, hgρ, hgs]
  · rw [hrs, hrρ, hrs, map_zero]

 
lemma equivariant_retraction_of_dual_section [Module.Finite k A]
    (ρA : Representation k G A) (ρB : Representation k G B) (f : A →ₗ[k] B)
    (s : Module.Dual k A →ₗ[k] Module.Dual k B)
    (hs : f.dualMap.comp s = LinearMap.id)
    (hsρ : ∀ a φ, s (Representation.dual ρA a φ) = Representation.dual ρB a (s φ)) :
    ∃ r : B →ₗ[k] A, r.comp f = LinearMap.id ∧
      ∀ a x, r (ρB a x) = ρA a (r x) := by
  let r : B →ₗ[k] A := (Module.evalEquiv k A).symm.toLinearMap.comp
    (s.dualMap.comp (Module.Dual.eval k B))
  have hr (x : B) (φ : Module.Dual k A) : φ (r x) = s φ x := by
    exact Module.apply_evalEquiv_symm_apply k A φ (s.dualMap (Module.Dual.eval k B x))
  refine ⟨r, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply (Module.evalEquiv k A).injective
    apply LinearMap.ext
    intro φ
    change φ (r (f x)) = φ x
    rw [hr]
    exact congrArg (fun ψ => ψ x) (LinearMap.congr_fun hs φ)
  · intro a x
    apply (Module.evalEquiv k A).injective
    apply LinearMap.ext
    intro φ
    change φ (r (ρB a x)) = φ (ρA a (r x))
    rw [hr]
    have hhe := congrArg (fun ψ => ψ x) (hsρ a⁻¹ φ)
    change s (Representation.dual ρA a⁻¹ φ) x = s φ (ρB (a⁻¹)⁻¹ x) at hhe
    rw [inv_inv] at hhe
    rw [← hhe, ← hr]
    change φ (ρA (a⁻¹)⁻¹ (r x)) = _
    rw [inv_inv]

lemma dual_sequence_exact [Module.Finite k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] Module.Dual k C)
    (he : LinearMap.ker g = LinearMap.range f) :
    LinearMap.ker f.dualMap =
      LinearMap.range (g.dualMap.comp (Module.Dual.eval k C)) := by
  rw [← Module.evalEquiv_toLinearMap,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range (Module.evalEquiv k C)),
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, he]

lemma dual_eval_intertwines
    (ρB : Representation k G B) (ρC : Representation k G C)
    (g : B →ₗ[k] Module.Dual k C)
    (hg : ∀ a x, g (ρB a x) = Representation.dual ρC a (g x)) :
    ∀ a x, (g.dualMap.comp (Module.Dual.eval k C)) (ρC a x) =
      Representation.dual ρB a ((g.dualMap.comp (Module.Dual.eval k C)) x) := by
  intro a x
  apply LinearMap.ext
  intro y
  change g y (ρC a x) = g (ρB a⁻¹ y) x
  rw [hg]
  change _ = g y (ρC (a⁻¹)⁻¹ x)
  rw [inv_inv]

end

section

universe u
variable (k : Type u) [Field k] [Infinite k]

 
theorem standard_costandard_split {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M]
    (ρ : Representation k (SL2 k) M) (hρ : IsRational k ρ)
    (n m : ℕ)
    (f : MvPolynomial.homogeneousSubmodule (Fin 2) k m →ₗ[k] M)
    (g : M →ₗ[k] Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n))
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.ker g = LinearMap.range f)
    (hfi : ∀ a x, f ((costandard k m).ρ a x) = ρ a (f x))
    (hgi : ∀ a x, g (ρ a x) = standardRepresentation k n a (g x)) :
    ∃ s : Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k] M,
      g.comp s = LinearMap.id ∧
      ∀ a x, s (standardRepresentation k n a x) = ρ a (s x) := by
  by_cases hmn : m ≤ n
  · exact standard_costandard_split_of_le k ρ hρ n m hmn f g hf hg he hfi hgi
  let H := MvPolynomial.homogeneousSubmodule (Fin 2) k n
  let f' : H →ₗ[k] Module.Dual k M := g.dualMap.comp (Module.Dual.eval k H)
  have hf' : Function.Injective f' :=
    (LinearMap.dualMap_injective_of_surjective hg).comp (Module.evalEquiv k H).injective
  have hg' : Function.Surjective f.dualMap :=
    LinearMap.dualMap_surjective_of_injective hf
  have he' : LinearMap.ker f.dualMap = LinearMap.range f' :=
    dual_sequence_exact f g he
  have hfi' : ∀ a x, f' ((costandard k n).ρ a x) = Representation.dual ρ a (f' x) :=
    dual_eval_intertwines ρ (costandard k n).ρ g hgi
  have hgi' : ∀ a x, f.dualMap (Representation.dual ρ a x) =
      standardRepresentation k m a (f.dualMap x) :=
    dual_intertwines k (costandard k m).ρ ρ f hfi
  obtain ⟨s', hs', hsρ'⟩ := standard_costandard_split_of_le k
    (Representation.dual ρ) (IsRational.dual k ρ hρ) m n (by omega)
    f' f.dualMap hf' hg' he' hfi' hgi'
  obtain ⟨r, hrf, hrρ⟩ := equivariant_retraction_of_dual_section
    (costandard k m).ρ ρ f s' hs' hsρ'
  exact equivariant_section_of_retraction (costandard k m).ρ ρ
    (standardRepresentation k n) f g hg he hgi r hrf hrρ

end

universe u
variable (k : Type u) [Field k]

lemma IsRational.of_injective {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (f : M →ₗ[k] N) (hf : Function.Injective f)
    (hi : ∀ g x, f (ρ g x) = σ g (f x)) (hσ : IsRational k σ) :
    IsRational k ρ := by
  intro v l
  obtain ⟨l', hl'⟩ := LinearMap.dualMap_surjective_of_injective hf l
  obtain ⟨P, hP⟩ := hσ (f v) l'
  refine ⟨P, fun g => ?_⟩
  rw [← hP, ← hi]
  exact congrArg (fun a => a (ρ g v)) hl'.symm

lemma IsRational.of_surjective {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (f : M →ₗ[k] N) (hf : Function.Surjective f)
    (hi : ∀ g x, f (ρ g x) = σ g (f x)) (hρ : IsRational k ρ) :
    IsRational k σ := by
  intro v l
  obtain ⟨w, rfl⟩ := hf v
  obtain ⟨P, hP⟩ := hρ w (l.comp f)
  refine ⟨P, fun g => ?_⟩
  rw [← hP]
  change l (σ g (f w)) = l (f (ρ g w))
  rw [hi]

 

lemma regular_linearChange_coeff {ι : Type*} [Fintype ι]
    {S : Type*} {τ : Type*} (z : S → τ → k) (A : S → Matrix ι ι k)
    (hA : ∀ i j, ∃ P : MvPolynomial τ k, ∀ g, A g i j = MvPolynomial.eval (z g) P)
    (v : MvPolynomial ι k) :
    ∀ l : MvPolynomial ι k →ₗ[k] k,
      ∃ P : MvPolynomial τ k, ∀ g, l (linearChange (A g) v) = MvPolynomial.eval (z g) P := by
  classical
  induction v using MvPolynomial.induction_on with
  | C a =>
    intro l
    exact ⟨MvPolynomial.C (l (MvPolynomial.C a)), by simp⟩
  | add v w hv hw =>
    intro l
    obtain ⟨P, hP⟩ := hv l
    obtain ⟨Q, hQ⟩ := hw l
    exact ⟨P + Q, by simp [hP, hQ]⟩
  | mul_X v i hv =>
    intro l
    choose P hP using fun j => hv (l.comp (LinearMap.mulRight k (MvPolynomial.X j)))
    choose Q hQ using fun j => hA j i
    refine ⟨∑ j, Q j * P j, fun g => ?_⟩
    simp only [map_mul, linearChange_X, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm (MvPolynomial.C _), ← mul_assoc, mul_comm _ (MvPolynomial.C _)]
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, hQ]
    change _ = _ * MvPolynomial.eval (z g) (P j)
    rw [← hP]
    rfl

lemma costandard_rational (n : ℕ) : IsRational k (costandard k n).ρ := by
  intro v l
  obtain ⟨l', hl'⟩ := LinearMap.dualMap_surjective_of_injective
    (MvPolynomial.homogeneousSubmodule (Fin 2) k n).injective_subtype l
  obtain ⟨P, hP⟩ := regular_linearChange_coeff k
    (fun g : SL2 k => fun ij : Fin 2 × Fin 2 => g ij.1 ij.2)
    (dualMatrix k) (fun i j => ⟨inverseCoordinatePolynomial k (j,i), fun g => by
      change (g⁻¹ : SL2 k) j i = _
      exact (eval_inverseCoordinatePolynomial k g (j,i)).symm⟩) v.val l'
  refine ⟨P, fun g => ?_⟩
  rw [← hP]
  exact congrArg (fun a => a ((costandard k n).ρ g v)) hl'.symm

end FiberFunctorProof

open CategoryTheory CategoryTheory.Limits
end

end OAI
