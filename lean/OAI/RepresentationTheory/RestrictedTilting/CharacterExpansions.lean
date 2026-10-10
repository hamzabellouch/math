import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.SL2Definitions

namespace OAI

/-! Character expansions on the diagonal torus and additive root group. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section

universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {M : Type w} [AddCommGroup M] [Module k M]

 
lemma character_sum_eq_zero (s : Finset (G →* k)) (c : (G →* k) → M)
    (h : ∀ g, ∑ χ ∈ s, χ g • c χ = 0) : ∀ χ ∈ s, c χ = 0 := by
  intro χ hχ
  apply (Module.forall_dual_apply_eq_zero_iff k (c χ)).mp
  intro φ
  apply (linearIndependent_iff'.mp (linearIndependent_monoidHom G k)) s
    (fun ψ => φ (c ψ)) ?_ χ hχ
  ext g
  have hg := congrArg φ (h g)
  simpa only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply, mul_comm] using hg

 
def HasCharacterExpansions (ρ : Representation k G M) : Prop :=
  ∀ v : M, ∃ c : (G →* k) →₀ M, ∀ g : G,
    ρ g v = c.sum (fun χ x => χ g • x)

lemma character_finsupp_eq_zero (c : (G →* k) →₀ M)
    (h : ∀ g, c.sum (fun χ x => χ g • x) = 0) : c = 0 := by
  classical
  ext χ
  by_cases hχ : χ ∈ c.support
  · exact character_sum_eq_zero c.support c h χ hχ
  · simpa using Finsupp.notMem_support_iff.mp hχ

lemma character_finsupp_ext (c d : (G →* k) →₀ M)
    (h : ∀ g, c.sum (fun χ x => χ g • x) = d.sum (fun χ x => χ g • x)) : c = d := by
  apply sub_eq_zero.mp
  apply character_finsupp_eq_zero
  intro g
  rw [Finsupp.sum_sub_index]
  · exact sub_eq_zero.mpr (h g)
  · intro χ x y
    exact smul_sub _ _ _

 
lemma character_coefficient_eigen (ρ : Representation k G M) (v : M)
    (c : (G →* k) →₀ M)
    (hc : ∀ g, ρ g v = c.sum (fun χ x => χ g • x)) :
    ∀ χ g, ρ g (c χ) = χ g • c χ := by
  classical
  intro χ t
  by_cases hχ : χ ∈ c.support
  · apply sub_eq_zero.mp
    apply character_sum_eq_zero c.support
      (fun ψ => ρ t (c ψ) - ψ t • c ψ) ?_ χ hχ
    intro g
    calc
      ∑ ψ ∈ c.support, ψ g • (ρ t (c ψ) - ψ t • c ψ) =
          ρ t (c.sum (fun ψ x => ψ g • x)) -
            c.sum (fun ψ x => ψ (t * g) • x) := by
        simp only [Finsupp.sum, map_sum, map_smul, smul_sub,
          Finset.sum_sub_distrib, map_mul, mul_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro ψ hψ
        exact smul_comm _ _ _
      _ = 0 := by rw [← hc, ← hc, map_mul]; simp
  · rw [Finsupp.notMem_support_iff.mp hχ, map_zero, smul_zero]

 

lemma eigenvector_lift {N : Type*} [AddCommGroup N] [Module k N]
    (ρ : Representation k G M) (σ : Representation k G N)
    (hρ : HasCharacterExpansions ρ) (f : M →ₗ[k] N)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hs : Function.Surjective f)
    (χ : G →* k) (w : N) (hw : ∀ g, σ g w = χ g • w) :
    ∃ v : M, f v = w ∧ ∀ g, ρ g v = χ g • v := by
  classical
  obtain ⟨v, hv⟩ := hs w
  obtain ⟨c, hc⟩ := hρ v
  have hcf : c.mapRange f f.map_zero = Finsupp.single χ w := by
    apply character_finsupp_ext
    intro g
    rw [Finsupp.sum_mapRange_index (fun _ => smul_zero _),
      Finsupp.sum_single_index (h := fun ψ : G →* k => fun x : N => ψ g • x)
        (smul_zero (χ g))]
    calc
      c.sum (fun ψ x => ψ g • f x) = f (c.sum (fun ψ x => ψ g • x)) := by
        simp only [Finsupp.sum, map_sum, map_smul]
      _ = χ g • w := by rw [← hc, hf, hv, hw]
  refine ⟨c χ, ?_, character_coefficient_eigen ρ v c hc χ⟩
  have := congrArg (fun d : (G →* k) →₀ N => d χ) hcf
  simpa using this

 
def characterFunctions : Submonoid (G → k) where
  carrier := Set.range (fun χ : G →* k => (χ : G → k))
  one_mem' := ⟨1, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨χ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨χ * ψ, rfl⟩

noncomputable def characterAlgebra : Subalgebra k (G → k) :=
  Algebra.adjoin k (characterFunctions (k := k) (G := G) : Set (G → k))

lemma characterAlgebra_toSubmodule :
    (characterAlgebra (k := k) (G := G)).toSubmodule =
      Submodule.span k (Set.range (fun χ : G →* k => (χ : G → k))) := by
  rw [characterAlgebra, Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rfl

lemma mem_characterAlgebra_iff (f : G → k) :
    f ∈ characterAlgebra (k := k) (G := G) ↔ ∃ c : (G →* k) →₀ k,
      ∀ g, f g = c.sum (fun χ x => χ g * x) := by
  change f ∈ (characterAlgebra (k := k) (G := G)).toSubmodule ↔ _
  rw [characterAlgebra_toSubmodule, Finsupp.mem_span_range_iff_exists_finsupp]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun g => ?_⟩
    have := congrFun hc g
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using this.symm
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext g
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using (hc g).symm

lemma character_mem_characterAlgebra (χ : G →* k) :
    (χ : G → k) ∈ characterAlgebra (k := k) (G := G) :=
  Algebra.subset_adjoin ⟨χ, rfl⟩

noncomputable def characterEvaluation (g : G) : ((G →* k) →₀ M) →ₗ[k] M :=
  Finsupp.lsum k (fun χ : G →* k => χ g • (LinearMap.id : M →ₗ[k] M))

lemma characterEvaluation_apply (g : G) (c : (G →* k) →₀ M) :
    characterEvaluation g c = c.sum (fun χ x => χ g • x) := rfl

 

lemma characterExpansions_of_coefficients [Module.Finite k M]
    (ρ : Representation k G M)
    (h : ∀ (v : M) (φ : M →ₗ[k] k),
      (fun g => φ (ρ g v)) ∈ characterAlgebra (k := k) (G := G)) :
    HasCharacterExpansions ρ := by
  classical
  intro v
  let b := Module.finBasis k M
  choose c hc using fun i => (mem_characterAlgebra_iff _).mp (h v (b.coord i))
  let c' : (G →* k) →₀ M :=
    ∑ i, (c i).mapRange (LinearMap.toSpanSingleton k M (b i)) (map_zero _)
  refine ⟨c', fun g => ?_⟩
  change ρ g v = characterEvaluation g c'
  dsimp only [c']
  rw [map_sum]
  calc
    ρ g v = ∑ i, b.repr (ρ g v) i • b i := (b.sum_repr (ρ g v)).symm
    _ = ∑ i, characterEvaluation g
        ((c i).mapRange (LinearMap.toSpanSingleton k M (b i)) (map_zero _)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [characterEvaluation_apply, Finsupp.sum_mapRange_index (fun _ => smul_zero _)]
      simp only [LinearMap.toSpanSingleton_apply, ← mul_smul, Finsupp.sum,
        ← Finset.sum_smul]
      congr 1
      exact hc i g

end

section

universe u
variable (k : Type u) [Field k]

 
def diagonalTorus : kˣ →* SL2 k where
  toFun a := ⟨!![(a : k), 0; 0, (↑a⁻¹ : k)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![(↑(a * b) : k), 0; 0, (↑(a * b)⁻¹ : k)] =
      !![(a : k), 0; 0, (↑a⁻¹ : k)] * !![(b : k), 0; 0, (↑b⁻¹ : k)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def inverseUnitCharacter : kˣ →* k where
  toFun a := ↑a⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm]

lemma diagonal_coordinate_mem_characterAlgebra (i j : Fin 2) :
    (fun a : kˣ => diagonalTorus k a i j) ∈
      characterAlgebra (k := k) (G := kˣ) := by
  fin_cases i <;> fin_cases j
  · exact character_mem_characterAlgebra (Units.coeHom k)
  · exact (characterAlgebra (k := k) (G := kˣ)).zero_mem
  · exact (characterAlgebra (k := k) (G := kˣ)).zero_mem
  · exact character_mem_characterAlgebra (inverseUnitCharacter k)

lemma polynomial_on_torus_mem_characterAlgebra
    (P : MvPolynomial (Fin 2 × Fin 2) k) :
    (fun a : kˣ => MvPolynomial.eval (fun ij => diagonalTorus k a ij.1 ij.2) P) ∈
      characterAlgebra (k := k) (G := kˣ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C, Pi.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply] using
      (characterAlgebra (k := k) (G := kˣ)).algebraMap_mem c
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval_add, Pi.add_def] using
      (characterAlgebra (k := k) (G := kˣ)).add_mem hP hQ
  | mul_X P ij hP =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.mul_def] using
      (characterAlgebra (k := k) (G := kˣ)).mul_mem hP
        (diagonal_coordinate_mem_characterAlgebra k ij.1 ij.2)

 

lemma rational_torus_characterExpansions {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M] (ρ : Representation k (SL2 k) M)
    (hρ : IsRational k ρ) : HasCharacterExpansions (ρ.comp (diagonalTorus k)) := by
  apply characterExpansions_of_coefficients
  intro v φ
  obtain ⟨P, hP⟩ := hρ v φ
  have heq : (fun a : kˣ => φ ((ρ.comp (diagonalTorus k)) a v)) =
      (fun a : kˣ => MvPolynomial.eval (fun ij => diagonalTorus k a ij.1 ij.2) P) := by
    funext a
    exact hP (diagonalTorus k a)
  rw [heq]
  exact polynomial_on_torus_mem_characterAlgebra k P

 
lemma rational_weight_lift {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module.Finite k M]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (hρ : IsRational k ρ) (f : M →ₗ[k] N)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hs : Function.Surjective f)
    (χ : kˣ →* k) (w : N) (hw : ∀ a, σ (diagonalTorus k a) w = χ a • w) :
    ∃ v : M, f v = w ∧ ∀ a, ρ (diagonalTorus k a) v = χ a • v :=
  eigenvector_lift (ρ.comp (diagonalTorus k)) (σ.comp (diagonalTorus k))
    (rational_torus_characterExpansions k ρ hρ) f
    (fun a v => hf (diagonalTorus k a) v) hs χ w hw

 
def integerCharacter (n : ℤ) : kˣ →* k :=
  (Units.coeHom k).comp (zpowGroupHom n)

lemma unit_power_functions_injective [Infinite k] :
    Function.Injective (fun n : ℕ => fun a : kˣ => (a : k) ^ n) := by
  intro n m h
  have hp : (Polynomial.X : Polynomial k) ^ n = Polynomial.X ^ m := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.finite_singleton (0 : k)).infinite_compl.mono
    intro a ha
    have ha0 : a ≠ 0 := ha
    simpa only [Polynomial.eval_pow, Polynomial.eval_X, Units.val_mk0, Set.mem_ofPred_eq] using
      congrFun h (Units.mk0 a ha0)
  have := congrArg Polynomial.natDegree hp
  simpa using this

lemma integerCharacter_injective [Infinite k] : Function.Injective (integerCharacter k) := by
  intro n m h
  have hz (a : kˣ) : a ^ (n - m) = 1 := by
    rw [zpow_sub, mul_inv_eq_one]
    apply Units.ext
    exact DFunLike.congr_fun h a
  have hn : (n - m).natAbs = 0 := by
    apply unit_power_functions_injective k
    funext a
    have ht : a ^ (n - m).natAbs = 1 := (pow_natAbs_eq_one).mpr (hz a)
    simpa using congrArg (fun x : kˣ => (x : k)) ht
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hn)

end

section

universe u v w
variable {k : Type u} [Field k] {G : Type v}
variable {M : Type w} [AddCommGroup M] [Module k M]

 

lemma vector_expansion_of_scalar_span [Module.Finite k M]
    {I : Type*} (f : G → M) (e : I → G → k)
    (h : ∀ φ : M →ₗ[k] k, (fun g => φ (f g)) ∈ Submodule.span k (Set.range e)) :
    ∃ c : I →₀ M, ∀ g, f g = c.sum (fun i x => e i g • x) := by
  classical
  let b := Module.finBasis k M
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.mp (h (b.coord i))
  let c' : I →₀ M :=
    ∑ i, (c i).mapRange (LinearMap.toSpanSingleton k M (b i)) (map_zero _)
  refine ⟨c', fun g => ?_⟩
  let E : (I →₀ M) →ₗ[k] M :=
    Finsupp.lsum k (fun i => e i g • (LinearMap.id : M →ₗ[k] M))
  change f g = E c'
  dsimp only [c']
  rw [map_sum]
  calc
    f g = ∑ i, b.repr (f g) i • b i := (b.sum_repr (f g)).symm
    _ = ∑ i, E ((c i).mapRange (LinearMap.toSpanSingleton k M (b i)) (map_zero _)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change _ = ((c i).mapRange _ _).sum (fun j x => e j g • x)
      rw [Finsupp.sum_mapRange_index (fun _ => smul_zero _)]
      simp only [LinearMap.toSpanSingleton_apply, ← mul_smul, Finsupp.sum,
        ← Finset.sum_smul]
      congr 1
      have hi' := congrFun (hc i) g
      simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_comm, Module.Basis.coord_apply] using hi'.symm

end

section

universe u
variable (k : Type u) [Field k]

 
def integerFunctions : Submonoid (kˣ → k) where
  carrier := Set.range (fun n : ℤ => (integerCharacter k n : kˣ → k))
  one_mem' := ⟨0, by ext a; simp [integerCharacter]⟩
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    refine ⟨n + m, ?_⟩
    ext a
    simp [integerCharacter, zpow_add]

noncomputable def integerAlgebra : Subalgebra k (kˣ → k) :=
  Algebra.adjoin k (integerFunctions k : Set (kˣ → k))

lemma integerAlgebra_toSubmodule : (integerAlgebra k).toSubmodule =
    Submodule.span k (Set.range (fun n : ℤ => (integerCharacter k n : kˣ → k))) := by
  rw [integerAlgebra, Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rfl

lemma integerCharacter_mem_integerAlgebra (n : ℤ) :
    (integerCharacter k n : kˣ → k) ∈ integerAlgebra k :=
  Algebra.subset_adjoin ⟨n, rfl⟩

lemma diagonal_coordinate_mem_integerAlgebra (i j : Fin 2) :
    (fun a : kˣ => diagonalTorus k a i j) ∈ integerAlgebra k := by
  fin_cases i <;> fin_cases j
  · convert integerCharacter_mem_integerAlgebra k 1 using 1
    ext a
    change (a : k) = integerCharacter k 1 a
    simp [integerCharacter]
  · exact (integerAlgebra k).zero_mem
  · exact (integerAlgebra k).zero_mem
  · convert integerCharacter_mem_integerAlgebra k (-1) using 1
    ext a
    change (↑a⁻¹ : k) = integerCharacter k (-1) a
    simp [integerCharacter]

lemma polynomial_on_torus_mem_integerAlgebra
    (P : MvPolynomial (Fin 2 × Fin 2) k) :
    (fun a : kˣ => MvPolynomial.eval (fun ij => diagonalTorus k a ij.1 ij.2) P) ∈
      integerAlgebra k := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C, Pi.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply] using (integerAlgebra k).algebraMap_mem c
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval_add, Pi.add_def] using (integerAlgebra k).add_mem hP hQ
  | mul_X P ij hP =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.mul_def] using
      (integerAlgebra k).mul_mem hP (diagonal_coordinate_mem_integerAlgebra k ij.1 ij.2)

 

lemma rational_torus_integerExpansions {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M] (ρ : Representation k (SL2 k) M)
    (hρ : IsRational k ρ) (v : M) : ∃ c : ℤ →₀ M, ∀ a : kˣ,
      ρ (diagonalTorus k a) v = c.sum (fun n x => integerCharacter k n a • x) := by
  apply vector_expansion_of_scalar_span
  intro φ
  obtain ⟨P, hP⟩ := hρ v φ
  have heq : (fun a : kˣ => φ (ρ (diagonalTorus k a) v)) =
      (fun a : kˣ => MvPolynomial.eval (fun ij => diagonalTorus k a ij.1 ij.2) P) := by
    funext a
    exact hP (diagonalTorus k a)
  rw [heq, ← integerAlgebra_toSubmodule]
  exact polynomial_on_torus_mem_integerAlgebra k P

end

section

universe u v w
variable {k : Type u} [Field k] {G : Type v}
variable {M : Type w} [AddCommGroup M] [Module k M]

lemma function_sum_eq_zero {I : Type*} (e : I → G → k)
    (he : LinearIndependent k e) (s : Finset I) (c : I → M)
    (h : ∀ g, ∑ i ∈ s, e i g • c i = 0) : ∀ i ∈ s, c i = 0 := by
  intro i hi
  apply (Module.forall_dual_apply_eq_zero_iff k (c i)).mp
  intro φ
  apply (linearIndependent_iff'.mp he) s (fun j => φ (c j)) ?_ i hi
  ext g
  have hg := congrArg φ (h g)
  simpa only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply, mul_comm] using hg

lemma function_finsupp_eq_zero {I : Type*} (e : I → G → k)
    (he : LinearIndependent k e) (c : I →₀ M)
    (h : ∀ g, c.sum (fun i x => e i g • x) = 0) : c = 0 := by
  classical
  ext i
  by_cases hi : i ∈ c.support
  · exact function_sum_eq_zero e he c.support c h i hi
  · simpa using Finsupp.notMem_support_iff.mp hi

lemma function_finsupp_ext {I : Type*} (e : I → G → k)
    (he : LinearIndependent k e) (c d : I →₀ M)
    (h : ∀ g, c.sum (fun i x => e i g • x) = d.sum (fun i x => e i g • x)) : c = d := by
  apply sub_eq_zero.mp
  apply function_finsupp_eq_zero e he
  intro g
  rw [Finsupp.sum_sub_index]
  · exact sub_eq_zero.mpr (h g)
  · intro χ x y
    exact smul_sub _ _ _

variable (k)

lemma linearIndependent_powerFunctions [Infinite k] :
    LinearIndependent k (fun (n : ℕ) (x : k) => x ^ n) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  have hp : (∑ j ∈ s, Polynomial.monomial j (a j)) = (0 : Polynomial k) := by
    apply Polynomial.funext
    intro x
    have hx := congrFun ha x
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      Polynomial.eval_zero, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] using hx
  have hc := congrArg (fun p : Polynomial k => p.coeff i) hp
  simpa [Polynomial.coeff_monomial, hi] using hc

end

universe u
variable (k : Type u) [Field k]

def powerFunctions : Submonoid (k → k) where
  carrier := Set.range (fun n : ℕ => fun t : k => t ^ n)
  one_mem' := ⟨0, by ext t; simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, by ext t; exact pow_add t n m⟩

noncomputable def powerAlgebra : Subalgebra k (k → k) :=
  Algebra.adjoin k (powerFunctions k : Set (k → k))

lemma powerAlgebra_toSubmodule : (powerAlgebra k).toSubmodule =
    Submodule.span k (Set.range (fun (n : ℕ) (t : k) => t ^ n)) := by
  rw [powerAlgebra, Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rfl

lemma power_mem_powerAlgebra (n : ℕ) :
    (fun t : k => t ^ n) ∈ powerAlgebra k := Algebra.subset_adjoin ⟨n, rfl⟩

lemma unipotent_coordinate_mem_powerAlgebra (i j : Fin 2) :
    (fun t : k => unipotent k t i j) ∈ powerAlgebra k := by
  fin_cases i <;> fin_cases j
  · exact (powerAlgebra k).one_mem
  · change (fun t : k => t) ∈ powerAlgebra k
    simpa only [pow_one] using power_mem_powerAlgebra k 1
  · exact (powerAlgebra k).zero_mem
  · exact (powerAlgebra k).one_mem

lemma polynomial_on_unipotent_mem_powerAlgebra
    (P : MvPolynomial (Fin 2 × Fin 2) k) :
    (fun t : k => MvPolynomial.eval (fun ij => unipotent k t ij.1 ij.2) P) ∈
      powerAlgebra k := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C, Pi.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply] using (powerAlgebra k).algebraMap_mem c
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval_add, Pi.add_def] using (powerAlgebra k).add_mem hP hQ
  | mul_X P ij hP =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.mul_def] using
      (powerAlgebra k).mul_mem hP (unipotent_coordinate_mem_powerAlgebra k ij.1 ij.2)

lemma rational_unipotent_expansion {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M] (ρ : Representation k (SL2 k) M)
    (hρ : IsRational k ρ) (v : M) : ∃ c : ℕ →₀ M, ∀ t : k,
      ρ (unipotent k t) v = c.sum (fun n x => t ^ n • x) := by
  apply vector_expansion_of_scalar_span
  intro φ
  obtain ⟨P, hP⟩ := hρ v φ
  have heq : (fun t : k => φ (ρ (unipotent k t) v)) =
      (fun t : k => MvPolynomial.eval (fun ij => unipotent k t ij.1 ij.2) P) := by
    funext t
    exact hP (unipotent k t)
  rw [heq, ← powerAlgebra_toSubmodule]
  exact polynomial_on_unipotent_mem_powerAlgebra k P

lemma diagonal_unipotent (a : kˣ) (t : k) :
    diagonalTorus k a * unipotent k t =
      unipotent k ((a : k) ^ 2 * t) * diagonalTorus k a := by
  apply Subtype.ext
  change !![(a : k), 0; 0, (↑a⁻¹ : k)] * !![1, t; 0, 1] =
    !![1, (a : k) ^ 2 * t; 0, 1] * !![(a : k), 0; 0, (↑a⁻¹ : k)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc, mul_comm]

 

lemma unipotent_coefficient_weight [Infinite k] {M : Type u}
    [AddCommGroup M] [Module k M] (ρ : Representation k (SL2 k) M)
    (v : M) (n : ℤ) (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
    (c : ℕ →₀ M) (hc : ∀ t, ρ (unipotent k t) v = c.sum (fun i x => t ^ i • x)) :
    ∀ i a, ρ (diagonalTorus k a) (c i) = integerCharacter k (n + 2 * i) a • c i := by
  classical
  intro i a
  by_cases hi : i ∈ c.support
  · apply sub_eq_zero.mp
    apply function_sum_eq_zero (fun (j : ℕ) (t : k) => t ^ j)
      (linearIndependent_powerFunctions k) c.support
      (fun j => ρ (diagonalTorus k a) (c j) - integerCharacter k (n + 2 * j) a • c j)
      ?_ i hi
    intro t
    calc
      ∑ j ∈ c.support, t ^ j •
          (ρ (diagonalTorus k a) (c j) - integerCharacter k (n + 2 * j) a • c j) =
          ρ (diagonalTorus k a) (c.sum (fun j x => t ^ j • x)) -
            integerCharacter k n a • c.sum (fun j x => ((a : k) ^ 2 * t) ^ j • x) := by
        simp only [Finsupp.sum, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
          Finset.smul_sum, smul_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        simp [integerCharacter, zpow_add, zpow_mul, mul_pow, ← pow_mul, mul_comm, mul_left_comm]
      _ = 0 := by
        rw [← hc, ← hc]
        apply sub_eq_zero.mpr
        have hh := congrArg (fun g => ρ g v) (diagonal_unipotent k a t)
        simpa only [map_mul, Module.End.mul_apply, hv, map_smul] using hh
  · rw [Finsupp.notMem_support_iff.mp hi, map_zero, smul_zero]

end FiberFunctorProof
end

end OAI
