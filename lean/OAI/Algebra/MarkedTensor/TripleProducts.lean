import Mathlib
import OAI.Algebra.MarkedTensor.AdjointCoordinates

namespace OAI

/-! Triple coordinate products and cubic nilpotence of local holonomy ideals. -/

noncomputable section
open scoped BigOperators commutatorElement
open Matrix

namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def tripleEvaluation (x y z : Vec₃ R) :
    (Vec₃ R →ₗ[R] Vec₃ R) →ₗ[R]
      (Vec₃ R →ₗ[R] Vec₃ R) →ₗ[R]
        (Vec₃ R →ₗ[R] Vec₃ R) →ₗ[R] Mat₂ R where
  toFun A :=
    { toFun := fun B ↦
        { toFun := fun C ↦ lie (tracelessLM (A x))
            (lie (tracelessLM (B y)) (tracelessLM (C z)))
          map_add' := by
            intro C D
            simp only [LinearMap.add_apply, map_add, lie, mul_add,add_mul]
            noncomm_ring
          map_smul' := by
            intro c C
            simp only [LinearMap.smul_apply, map_smul, lie, mul_smul_comm,
              smul_mul_assoc, ← smul_sub, RingHom.id_apply] }
      map_add' := by
        intro B C; apply LinearMap.ext; intro D
        change lie (tracelessLM (A x))
          (lie (tracelessLM ((B+C) y)) (tracelessLM (D z))) =
          lie (tracelessLM (A x)) (lie (tracelessLM (B y)) (tracelessLM (D z))) +
          lie (tracelessLM (A x)) (lie (tracelessLM (C y)) (tracelessLM (D z)))
        simp only [LinearMap.add_apply, map_add, lie, mul_add,add_mul]
        noncomm_ring
      map_smul' := by
        intro c B; apply LinearMap.ext; intro D
        change lie (tracelessLM (A x))
          (lie (tracelessLM ((c • B) y)) (tracelessLM (D z))) =
          c • lie (tracelessLM (A x)) (lie (tracelessLM (B y)) (tracelessLM (D z)))
        simp only [LinearMap.smul_apply, map_smul, lie, mul_smul_comm,
          smul_mul_assoc, ← smul_sub] }
  map_add' := by
    intro A B; apply LinearMap.ext; intro C; apply LinearMap.ext; intro D
    change lie (tracelessLM ((A+B) x))
      (lie (tracelessLM (C y)) (tracelessLM (D z))) =
      lie (tracelessLM (A x)) (lie (tracelessLM (C y)) (tracelessLM (D z))) +
      lie (tracelessLM (B x)) (lie (tracelessLM (C y)) (tracelessLM (D z)))
    simp only [LinearMap.add_apply, map_add, lie, mul_add,add_mul]
    noncomm_ring
  map_smul' := by
    intro c A; apply LinearMap.ext; intro B; apply LinearMap.ext; intro C
    change lie (tracelessLM ((c • A) x))
      (lie (tracelessLM (B y)) (tracelessLM (C z))) =
      c • lie (tracelessLM (A x)) (lie (tracelessLM (B y)) (tracelessLM (C z)))
    simp only [LinearMap.smul_apply, map_smul, lie, mul_smul_comm,
      smul_mul_assoc, ← smul_sub]

def entriesSubmodule (I : Ideal R) : Submodule R (Mat₂ R) where
  carrier := {A | A ∈ I.matrix (Fin 2)}
  zero_mem' := (I.matrix _).zero_mem
  add_mem' := fun h h' ↦ (I.matrix _).add_mem h h'
  smul_mem' := by
    intro c A h i j
    exact I.mul_mem_left c (h i j)

omit [Algebra ℚ R] in
lemma span_map_mem {V M : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup M] [Module R M] (W : Submodule R M)
    (f : V →ₗ[R] M) {s : Set V} (h : ∀ x ∈ s, f x ∈ W) :
    ∀ x ∈ Submodule.span R s, f x ∈ W := by
  exact fun x hx ↦ (Submodule.span_le.mpr h : Submodule.span R s ≤ W.comap f) hx

omit [Algebra ℚ R] in
lemma span_three_mem {V M : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup M] [Module R M] (W : Submodule R M)
    (f : V →ₗ[R] V →ₗ[R] V →ₗ[R] M) {s : Set V}
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, f a b c ∈ W)
    {a b c : V} (ha : a ∈ Submodule.span R s) (hb : b ∈ Submodule.span R s)
    (hc : c ∈ Submodule.span R s) : f a b c ∈ W := by
  apply span_map_mem W ((f.flip b).flip c) (fun a ha ↦ ?_) a ha
  apply span_map_mem W ((f a).flip c) (fun b hb ↦ ?_) b hb
  exact span_map_mem W (f a b) (h a ha b hb) c hc

noncomputable def rankMap (i j : Fin 3) : Vec₃ R →ₗ[R] Vec₃ R where
  toFun v := v j • Pi.single i 1
  map_add' v w := by simp only [Pi.add_apply,add_smul]
  map_smul' c v := by simp only [Pi.smul_apply,smul_smul,RingHom.id_apply,smul_eq_mul]

 

lemma coordinate_product_mem {H : Type*} (G : H → SpecialLinearGroup (Fin 2) R)
    (hspan : Submodule.span R (Set.range (fun h ↦ adjoint (G h))) = ⊤)
    {J : Ideal R} (x y z : Vec₃ R)
    (h : ∀ a b c, lie (traceless (adjoint (G a) x))
      (lie (traceless (adjoint (G b) y)) (traceless (adjoint (G c) z))) ∈
        J.matrix (Fin 2)) (i j k : Fin 3) : x i*y j*z k ∈ J := by
  have hgen : ∀ A ∈ Set.range (fun h ↦ adjoint (G h)),
      ∀ B ∈ Set.range (fun h ↦ adjoint (G h)),
      ∀ C ∈ Set.range (fun h ↦ adjoint (G h)),
        tripleEvaluation x y z A B C ∈ entriesSubmodule J := by
    rintro A ⟨a,rfl⟩ B ⟨b,rfl⟩ C ⟨c,rfl⟩
    exact h a b c
  have hp (A : Vec₃ R →ₗ[R] Vec₃ R) :
      A ∈ Submodule.span R (Set.range (fun h ↦ adjoint (G h))) := by
    rw [hspan]; trivial
  have hh := span_three_mem (entriesSubmodule J) (tripleEvaluation x y z) hgen
    (hp (rankMap 0 i)) (hp (rankMap 1 j)) (hp (rankMap 2 k))
  have hentry := hh 0 0
  have he : tripleEvaluation x y z (rankMap 0 i) (rankMap 1 j) (rankMap 2 k) 0 0 =
      -2*(x i*y j*z k) := by
    simp [tripleEvaluation,rankMap,tracelessLM,traceless,lie]
    ring
  rw [he] at hentry
  have hmul := J.mul_mem_left (-half (R := R)) hentry
  have heq : (-half (R := R))*(-2*(x i*y j*z k)) = x i*y j*z k := by
    linear_combination (x i*y j*z k)*two_half (R := R)
  rwa [heq] at hmul

end BoundaryOnly.Holonomy
namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators Pointwise
variable {R E : Type*} [CommRing R] [Algebra ℚ R]

def deviationIdeal (z : E → SpecialLinearGroup (Fin 2) R) : Ideal R :=
  Ideal.span (Set.range (fun p : E × Fin 2 × Fin 2 ↦ (mat (z p.1)-1) p.2.1 p.2.2))
noncomputable def coordinateIdeal (z : E → SpecialLinearGroup (Fin 2) R) : Ideal R :=
  Ideal.span (Set.range (fun p : E × Fin 3 ↦ coordinates (mat (z p.1)-1) p.2))

omit [Algebra ℚ R] in
lemma deviation_mem (z : E → SpecialLinearGroup (Fin 2) R) (e : E) :
    mat (z e)-1 ∈ (deviationIdeal z).matrix (Fin 2) :=
  fun i j ↦ Ideal.subset_span ⟨(e,i,j),rfl⟩

lemma coordinates_mem {N : Ideal R} {A : Mat₂ R} (hA : A ∈ N.matrix (Fin 2)) (i : Fin 3) :
    coordinates A i ∈ N := by
  fin_cases i
  · exact hA 0 1
  · exact N.mul_mem_right _ (N.sub_mem (hA 0 0) (hA 1 1))
  · exact hA 1 0

lemma coordinateIdeal_le (z : E → SpecialLinearGroup (Fin 2) R) :
    coordinateIdeal z ≤ deviationIdeal z := by
  apply Ideal.span_le.mpr
  rintro a ⟨⟨e,i⟩,rfl⟩
  exact coordinates_mem (deviation_mem z e) i

omit [Algebra ℚ R] in
lemma trace_deviation_mem {N : Ideal R} (z : SpecialLinearGroup (Fin 2) R)
    (hz : mat z-1 ∈ N.matrix (Fin 2)) : Matrix.trace (mat z-1) ∈ N^2 := by
  have hd := z.property
  change Matrix.det (mat z)=1 at hd
  rw [Matrix.det_fin_two] at hd
  have he : Matrix.trace (mat z-1) =
      -((mat z-1) 0 0*(mat z-1) 1 1-(mat z-1) 0 1*(mat z-1) 1 0) := by
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Matrix.sub_apply,
      Matrix.one_apply, ite_true, show (0:Fin 2) ≠ 1 by decide,
      show (1:Fin 2) ≠ 0 by decide, ite_false, sub_zero]
    linear_combination hd
  rw [he,pow_two]
  exact (N*N).neg_mem ((N*N).sub_mem (Ideal.mul_mem_mul (hz 0 0) (hz 1 1))
    (Ideal.mul_mem_mul (hz 0 1) (hz 1 0)))

omit [Algebra ℚ R] in
lemma scalar_mem {I : Ideal R} {r : R} (hr : r ∈ I) :
    scalar (Fin 2) r ∈ I.matrix (Fin 2) := by
  intro i j
  change (if i=j then r else 0) ∈ I
  split_ifs
  · exact hr
  · exact I.zero_mem

omit [Algebra ℚ R] in
lemma traceless_mem {I : Ideal R} {v : Vec₃ R} (hv : ∀ i, v i ∈ I) :
    traceless v ∈ I.matrix (Fin 2) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hv 1
  · exact hv 0
  · exact hv 2
  · exact I.neg_mem (hv 1)

lemma deviation_le_coordinates (z : E → SpecialLinearGroup (Fin 2) R) :
    deviationIdeal z ≤ coordinateIdeal z ⊔ deviationIdeal z^2 := by
  apply Ideal.span_le.mpr
  rintro a ⟨⟨e,i,j⟩,rfl⟩
  let A := mat (z e)-1
  have hT : traceless (coordinates A) ∈ (coordinateIdeal z).matrix (Fin 2) := by
    apply traceless_mem
    exact fun k ↦ Ideal.subset_span ⟨(e,k),rfl⟩
  have hS : scalar (Fin 2) (Matrix.trace A*half) ∈
      (deviationIdeal z^2).matrix (Fin 2) :=
    scalar_mem ((deviationIdeal z^2).mul_mem_right _
      (trace_deviation_mem (z e) (deviation_mem z e)))
  have he : A = traceless (coordinates A)+scalar (Fin 2) (Matrix.trace A*half) := by
    rw [traceless_coordinates]; abel
  change A i j ∈ coordinateIdeal z ⊔ deviationIdeal z^2
  rw [he, Matrix.add_apply]
  exact Submodule.add_mem_sup (hT i j) (hS i j)

 

lemma deviationIdeal_eq_coordinates [IsNoetherianRing R] [IsLocalRing R]
    (z : E → SpecialLinearGroup (Fin 2) R)
    (hz : deviationIdeal z ≤ IsLocalRing.maximalIdeal R) :
    deviationIdeal z = coordinateIdeal z := by
  apply le_antisymm _ (coordinateIdeal_le z)
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian (deviationIdeal z))
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  apply (deviation_le_coordinates z).trans
  apply sup_le_sup_left
  change deviationIdeal z^2 ≤ IsLocalRing.maximalIdeal R * deviationIdeal z
  rw [pow_two]
  exact Ideal.mul_mono hz le_rfl

lemma coordinate_cube_le (z : E → SpecialLinearGroup (Fin 2) R) (J : Ideal R)
    (h : ∀ e f g i j k, coordinates (mat (z e)-1) i *
      coordinates (mat (z f)-1) j*coordinates (mat (z g)-1) k ∈ J) :
    coordinateIdeal z^3 ≤ J := by
  rw [show (3:ℕ)=2+1 by rfl, pow_succ, pow_two]
  simp only [coordinateIdeal, Ideal.span_mul_span]
  apply Ideal.span_le.mpr
  rintro a ⟨b,⟨c,⟨⟨e,i⟩,rfl⟩,d,⟨⟨f,j⟩,rfl⟩,rfl⟩,
    e',⟨⟨g,k⟩,rfl⟩,rfl⟩
  exact h e f g i j k

end BoundaryOnly.Holonomy
namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators commutatorElement
variable {R E H : Type*} [CommRing R] [Algebra ℚ R]

 

theorem cubic_nilpotence_local [IsNoetherianRing R] [IsLocalRing R]
    (z : E → SpecialLinearGroup (Fin 2) R)
    (u G : H → SpecialLinearGroup (Fin 2) R)
    (hz : ∀ e, mat (z e)-1 ∈ (IsLocalRing.maximalIdeal R).matrix (Fin 2))
    (hu : ∀ c, mat (u c)-mat (G c) ∈ (IsLocalRing.maximalIdeal R).matrix (Fin 2))
    (hspan : Submodule.span R (Set.range (fun h ↦ adjoint (G h))) = ⊤)
    (hrel : ∀ e f g a b c,
      ⁅u a*z e*(u a)⁻¹,⁅u b*z f*(u b)⁻¹,u c*z g*(u c)⁻¹⁆⁆ = 1) :
    deviationIdeal z^3 = ⊥ := by
  let m := IsLocalRing.maximalIdeal R
  let N := deviationIdeal z
  have hNm : N ≤ m := by
    apply Ideal.span_le.mpr
    rintro x ⟨⟨e,i,j⟩,rfl⟩
    exact hz e i j
  have hNT := deviationIdeal_eq_coordinates z hNm
  have hproducts (e f g : E) (i j k : Fin 3) :
      coordinates (mat (z e)-1) i*coordinates (mat (z f)-1) j*
        coordinates (mat (z g)-1) k ∈ m*N^3 := by
    apply coordinate_product_mem G hspan
    intro a b c
    exact reference_traceless_triple hNm (hu a) (hu b) (hu c)
      (deviation_mem z e) (deviation_mem z f) (deviation_mem z g) (hrel e f g a b c)
  have hle : N^3 ≤ m*N^3 := by
    change deviationIdeal z^3 ≤ m*N^3
    rw [hNT]
    exact coordinate_cube_le z (m*N^3) hproducts
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m (N^3)
    (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)

end BoundaryOnly.Holonomy
end

end OAI
