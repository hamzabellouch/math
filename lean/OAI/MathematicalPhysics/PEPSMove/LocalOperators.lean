import Mathlib
import OAI.MathematicalPhysics.PEPSMove.GridStates

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace PolynomialPEPS.PhysicalMove
open Matrix

@[simp] theorem joinConfigurations_left {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ)
    (v : {v : Vertex L // v ∈ A}) : joinConfigurations A x z v = x v := by
  simp [joinConfigurations, v.property]

@[simp] theorem joinConfigurations_right {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ)
    (v : {v : Vertex L // v ∈ Aᶜ}) : joinConfigurations A x z v = z v := by
  simp [joinConfigurations, Finset.mem_compl.mp v.property]

def joinEquiv {L q : ℕ} (A : Finset (Vertex L)) :
    (RegionConfiguration q A × RegionConfiguration q Aᶜ) ≃ Configuration L q where
  toFun x := joinConfigurations A x.1 x.2
  invFun x := (fun v => x v.val, fun v => x v.val)
  left_inv x := by ext v <;> simp
  right_inv x := by
    funext v
    simp only [joinConfigurations]
    split_ifs <;> rfl

@[simp] theorem joinEquiv_apply {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A × RegionConfiguration q Aᶜ) :
    joinEquiv A x = joinConfigurations A x.1 x.2 := rfl

@[simp] theorem joinEquiv_symm_join {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) :
    (joinEquiv A).symm (joinConfigurations A x z) = (x,z) :=
  (joinEquiv A).symm_apply_apply (x,z)

@[simp] theorem liftLocal_join {L q : ℕ} (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (x y : RegionConfiguration q A) (z w : RegionConfiguration q Aᶜ) :
    liftLocal A a (joinConfigurations A x z) (joinConfigurations A y w) =
      a x y * (if z = w then 1 else 0) := by
  classical
  have hout : (∀ v, v ∉ A → joinConfigurations A x z v = joinConfigurations A y w v)
      ↔ z = w := by
    constructor
    · intro h
      funext v
      simpa [joinConfigurations, Finset.mem_compl.mp v.property] using
        h v (Finset.mem_compl.mp v.property)
    · intro h v hv
      simp [joinConfigurations, hv, h]
  simp only [liftLocal, hout]
  have hx : (fun v : {v : Vertex L // v ∈ A} => joinConfigurations A x z v) = x := by
    funext v
    exact joinConfigurations_left A x z v
  have hy : (fun v : {v : Vertex L // v ∈ A} => joinConfigurations A y w v) = y := by
    funext v
    exact joinConfigurations_left A y w v
  rw [hx, hy]
  split_ifs <;> simp

                                                                             
theorem liftLocal_eq_reindex {L q : ℕ} (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A a = Matrix.reindex (joinEquiv A) (joinEquiv A)
      (Matrix.kronecker a (1 : Matrix (RegionConfiguration q Aᶜ)
        (RegionConfiguration q Aᶜ) ℂ)) := by
  classical
  apply Matrix.ext
  intro x y
  obtain ⟨⟨u,z⟩,rfl⟩ := (joinEquiv (q := q) A).surjective x
  obtain ⟨⟨v,w⟩,rfl⟩ := (joinEquiv (q := q) A).surjective y
  simp only [Matrix.reindex_apply]
  simp [Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply]

@[simp] theorem liftLocal_one {L q : ℕ} (A : Finset (Vertex L)) :
    liftLocal A (1 : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) = 1 := by
  classical
  rw [liftLocal_eq_reindex]
  simp only [Matrix.kronecker, Matrix.one_kronecker_one]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (joinEquiv A)).map_one

@[simp] theorem liftLocal_mul {L q : ℕ} (A : Finset (Vertex L))
    (a b : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A (a*b) = liftLocal A a * liftLocal A b := by
  classical
  simp only [liftLocal_eq_reindex]
  have hk := Matrix.mul_kronecker_mul a b
    (1 : Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ) (1 : Matrix (RegionConfiguration q Aᶜ)
      (RegionConfiguration q Aᶜ) ℂ)
  simp only [Matrix.one_mul] at hk
  simp only [Matrix.kronecker]
  rw [hk]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (joinEquiv A)).map_mul _ _

@[simp] theorem liftLocal_star {L q : ℕ} (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A (star a) = star (liftLocal A a) := by
  classical
  simp only [liftLocal_eq_reindex, Matrix.star_eq_conjTranspose]
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker]
  simp

@[simp] theorem liftLocal_zero {L q : ℕ} (A : Finset (Vertex L)) :
    liftLocal A (0 : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) = 0 := by
  classical
  ext x y
  simp only [liftLocal, Matrix.zero_apply]
  split_ifs <;> rfl

@[simp] theorem liftLocal_add {L q : ℕ} (A : Finset (Vertex L))
    (a b : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A (a+b) = liftLocal A a + liftLocal A b := by
  classical
  ext x y
  simp only [liftLocal, Matrix.add_apply]
  split_ifs <;> simp

@[simp] theorem liftLocal_smul {L q : ℕ} (A : Finset (Vertex L)) (c : ℂ)
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A (c • a) = c • liftLocal A a := by
  classical
  ext x y
  simp only [liftLocal, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

                                                                            
def localLiftHom {L q : ℕ} (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ →⋆ₐ[ℂ]
      Operator L q where
  toFun := liftLocal A
  map_one' := liftLocal_one A
  map_mul' := liftLocal_mul A
  map_zero' := by ext x y; simp [liftLocal]
  map_add' := liftLocal_add A
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, liftLocal_smul, liftLocal_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm
  map_star' := liftLocal_star A

open scoped Matrix.Norms.L2Operator in
                                                                               
theorem opNorm_liftLocal_le {L q : ℕ} (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    opNorm (liftLocal A a) ≤ ‖a‖ := by
  change ‖Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) (liftLocal A a)‖ ≤ ‖a‖
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact NonUnitalStarAlgHom.norm_apply_le (localLiftHom A) a

@[simp] theorem asMap_liftLocal_join {L q : ℕ} (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (Ω : State L q) (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) :
    asMap (liftLocal A a) Ω (joinConfigurations A x z) =
      ∑ y, a x y * Ω (joinConfigurations A y z) := by
  classical
  change (∑ y, liftLocal A a (joinConfigurations A x z) y * Ω y) = _
  rw [← Equiv.sum_comp (joinEquiv A)]
  simp only [Fintype.sum_prod_type, joinEquiv_apply, liftLocal_join]
  simp

theorem reducedDensity_posSemidef {L q : ℕ} (Ω : State L q)
    (A : Finset (Vertex L)) : (reducedDensity Ω A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

                                                                             
theorem inner_liftLocal_trace {L q : ℕ} (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (Ω : State L q) :
    inner ℂ Ω (asMap (liftLocal A a) Ω) = Matrix.trace (a * reducedDensity Ω A) := by
  classical
  rw [PiLp.inner_apply, ← Equiv.sum_comp (joinEquiv A)]
  simp only [Fintype.sum_prod_type, joinEquiv_apply, asMap_liftLocal_join,
    RCLike.inner_apply, Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, reducedDensity,
    Matrix.conjTranspose_apply, coefficientMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  simp only [starRingEnd_apply]
  ring

                                                                  
def restrictRegion {L q : ℕ} {A B : Finset (Vertex L)} (h : A ⊆ B)
    (x : RegionConfiguration q B) : RegionConfiguration q A :=
  fun v => x ⟨v.val, h v.property⟩

                                                                            
def liftBetween {L q : ℕ} {A B : Finset (Vertex L)} (h : A ⊆ B)
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    Matrix (RegionConfiguration q B) (RegionConfiguration q B) ℂ := by
  classical
  exact fun x y => if ∀ v : {v : Vertex L // v ∈ B}, v.val ∉ A → x v = y v
    then a (restrictRegion h x) (restrictRegion h y) else 0

theorem liftLocal_liftBetween {L q : ℕ} {A B : Finset (Vertex L)} (h : A ⊆ B)
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal B (liftBetween h a) = liftLocal A a := by
  classical
  ext x y
  have heq : (∀ v, v ∉ A → x v = y v) ↔
      (∀ v, v ∉ B → x v = y v) ∧
        (∀ v : {v : Vertex L // v ∈ B}, v.val ∉ A → x v.val = y v.val) := by
    constructor
    · intro ha
      exact ⟨fun v hv => ha v (fun hva => hv (h hva)), fun v hv => ha v hv⟩
    · rintro ⟨hb, hi⟩ v hv
      by_cases hvb : v ∈ B
      · exact hi ⟨v,hvb⟩ hv
      · exact hb v hvb
  simp only [liftLocal, liftBetween, heq]
  split_ifs <;> simp_all
  rfl

theorem liftLocal_injective {L q : ℕ} (hq : 0 < q) (A : Finset (Vertex L)) :
    Function.Injective (liftLocal (q := q) A) := by
  classical
  intro a b hab
  ext x y
  let z : RegionConfiguration q Aᶜ := fun _ => ⟨0,hq⟩
  have h := congrArg (fun M => M (joinConfigurations A x z)
    (joinConfigurations A y z)) hab
  simpa only [liftLocal_join, ite_true, mul_one] using h

                                                                             
                                                               
def liftBetweenHom {L q : ℕ} (hq : 0 < q) {A B : Finset (Vertex L)} (h : A ⊆ B) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ →⋆ₐ[ℂ]
      Matrix (RegionConfiguration q B) (RegionConfiguration q B) ℂ where
  toFun := liftBetween h
  map_one' := by
    apply liftLocal_injective hq B
    simp [liftLocal_liftBetween]
  map_mul' a b := by
    apply liftLocal_injective hq B
    simp [liftLocal_liftBetween]
  map_zero' := by
    apply liftLocal_injective hq B
    simp [liftLocal_liftBetween]
  map_add' a b := by
    apply liftLocal_injective hq B
    simp [liftLocal_liftBetween]
  commutes' c := by
    apply liftLocal_injective hq B
    simp only [liftLocal_liftBetween, Algebra.algebraMap_eq_smul_one,
      liftLocal_smul, liftLocal_one]
  map_star' a := by
    apply liftLocal_injective hq B
    simp [liftLocal_liftBetween]

end PolynomialPEPS.PhysicalMove

end

end OAI
