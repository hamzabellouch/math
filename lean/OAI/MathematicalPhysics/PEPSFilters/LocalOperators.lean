import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Basic

namespace OAI

/-! Local matrix embeddings, reduced density operators and tensor corners. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace PolynomialPEPS.PinnedEntropy

def restrictConfiguration {L q : ℕ} (A : Finset (Vertex L))
    (x : Configuration L q) : RegionConfiguration q A := fun v => x v.val

@[simp] lemma restrict_join_left {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) :
    restrictConfiguration A (joinConfigurations A x z) = x := by
  funext v
  simp [restrictConfiguration, joinConfigurations, v.property]

@[simp] lemma restrict_join_right {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) :
    restrictConfiguration Aᶜ (joinConfigurations A x z) = z := by
  funext v
  simp [restrictConfiguration, joinConfigurations, Finset.mem_compl.mp v.property]

@[simp] lemma join_restrict {L q : ℕ} (A : Finset (Vertex L))
    (x : Configuration L q) :
    joinConfigurations A (restrictConfiguration A x) (restrictConfiguration Aᶜ x) = x := by
  funext v
  simp only [joinConfigurations, restrictConfiguration]
  split_ifs <;> rfl

def splitConfigurations {L q : ℕ} (A : Finset (Vertex L)) :
    Configuration L q ≃ RegionConfiguration q A × RegionConfiguration q Aᶜ where
  toFun x := (restrictConfiguration A x, restrictConfiguration Aᶜ x)
  invFun p := joinConfigurations A p.1 p.2
  left_inv x := join_restrict A x
  right_inv p := by simp

lemma agree_complement_iff {L q : ℕ} (A : Finset (Vertex L))
    (x y : Configuration L q) :
    (∀ v, v ∉ A → x v = y v) ↔ restrictConfiguration Aᶜ x = restrictConfiguration Aᶜ y := by
  constructor
  · intro h
    funext v
    exact h v (Finset.mem_compl.mp v.property)
  · intro h v hv
    exact congrFun h ⟨v, Finset.mem_compl.mpr hv⟩

open scoped Kronecker

lemma liftLocal_eq_kronecker {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A B = (B ⊗ₖ (1 : Matrix (RegionConfiguration q Aᶜ)
      (RegionConfiguration q Aᶜ) ℂ)).submatrix (splitConfigurations A) (splitConfigurations A) := by
  ext x y
  simp only [liftLocal, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    splitConfigurations, Equiv.coe_fn_mk, Matrix.one_apply, agree_complement_iff]
  by_cases h : restrictConfiguration Aᶜ x = restrictConfiguration Aᶜ y <;> simp [h]
  rfl

@[simp] lemma liftLocal_one {L q : ℕ} (A : Finset (Vertex L)) :
    liftLocal (q := q) A 1 = 1 := by
  rw [liftLocal_eq_kronecker, Matrix.one_kronecker_one]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq]

@[simp] lemma liftLocal_mul {L q : ℕ} (A : Finset (Vertex L))
    (B C : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A (B * C) = liftLocal A B * liftLocal A C := by
  simp only [liftLocal_eq_kronecker, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, one_mul]

@[simp] lemma liftLocal_star {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A (star B) = star (liftLocal A B) := by
  simp only [liftLocal_eq_kronecker, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

def liftLocalHom {L q : ℕ} (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ →⋆ₐ[ℂ] Operator L q where
  toFun := liftLocal A
  map_one' := liftLocal_one A
  map_mul' := liftLocal_mul A
  map_zero' := by ext x y; simp [liftLocal]
  map_add' B C := by
    ext x y
    simp only [Matrix.add_apply, liftLocal]
    split_ifs <;> simp only [add_zero]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    have hs : liftLocal (q := q) A (c • 1) = c • liftLocal A 1 := by
      ext x y
      simp only [liftLocal, Matrix.smul_apply]
      split_ifs <;> simp
    rw [hs, liftLocal_one]
  map_star' := liftLocal_star A

lemma liftLocal_positive {L q : ℕ} (A : Finset (Vertex L))
    {B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ}
    (hB : B.PosSemidef) : (liftLocal A B).PosSemidef := by
  rw [liftLocal_eq_kronecker]
  exact (hB.kronecker (Matrix.PosSemidef.one)).submatrix _

lemma liftLocal_unitary {L q : ℕ} (A : Finset (Vertex L))
    {B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ}
    (hB : B ∈ unitary _) : liftLocal A B ∈ unitary _ := by
  constructor
  · rw [← liftLocal_star, ← liftLocal_mul, hB.1, liftLocal_one]
  · rw [← liftLocal_star, ← liftLocal_mul, hB.2, liftLocal_one]

lemma liftLocal_join {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (x y : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) :
    liftLocal A B (joinConfigurations A x z) (joinConfigurations A y z) = B x y := by
  change (if ∀ v, v ∉ A → joinConfigurations A x z v = joinConfigurations A y z v then
    B (restrictConfiguration A (joinConfigurations A x z))
      (restrictConfiguration A (joinConfigurations A y z)) else 0) = _
  rw [ite_eq_left, restrict_join_left, restrict_join_left]
  intro v hv
  simp [joinConfigurations, hv]

lemma liftLocal_injective {L q : ℕ} [NeZero q] (A : Finset (Vertex L)) :
    Function.Injective (liftLocal (q := q) A) := by
  intro B C h
  ext x y
  have he := congrArg (fun M => M (joinConfigurations A x (fun _ => 0))
    (joinConfigurations A y (fun _ => 0))) h
  simpa only [liftLocal_join] using he

lemma liftLocal_extend {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (B : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ) :
    ∃ C : Matrix (RegionConfiguration q T) (RegionConfiguration q T) ℂ,
      liftLocal T C = liftLocal S B := by
  let C : Matrix (RegionConfiguration q T) (RegionConfiguration q T) ℂ := fun x y =>
    if ∀ v (hv : v ∈ T), v ∉ S → x ⟨v, hv⟩ = y ⟨v, hv⟩ then
      B (fun v => x ⟨v, hST v.property⟩) (fun v => y ⟨v, hST v.property⟩) else 0
  refine ⟨C, ?_⟩
  ext x y
  change (if ∀ v, v ∉ T → x v = y v then
    C (fun v => x v.val) (fun v => y v.val) else 0) =
    (if ∀ v, v ∉ S → x v = y v then
      B (fun v => x v.val) (fun v => y v.val) else 0)
  by_cases hS : ∀ v, v ∉ S → x v = y v
  · have hT : ∀ v, v ∉ T → x v = y v := fun v hv => hS v (fun h => hv (hST h))
    rw [ite_eq_left hT, ite_eq_left hS]
    change (if ∀ v (_ : v ∈ T), v ∉ S → x v = y v then _ else 0) = _
    rw [ite_eq_left (fun v _ hv => hS v hv)]
  · rw [ite_eq_right hS]
    by_cases hT : ∀ v, v ∉ T → x v = y v
    · have hC : ¬∀ v (_ : v ∈ T), v ∉ S → x v = y v := by
        intro h
        apply hS
        intro v hv
        by_cases ht : v ∈ T
        · exact h v ht hv
        · exact hT v ht
      rw [ite_eq_left hT]
      exact ite_eq_right hC
    · rw [ite_eq_right hT]

lemma SupportedOn.mono {L q : ℕ} {S T : Finset (Vertex L)} {B : Operator L q}
    (hB : SupportedOn B S) (hST : S ⊆ T) : SupportedOn B T := by
  obtain ⟨B₀, rfl⟩ := hB
  obtain ⟨C, hC⟩ := liftLocal_extend hST B₀
  exact ⟨C, hC.symm⟩

lemma SupportedOn.one {L q : ℕ} (T : Finset (Vertex L)) :
    SupportedOn (1 : Operator L q) T := ⟨1, (liftLocal_one T).symm⟩

lemma SupportedOn.mul {L q : ℕ} {S : Finset (Vertex L)} {B C : Operator L q}
    (hB : SupportedOn B S) (hC : SupportedOn C S) : SupportedOn (B * C) S := by
  obtain ⟨B₀, rfl⟩ := hB
  obtain ⟨C₀, rfl⟩ := hC
  exact ⟨B₀ * C₀, (liftLocal_mul S B₀ C₀).symm⟩

lemma SupportedOn.star {L q : ℕ} {S : Finset (Vertex L)} {B : Operator L q}
    (hB : SupportedOn B S) : SupportedOn (star B) S := by
  obtain ⟨B₀, rfl⟩ := hB
  exact ⟨Star.star B₀, (liftLocal_star S B₀).symm⟩

lemma liftLocal_unitary_iff {L q : ℕ} [NeZero q] (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    liftLocal A B ∈ unitary _ ↔ B ∈ unitary _ := by
  refine ⟨fun h => ?_, liftLocal_unitary A⟩
  constructor
  · apply liftLocal_injective A
    simpa only [liftLocal_mul, liftLocal_star, liftLocal_one] using h.1
  · apply liftLocal_injective A
    simpa only [liftLocal_mul, liftLocal_star, liftLocal_one] using h.2

lemma SupportedOn.unitary_rep {L q : ℕ} [NeZero q]
    {A : Finset (Vertex L)} {U : Operator L q} (hU : SupportedOn U A)
    (hu : U ∈ unitary _) :
    ∃ u : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ),
      U = liftLocal A (u : Matrix _ _ ℂ) := by
  obtain ⟨B, rfl⟩ := hU
  exact ⟨⟨B, (liftLocal_unitary_iff A B).mp hu⟩, rfl⟩

end PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.PinnedEntropy
open scoped Matrix.Norms.L2Operator

lemma liftLocal_norm {L q : ℕ} [NeZero q] (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    ‖liftLocal A B‖ = ‖B‖ :=
  NonUnitalStarAlgHom.norm_map (liftLocalHom A) (liftLocal_injective A) B

end PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.PinnedEntropy

lemma asMap_apply {L q : ℕ} (B : Operator L q) (v : State L q)
    (x : Configuration L q) : asMap B v x = ∑ y, B x y * v y := by
  rfl

lemma liftLocal_apply_join {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (x y : RegionConfiguration q A) (z w : RegionConfiguration q Aᶜ) :
    liftLocal A B (joinConfigurations A x z) (joinConfigurations A y w) =
      B x y * if z = w then 1 else 0 := by
  rw [liftLocal_eq_kronecker]
  simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, splitConfigurations,
    Matrix.one_apply]

lemma coefficientMatrix_asMap_liftLocal {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (v : State L q) :
    coefficientMatrix (asMap (liftLocal A B) v) A = B * coefficientMatrix v A := by
  classical
  ext x z
  rw [coefficientMatrix, asMap_apply]
  rw [← (splitConfigurations (q := q) A).symm.sum_comp]
  simp only [Fintype.sum_prod_type, splitConfigurations, Equiv.coe_fn_symm_mk,
    liftLocal_apply_join, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Matrix.mul_apply, coefficientMatrix]

lemma coefficientMatrix_injective {L q : ℕ} (A : Finset (Vertex L)) :
    Function.Injective (fun v : State L q => coefficientMatrix v A) := by
  intro v w h
  ext x
  have ht := congrFun (congrFun h (restrictConfiguration A x)) (restrictConfiguration Aᶜ x)
  simpa only [coefficientMatrix, join_restrict] using ht

lemma inner_eq_trace_coefficient {L q : ℕ} (A : Finset (Vertex L))
    (v w : State L q) :
    inner ℂ v w = (coefficientMatrix w A * (coefficientMatrix v A).conjTranspose).trace := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [← (splitConfigurations (q := q) A).symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma inner_asMap_liftLocal {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (v : State L q) :
    inner ℂ v (asMap (liftLocal A B) v) = (B * reducedDensity v A).trace := by
  rw [inner_eq_trace_coefficient A, coefficientMatrix_asMap_liftLocal]
  rw [Matrix.mul_assoc]
  rfl

lemma trace_reducedDensity {L q : ℕ} (A : Finset (Vertex L)) (v : State L q) :
    (reducedDensity v A).trace = (‖v‖ ^ 2 : ℂ) := by
  rw [reducedDensity, ← inner_eq_trace_coefficient]
  exact inner_self_eq_norm_sq_to_K v

lemma reducedDensity_posSemidef {L q : ℕ} (A : Finset (Vertex L)) (v : State L q) :
    (reducedDensity v A).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma asMap_liftLocal_fix_of_mul_density {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (v : State L q) (hB : B * reducedDensity v A = reducedDensity v A) :
    asMap (liftLocal A B) v = v := by
  apply coefficientMatrix_injective A
  change coefficientMatrix (asMap (liftLocal A B) v) A = coefficientMatrix v A
  rw [coefficientMatrix_asMap_liftLocal]
  have h : (B - 1) * (coefficientMatrix v A * (coefficientMatrix v A).conjTranspose) = 0 := by
    change (B - 1) * reducedDensity v A = 0
    rw [Matrix.sub_mul, one_mul, hB, sub_self]
  have hz := (Matrix.mul_self_mul_conjTranspose_eq_zero (coefficientMatrix v A) (B - 1)).mp h
  simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using hz


open scoped Kronecker

def splitRegion {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T) :
    RegionConfiguration q T ≃ RegionConfiguration q S × RegionConfiguration q (T \ S) where
  toFun x := (fun v => x ⟨v, hST v.property⟩,
    fun v => x ⟨v, (Finset.mem_sdiff.mp v.property).1⟩)
  invFun p := fun v => if h : v.val ∈ S then p.1 ⟨v, h⟩
    else p.2 ⟨v, Finset.mem_sdiff.mpr ⟨v.property, h⟩⟩
  left_inv x := by funext v; dsimp only; split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext v; simp only [v.property, ↓reduceDIte]
    · funext v; simp only [(Finset.mem_sdiff.mp v.property).2, ↓reduceDIte]

lemma splitRegion_restrict {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (x : Configuration L q) :
    splitRegion (q := q) hST (restrictConfiguration T x) =
      (restrictConfiguration S x, restrictConfiguration (T \ S) x) := rfl

def regionTensor {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    Matrix (RegionConfiguration q T) (RegionConfiguration q T) ℂ :=
  (P ⊗ₖ B).submatrix (splitRegion hST) (splitRegion hST)

lemma regionTensor_mul {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P Q : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (B C : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    regionTensor hST (P * Q) (B * C) = regionTensor hST P B * regionTensor hST Q C := by
  simp only [regionTensor, Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

lemma regionTensor_star {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    regionTensor hST (star P) (star B) = star (regionTensor hST P B) := by
  simp [regionTensor, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker]

lemma regionTensor_positive {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    {P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ}
    {B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ}
    (hP : P.PosSemidef) (hB : B.PosSemidef) : (regionTensor hST P B).PosSemidef :=
  (hP.kronecker hB).submatrix _

lemma regionTensor_trace {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    (regionTensor hST P B).trace = P.trace * B.trace := by
  change (∑ x, (P ⊗ₖ B) ((splitRegion hST) x) ((splitRegion hST) x)) = _
  rw [(splitRegion hST).sum_comp (fun x => (P ⊗ₖ B) x x)]
  exact Matrix.trace_kronecker P B

lemma outside_core_iff {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (x y : Configuration L q) :
    (∀ v, v ∉ S → x v = y v) ↔
    (∀ v, v ∉ T → x v = y v) ∧ restrictConfiguration (T \ S) x = restrictConfiguration (T \ S) y := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (fun hs => hv (hST hs)), funext fun v => h v
      (Finset.mem_sdiff.mp v.property).2⟩
  · rintro ⟨hout, hsh⟩ v hv
    by_cases ht : v ∈ T
    · exact congrFun hsh ⟨v, Finset.mem_sdiff.mpr ⟨ht, hv⟩⟩
    · exact hout v ht

lemma outside_shell_iff {L q : ℕ} {S T : Finset (Vertex L)} (_ : S ⊆ T)
    (x y : Configuration L q) :
    (∀ v, v ∉ T \ S → x v = y v) ↔
    (∀ v, v ∉ T → x v = y v) ∧ restrictConfiguration S x = restrictConfiguration S y := by
  constructor
  · intro h
    refine ⟨fun v hv => h v (fun ht => hv (Finset.mem_sdiff.mp ht).1), ?_⟩
    funext v
    exact h v (fun ht => (Finset.mem_sdiff.mp ht).2 v.property)
  · rintro ⟨hout, hc⟩ v hv
    by_cases ht : v ∈ T
    · have hs : v ∈ S := by simpa only [Finset.mem_sdiff, ht, true_and, not_not] using hv
      exact congrFun hc ⟨v, hs⟩
    · exact hout v ht

lemma lift_regionTensor_one_right {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ) :
    liftLocal T (regionTensor hST P 1) = liftLocal S P := by
  classical
  ext x y
  change (if ∀ v, v ∉ T → x v = y v then
    P (restrictConfiguration S x) (restrictConfiguration S y) *
      (if restrictConfiguration (T \ S) x = restrictConfiguration (T \ S) y then 1 else 0)
    else 0) = (if ∀ v, v ∉ S → x v = y v then
      P (restrictConfiguration S x) (restrictConfiguration S y) else 0)
  simp only [outside_core_iff hST]
  split_ifs <;> simp_all

lemma lift_regionTensor_one_left {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    liftLocal T (regionTensor hST 1 B) = liftLocal (T \ S) B := by
  classical
  ext x y
  change (if ∀ v, v ∉ T → x v = y v then
    (if restrictConfiguration S x = restrictConfiguration S y then 1 else 0) *
      B (restrictConfiguration (T \ S) x) (restrictConfiguration (T \ S) y)
    else 0) = (if ∀ v, v ∉ T \ S → x v = y v then
      B (restrictConfiguration (T \ S) x) (restrictConfiguration (T \ S) y) else 0)
  simp only [outside_shell_iff hST]
  split_ifs <;> simp_all

lemma lift_regionTensor {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    liftLocal T (regionTensor hST P B) = liftLocal S P * liftLocal (T \ S) B := by
  rw [← lift_regionTensor_one_right hST, ← lift_regionTensor_one_left hST,
    ← liftLocal_mul, ← regionTensor_mul, mul_one, one_mul]

lemma lift_core_shell_commute {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    Commute (liftLocal S P) (liftLocal (T \ S) B) := by
  show liftLocal S P * liftLocal (T \ S) B = liftLocal (T \ S) B * liftLocal S P
  rw [← lift_regionTensor hST, ← lift_regionTensor_one_right hST,
    ← lift_regionTensor_one_left hST, ← liftLocal_mul, ← regionTensor_mul, one_mul, mul_one]

def regionCornerHom {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (hP : P.IsHermitian) (hP2 : P * P = P) :
    Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ →⋆ₙₐ[ℂ]
      Matrix (RegionConfiguration q T) (RegionConfiguration q T) ℂ where
  toFun := regionTensor hST P
  map_zero' := by ext x y; simp [regionTensor]
  map_add' B C := by ext x y; simp [regionTensor, mul_add]
  map_mul' B C := by rw [← regionTensor_mul, hP2]
  map_smul' c B := by ext x y; simp [regionTensor, mul_left_comm]
  map_star' B := by rw [← regionTensor_star, show star P = P from hP]

end PolynomialPEPS.PinnedEntropy

end

end OAI
