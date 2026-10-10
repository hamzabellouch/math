import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinEmbedding
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.GlobalSuperexchange
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Polynomial operator bounds from the actual exterior occupation basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Q : ℕ}

/-- A creator sends an unoccupied canonical basis vector to the inserted
occupation with its actual exterior permutation sign. -/
theorem create_unoccupied_basis_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      create i (fockBasis Q A) = c • fockBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hd : Disjoint S.val T.val := by simpa only [S, T, Finset.disjoint_singleton_left]
  have h := ExteriorAlgebra.basis_mul_of_disjoint
    (Pi.basisFun ℂ (Fin (Q + 1))) S T hd
  have hset : (Set.powersetCard.disjUnion hd).val = insert i A := by
    ext k
    simp [Set.powersetCard.disjUnion, S, T]
  change fockBasis Q {i} * fockBasis Q A =
    (Set.powersetCard.permOfDisjoint hd).sign •
      fockBasis Q (Set.powersetCard.disjUnion hd).val at h
  rw [fockBasis_singleton, hset] at h
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [hs, one_smul, create, LinearMap.coe_mk, AddHom.coe_mk] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [hs, Units.neg_smul, one_smul, neg_smul,
      create, LinearMap.coe_mk, AddHom.coe_mk] using h

def creationCoefficient (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) : ℂ :=
  (fockBasis Q).repr (create i (fockBasis Q A)) (insert i A)

theorem creationCoefficient_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    creationCoefficient i A = 1 ∨ creationCoefficient i A = -1 := by
  obtain ⟨c, hc, h⟩ := create_unoccupied_basis_signed i A hi
  have heq : creationCoefficient i A = c := by
    simp [creationCoefficient, h]
  simpa only [heq] using hc

theorem creationCoefficient_occupied (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : creationCoefficient i A = 0 := by
  simp [creationCoefficient, create_occupied_basis i A hi]

theorem create_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    create i (fockBasis Q A) = creationCoefficient i A • fockBasis Q (insert i A) := by
  by_cases hi : i ∈ A
  · simp [create_occupied_basis i A hi, creationCoefficient_occupied i A hi]
  · obtain ⟨c, _, hc⟩ := create_unoccupied_basis_signed i A hi
    have heq : creationCoefficient i A = c := by simp [creationCoefficient, hc]
    rw [heq, hc]

theorem annihilate_create_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (create i (fockBasis Q A)) = fockBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
  change annihilate i (create i (fockBasis Q A)) +
    number i (fockBasis Q A) = (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
  simpa [number_basis, hi] using h

theorem annihilate_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) :
    annihilate i (fockBasis Q A) =
      creationCoefficient i (A.erase i) • fockBasis Q (A.erase i) := by
  have h := annihilate_create_unoccupied_basis i (A.erase i) (Finset.notMem_erase _ _)
  rw [create_basis, Finset.insert_erase hi, map_smul] at h
  have hc : creationCoefficient i (A.erase i) * creationCoefficient i (A.erase i) = 1 := by
    rcases creationCoefficient_signed i (A.erase i) (Finset.notMem_erase _ _) with hc | hc
    all_goals simp [hc]
  calc
    _ = creationCoefficient i (A.erase i) •
        (creationCoefficient i (A.erase i) • annihilate i (fockBasis Q A)) := by
      rw [smul_smul, hc, one_smul]
    _ = _ := congrArg (fun x => creationCoefficient i (A.erase i) • x) h

def insertModeEquiv (i : Fin (Q + 1)) :
    {A : Finset (Fin (Q + 1)) // i ∉ A} ≃ {A : Finset (Fin (Q + 1)) // i ∈ A} where
  toFun A := ⟨insert i A.val, Finset.mem_insert_self _ _⟩
  invFun A := ⟨A.val.erase i, Finset.notMem_erase _ _⟩
  left_inv A := Subtype.ext (Finset.erase_insert A.property)
  right_inv A := Subtype.ext (Finset.insert_erase A.property)

@[simp] theorem insertModeEquiv_val (i : Fin (Q + 1))
    (A : {A : Finset (Fin (Q + 1)) // i ∉ A}) :
    (insertModeEquiv i A).val = insert i A.val := rfl

@[simp] theorem insertModeEquiv_erase (i : Fin (Q + 1))
    (A : {A : Finset (Fin (Q + 1)) // i ∉ A}) :
    (insertModeEquiv i A).val.erase i = A.val := Finset.erase_insert A.property

@[simp] theorem insertModeEquiv_symm_insert (i : Fin (Q + 1))
    (A : {A : Finset (Fin (Q + 1)) // i ∈ A}) :
    insert i ((insertModeEquiv i).symm A).val = A.val := Finset.insert_erase A.property

theorem create_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (create i x) B =
      if i ∈ B then creationCoefficient i (B.erase i) * (fockBasis Q).repr x (B.erase i)
      else 0 := by
  classical
  have h : create i x = ∑ A, (fockBasis Q).repr x A • create i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  simp only [create_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ B
  · rw [ite_eq_left hi, Finset.sum_eq_single (B.erase i)]
    · simp [Finset.insert_erase hi, mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · simp [creationCoefficient_occupied i A hiA]
      · have hne : insert i A ≠ B := by
          intro hAB
          apply hA
          have he := congrArg (Finset.erase · i) hAB
          simpa only [Finset.erase_insert hiA] using he
        simp [Module.Basis.repr_self, hne]
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro A _
    have hne : insert i A ≠ B := by
      intro hAB
      exact hi (hAB ▸ Finset.mem_insert_self i A)
    simp [Module.Basis.repr_self, hne]

theorem annihilate_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (annihilate i x) B =
      if i ∉ B then creationCoefficient i B * (fockBasis Q).repr x (insert i B)
      else 0 := by
  classical
  have h : annihilate i x =
      ∑ A, (fockBasis Q).repr x A • annihilate i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  by_cases hi : i ∈ B
  · rw [ite_eq_right (not_not.mpr hi)]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hiA : i ∈ A
    · rw [annihilate_occupied_basis i A hiA]
      have hne : A.erase i ≠ B := by
        intro he
        exact (Finset.notMem_erase i A) (he.symm ▸ hi)
      simp [Module.Basis.repr_self, hne]
    · simp [annihilate_unoccupied_basis i A hiA]
  · rw [ite_eq_left hi, Finset.sum_eq_single (insert i B)]
    · rw [annihilate_occupied_basis i (insert i B) (Finset.mem_insert_self _ _),
        Finset.erase_insert hi]
      simp [mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · rw [annihilate_occupied_basis i A hiA]
        have hne : A.erase i ≠ B := by
          intro he
          exact hA ((Finset.insert_erase hiA).symm.trans (congrArg (insert i) he))
        simp [Module.Basis.repr_self, hne]
      · simp [annihilate_unoccupied_basis i A hiA]
    · simp

theorem creationCoefficient_conj (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) :
    star (creationCoefficient i A) = creationCoefficient i A := by
  by_cases hi : i ∈ A
  · simp [creationCoefficient_occupied i A hi]
  · rcases creationCoefficient_signed i A hi with hc | hc
    all_goals simp [hc]

/-- The creator and contraction are actual adjoints in the canonical
occupation norm; the signs come from the exterior basis above. -/
theorem fock_inner_create_annihilate (i : Fin (Q + 1)) (x y : Space Q) :
    (∑ B, star ((fockBasis Q).repr (create i x) B) * (fockBasis Q).repr y B) =
      ∑ A, star ((fockBasis Q).repr x A) * (fockBasis Q).repr (annihilate i y) A := by
  classical
  have hleft (B : Finset (Fin (Q + 1))) :
      star ((fockBasis Q).repr (create i x) B) * (fockBasis Q).repr y B =
        if i ∈ B then creationCoefficient i (B.erase i) *
          star ((fockBasis Q).repr x (B.erase i)) * (fockBasis Q).repr y B else 0 := by
    rw [create_coordinate]
    split_ifs <;> simp [star_mul, creationCoefficient_conj, mul_comm, mul_left_comm]
  have hright (A : Finset (Fin (Q + 1))) :
      star ((fockBasis Q).repr x A) * (fockBasis Q).repr (annihilate i y) A =
        if i ∉ A then creationCoefficient i A *
          star ((fockBasis Q).repr x A) * (fockBasis Q).repr y (insert i A) else 0 := by
    rw [annihilate_coordinate]
    split_ifs <;> simp [mul_comm, mul_left_comm]
  simp_rw [hleft, hright]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∈ A) _ (by simp),
    Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∉ A) _ (by simp)]
  have h := (insertModeEquiv i).sum_comp (fun B => creationCoefficient i (B.val.erase i) *
    star ((fockBasis Q).repr x (B.val.erase i)) * (fockBasis Q).repr y B.val)
  simp_rw [insertModeEquiv_erase, insertModeEquiv_val] at h
  exact h.symm

theorem fockMass_create (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∉ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (create i x) B) =
        if i ∈ B then Complex.normSq ((fockBasis Q).repr x (B.erase i)) else 0 := by
    rw [create_coordinate]
    by_cases hi : i ∈ B
    · simp only [hi, ↓reduceIte]
      rcases creationCoefficient_signed i (B.erase i) (Finset.notMem_erase _ _) with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∈ A) _ (by simp)]
  have h := (insertModeEquiv i).sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (B.val.erase i)))
  simp_rw [insertModeEquiv_erase] at h
  exact h.symm

theorem fockMass_annihilate (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∈ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (annihilate i x) B) =
        if i ∉ B then Complex.normSq ((fockBasis Q).repr x (insert i B)) else 0 := by
    rw [annihilate_coordinate]
    by_cases hi : i ∉ B
    · simp only [hi]
      rcases creationCoefficient_signed i B hi with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∉ A) _ (by simp)]
  have h := (insertModeEquiv i).symm.sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (insert i B.val)))
  simp_rw [insertModeEquiv_symm_insert] at h
  exact h.symm

theorem fockMass_create_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) ≤ fockMass x := by
  classical
  rw [fockMass_create]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∉ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∉ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockMass_annihilate_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) ≤ fockMass x := by
  classical
  rw [fockMass_annihilate]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∈ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∈ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

abbrev FockCoordinateSpace (Q : ℕ) := EuclideanSpace ℂ (Finset (Fin (Q + 1)))

def fockCoordinates (Q : ℕ) : Space Q ≃ₗ[ℂ] FockCoordinateSpace Q :=
  (fockBasis Q).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

@[simp] theorem fockCoordinates_apply (x : Space Q) (A : Finset (Fin (Q + 1))) :
    fockCoordinates Q x A = (fockBasis Q).repr x A := rfl

theorem fockCoordinates_norm_sq (x : Space Q) :
    ‖fockCoordinates Q x‖ ^ 2 = fockMass x := by
  simp only [EuclideanSpace.norm_sq_eq, fockCoordinates_apply,
    Complex.normSq_eq_norm_sq, fockMass]

def fockOperatorLinear (T : Module.End ℂ (Space Q)) :
    Module.End ℂ (FockCoordinateSpace Q) :=
  (fockCoordinates Q).toLinearMap.comp (T.comp (fockCoordinates Q).symm.toLinearMap)

def fockOperator (T : Module.End ℂ (Space Q)) :
    FockCoordinateSpace Q →L[ℂ] FockCoordinateSpace Q :=
  LinearMap.toContinuousLinearMap (fockOperatorLinear T)

@[simp] theorem fockOperator_coordinates (T : Module.End ℂ (Space Q)) (x : Space Q) :
    fockOperator T (fockCoordinates Q x) = fockCoordinates Q (T x) := by
  simp [fockOperator, fockOperatorLinear]

theorem fockOperator_norm_le_one (T : Module.End ℂ (Space Q))
    (hT : ∀ x, fockMass (T x) ≤ fockMass x) : ‖fockOperator T‖ ≤ 1 := by
  apply (fockOperator T).opNorm_le_bound zero_le_one
  intro v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  rw [fockOperator_coordinates, one_mul]
  have h := hT x
  rw [← fockCoordinates_norm_sq, ← fockCoordinates_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Actual CAR creators and annihilators are contractions in the
canonical occupation norm, uniformly in the number of spectator modes. -/
theorem fockOperator_create_norm (i : Fin (Q + 1)) :
    ‖fockOperator (create i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_create_le i)

theorem fockOperator_annihilate_norm (i : Fin (Q + 1)) :
    ‖fockOperator (annihilate i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_annihilate_le i)

theorem fockOperator_create_adjoint (i : Fin (Q + 1)) :
    (fockOperator (create i)).adjoint = fockOperator (annihilate i) := by
  have h : fockOperator (create i) = (fockOperator (annihilate i)).adjoint := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro u v
    obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective u
    obtain ⟨y, rfl⟩ := (fockCoordinates Q).surjective v
    simp only [fockOperator_coordinates, PiLp.inner_apply, RCLike.inner_apply',
      fockCoordinates_apply]
    exact fock_inner_create_annihilate i x y
  simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg
    ContinuousLinearMap.adjoint h

@[simp] theorem fockOperator_add (T S : Module.End ℂ (Space Q)) :
    fockOperator (T + S) = fockOperator T + fockOperator S := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, add_apply,
    LinearMap.add_apply, map_add]

@[simp] theorem fockOperator_smul (c : ℂ) (T : Module.End ℂ (Space Q)) :
    fockOperator (c • T) = c • fockOperator T := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, smul_apply,
    LinearMap.smul_apply, map_smul]

@[simp] theorem fockOperator_mul (T S : Module.End ℂ (Space Q)) :
    fockOperator (T * S) = (fockOperator T).comp (fockOperator S) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, ContinuousLinearMap.comp_apply,
    Module.End.mul_apply]

theorem fockOperator_sum {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Space Q)) :
    fockOperator (∑ i ∈ s, T i) = ∑ i ∈ s, fockOperator (T i) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, sum_apply,
    LinearMap.sum_apply, map_sum]

theorem fockOperator_transfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (transfer i j)‖ ≤ 1 := by
  rw [transfer, fockOperator_mul]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (fockOperator_create_norm i) (fockOperator_annihilate_norm j)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem fockOperator_bondTransfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (bondTransfer i j)‖ ≤ 2 := by
  rw [bondTransfer, fockOperator_add]
  calc
    _ ≤ ‖fockOperator (transfer i j)‖ + ‖fockOperator (transfer j i)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (fockOperator_transfer_norm i j) (fockOperator_transfer_norm j i)
    _ = 2 := by norm_num

theorem fockOperator_siteHopping_norm (m : ℕ) (i j : Fin (m + 1)) :
    ‖fockOperator (siteHopping m i j)‖ ≤ 4 := by
  change ‖fockOperator (_ + _)‖ ≤ _
  rw [fockOperator_add]
  calc
    _ ≤ ‖fockOperator (bondTransfer (siteMode m i 0) (siteMode m j 0))‖ +
        ‖fockOperator (bondTransfer (siteMode m i 1) (siteMode m j 1))‖ := norm_add_le _ _
    _ ≤ 2 + 2 := add_le_add
      (fockOperator_bondTransfer_norm (siteMode m i 0) (siteMode m j 0))
      (fockOperator_bondTransfer_norm (siteMode m i 1) (siteMode m j 1))
    _ = 4 := by norm_num

/-- The actual global hopping has an edge-sum bound, independent of
the exponentially large Fock-space dimension. -/
theorem fockOperator_graphHopping_norm {Edge : Type*} [Fintype Edge]
    (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    ‖fockOperator (graphHopping m left right t)‖ ≤ 4 * ∑ e, ‖t e‖ := by
  unfold graphHopping
  rw [fockOperator_sum]
  simp only [fockOperator_smul]
  calc
    _ ≤ ∑ e, ‖t e • fockOperator (siteHopping m (left e) (right e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖t e‖ * 4 := Finset.sum_le_sum fun e _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (fockOperator_siteHopping_norm m (left e) (right e)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem fockOperator_annihilate_adjoint (i : Fin (Q + 1)) :
    (fockOperator (annihilate i)).adjoint = fockOperator (create i) := by
  rw [← fockOperator_create_adjoint, ContinuousLinearMap.adjoint_adjoint]

theorem fockOperator_transfer_adjoint (i j : Fin (Q + 1)) :
    (fockOperator (transfer i j)).adjoint = fockOperator (transfer j i) := by
  simp only [transfer, fockOperator_mul, ContinuousLinearMap.adjoint_comp,
    fockOperator_create_adjoint, fockOperator_annihilate_adjoint]

theorem fockOperator_bondTransfer_adjoint (i j : Fin (Q + 1)) :
    (fockOperator (bondTransfer i j)).adjoint = fockOperator (bondTransfer i j) := by
  simp only [bondTransfer, fockOperator_add, map_add,
    fockOperator_transfer_adjoint, add_comm]

theorem fockOperator_siteHopping_adjoint (m : ℕ) (i j : Fin (m + 1)) :
    (fockOperator (siteHopping m i j)).adjoint = fockOperator (siteHopping m i j) := by
  change (fockOperator (_ + _)).adjoint = fockOperator (_ + _)
  simp only [fockOperator_add, map_add, fockOperator_bondTransfer_adjoint]

theorem fockOperator_graphHopping_adjoint {Edge : Type*} [Fintype Edge]
    (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) :
    (fockOperator (graphHopping m left right (fun e => (t e : ℂ)))).adjoint =
      fockOperator (graphHopping m left right (fun e => (t e : ℂ))) := by
  unfold graphHopping
  rw [fockOperator_sum]
  simp only [fockOperator_smul, map_sum, map_smulₛₗ,
    fockOperator_siteHopping_adjoint, Complex.conj_ofReal]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
