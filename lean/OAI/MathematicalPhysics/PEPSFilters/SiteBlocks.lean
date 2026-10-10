import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Matrix blocks and bounded single-site factors for two-site operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def injectionMatrix (e : n ↪ m) : Matrix m n ℂ := fun i j => if i = e j then 1 else 0

omit [Fintype n] in
lemma injectionMatrix_star_mul (e : n ↪ m) :
    (injectionMatrix e).conjTranspose * injectionMatrix e = 1 := by
  classical
  ext i j
  by_cases h : i = j <;> simp [Matrix.mul_apply, Matrix.conjTranspose_apply, injectionMatrix,
    Matrix.one_apply, apply_ite, h, eq_comm]

lemma injectionMatrix_norm_le [Nonempty n] (e : n ↪ m) : ‖injectionMatrix e‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (injectionMatrix e)
  rw [injectionMatrix_star_mul] at hh
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := le_of_eq (norm_one)
  nlinarith [norm_nonneg (injectionMatrix e)]

omit [Fintype n] [DecidableEq n] in
lemma matrix_block_apply (H : Matrix m m ℂ) (e f : n ↪ m) (i j : n) :
    ((injectionMatrix e).conjTranspose * H * injectionMatrix f) i j = H (e i) (f j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, injectionMatrix, apply_ite]

lemma matrix_block_norm_le [Nonempty n] (H : Matrix m m ℂ) (e f : n ↪ m) :
    ‖(injectionMatrix e).conjTranspose * H * injectionMatrix f‖ ≤ ‖H‖ := by
  calc
    _ ≤ ‖(injectionMatrix e).conjTranspose‖ * ‖H‖ * ‖injectionMatrix f‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖H‖ * 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (injectionMatrix_norm_le e) (norm_nonneg H))
        (injectionMatrix_norm_le f) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def reindexStarAlgEquiv (e : n ≃ m) : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

lemma norm_reindex (e : n ≃ m) (H : Matrix n n ℂ) :
    ‖Matrix.reindex e e H‖ = ‖H‖ :=
  StarAlgEquiv.norm_map (reindexStarAlgEquiv e) H

lemma matrix_single_norm_le (i j : n) : ‖(Matrix.single i j 1 : Matrix n n ℂ)‖ ≤ 1 := by
  let e : Unit ↪ n := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  let f : Unit ↪ n := ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩
  have he : injectionMatrix e * (injectionMatrix f).conjTranspose = Matrix.single i j 1 := by
    ext a b
    change (∑ _ : Unit, (if a = i then (1:ℂ) else 0) * star (if b = j then (1:ℂ) else 0)) = _
    by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [Matrix.single, ha, hb] <;> grind
  rw [← he]
  calc _ ≤ ‖injectionMatrix e‖ * ‖(injectionMatrix f).conjTranspose‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul (injectionMatrix_norm_le e) (injectionMatrix_norm_le f) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

def siteConfigurationEquiv (v : Vertex L) : RegionConfiguration q {v} ≃ Fin q where
  toFun x := x ⟨v, Finset.mem_singleton_self v⟩
  invFun a := fun _ => a
  left_inv x := by
    funext u
    have hu : u.val = v := Finset.mem_singleton.mp u.property
    change x ⟨v, _⟩ = x u
    congr 1
    exact Subtype.ext hu.symm
  right_inv _ := rfl

def siteLocal (v : Vertex L) (B : Matrix (Fin q) (Fin q) ℂ) : Operator L q :=
  liftLocal {v} (reindexStarAlgEquiv (siteConfigurationEquiv v).symm B)

lemma siteLocal_supported (v : Vertex L) (B : Matrix (Fin q) (Fin q) ℂ) :
    SupportedOn (siteLocal v B) {v} := ⟨_, rfl⟩

lemma siteLocal_norm [NeZero q] (v : Vertex L) (B : Matrix (Fin q) (Fin q) ℂ) :
    ‖siteLocal v B‖ = ‖B‖ := by
  rw [siteLocal, liftLocal_norm, StarAlgEquiv.norm_map]

lemma siteLocal_apply (v : Vertex L) (B : Matrix (Fin q) (Fin q) ℂ) (x y : Configuration L q) :
    siteLocal v B x y = if ∀ u, u ≠ v → x u = y u then B (x v) (y v) else 0 := by
  simp only [siteLocal, liftLocal, Finset.mem_singleton]
  rfl

lemma siteLocal_mul_apply (v w : Vertex L) (hvw : v ≠ w)
    (B C : Matrix (Fin q) (Fin q) ℂ) (x y : Configuration L q) :
    (siteLocal v B * siteLocal w C) x y =
      if ∀ u, u ≠ v → u ≠ w → x u = y u then B (x v) (y v) * C (x w) (y w) else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [siteLocal_apply]
  by_cases h : ∀ u, u ≠ v → u ≠ w → x u = y u
  · rw [ite_eq_left h]
    let z : Configuration L q := Function.update x v (y v)
    have hzv : z v = y v := Function.update_self _ _ _
    have hzw : z w = x w := Function.update_of_ne hvw.symm _ _
    have h1 : ∀ u, u ≠ v → x u = z u := fun u hu => (Function.update_of_ne hu _ _).symm
    have h2 : ∀ u, u ≠ w → z u = y u := by
      intro u hu
      by_cases huv : u = v
      · subst u; exact hzv
      · rw [show z u = x u from Function.update_of_ne huv _ _]
        exact h u huv hu
    rw [Finset.sum_eq_single z]
    · rw [ite_eq_left h1, ite_eq_left h2, hzv, hzw]
    · intro z' _ hne
      by_cases hh1 : ∀ u, u ≠ v → x u = z' u
      · by_cases hh2 : ∀ u, u ≠ w → z' u = y u
        · exfalso
          apply hne
          funext u
          by_cases hu : u = v
          · subst u; rw [hzv]; exact hh2 v hvw
          · rw [show z u = x u from Function.update_of_ne hu _ _]; exact (hh1 u hu).symm
        · rw [ite_eq_right hh2, mul_zero]
      · rw [ite_eq_right hh1, zero_mul]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : ∀ u, u ≠ v → x u = z u
    · have h2 : ¬ ∀ u, u ≠ w → z u = y u := by
        intro h2
        exact h (fun u hu hv => (h1 u hu).trans (h2 u hv))
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

def pairConfiguration (v w : Vertex L) (a b : Fin q) : RegionConfiguration q {v,w} :=
  fun u => if u.val = v then a else b

lemma pairConfiguration_left (v w : Vertex L) (a b : Fin q) :
    pairConfiguration v w a b ⟨v, by simp⟩ = a := by simp [pairConfiguration]

lemma pairConfiguration_right (v w : Vertex L) (hvw : v ≠ w) (a b : Fin q) :
    pairConfiguration v w a b ⟨w, by simp⟩ = b := by simp [pairConfiguration, hvw.symm]

def pairConfigurationEquiv (v w : Vertex L) (hvw : v ≠ w) :
    RegionConfiguration q {v,w} ≃ Fin q × Fin q where
  toFun x := (x ⟨v, by simp⟩, x ⟨w, by simp⟩)
  invFun ab := pairConfiguration v w ab.1 ab.2
  left_inv x := by
    funext u
    rcases u with ⟨u, hu⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · simp [pairConfiguration]
    · simp [pairConfiguration, hvw.symm]
  right_inv ab := by
    ext <;> simp [pairConfiguration_left, pairConfiguration_right, hvw]

lemma pairConfiguration_restrict (v w : Vertex L) (x : Configuration L q) :
    pairConfiguration v w (x v) (x w) = restrictConfiguration {v,w} x := by
  funext u
  have hu : u.val = v ∨ u.val = w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using u.property
  dsimp only [pairConfiguration, restrictConfiguration]
  split_ifs with hv
  · rw [hv]
  · rw [hu.resolve_left hv]

def pairBlock (K : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ) (a b : Fin q) :
    Matrix (Fin q) (Fin q) ℂ := fun i j => K (a,i) (b,j)

lemma pairBlock_norm_le [NeZero q]
    (K : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ) (a b : Fin q) :
    ‖pairBlock K a b‖ ≤ ‖K‖ := by
  let e : Fin q ↪ Fin q × Fin q := ⟨fun i => (a,i), fun _ _ h => (Prod.mk.inj h).2⟩
  let f : Fin q ↪ Fin q × Fin q := ⟨fun i => (b,i), fun _ _ h => (Prod.mk.inj h).2⟩
  have he : pairBlock K a b = (injectionMatrix e).conjTranspose * K * injectionMatrix f := by
    ext i j
    exact (matrix_block_apply K e f i j).symm
  rw [he]
  exact matrix_block_norm_le K e f

lemma two_site_decomposition (v w : Vertex L) (hvw : v ≠ w)
    (H : Matrix (RegionConfiguration q {v,w}) (RegionConfiguration q {v,w}) ℂ) :
    let K := reindexStarAlgEquiv (pairConfigurationEquiv v w hvw) H
    liftLocal {v,w} H = ∑ ab : Fin q × Fin q,
      siteLocal v (Matrix.single ab.1 ab.2 1) * siteLocal w (pairBlock K ab.1 ab.2) := by
  classical
  dsimp only
  ext x y
  rw [Matrix.sum_apply]
  simp_rw [siteLocal_mul_apply v w hvw]
  change (if ∀ u, u ∉ ({v,w} : Finset (Vertex L)) → x u = y u then _ else 0) = _
  have hlogic : (∀ u, u ∉ ({v,w} : Finset (Vertex L)) → x u = y u) ↔
      (∀ u, u ≠ v → u ≠ w → x u = y u) := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; tauto
  simp only [hlogic]
  by_cases h : ∀ u, u ≠ v → u ≠ w → x u = y u
  · simp only [ite_eq_left h]
    simp only [Fintype.sum_prod_type, Matrix.single_apply, ite_and, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change _ = H (pairConfiguration v w (x v) (x w)) (pairConfiguration v w (y v) (y w))
    rw [pairConfiguration_restrict, pairConfiguration_restrict]
    rfl
  · simp only [ite_eq_right h, Finset.sum_const_zero]

lemma siteLocal_inside [NeZero q] (A : Finset (Vertex L)) (v : Vertex L)
    (hv : v ∈ A) (B : Matrix (Fin q) (Fin q) ℂ) :
    ∃ BA : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ,
      liftLocal A BA = siteLocal v B ∧ ‖BA‖ = ‖B‖ := by
  obtain ⟨BA, he⟩ := liftLocal_extend (Finset.singleton_subset_iff.mpr hv)
    (reindexStarAlgEquiv (siteConfigurationEquiv v).symm B)
  refine ⟨BA, he, ?_⟩
  rw [← liftLocal_norm A, he]
  exact siteLocal_norm v B

lemma exists_two_site_crossing_factors [NeZero q] (A : Finset (Vertex L))
    (v w : Vertex L) (hv : v ∈ A) (hw : w ∉ A)
    (H : Operator L q) (hH : SupportedOn H {v,w}) :
    ∃ (B : Fin q × Fin q → Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
      (C : Fin q × Fin q → Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ),
      H = ∑ z, liftLocal A (B z) * liftLocal Aᶜ (C z) ∧
      (∀ z, ‖B z‖ ≤ 1) ∧ (∀ z, ‖C z‖ ≤ ‖H‖) := by
  classical
  have hvw : v ≠ w := fun h => hw (h ▸ hv)
  obtain ⟨H, rfl⟩ := hH
  let K := reindexStarAlgEquiv (pairConfigurationEquiv v w hvw) H
  have he : liftLocal {v,w} H = ∑ z : Fin q × Fin q,
      siteLocal v (Matrix.single z.1 z.2 1) * siteLocal w (pairBlock K z.1 z.2) :=
    two_site_decomposition v w hvw H
  have hB := fun z : Fin q × Fin q => siteLocal_inside A v hv (Matrix.single z.1 z.2 1)
  choose B hB hBn using hB
  have hC := fun z : Fin q × Fin q => siteLocal_inside Aᶜ w (Finset.mem_compl.mpr hw) (pairBlock K z.1 z.2)
  choose C hC hCn using hC
  refine ⟨B, C, ?_, ?_, ?_⟩
  · simpa only [hB, hC] using he
  · intro z
    rw [hBn z]
    exact matrix_single_norm_le _ _
  · intro z
    rw [hCn z, liftLocal_norm]
    exact (pairBlock_norm_le K z.1 z.2).trans_eq (StarAlgEquiv.norm_map _ H)

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
