import Mathlib
import OAI.Combinatorics.StripMass.Basic

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

abbrev Vec (n : ℕ) := Fin n → ℂ
abbrev Grassmann (n : ℕ) := ExteriorAlgebra ℂ (Vec n)

def standardBasis (n : ℕ) : Module.Basis (Fin n) ℂ (Vec n) := Pi.basisFun ℂ (Fin n)
def generator (n : ℕ) (i : Fin n) : Grassmann n :=
  ExteriorAlgebra.ι ℂ (standardBasis n i)
def twoForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Grassmann n :=
  ∑ i, ∑ j ∈ Finset.Ioi i, A i j • (generator n i * generator n j)
def pfaffian (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((standardBasis n).ExteriorAlgebra.repr ((twoForm A) ^ (n / 2))) Finset.univ /
    (Nat.factorial (n / 2) : ℂ)

def d : ℂ := (Real.cos (2 * (Real.pi / 8)) : ℝ)
def rho : ℂ := (1 / Real.sqrt (2 + Real.sqrt 2) : ℝ)
def D (a b : ℂ) : ℂ := a ^ 2 + b ^ 2 + 2 * d * a * b - d ^ 2
def kernel (a b : ℂ) : ℂ := (a - b) * (a + b + rho) / D a b

def pfSize (N : ℕ) : ℕ := 2 * ((N + 1) / 2)
def augmentedKernel (N : ℕ) (a : Fin N → ℂ) : Matrix (Fin (pfSize N)) (Fin (pfSize N)) ℂ :=
  fun i j => if hi : i.val < N then
    if hj : j.val < N then kernel (a ⟨i.val, hi⟩) (a ⟨j.val, hj⟩) else 1
    else if j.val < N then -1 else 0

def p (N : ℕ) (a : Fin N → ℂ) : ℂ :=
  (∏ i, ∏ j ∈ Finset.Ioi i, D (a i) (a j) / (a i - a j)) *
    pfaffian (pfSize N) (augmentedKernel N a)



def topWedge (n : ℕ) : Grassmann n := ExteriorAlgebra.ιMulti ℂ n (standardBasis n)
def topCoord (n : ℕ) : Grassmann n →ₗ[ℂ] ℂ :=
  (standardBasis n).ExteriorAlgebra.coord Finset.univ

lemma top_wedge_determinant (n : ℕ) (v : Fin n → Vec n) :
    ExteriorAlgebra.ιMulti ℂ n v = (standardBasis n).det v • topWedge n := by
  have hf : ExteriorAlgebra.ιMulti ℂ n (M := Vec n) =
      ((standardBasis n).det).smulRight (topWedge n) := by
    apply (standardBasis n).ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change ExteriorAlgebra.ιMulti ℂ n ((standardBasis n) ∘ σ) =
      (((standardBasis n).det).smulRight (topWedge n)) ((standardBasis n) ∘ σ)
    simp [AlternatingMap.map_perm, topWedge, Module.Basis.det_self]
  exact DFunLike.congr_fun hf v

lemma generator_mem (n : ℕ) (i : Fin n) :
    generator n i ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ : Vec n →ₗ[ℂ] Grassmann n)) :=
  LinearMap.mem_range_self _ _

lemma twoForm_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    twoForm A ∈ ExteriorAlgebra.exteriorPower ℂ 2 (Vec n) := by
  unfold twoForm ExteriorAlgebra.exteriorPower
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  simpa only [pow_two] using Submodule.mul_mem_mul (generator_mem n i) (generator_mem n j)

lemma twoForm_pow_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    twoForm A ^ m ∈ ExteriorAlgebra.exteriorPower ℂ (2 * m) (Vec n) := by
  convert Submodule.pow_mem_pow _ (twoForm_mem A) m using 1
  exact pow_mul _ 2 m

lemma exteriorBasis_univ (n : ℕ) :
    (standardBasis n).ExteriorAlgebra Finset.univ = topWedge n := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin n)).card = n)]
  unfold ExteriorAlgebra.ιMulti_family topWedge
  congr 1
  funext i
  simp only [Function.comp_apply]
  apply congrArg (standardBasis n)
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change Finset.univ.orderEmbOfFin (by simp) i = i
  exact congr_fun (Finset.orderEmbOfFin_unique (by simp)
    (fun x : Fin n => Finset.mem_univ x) (fun _ _ h => h)).symm i

@[simp] lemma topCoord_topWedge (n : ℕ) : topCoord n (topWedge n) = 1 := by
  rw [← exteriorBasis_univ]
  simp [topCoord, Module.Basis.coord_apply]

lemma topCoord_wedge (n : ℕ) (v : Fin n → Vec n) :
    topCoord n (ExteriorAlgebra.ιMulti ℂ n v) = (standardBasis n).det v := by
  rw [top_wedge_determinant, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma homogeneous_eq_coord_topWedge (n : ℕ) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    x = topCoord n x • topWedge n := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    rw [topCoord_wedge, top_wedge_determinant]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add, add_smul, ← ihx, ← ihy]
  | smul r x hx ih =>
    rw [map_smul, smul_eq_mul, ← smul_smul, ← ih]

lemma topCoord_map (n : ℕ) (f : Vec n →ₗ[ℂ] Vec n) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord n (ExteriorAlgebra.map f x) = f.det * topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul]
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti, topCoord_wedge]
  have hd : (standardBasis n).det (f ∘ standardBasis n) = f.det := by
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hd, smul_eq_mul, mul_comm]

lemma generator_anticomm (n : ℕ) (i j : Fin n) :
    generator n i * generator n j = -(generator n j * generator n i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma sum_symmetric_offdiag {n : ℕ} {E : Type*} [AddCommGroup E]
    (F : Fin n → Fin n → E) (hF : ∀ i j, F i j = F j i)
    (hzero : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
  have hij (i j : Fin n) : F i j =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hzero]
    · simp [h, not_lt_of_gt h, hF i j]
  have hsum (i : Fin n) : (∑ j, if i < j then F i j else 0) =
      ∑ j ∈ Finset.Ioi i, F i j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  calc
    ∑ i, ∑ j, F i j =
        (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ i, ∑ j, if j < i then F j i else 0) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j
    _ = (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ j, ∑ i, if j < i then F j i else 0) := by
      rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
    _ = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
      simp only [hsum, two_nsmul]

lemma twoForm_full {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    twoForm A = (1 / 2 : ℂ) • ∑ i, ∑ j, A i j • (generator n i * generator n j) := by
  have hs := sum_symmetric_offdiag
    (fun i j => A i j • (generator n i * generator n j))
    (fun i j => by rw [hA i j, generator_anticomm n j i, neg_smul, smul_neg, neg_neg])
    (fun i => by simp [generator])
  rw [hs]
  change twoForm A = (1 / 2 : ℂ) • (2 • twoForm A)
  rw [← Nat.cast_smul_eq_nsmul ℂ 2, smul_smul]
  norm_num

def permMap (n : ℕ) (σ : Equiv.Perm (Fin n)) : Vec n →ₗ[ℂ] Vec n :=
  (standardBasis n).constr ℂ (fun i => standardBasis n (σ i))

@[simp] lemma permMap_basis (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permMap n σ (standardBasis n i) = standardBasis n (σ i) := by
  simp [permMap]

@[simp] lemma permMap_generator (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ExteriorAlgebra.map (permMap n σ) (generator n i) = generator n (σ i) := by
  simp [generator]

lemma permMap_det (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permMap n σ).det = (Equiv.Perm.sign σ : ℂ) := by
  have he : permMap n σ ∘ standardBasis n = standardBasis n ∘ σ := by
    funext i
    exact permMap_basis n σ i
  have hd := Module.Basis.det_comp (standardBasis n) (permMap n σ) (standardBasis n)
  rw [he, AlternatingMap.map_perm, Module.Basis.det_self, mul_one] at hd
  simpa [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul] using hd.symm

lemma twoForm_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    ExteriorAlgebra.map (permMap n σ) (twoForm A) =
      twoForm (fun i j => A (σ.symm i) (σ.symm j)) := by
  rw [twoForm_full A hA, twoForm_full _ (fun i j => hA _ _)]
  simp only [map_smul, map_sum, map_mul, permMap_generator]
  congr 1
  apply Fintype.sum_equiv σ
  intro i
  simp only [Equiv.symm_apply_apply]
  apply Fintype.sum_equiv σ
  intro j
  simp

lemma pfaffian_perm (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    pfaffian n (fun i j => A (σ.symm i) (σ.symm j)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    (Equiv.Perm.sign σ : ℂ) * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_perm A hA σ, ← map_pow, topCoord_map n _ _ hhom, permMap_det]
  ring

lemma pfaffian_duplicate (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (i j : Fin n) (hij : i ≠ j)
    (hrow : ∀ k, A i k = A j k) : pfaffian n A = 0 := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hs_left (x y : Fin n) : A (σ x) y = A x y := by
    by_cases hxi : x = i
    · subst x
      simpa [σ] using (hrow y).symm
    by_cases hxj : x = j
    · subst x
      simpa [σ] using hrow y
    simp [σ, Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have hs_right (x y : Fin n) : A x (σ y) = A x y := by
    rw [hA, hs_left, hA, neg_neg]
  have he : (fun x y => A (σ.symm x) (σ.symm y)) = A := by
    funext x y
    change A (Equiv.swap i j x) (Equiv.swap i j y) = A x y
    rw [show Equiv.swap i j = σ from rfl, hs_left, hs_right]
  have hp := pfaffian_perm n hn A hA σ
  rw [he] at hp
  have hsign : (Equiv.Perm.sign σ : ℂ) = -1 := by
    simp [σ, Equiv.Perm.sign_swap hij]
  rw [hsign, neg_one_mul] at hp
  linear_combination hp / 2

lemma wedge_anticomm {n : ℕ} (u v : Vec n) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v =
      -(ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma wedge_commutes {n : ℕ} (u v : Vec n) (x : Grassmann n) :
    Commute (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι w =>
    change (_ * _) * _ = _ * (_ * _)
    calc
      _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) :=
        mul_assoc _ _ _
      _ = -(ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
        rw [wedge_anticomm v w, mul_neg]
      _ = -((ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ v) := by
        rw [mul_assoc]
      _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ v := by
        rw [wedge_anticomm u w, neg_mul, neg_neg]
      _ = _ := mul_assoc _ _ _
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

lemma twoForm_commutes {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Grassmann n) :
    Commute (twoForm A) x := by
  unfold twoForm
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_left
  intro j hj
  exact (wedge_commutes (standardBasis n i) (standardBasis n j) x).smul_left (A i j)

lemma wedge_sq_zero {n : ℕ} (u v : Vec n) :
    (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) ^ 2 = 0 := by
  rw [pow_two, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι ℂ v), wedge_anticomm v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]
  simp

lemma twoForm_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    twoForm (A + B) = twoForm A + twoForm B := by
  simp [twoForm, add_smul, Finset.sum_add_distrib]

lemma twoForm_smul {n : ℕ} (t : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    twoForm (t • A) = t • twoForm A := by
  simp [twoForm, smul_smul, Finset.smul_sum]

lemma generator_expansion (n : ℕ) (u : Vec n) :
    (∑ i, u i • generator n i) = ExteriorAlgebra.ι ℂ u := by
  have h := congrArg (ExteriorAlgebra.ι ℂ) ((standardBasis n).sum_repr u)
  simpa [standardBasis, generator, map_sum, map_smul] using h

def rankTwo {n : ℕ} (u v : Vec n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => u i * v j - v i * u j

lemma rankTwo_skew {n : ℕ} (u v : Vec n) (i j : Fin n) :
    rankTwo u v j i = -rankTwo u v i j := by
  unfold rankTwo
  ring

lemma twoForm_rankTwo {n : ℕ} (u v : Vec n) :
    twoForm (rankTwo u v) = ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v := by
  rw [twoForm_full _ (rankTwo_skew u v)]
  simp only [rankTwo, sub_smul, Finset.sum_sub_distrib,
    ← smul_mul_smul_comm, ← Finset.sum_mul_sum, generator_expansion]
  rw [wedge_anticomm v u, sub_neg_eq_add, ← two_smul ℂ]
  rw [smul_smul]
  norm_num

lemma pow_add_sq_zero {E : Type*} [Ring E] [Algebra ℂ E] (a b : E)
    (hab : Commute a b) (hb : b ^ 2 = 0) (m : ℕ) :
    (a + b) ^ (m + 1) = a ^ (m + 1) + (m + 1 : ℂ) • (a ^ m * b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (a + b), ih, add_mul, mul_add, mul_add,
      smul_mul_assoc, smul_mul_assoc]
    have hba : a ^ m * b * a = a ^ (m + 1) * b := by
      rw [mul_assoc, hab.eq.symm, ← mul_assoc, ← pow_succ]
    have hbb : a ^ m * b * b = 0 := by rw [mul_assoc, ← pow_two, hb, mul_zero]
    rw [hba, hbb, smul_zero, add_zero, ← pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    module

lemma high_degree_zero {n k : ℕ} (hk : n < k) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ k (Vec n)) : x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    apply AlternatingMap.map_linearDependent
    intro hv
    have h := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at h
    omega
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul r x hx ih => simp [ih]

def embedMap (n : ℕ) : Vec n →ₗ[ℂ] Vec (n + 1) :=
  (standardBasis n).constr ℂ (fun i => standardBasis (n + 1) i.castSucc)

@[simp] lemma embedMap_basis (n : ℕ) (i : Fin n) :
    embedMap n (standardBasis n i) = standardBasis (n + 1) i.castSucc := by
  simp [embedMap]

@[simp] lemma embedMap_generator (n : ℕ) (i : Fin n) :
    ExteriorAlgebra.map (embedMap n) (generator n i) = generator (n + 1) i.castSucc := by
  simp [generator]

lemma embedMap_apply (n : ℕ) (u : Vec n) : embedMap n u = Fin.snoc u 0 := by
  conv_lhs => rw [← (standardBasis n).sum_repr u, map_sum]
  simp only [map_smul, embedMap_basis]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [standardBasis, Pi.basisFun_apply]
  · simp [standardBasis, Pi.basisFun_apply, Pi.single_apply]

def border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => -u j) j)
    (fun i => Fin.lastCases (u i) (fun j => A i j) j) i

@[simp] lemma border_old_old {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) (i j : Fin n) :
    border A u i.castSucc j.castSucc = A i j := by simp [border]
@[simp] lemma border_old_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) (i : Fin n) :
    border A u i.castSucc (Fin.last n) = u i := by simp [border]
@[simp] lemma border_last_old {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) (i : Fin n) :
    border A u (Fin.last n) i.castSucc = -u i := by simp [border]
@[simp] lemma border_last_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    border A u (Fin.last n) (Fin.last n) = 0 := by simp [border]

lemma border_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (i j : Fin (n + 1)) :
    border A u j i = -border A u i j := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [border_last_last, border_last_old, border_old_last, border_old_old,
      neg_zero, neg_neg]
  exact hA _ _

lemma twoForm_border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    twoForm (border A u) = ExteriorAlgebra.map (embedMap n) (twoForm A) +
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
  rw [twoForm_full _ (border_skew A hA u), twoForm_full A hA]
  simp only [map_smul, map_sum, map_mul, embedMap_generator]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, border_old_old, border_old_last,
    border_last_old, border_last_last, zero_smul, add_zero, Finset.sum_add_distrib]
  have hu : (∑ i : Fin n, u i • generator (n + 1) i.castSucc) =
      ExteriorAlgebra.ι ℂ (embedMap n u) := by
    have h := congrArg (ExteriorAlgebra.map (embedMap n)) (generator_expansion n u)
    simpa using h
  have hp : (∑ i : Fin n, u i • (generator (n + 1) i.castSucc * generator (n + 1) (Fin.last n))) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hu, Finset.sum_mul]
    simp only [smul_mul_assoc]
  have hm : (∑ i : Fin n, -u i • (generator (n + 1) (Fin.last n) * generator (n + 1) i.castSucc)) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [generator_anticomm (n + 1) (Fin.last n), neg_smul, smul_neg, neg_neg]
  rw [hp, hm]
  module

lemma topWedge_snoc (n : ℕ) :
    topWedge (n + 1) = ExteriorAlgebra.map (embedMap n) (topWedge n) *
      generator (n + 1) (Fin.last n) := by
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti]
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Function.comp_apply, embedMap_basis, generator]

lemma topCoord_embed_mul_last {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 1) (ExteriorAlgebra.map (embedMap n) x * generator (n + 1) (Fin.last n)) =
      topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, smul_mul_assoc, ← topWedge_snoc,
    map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

def borderLinear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Vec n →ₗ[ℂ] ℂ where
  toFun u := topCoord (n + 1) (ExteriorAlgebra.map (embedMap n) (twoForm A) ^ (n / 2) *
    (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n))) / (n / 2).factorial
  map_add' u v := by simp [mul_add, add_mul, add_div]
  map_smul' t u := by simp [smul_eq_mul, mul_div_assoc]

end
end StripPfaffian

end OAI
