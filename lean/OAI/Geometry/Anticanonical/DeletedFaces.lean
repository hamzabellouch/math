import Mathlib

namespace OAI

/-!
# Deleted-face retractions and preliminaries for anticanonical indices

The coordinate invariant Dolbeault index is defined, with high-degree vanishing proved.
The deleted-face deformation retraction and contractibility are supporting results,
alongside positive-weight lattice fibers, compactness, polarization and polynomial continuation.
No theorem identifies this geometric index with a polynomial: Euler-characteristic cancellation,
equivariant Dolbeault localization and the weighted Ehrhart step remain unproved.
The metric and direct-image arguments for pseudoeffective-error conversion are also absent.
-/

open Set
open scoped BigOperators ContDiff

noncomputable section
namespace AnticanonicalIndex
namespace Geometry

abbrev Space (n : ℕ) := Fin n → ℂ

structure Atlas (n c : ℕ) (F : Type*) [TopologicalSpace F] where
  chart : Fin c → OpenPartialHomeomorph F (Space n)
  cover : ∀ x, ∃ i, x ∈ (chart i).source
  holomorphic_transition : ∀ i j, AnalyticOnNhd ℂ
    (fun z => chart j ((chart i).symm z))
    ((chart i).target ∩ (chart i).symm ⁻¹' (chart j).source)

variable {n c : ℕ} {F : Type*} [TopologicalSpace F]

def Atlas.transition (M : Atlas n c F) (i j : Fin c) (z : Space n) : Space n :=
  M.chart j ((M.chart i).symm z)

def Atlas.overlap (M : Atlas n c F) (i j : Fin c) : Set (Space n) :=
  (M.chart i).target ∩ (M.chart i).symm ⁻¹' (M.chart j).source

def jacobian (f : Space n → Space n) (z : Space n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => fderiv ℂ f z (Pi.single j 1) i

def antiDir (v : Space n) (f : Space n → ℂ) (z : Space n) : ℂ :=
  (fderiv ℝ f z v + Complex.I * fderiv ℝ f z (Complex.I • v)) / 2

abbrev Coefficients (n c q : ℕ) := Fin c → Space n → (Fin q → Fin n) → ℂ

def pullCoefficient {q : ℕ} (f : Space n → Space n) (z : Space n)
    (a : (Fin q → Fin n) → ℂ) (J : Fin q → Fin n) : ℂ :=
  ∑ K : Fin q → Fin n,
    a K * ∏ k : Fin q, starRingEnd ℂ (fderiv ℂ f z (Pi.single (J k) 1) (K k))

def AlternatingCoefficients {q : ℕ} (a : (Fin q → Fin n) → ℂ) : Prop :=
  (∀ J, ¬ Function.Injective J → a J = 0) ∧
  ∀ (σ : Equiv.Perm (Fin q)) J,
    a (J ∘ σ) = (((σ.sign : ℤ) : ℂ)) * a J

def IsForm (M : Atlas n c F) (m q : ℕ) (a : Coefficients n c q) : Prop :=
  (∀ i z, z ∉ (M.chart i).target → ∀ J, a i z J = 0) ∧
  (∀ i J, ContDiffOn ℝ ∞ (fun z => a i z J) (M.chart i).target) ∧
  (∀ i z, AlternatingCoefficients (a i z)) ∧
  ∀ i j z, z ∈ M.overlap i j → ∀ J,
    pullCoefficient (M.transition i j) z (a j (M.transition i j z)) J =
      (jacobian (M.transition i j) z).det ^ m * a i z J

def dbar {q : ℕ} (a : Coefficients n c q) (i : Fin c) (z : Space n)
    (J : Fin (q + 1) → Fin n) : ℂ :=
  ∑ k : Fin (q + 1), (-1 : ℂ) ^ (k : ℕ) *
    antiDir (Pi.single (J k) 1) (fun w => a i w (J ∘ k.succAbove)) z

def IsClosedForm (M : Atlas n c F) {q : ℕ} (a : Coefficients n c q) : Prop :=
  ∀ i z, z ∈ (M.chart i).target → ∀ J, dbar a i z J = 0

def IsExact (M : Atlas n c F) (m : ℕ) :
    (q : ℕ) → Coefficients n c q → Prop
  | 0, a => a = 0
  | q + 1, a => ∃ b : Coefficients n c q, IsForm M m q b ∧
      ∀ i z, z ∈ (M.chart i).target → ∀ J, a i z J = dbar b i z J

structure Torus (r : ℕ) (T : Type*) [Group T] [TopologicalSpace T] where
  coordinates : T ≃ₜ* (Fin r → Circle)

def Torus.exp {r : ℕ} {T : Type*} [Group T] [TopologicalSpace T]
    (G : Torus r T) (θ : Fin r → ℝ) : T :=
  G.coordinates.symm (fun k => Circle.exp (θ k))

structure HolomorphicAction (M : Atlas n c F) {r : ℕ} {T : Type*}
    [Group T] [TopologicalSpace T] (G : Torus r T) where
  act : T → F → F
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ t u x, act (t * u) x = act t (act u x)
  continuous_act : Continuous (fun p : T × F => act p.1 p.2)
  holomorphic_act : ∀ t i j, AnalyticOnNhd ℂ
    (fun z => M.chart j (act t ((M.chart i).symm z)))
    {z | z ∈ (M.chart i).target ∧ act t ((M.chart i).symm z) ∈ (M.chart j).source}
  smooth_act : ∀ i j, ContDiffOn ℝ ∞
    (fun p : (Fin r → ℝ) × Space n => M.chart j (act (G.exp p.1) ((M.chart i).symm p.2)))
    {p | p.2 ∈ (M.chart i).target ∧
      act (G.exp p.1) ((M.chart i).symm p.2) ∈ (M.chart j).source}

variable {r : ℕ} {T : Type*} [Group T] [TopologicalSpace T]
variable {M : Atlas n c F} {G : Torus r T}

def HolomorphicAction.coordinateMap (A : HolomorphicAction M G) (t : T)
    (i j : Fin c) (z : Space n) : Space n :=
  M.chart j (A.act t ((M.chart i).symm z))

def HolomorphicAction.coordinateDomain (A : HolomorphicAction M G) (t : T)
    (i j : Fin c) : Set (Space n) :=
  {z | z ∈ (M.chart i).target ∧ A.act t ((M.chart i).symm z) ∈ (M.chart j).source}

def IsInvariantClass (A : HolomorphicAction M G) (m q : ℕ)
    (a : Coefficients n c q) : Prop :=
  ∀ t, ∃ b : Coefficients n c q, IsForm M m q b ∧ IsExact M m q b ∧
    ∀ i j z, z ∈ A.coordinateDomain t i j → ∀ J,
      pullCoefficient (A.coordinateMap t i j) z (a j (A.coordinateMap t i j z)) J =
        (jacobian (A.coordinateMap t i j) z).det ^ m * (a i z J + b i z J)

def invariantCycles (A : HolomorphicAction M G) (m q : ℕ) :
    Submodule ℂ (Coefficients n c q) :=
  Submodule.span ℂ {a | IsForm M m q a ∧ IsClosedForm M a ∧ IsInvariantClass A m q a}

def exactForms (M : Atlas n c F) (m q : ℕ) : Submodule ℂ (Coefficients n c q) :=
  Submodule.span ℂ {a | IsForm M m q a ∧ IsExact M m q a}

abbrev InvariantDolbeault (A : HolomorphicAction M G) (m q : ℕ) :=
  (invariantCycles A m q) ⧸
    (exactForms M m q).comap (invariantCycles A m q).subtype

def invariantIndex (A : HolomorphicAction M G) (m : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q *
    (Module.finrank ℂ (InvariantDolbeault A m q) : ℤ)

lemma form_eq_zero_of_dimension_lt {m q : ℕ} (a : Coefficients n c q)
    (ha : IsForm M m q a) (hnq : n < q) : a = 0 := by
  funext i z J
  apply (ha.2.2.1 i z).1 J
  intro hJ
  have h := Fintype.card_le_of_injective J hJ
  simp only [Fintype.card_fin] at h
  exact Nat.not_le_of_gt hnq h

lemma invariantCycles_eq_bot_of_dimension_lt (A : HolomorphicAction M G)
    (m q : ℕ) (hnq : n < q) : invariantCycles A m q = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  intro a ha
  simpa using form_eq_zero_of_dimension_lt a ha.1 hnq

theorem invariantDolbeault_finrank_eq_zero_of_dimension_lt
    (A : HolomorphicAction M G) (m q : ℕ) (hnq : n < q) :
    Module.finrank ℂ (InvariantDolbeault A m q) = 0 := by
  have hbot := invariantCycles_eq_bot_of_dimension_lt A m q hnq
  have hsub : Subsingleton (invariantCycles A m q) := by
    rw [hbot]
    infer_instance
  let := hsub
  exact Module.finrank_zero_of_subsingleton

end Geometry

end AnticanonicalIndex

open Set
open scoped BigOperators

noncomputable section

namespace AnticanonicalIndex
namespace DeletedFaces

variable {ι V : Type*} [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

def vertex (I : Finset ι) : ι → ℝ := fun i => if i ∈ I then -1 else 1

def domain (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ L x = L (vertex I)}

def boundary (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) : Set (ι → ℝ) :=
  {x | x ∈ domain L I ∧ ∃ i ∈ I, x i = 0}

lemma boundary_subset_domain (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) :
    boundary L I ⊆ domain L I := fun _ hx => hx.1

lemma convex_domain (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) :
    Convex ℝ (domain L I) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [map_add, map_smul, hx.2, hy.2, ← add_smul, hab, one_smul]

def inclusion (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) :
    C(boundary L I, domain L I) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def entryTime (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) : ℝ :=
  I.sup' hI (fun i => (x.1 i + 1)⁻¹)

lemma inv_le_entryTime (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) {i : ι} (hi : i ∈ I) :
    (x.1 i + 1)⁻¹ ≤ entryTime L I hI x :=
  Finset.le_sup' (fun i => (x.1 i + 1)⁻¹) hi

lemma entryTime_pos (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) : 0 < entryTime L I hI x := by
  let i := hI.choose
  have hi : i ∈ I := hI.choose_spec
  exact (inv_pos.mpr (by linarith [x.2.1 i])).trans_le (inv_le_entryTime L I hI x hi)

lemma entryTime_le_one (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) : entryTime L I hI x ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  exact (inv_le_one₀ (by linarith [x.2.1 i])).mpr (by linarith [x.2.1 i])

lemma continuous_entryTime (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty) :
    Continuous (entryTime L I hI) := by
  apply Continuous.finset_sup'_apply
  intro i _
  apply (((continuous_apply i).comp continuous_subtype_val).add continuous_const).inv₀
  intro x
  change x.1 i + 1 ≠ 0
  linarith [x.2.1 i]

def retractPoint (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) : ι → ℝ :=
  vertex I + entryTime L I hI x • (x.1 - vertex I)

lemma retractPoint_mem (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) : retractPoint L I hI x ∈ boundary L I := by
  have ht0 := (entryTime_pos L I hI x).le
  have ht1 := entryTime_le_one L I hI x
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · by_cases hi : i ∈ I
    · have hxi : 0 < x.1 i + 1 := by linarith [x.2.1 i]
      have hmul : 1 ≤ entryTime L I hI x * (x.1 i + 1) := by
        calc
          1 = (x.1 i + 1)⁻¹ * (x.1 i + 1) := (inv_mul_cancel₀ hxi.ne').symm
          _ ≤ entryTime L I hI x * (x.1 i + 1) :=
            mul_le_mul_of_nonneg_right (inv_le_entryTime L I hI x hi) hxi.le
      simp only [retractPoint, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, vertex, ite_eq_left hi]
      linarith
    · have hx := mul_nonneg ht0 (x.2.1 i)
      simp only [retractPoint, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, vertex, ite_eq_right hi]
      nlinarith
  · simp only [retractPoint, map_add, map_smul, map_sub, x.2.2, sub_self,
      smul_zero, add_zero]
  · obtain ⟨i, hi, ht⟩ := Finset.exists_mem_eq_sup' hI (fun i => (x.1 i + 1)⁻¹)
    refine ⟨i, hi, ?_⟩
    have hxi : x.1 i + 1 ≠ 0 := by linarith [x.2.1 i]
    simp only [retractPoint, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      vertex, ite_eq_left hi, entryTime, ht]
    rw [sub_neg_eq_add, inv_mul_cancel₀ hxi]
    ring

lemma entryTime_eq_one (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) (hx : x.1 ∈ boundary L I) : entryTime L I hI x = 1 := by
  obtain ⟨i, hi, hxi⟩ := hx.2
  apply le_antisymm (entryTime_le_one L I hI x)
  simpa [hxi] using inv_le_entryTime L I hI x hi

lemma retractPoint_fixed (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : domain L I) (hx : x.1 ∈ boundary L I) : retractPoint L I hI x = x.1 := by
  simp [retractPoint, entryTime_eq_one L I hI x hx]

lemma continuous_retractPoint (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty) :
    Continuous (retractPoint L I hI) :=
  continuous_const.add ((continuous_entryTime L I hI).smul
    (continuous_subtype_val.sub continuous_const))

def retraction (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty) :
    C(domain L I, boundary L I) :=
  ⟨fun x => ⟨retractPoint L I hI x, retractPoint_mem L I hI x⟩,
    (continuous_retractPoint L I hI).subtype_mk _⟩

lemma retraction_inclusion (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty)
    (x : boundary L I) : retraction L I hI (inclusion L I x) = x := by
  apply Subtype.ext
  exact retractPoint_fixed L I hI _ x.2

def retractionHomotopy (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (domain L I))
      ((inclusion L I).comp (retraction L I hI)) {x | x.1 ∈ boundary L I} where
  toFun p := ⟨(1 - (p.1 : ℝ)) • p.2.1 + (p.1 : ℝ) • retractPoint L I hI p.2,
    convex_domain L I p.2.2 (retractPoint_mem L I hI p.2).1
      (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((continuous_retractPoint L I hI).comp continuous_snd))
  map_zero_left x := by apply Subtype.ext; simp
  map_one_left x := by apply Subtype.ext; simp [inclusion, retraction]
  prop' t x hx := by
    apply Subtype.ext
    change (1 - (t : ℝ)) • x.1 + (t : ℝ) • retractPoint L I hI x = x.1
    rw [retractPoint_fixed L I hI x hx, ← add_smul]
    simp

theorem deleted_faces_deformation_retract (L : (ι → ℝ) →ₗ[ℝ] V)
    (I : Finset ι) (hI : I.Nonempty) :
    ∃ r : C(domain L I, boundary L I),
      (∀ x, r (inclusion L I x) = x) ∧
      (ContinuousMap.id (domain L I)).HomotopicRel ((inclusion L I).comp r)
        {x | x.1 ∈ boundary L I} :=
  ⟨retraction L I hI, retraction_inclusion L I hI, ⟨retractionHomotopy L I hI⟩⟩

def homotopyEquiv (L : (ι → ℝ) →ₗ[ℝ] V) (I : Finset ι) (hI : I.Nonempty) :
    ContinuousMap.HomotopyEquiv (domain L I) (boundary L I) where
  toFun := retraction L I hI
  invFun := inclusion L I
  left_inv := ⟨(retractionHomotopy L I hI).toHomotopy.symm⟩
  right_inv := by
    have h : (retraction L I hI).comp (inclusion L I) = ContinuousMap.id _ := by
      ext x : 1
      exact retraction_inclusion L I hI x
    rw [h]

theorem deleted_faces_contractible (L : (ι → ℝ) →ₗ[ℝ] V)
    (I : Finset ι) (hI : I.Nonempty) (hD : (domain L I).Nonempty) :
    ContractibleSpace (boundary L I) := by
  let : ContractibleSpace (domain L I) := (convex_domain L I).contractibleSpace hD
  exact (homotopyEquiv L I hI).symm.contractibleSpace

end DeletedFaces
namespace PositiveWeights
variable {ι V : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V]

def equation (α : ι → V) : (ι → ℝ) →ₗ[ℝ] V where
  toFun x := ∑ i, x i • α i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]

lemma pair_equation (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    ℓ (equation α x) = ∑ i, x i * ℓ (α i) := by
  simp [equation, map_sum]

lemma coordinate_bound (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i : ι) :
    x i ≤ ℓ (equation α x) / ℓ (α i) := by
  apply (le_div_iff₀ (hα i)).mpr
  rw [pair_equation]
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hx j) (hα j).le) (Finset.mem_univ i)

theorem zero_fiber (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (heq : equation α x = 0) : x = 0 := by
  funext i
  have h := coordinate_bound α ℓ hα hx i
  simp only [heq, map_zero, zero_div] at h
  exact le_antisymm h (hx i)

theorem zero_fiber_with_deleted_faces (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) (I : Finset ι) (x : ι → ℝ) :
    ((∀ i, 0 ≤ x i) ∧ equation α x = 0 ∧ (∀ i ∈ I, 0 < x i)) ↔
      x = 0 ∧ I = ∅ := by
  constructor
  · rintro ⟨hx, heq, hstrict⟩
    have hzero := zero_fiber α ℓ hα hx heq
    refine ⟨hzero, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro i hi
    simpa [hzero] using hstrict i hi
  · rintro ⟨rfl, rfl⟩
    simp

theorem nonnegative_integral_fiber_finite (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) (v : V) :
    {b : ι → ℕ | equation α (fun i => (b i : ℝ)) = v}.Finite := by
  let N : ι → ℕ := fun i => Nat.ceil (ℓ v / ℓ (α i))
  apply (Set.Finite.pi (fun i => Set.finite_Iic (N i))).subset
  intro b hb i _
  have h := coordinate_bound α ℓ hα (x := fun i => (b i : ℝ))
    (fun i => Nat.cast_nonneg (b i)) i
  rw [hb] at h
  exact Nat.cast_le.mp (h.trans (Nat.le_ceil _))

def latticeFiber (α : ι → V) (v : V) (I : Finset ι) : Set (ι → ℕ) :=
  {b | equation α (fun i => (b i : ℝ)) = v ∧ ∀ i ∈ I, 0 < b i}

lemma latticeFiber_finite (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) (v : V) (I : Finset ι) :
    (latticeFiber α v I).Finite :=
  (nonnegative_integral_fiber_finite α ℓ hα v).subset (fun _ hb => hb.1)

lemma mem_latticeFiber_zero (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) (I : Finset ι) (b : ι → ℕ) :
    b ∈ latticeFiber α 0 I ↔ b = 0 ∧ I = ∅ := by
  constructor
  · rintro ⟨heq, hstrict⟩
    have hz : (fun i => (b i : ℝ)) = 0 :=
      zero_fiber α ℓ hα (fun i => Nat.cast_nonneg (b i)) heq
    have hb : b = 0 := by
      funext i
      exact Nat.cast_eq_zero.mp (congr_fun hz i)
    refine ⟨hb, Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => ?_)⟩
    simpa [hb] using hstrict i hi
  · rintro ⟨rfl, rfl⟩
    simp [latticeFiber, equation]

theorem weighted_count_at_zero [DecidableEq ι] {R : Type*} [AddCommMonoid R]
    (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ) (hα : ∀ i, 0 < ℓ (α i))
    (I : Finset ι) (W : (ι → ℕ) → R) :
    ∑ b ∈ (latticeFiber_finite α ℓ hα 0 I).toFinset, W b =
      if I = ∅ then W 0 else 0 := by
  classical
  have hset : latticeFiber α 0 I = if I = ∅ then {0} else ∅ := by
    ext b
    rw [mem_latticeFiber_zero α ℓ hα]
    by_cases hi : I = ∅ <;> simp [hi]
  by_cases hi : I = ∅
  · have hfin : (latticeFiber_finite α ℓ hα 0 I).toFinset = {0} := by
      ext b
      rw [Set.Finite.mem_toFinset, hset, ite_eq_left hi]
      simp
    rw [hfin, Finset.sum_singleton, ite_eq_left hi]
  · have hfin : (latticeFiber_finite α ℓ hα 0 I).toFinset = ∅ := by
      ext b
      rw [Set.Finite.mem_toFinset, hset, ite_eq_right hi]
      simp
    rw [hfin, Finset.sum_empty, ite_eq_right hi]

end PositiveWeights

namespace DeletedFaces

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem domain_compact (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) (I : Finset ι) :
    IsCompact (domain (PositiveWeights.equation α) I) := by
  let L := PositiveWeights.equation α
  have hclosed : IsClosed (domain L I) := by
    change IsClosed ({x : ι → ℝ | ∀ i, 0 ≤ x i} ∩ {x | L x = L (vertex I)})
    apply IsClosed.inter
    · simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq L.continuous_of_finiteDimensional continuous_const
  apply (isCompact_Icc (a := (0 : ι → ℝ))
    (b := fun i => ℓ (L (vertex I)) / ℓ (α i))).of_isClosed_subset hclosed
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  have hi := PositiveWeights.coordinate_bound α ℓ hα hx.1 i
  rwa [hx.2] at hi

theorem boundary_compact (α : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ i, 0 < ℓ (α i)) (I : Finset ι) :
    IsCompact (boundary (PositiveWeights.equation α) I) := by
  have hclosed : IsClosed {x : ι → ℝ | ∃ i ∈ I, x i = 0} := by
    have h := isClosed_biUnion_finset (s := I)
      (f := fun i => {x : ι → ℝ | x i = 0})
      (fun i _ => isClosed_eq (continuous_apply i) continuous_const)
    convert h using 1
    ext x
    simp
  exact (domain_compact α ℓ hα I).inter_right hclosed

end DeletedFaces

namespace Polarization

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

def weights (ν : ι → V) (I : Finset ι) (i : ι) : V :=
  if i ∈ I then ν i else -ν i

def character (ν : ι → V) : V := ∑ i, ν i

lemma anticanonical_equation (ν : ι → V) (I : Finset ι) :
    PositiveWeights.equation (weights ν I) (DeletedFaces.vertex I) = -character ν := by
  unfold PositiveWeights.equation character
  simp only [LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I <;> simp [weights, DeletedFaces.vertex, hi]

lemma positive (ν : ι → V) (ℓ : V →ₗ[ℝ] ℝ)
    (hν : ∀ i, ℓ (ν i) ≠ 0) (i : ι) :
    0 < ℓ (weights ν (Finset.univ.filter (fun j => 0 < ℓ (ν j))) i) := by
  by_cases hi : 0 < ℓ (ν i)
  · simp [weights, hi]
  · simpa [weights, hi] using neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hi) (hν i))

lemma domain_nonempty_of_no_deletions (ν : ι → V) :
    (DeletedFaces.domain (PositiveWeights.equation (weights ν ∅)) ∅).Nonempty := by
  refine ⟨DeletedFaces.vertex ∅, ?_, rfl⟩
  intro i
  simp [DeletedFaces.vertex]

end Polarization

namespace PolynomialContinuation
variable {K : Type*} [Field K] [CharZero K]

lemma progression_injective (a : ℕ) (ha : 0 < a) :
    Function.Injective (fun n : ℕ => ((a * (n + 1) : ℕ) : K)) := by
  intro i j hij
  have h : a * (i + 1) = a * (j + 1) := Nat.cast_injective hij
  exact Nat.add_right_cancel (Nat.mul_left_cancel ha h)

theorem unique (a : ℕ) (ha : 0 < a) (p q : Polynomial K)
    (h : ∀ n : ℕ, 0 < n → p.eval ((a * n : ℕ) : K) = q.eval ((a * n : ℕ) : K)) :
    p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (progression_injective (K := K) a ha)).mono
  rintro _ ⟨n, rfl⟩
  exact h (n + 1) (Nat.succ_pos n)

theorem rational_of_integral_values (a : ℕ) (ha : 0 < a) (p : Polynomial K)
    (h : ∀ n : ℕ, 0 < n → ∃ z : ℤ, p.eval ((a * n : ℕ) : K) = (z : K)) :
    ∃ q : Polynomial ℚ, q.map (algebraMap ℚ K) = p := by
  classical
  choose z hz using fun n : ℕ => h (n + 1) (Nat.succ_pos n)
  let s := Finset.range (p.natDegree + 1)
  let v : ℕ → ℚ := fun n => (a * (n + 1) : ℕ)
  have hv : Function.Injective v := progression_injective a ha
  let q : Polynomial ℚ := Lagrange.interpolate s v (fun n => (z n : ℚ))
  refine ⟨q, ?_⟩
  have hdegree : p.degree < (s.card : WithBot ℕ) := by
    calc
      p.degree ≤ (p.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < ↑s.card := by
        simp only [s, Finset.card_range]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq s
    (progression_injective (K := K) a ha).injOn
  · exact Polynomial.degree_map_le.trans_lt
      (Lagrange.degree_interpolate_lt (fun n => (z n : ℚ)) hv.injOn)
  · exact hdegree
  · intro n hn
    have heval := Lagrange.eval_interpolate_at_node (fun n => (z n : ℚ)) hv.injOn hn
    change q.eval (v n) = (z n : ℚ) at heval
    calc
      (q.map (algebraMap ℚ K)).eval ((a * (n + 1) : ℕ) : K) =
          (algebraMap ℚ K) (q.eval (v n)) := by
        simpa [v] using Polynomial.eval_map_apply (p := q) (algebraMap ℚ K) (v n)
      _ = (z n : K) := by rw [heval]; simp
      _ = p.eval ((a * (n + 1) : ℕ) : K) := (hz n).symm

end PolynomialContinuation

end AnticanonicalIndex

end
end

end OAI
