import Mathlib
import OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisRigidity
open Module

variable {K : Type*} [Field K] (m : ℕ) (y : K) (hy : y ≠ 0)

def frameEquiv : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) where
  toFun c := Fin.cases (y * c 0) (fun i => c i.succ + c 0)
  invFun t := Fin.cases (t 0 / y) (fun i => t i.succ - t 0 / y)
  left_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hy]
    · simp [hy]
  right_inv t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change y * (t 0 / y) = t 0
      field_simp
    · simp
  map_add' c d := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · simp only [Pi.add_apply, Fin.cases_succ]
      ring
  map_smul' a c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, Fin.cases_zero, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [mul_add]

def frameBasis : Basis (Fin (m + 1)) K (Fin (m + 1) → K) :=
  (Pi.basisFun K _).map (frameEquiv m y hy)

@[simp] lemma frameBasis_repr_zero (t : Fin (m + 1) → K) :
    (frameBasis m y hy).repr t 0 = t 0 / y := by
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) 0 = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_repr_succ (t : Fin (m + 1) → K) (i : Fin m) :
    (frameBasis m y hy).repr t i.succ = t i.succ - t 0 / y := by
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) i.succ = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_succ (i : Fin m) :
    frameBasis m y hy i.succ = Pi.basisFun K _ i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply]
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] lemma frameBasis_zero_zero : frameBasis m y hy 0 0 = y := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] lemma frameBasis_zero_succ (i : Fin m) : frameBasis m y hy 0 i.succ = 1 := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

variable {V : Type*} [AddCommGroup V] [Module K V]

lemma mandatory_logarithmic_differential (q : (Fin (m + 1) → K) →ₗ[K] V)
    (hq : Submodule.span K (Set.range (fun j => q (frameBasis m y hy j))) = ⊤)
    (i : Fin m)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) A → i.succ ∈ A)
    (t : Fin (m + 1) → K) (ht : q t = 0) : t i.succ = t 0 / y := by
  have h := mandatory_coordinate_eq_zero (frameBasis m y hy) q hq i.succ hi t ht
  rw [frameBasis_repr_succ] at h
  exact sub_eq_zero.mp h

lemma span_mapped_basis_eq_top {ι U : Type*} [Fintype ι]
    [AddCommGroup U] [Module K U] (b : Basis ι K U) (q : U →ₗ[K] V)
    (hq : Function.Surjective q) :
    Submodule.span K (Set.range (fun j => q (b j))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := hq x
  rw [← b.sum_repr t, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem normal_basis_differential_dichotomy
    (q : (Fin (m + 1) → K) →ₗ[K] V) (hq : Function.Surjective q) (hq0 : q ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    (∀ t, q t = 0 → t 0 = 0) ∨
      ∃ i : Fin m, ∀ t, q t = 0 → t i.succ = t 0 / y := by
  classical
  let b := Pi.basisFun K (Fin (m + 1))
  let S := Finset.univ.filter (fun i : Fin (m + 1) => i ≠ 0 ∧ q (b i) ≠ 0)
  by_cases hS : S.Nonempty
  · let i := S.max' hS
    have hiS : i ∈ S := Finset.max'_mem _ _
    have hi := (Finset.mem_filter.mp hiS).2
    have hlarge : ∀ j, i < j → q (b j) = 0 := by
      intro j hj
      by_contra hjq
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        exact (not_lt_of_ge (Fin.zero_le _)) hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0, hjq⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ hjS)) hj
    have hvu : ∀ j : Fin (m + 1), j ≠ 0 → q (frameBasis m y hy j) = q (b j) := by
      intro j
      refine Fin.cases ?_ (fun k _ => ?_) j
      · intro hz
        exact (hz rfl).elim
      · rw [frameBasis_succ]
    have hmand : ∀ B, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B → i ∈ B :=
      largest_nontangent_mandatory (fun j => q (b j))
        (fun j => q (frameBasis m y hy j)) (span_mapped_basis_eq_top b q hq)
        hvu hexclude i hi.1 hi.2 hlarge
    rcases Fin.eq_zero_or_eq_succ i with hz | ⟨j, hj⟩
    · exact (hi.1 hz).elim
    · right
      refine ⟨j, ?_⟩
      intro t ht
      apply mandatory_logarithmic_differential m y hy q
        (span_mapped_basis_eq_top (frameBasis m y hy) q hq) j ?_ t ht
      intro B hB
      rw [← hj]
      exact hmand B hB
  · have hpos : ∀ j : Fin m, q (b j.succ) = 0 := by
      intro j
      by_contra hj
      exact hS ⟨j.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_ne_zero _, hj⟩⟩
    have he0 : q (b 0) ≠ 0 := by
      intro he
      apply hq0
      apply b.ext
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact he
      · exact hpos k
    have hqform (t : Fin (m + 1) → K) : q t = t 0 • q (b 0) := by
      calc
        q t = q (∑ j, b.repr t j • b j) := congrArg q (b.sum_repr t).symm
        _ = ∑ j, b.repr t j • q (b j) := by simp only [map_sum, map_smul]
        _ = t 0 • q (b 0) := by
          rw [Fin.sum_univ_succ]
          simp only [hpos, smul_zero, Finset.sum_const_zero, add_zero]
          simp only [b, Pi.basisFun_repr]
    left
    intro t ht
    rw [hqform] at ht
    exact (smul_eq_zero.mp ht).resolve_right he0

end PiExponent.NormalBasisRigidity

end

end OAI
