import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

open InnerProductSpace

namespace Invariant233.JointEigenspaceAlgebra

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_rankOne_of_same_eigenvalue
    {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {eig : ℝ} {x y : H}
    (hx : A x = (eig : ℂ) • x) (hy : A y = (eig : ℂ) • y) :
    Commute A (rankOne ℂ x y) := by
  apply ContinuousLinearMap.ext
  intro z
  change A (rankOne ℂ x y z) = rankOne ℂ x y (A z)
  rw [rankOne_apply, rankOne_apply, map_smul, hx]
  have hadj : A.adjoint = A := hA.star_eq
  rw [← A.adjoint_inner_left z y, hadj, hy, inner_smul_left]
  simp only [Complex.conj_ofReal, smul_smul]
  rw [mul_comm]

theorem exists_scalar_on_common_eigenspace
    (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : I → ℝ) (K : Submodule ℂ H)
    (hK : ∀ i, ∀ x ∈ K, A i x = (eig i : ℂ) • x)
    {B : H →L[ℂ] H}
    (hB : B ∈ Set.centralizer (Set.centralizer (Set.range A))) :
    ∃ c : ℂ, ∀ x ∈ K, B x = c • x := by
  classical
  by_cases hK0 : K = ⊥
  · refine ⟨0, ?_⟩
    intro x hx
    have hx0 : x = 0 := by simpa [hK0] using hx
    simp [hx0]
  · obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
    let d : ℂ := inner ℂ x x
    have hd : d ≠ 0 := by
      dsimp [d]
      exact inner_self_ne_zero.mpr hx0
    refine ⟨inner ℂ x (B x) / d, ?_⟩
    intro y hyK
    have hrank : rankOne ℂ y x ∈ Set.centralizer (Set.range A) := by
      intro C hC
      obtain ⟨i, rfl⟩ := hC
      exact (commute_rankOne_of_same_eigenvalue (hA i) (hK i y hyK) (hK i x hxK)).eq
    have hcomm := hB (rankOne ℂ y x) hrank
    have heq : d • B y = inner ℂ x (B x) • y := by
      have heval := congrArg (fun C : H →L[ℂ] H => C x) hcomm
      simpa only [mul_apply_eq_comp, rankOne_apply, map_smul] using heval.symm
    calc
      B y = d⁻¹ • (d • B y) := by simp [hd]
      _ = d⁻¹ • (inner ℂ x (B x) • y) := by rw [heq]
      _ = (inner ℂ x (B x) / d) • y := by
        rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem commute_starProjection_of_maps
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (B : H →L[ℂ] H)
    (hB : ∀ x ∈ K, B x ∈ K) (hBstar : ∀ x ∈ K, B.adjoint x ∈ K) :
    Commute K.starProjection B := by
  apply ContinuousLinearMap.ext
  intro z
  change K.starProjection (B z) = B (K.starProjection z)
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (hB _ (K.starProjection_apply_mem z))
  rw [← map_sub]
  apply (Submodule.mem_orthogonal K _).2
  intro x hx
  rw [← B.adjoint_inner_left]
  exact (Submodule.mem_orthogonal K _).1 (K.sub_starProjection_mem_orthogonal z)
    _ (hBstar x hx)

omit [CompleteSpace H] in

theorem common_eigenspace_mapsTo
    (A : I → H →L[ℂ] H) (eig : I → ℝ) (K : Submodule ℂ H)
    (hK : ∀ x, x ∈ K ↔ ∀ i, A i x = (eig i : ℂ) • x)
    {B : H →L[ℂ] H} (hB : B ∈ Set.centralizer (Set.range A)) :
    ∀ x ∈ K, B x ∈ K := by
  intro x hx
  apply (hK _).2
  intro i
  have hcomm := hB (A i) (Set.mem_range_self i)
  have heval := congrArg (fun C : H →L[ℂ] H => C x) hcomm
  change A i (B x) = B (A i x) at heval
  rw [heval, (hK x).1 hx i, map_smul]

theorem common_eigenspace_projection_mem_bicommutant
    (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : I → ℝ) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (hK : ∀ x, x ∈ K ↔ ∀ i, A i x = (eig i : ℂ) • x) :
    K.starProjection ∈ Set.centralizer (Set.centralizer (Set.range A)) := by
  intro B hB
  have hstar : star B ∈ Set.centralizer (Set.range A) := by
    apply Set.star_mem_centralizer' _ hB
    intro C hC
    obtain ⟨i, rfl⟩ := hC
    rw [(hA i).star_eq]
    exact Set.mem_range_self i
  exact (commute_starProjection_of_maps K B
    (common_eigenspace_mapsTo A eig K hK hB)
    (common_eigenspace_mapsTo A eig K hK hstar)).eq.symm

theorem eq_zero_or_eq_joint_projection_of_le
    (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : I → ℝ) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (hK : ∀ i, ∀ x ∈ K, A i x = (eig i : ℂ) • x)
    {q : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqmem : q ∈ Set.centralizer (Set.centralizer (Set.range A)))
    (hle : q ≤ K.starProjection) : q = 0 ∨ q = K.starProjection := by
  have hp : IsStarProjection K.starProjection := isStarProjection_starProjection
  by_cases hp0 : K.starProjection = 0
  · left
    exact le_antisymm (hp0 ▸ hle) hq.nonneg
  · obtain ⟨c, hc⟩ := exists_scalar_on_common_eigenspace A hA eig K hK hqmem
    have hqp : q * K.starProjection = q := (hq.le_iff_mul_eq_left hp).1 hle
    have hqeq : q = c • K.starProjection := by
      rw [← hqp]
      apply ContinuousLinearMap.ext
      intro x
      exact hc _ (K.starProjection_apply_mem x)
    have hscalar : (c * c) • K.starProjection = c • K.starProjection := by
      have hidem := hq.isIdempotentElem.eq
      rw [hqeq] at hidem
      simpa only [smul_mul_assoc, mul_smul_comm, smul_smul,
        K.isIdempotentElem_starProjection.eq] using hidem
    have hcid : IsIdempotentElem c := smul_left_injective ℂ hp0 hscalar
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hcid with hc0 | hc1
    · left
      simpa [hc0] using hqeq
    · right
      simpa [hc1] using hqeq

theorem exists_minimal_projection_below_of_joint_eigenspaces
    {J : Type*} (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : J → I → ℝ) (K : J → Submodule ℂ H)
    [∀ j, (K j).HasOrthogonalProjection]
    (hK : ∀ j x, x ∈ K j ↔ ∀ i, A i x = (eig j i : ℂ) • x)
    (hdense : (⨆ j, K j).topologicalClosure = ⊤)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hqmem : q ∈ Set.centralizer (Set.centralizer (Set.range A))) :
    ∃ j, (K j).starProjection ≠ 0 ∧
      (K j).starProjection ∈ Set.centralizer (Set.centralizer (Set.range A)) ∧
      (K j).starProjection ≤ q ∧
      ∀ r : H →L[ℂ] H, IsStarProjection r →
        r ∈ Set.centralizer (Set.centralizer (Set.range A)) →
        r ≤ (K j).starProjection → r = 0 ∨ r = (K j).starProjection := by
  classical
  have hex : ∃ j, ∃ x ∈ K j, q x ≠ 0 := by
    by_contra! hzero
    have hle : (⨆ j, K j) ≤ q.ker := by
      apply iSup_le
      intro j x hx
      exact hzero j x hx
    have hclosed : (⨆ j, K j).topologicalClosure ≤ q.ker :=
      (⨆ j, K j).topologicalClosure_minimal hle q.isClosed_ker
    rw [hdense] at hclosed
    apply hq0
    apply ContinuousLinearMap.ext
    intro x
    exact hclosed (Submodule.mem_top)
  obtain ⟨j, x, hxK, hqx⟩ := hex
  have hx0 : x ≠ 0 := by
    intro hx
    exact hqx (by simp [hx])
  obtain ⟨c, hc⟩ := exists_scalar_on_common_eigenspace A hA (eig j) (K j)
    (fun i y hy => (hK j y).1 hy i) hqmem
  have hcid : IsIdempotentElem c := by
    have hidem := congrArg (fun B : H →L[ℂ] H => B x) hq.isIdempotentElem.eq
    change q (q x) = q x at hidem
    rw [hc x hxK, map_smul, hc x hxK, smul_smul] at hidem
    exact smul_left_injective ℂ hx0 hidem
  have hc1 : c = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hcid with hc0 | hc1
    · exact False.elim (hqx (by simp [hc x hxK, hc0]))
    · exact hc1
  refine ⟨j, ?_, common_eigenspace_projection_mem_bicommutant A hA _ _ (hK j), ?_, ?_⟩
  · intro hpzero
    have hpx : (K j).starProjection x = x :=
      (K j).starProjection_eq_self_iff.2 hxK
    rw [hpzero] at hpx
    exact hx0 hpx.symm
  · apply (isStarProjection_starProjection.le_iff_mul_eq_right hq).2
    apply ContinuousLinearMap.ext
    intro y
    change q ((K j).starProjection y) = (K j).starProjection y
    simpa [hc1] using hc _ ((K j).starProjection_apply_mem y)
  · intro r hr hrmem hrle
    exact eq_zero_or_eq_joint_projection_of_le A hA (eig j) (K j)
      (fun i y hy => (hK j y).1 hy i) hr hrmem hrle

theorem atomic_bicommutant_of_dense_joint_eigenspaces
    {J : Type*} (A : I → H →L[ℂ] H) (hA : ∀ i, IsSelfAdjoint (A i))
    (eig : J → I → ℝ)
    (hdense : (⨆ j, ⨅ i, Module.End.eigenspace (A i).toLinearMap (eig j i : ℂ)).topologicalClosure = ⊤)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hqmem : q ∈ Set.centralizer (Set.centralizer (Set.range A))) :
    ∃ p : H →L[ℂ] H, IsStarProjection p ∧ p ≠ 0 ∧
      p ∈ Set.centralizer (Set.centralizer (Set.range A)) ∧ p ≤ q ∧
      ∀ r : H →L[ℂ] H, IsStarProjection r →
        r ∈ Set.centralizer (Set.centralizer (Set.range A)) →
        r ≤ p → r = 0 ∨ r = p := by
  let K : J → Submodule ℂ H := fun j =>
    ⨅ i, Module.End.eigenspace (A i).toLinearMap (eig j i : ℂ)
  have hclosed : ∀ j, IsClosed ((K j : Submodule ℂ H) : Set H) := by
    intro j
    simp only [K, Submodule.coe_iInf]
    exact isClosed_iInter fun i => (A i).isClosed_eigenspace (eig j i : ℂ)
  let : ∀ j, CompleteSpace (K j) := fun j => (hclosed j).completeSpace_coe
  have hK : ∀ j x, x ∈ K j ↔ ∀ i, A i x = (eig j i : ℂ) • x := by
    intro j x
    simp only [K, Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
      ContinuousLinearMap.coe_coe]
  obtain ⟨j, hp0, hpmem, hple, hpmin⟩ :=
    exists_minimal_projection_below_of_joint_eigenspaces A hA eig K hK hdense hq hq0 hqmem
  exact ⟨(K j).starProjection, isStarProjection_starProjection, hp0, hpmem, hple, hpmin⟩

end Invariant233.JointEigenspaceAlgebra

end OAI
