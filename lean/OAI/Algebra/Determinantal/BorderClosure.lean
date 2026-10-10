import OAI.Algebra.Determinantal.Model
import Mathlib.Data.Finsupp.Encodable

namespace OAI

namespace PermanentBorder

open Filter
open scoped Topology

/-- Fixed-size border representations are closed under sequential coefficientwise
limits. The approximating matrices remain arbitrary complex affine matrices of
exactly the original size; no uniform rate or coefficient bound is assumed. -/
theorem HasBorderDeterminant.coefficientwise_limit
    {σ : Type*} [Fintype σ] {n : ℕ} {P : ℕ → Poly σ} {p : Poly σ}
    (hP : ∀ j, HasBorderDeterminant n (P j))
    (hp : ∀ d : σ →₀ ℕ,
      Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    HasBorderDeterminant n p := by
  classical
  let Coeff := (σ →₀ ℕ) → ℂ
  let MatData := Matrix (Fin n) (Fin n) ℂ ×
    (σ → Matrix (Fin n) (Fin n) ℂ)
  let coefficients : MatData → Coeff := fun B d =>
    (affineMatrixPolynomial n B.1 B.2).coeff d
  let S : Set Coeff := Set.range coefficients
  have hmem : ∀ j, (fun d => (P j).coeff d) ∈ closure S := by
    intro j
    obtain ⟨_, A₀, A, hA⟩ := hP j
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun k => coefficients (A₀ k, A k), ?_, ?_⟩
    · intro k
      exact ⟨(A₀ k, A k), rfl⟩
    · exact tendsto_pi_nhds.mpr hA
  have hclosed : (fun d => p.coeff d) ∈ closure S :=
    isClosed_closure.mem_of_tendsto (tendsto_pi_nhds.mpr hp)
      (Filter.Eventually.of_forall hmem)
  obtain ⟨Q, hQ, hlim⟩ := mem_closure_iff_seq_limit.mp hclosed
  have hchoose : ∀ j, ∃ B : MatData, coefficients B = Q j := hQ
  choose B hB using hchoose
  refine ⟨(hP 0).1, (fun j => (B j).1), (fun j => (B j).2), ?_⟩
  intro d
  have he :
      (fun j => (affineMatrixPolynomial n (B j).1 (B j).2).coeff d) =
      (fun j => Q j d) := by
    funext j
    exact congrFun (hB j) d
  rw [he]
  exact tendsto_pi_nhds.mp hlim d

end PermanentBorder

end OAI
