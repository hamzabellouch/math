import OAI.Analysis.KadisonKastler.MatrixBlockSwap
import OAI.Analysis.KadisonKastler.ProductStateCentralizer
import OAI.Analysis.KadisonKastler.PublishedKaplansky

namespace OAI

/-! # Product moments put finite block swaps in the state centralizer

The finite calculation needs only the three-block product formula and
equal moments on the two blocks being exchanged. Strong density then
extends the resulting identities from local matrix algebras to their
generated von Neumann algebra.
-/

namespace KadisonKastler

open Generator Filter
open scoped BigOperators Topology

noncomputable section

section Finite

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring A] [StarRing A] [_root_.Algebra ℂ A] [StarModule ℂ A]

omit [_root_.Algebra ℂ A] [StarModule ℂ A] in
private theorem unitary_conjugation_mul (u : unitary A) (x y : A) :
    (u : A) * (x * y) * star (u : A) =
      ((u : A) * x * star (u : A)) * ((u : A) * y * star (u : A)) := by
  symm
  calc
    _ = (u : A) * x * (star (u : A) * u) * y * star (u : A) := by noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem u.property]; simp only [mul_one, mul_assoc]

/-- Equality on the matrix-unit coefficients implies equality on the
whole finite matrix algebra. -/
theorem matrix_functional_invariant_of_entries
    (E : MatrixUnitSystem ι A) (φ : A →ₗ[ℂ] ℂ) (u : unitary A)
    (hφ : ∀ i j, φ ((u : A) * E.entry i j * star (u : A)) = φ (E.entry i j))
    (x : A) (hx : x ∈ E.algebra) :
    φ ((u : A) * x * star (u : A)) = φ x := by
  obtain ⟨c, rfl⟩ := (E.mem_algebra x).mp hx
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, hφ]

/-- Three-block product moments are invariant under swapping the two
equal-state blocks, with an arbitrary finite complement left in place. -/
theorem finiteMatrixBlockSwap_product_invariant
    (E : MatrixUnitSystem (ι × ι) A) (C : MatrixUnitSystem κ A)
    (hEC : ∀ i j k l, Commute (E.entry i j) (C.entry k l))
    (φ : A →ₗ[ℂ] ℂ) (α : ι → ι → ℂ) (β : κ → κ → ℂ)
    (hφ : ∀ i j k l r s,
      φ (E.entry (i, j) (k, l) * C.entry r s) = α i k * α j l * β r s)
    (x : A) (hx : x ∈ (E.product C hEC).algebra) :
    φ ((finiteMatrixBlockSwap E : A) * x * star (finiteMatrixBlockSwap E : A)) = φ x := by
  apply matrix_functional_invariant_of_entries (E.product C hEC) φ
    (finiteMatrixBlockSwap E) _ x hx
  rintro ⟨⟨i, j⟩, r⟩ ⟨⟨k, l⟩, s⟩
  have hc : Commute (finiteMatrixBlockSwap E : A) (C.entry r s) :=
    (E.commute_algebra_iff (C.entry r s)).mpr (fun a b => hEC a b r s)
      _ (finiteMatrixBlockSwap_mem E)
  have hfix : (finiteMatrixBlockSwap E : A) * C.entry r s *
      star (finiteMatrixBlockSwap E : A) = C.entry r s :=
    (commute_unitary_iff_star_right_conjugate (finiteMatrixBlockSwap E).property).mp hc
  change φ ((finiteMatrixBlockSwap E : A) *
      (E.entry (i, j) (k, l) * C.entry r s) * star (finiteMatrixBlockSwap E : A)) = _
  rw [unitary_conjugation_mul, finiteMatrixBlockSwap_conjugate_entry, hfix]
  change φ (E.entry (j, i) (l, k) * C.entry r s) =
    φ (E.entry (i, j) (k, l) * C.entry r s)
  rw [hφ, hφ]
  ring

/-- Product moments imply centralization on the finite joint algebra. -/
theorem finiteMatrixBlockSwap_product_centralizes
    (E : MatrixUnitSystem (ι × ι) A) (C : MatrixUnitSystem κ A)
    (hEC : ∀ i j k l, Commute (E.entry i j) (C.entry k l))
    (φ : A →ₗ[ℂ] ℂ) (α : ι → ι → ℂ) (β : κ → κ → ℂ)
    (hφ : ∀ i j k l r s,
      φ (E.entry (i, j) (k, l) * C.entry r s) = α i k * α j l * β r s)
    (x : A) (hx : x ∈ (E.product C hEC).algebra) :
    φ ((finiteMatrixBlockSwap E : A) * x) = φ (x * finiteMatrixBlockSwap E) := by
  have hu : (finiteMatrixBlockSwap E : A) ∈ (E.product C hEC).algebra :=
    (E.algebra_le_product_left C hEC) (finiteMatrixBlockSwap_mem E)
  have hi := finiteMatrixBlockSwap_product_invariant E C hEC φ α β hφ
    (x * finiteMatrixBlockSwap E) ((E.product C hEC).algebra.mul_mem hx hu)
  simpa only [mul_assoc, Unitary.mul_star_self_of_mem (finiteMatrixBlockSwap E).property,
    mul_one] using hi

omit [StarModule ℂ A] in
/-- In the product of two commuting copies, the block swap carries each
left matrix unit to the corresponding right matrix unit. -/
theorem finiteMatrixBlockSwap_conjugate_left_entry
    (E F : MatrixUnitSystem ι A)
    (hEF : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (i j : ι) :
    (finiteMatrixBlockSwap (E.product F hEF) : A) * E.entry i j *
      star (finiteMatrixBlockSwap (E.product F hEF) : A) = F.entry i j := by
  rw [← E.product_sum_left F hEF i j]
  simp only [Finset.mul_sum, Finset.sum_mul, finiteMatrixBlockSwap_conjugate_entry]
  exact E.product_sum_right F hEF i j

theorem finiteMatrixBlockSwap_conjugate_left_hom
    (E F : MatrixUnitSystem ι A)
    (hEF : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (c : Matrix ι ι ℂ) :
    (finiteMatrixBlockSwap (E.product F hEF) : A) * E.hom c *
      star (finiteMatrixBlockSwap (E.product F hEF) : A) = F.hom c := by
  rw [E.hom_apply, F.hom_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    finiteMatrixBlockSwap_conjugate_left_entry]

/-- Independence of the remote block on matrix units implies the desired
factorization for every observable in the original finite block. -/
theorem finiteMatrixBlockSwap_independent
    (E F : MatrixUnitSystem ι A)
    (hEF : ∀ i j k l, Commute (E.entry i j) (F.entry k l))
    (φ : A →ₗ[ℂ] ℂ) (b : A)
    (hfar : ∀ i j, φ (F.entry i j * b) = φ (E.entry i j) * φ b)
    (a : A) (ha : a ∈ E.algebra) :
    φ (((finiteMatrixBlockSwap (E.product F hEF) : A) * a *
      star (finiteMatrixBlockSwap (E.product F hEF) : A)) * b) = φ a * φ b := by
  obtain ⟨c, rfl⟩ := (E.mem_algebra a).mp ha
  change φ (((finiteMatrixBlockSwap (E.product F hEF) : A) * E.hom c *
      star (finiteMatrixBlockSwap (E.product F hEF) : A)) * b) = φ (E.hom c) * φ b
  rw [finiteMatrixBlockSwap_conjugate_left_hom]
  simp only [F.hom_apply, E.hom_apply, Finset.sum_mul, smul_mul_assoc,
    map_sum, map_smul, hfar, smul_eq_mul, mul_assoc]

end Finite

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The linear vector functional used by the finite product calculation. -/
def productVectorLinear (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun := productVectorState Ω
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

/-- Centralization on a dense star algebra extends to its actual
bicommutant. This uses the proved unbounded strong-density theorem. -/
theorem productStateCentralizes_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (u : H →L[ℂ] H)
    (hS : ∀ x ∈ S, productVectorState Ω (u * x) = productVectorState Ω (x * u)) :
    ProductStateCentralizes (generatedVonNeumannAlgebra S) Ω u := by
  classical
  intro x hx
  have hx' : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    change x ∈ (generatedVonNeumannAlgebra S : Set (H →L[ℂ] H)) at hx
    rwa [generatedVonNeumannAlgebra_coe] at hx
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net S x hx'
  have hl : Tendsto (fun d => productVectorState Ω (u * (a d : H →L[ℂ] H))) atTop
      (𝓝 (productVectorState Ω (u * x))) := by
    change Tendsto (fun d => inner ℂ Ω (u ((a d : H →L[ℂ] H) Ω))) atTop
      (𝓝 (inner ℂ Ω (u (x Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (u.continuous.continuousAt.tendsto.comp (ha Ω))
  have hr : Tendsto (fun d => productVectorState Ω ((a d : H →L[ℂ] H) * u)) atTop
      (𝓝 (productVectorState Ω (x * u))) := by
    change Tendsto (fun d => inner ℂ Ω ((a d : H →L[ℂ] H) (u Ω))) atTop
      (𝓝 (inner ℂ Ω (x (u Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha (u Ω))
  exact tendsto_nhds_unique (hl.congr (fun d => hS _ (a d).property)) hr

/-- Stage-by-stage finite centralization supplies centralization on the
von Neumann algebra generated by the increasing local algebras. -/
theorem productStateCentralizes_of_local
    (S : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hmono : Monotone S)
    (Ω : H) (u : H →L[ℂ] H)
    (hS : ∀ n x, x ∈ S n → productVectorState Ω (u * x) = productVectorState Ω (x * u)) :
    ProductStateCentralizes (generatedVonNeumannAlgebra (⨆ n, S n)) Ω u := by
  apply productStateCentralizes_generated
  intro x hx
  have hx' : x ∈ ((⨆ n, S n : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := hx
  rw [StarSubalgebra.coe_iSup_of_directed hmono.directed_le] at hx'
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx'
  exact hS n x hn

end Vector

end

end KadisonKastler

end OAI
