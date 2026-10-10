import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

namespace CriticalSK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def basisSpan {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Finset (Fin n)) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i : s => b i))

omit [FiniteDimensional ℝ E] in
lemma basisSpan_finrank {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Finset (Fin n)) :
    finrank ℝ (basisSpan b s) = s.card := by
  have hli : LinearIndependent ℝ (fun i : s => b i) :=
    b.orthonormal.linearIndependent.comp (fun i : s => (i : Fin n)) Subtype.val_injective
  rw [basisSpan, finrank_span_eq_card hli, Fintype.card_coe]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_repr_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s)
    (i : Fin n) (hi : i ∉ s) : b.repr x i = 0 := by
  have hmem : x ∈ Submodule.span ℝ (b.toBasis '' (s : Set (Fin n))) := by
    convert hx using 1
    congr 1
    ext y
    simp [Set.mem_range, Set.mem_image]
  have hs := b.toBasis.repr_support_subset_of_mem_span _ hmem
  have hz : b.toBasis.repr x i = 0 := by
    by_contra hz
    exact hi (hs (Finsupp.mem_support_iff.mpr hz))
  simpa only [b.coe_toBasis_repr_apply] using hz

lemma basisSpan_intersection_unit {n : ℕ}
    (b c : OrthonormalBasis (Fin n) ℝ E) (s t : Finset (Fin n))
    (hcard : n < s.card + t.card) :
    ∃ x : E, ‖x‖ = 1 ∧ x ∈ basisSpan b s ∧ x ∈ basisSpan c t := by
  have hn : finrank ℝ E = n := by
    rw [finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hnot : ¬ Disjoint (basisSpan b s) (basisSpan c t) := by
    intro hd
    have h := Submodule.finrank_add_finrank_le_of_disjoint hd
    rw [basisSpan_finrank, basisSpan_finrank, hn] at h
    omega
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxs, hxt, hx⟩ := hnot
  refine ⟨‖x‖⁻¹ • x, ?_, (basisSpan b s).smul_mem _ hxs, (basisSpan c t).smul_mem _ hxt⟩
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

def basisQuadratic {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) (x : E) : ℝ :=
  ∑ i, a i * (b.repr x i) ^ 2

omit [FiniteDimensional ℝ E] in
lemma basis_sum_squares {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    ∑ i, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  simp only [b.repr_apply_apply]
  exact b.sum_sq_inner_right x

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, a i ≤ r) : basisQuadratic b a x ≤ r := by
  calc
    _ ≤ ∑ i, r * (b.repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]
    _ = r := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_ge {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, r ≤ a i) : r ≤ basisQuadratic b a x := by
  calc
    _ = ∑ i, r * (b.repr x i) ^ 2 := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]

lemma basis_minmax_upper {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E)
    (α β : Fin n → ℝ) (hα : Antitone α) (hβ : Antitone β)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f S)
    (hβS : ∀ i, β i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → basisQuadratic b β x ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 → basisQuadratic a α x ≤ f (basisQuadratic b β x))
    (i : Fin n) : α i ≤ f (β i) := by
  have hcard : n < (Finset.Iic i).card + (Finset.Ici i).card := by
    simp only [Fin.card_Iic, Fin.card_Ici]
    omega
  obtain ⟨x, hx, hxa, hxb⟩ := basisSpan_intersection_unit a b
    (Finset.Iic i) (Finset.Ici i) hcard
  have hlow : α i ≤ basisQuadratic a α x :=
    basisQuadratic_ge a α (Finset.Iic i) hxa hx
      (fun j hj => hα (Finset.mem_Iic.mp hj))
  have hupp : basisQuadratic b β x ≤ β i :=
    basisQuadratic_le b β (Finset.Ici i) hxb hx
      (fun j hj => hβ (Finset.mem_Ici.mp hj))
  exact hlow.trans ((hform x hx).trans (hf (hqS x hx) (hβS i) hupp))

lemma basis_minmax_lower {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E)
    (α β : Fin n → ℝ) (hα : Antitone α) (hβ : Antitone β)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f S)
    (hβS : ∀ i, β i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → basisQuadratic b β x ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 → f (basisQuadratic b β x) ≤ basisQuadratic a α x)
    (i : Fin n) : f (β i) ≤ α i := by
  have hcard : n < (Finset.Ici i).card + (Finset.Iic i).card := by
    simp only [Fin.card_Iic, Fin.card_Ici]
    omega
  obtain ⟨x, hx, hxa, hxb⟩ := basisSpan_intersection_unit a b
    (Finset.Ici i) (Finset.Iic i) hcard
  have hupp : basisQuadratic a α x ≤ α i :=
    basisQuadratic_le a α (Finset.Ici i) hxa hx
      (fun j hj => hα (Finset.mem_Ici.mp hj))
  have hlow : β i ≤ basisQuadratic b β x :=
    basisQuadratic_ge b β (Finset.Iic i) hxb hx
      (fun j hj => hβ (Finset.mem_Iic.mp hj))
  exact (hf (hβS i) (hqS x hx) hlow).trans ((hform x hx).trans hupp)

lemma eigenbasisQuadratic_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    basisQuadratic (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x = inner ℝ x (T x) := by
  rw [basisQuadratic, ← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm ((hT.eigenvectorBasis hn) i) x, ← (hT.eigenvectorBasis hn).repr_apply_apply,
    ← (hT.eigenvectorBasis hn).repr_apply_apply, hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

lemma eigenvalue_form_comparison {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) {S : Set ℝ} {Φ : ℝ → ℝ}
    (hplus : MonotoneOn (fun e => e + Φ e) S)
    (hminus : MonotoneOn (fun e => e - Φ e) S)
    (hBS : ∀ i, hB.eigenvalues hn i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → inner ℝ x (B x) ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 →
      |inner ℝ x (A x) - inner ℝ x (B x)| ≤ Φ (inner ℝ x (B x)))
    (i : Fin n) : |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ Φ (hB.eigenvalues hn i) := by
  have hu := basis_minmax_upper (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn) (hA.eigenvalues_antitone hn)
    (hB.eigenvalues_antitone hn) hplus hBS
    (fun x hx => by simpa only [eigenbasisQuadratic_eq] using hqS x hx)
    (fun x hx => by
      simp only [eigenbasisQuadratic_eq]
      have h := (abs_le.mp (hform x hx)).2
      linarith) i
  have hl := basis_minmax_lower (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn) (hA.eigenvalues_antitone hn)
    (hB.eigenvalues_antitone hn) hminus hBS
    (fun x hx => by simpa only [eigenbasisQuadratic_eq] using hqS x hx)
    (fun x hx => by
      simp only [eigenbasisQuadratic_eq]
      have h := (abs_le.mp (hform x hx)).1
      linarith) i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CriticalSK

end

end OAI
