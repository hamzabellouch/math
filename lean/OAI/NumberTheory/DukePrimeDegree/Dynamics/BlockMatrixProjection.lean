import OAI.NumberTheory.DukePrimeDegree.Dynamics.TransverseStabilizerLimit

namespace OAI

/-!
# The within-block matrix projection

The projection onto the within-block entries commutes with multiplication
by block-diagonal matrices on either side. Hence a scalar within-block
part stays scalar under every within-block conjugation, including the
unipotent shears used in the stopping-time argument.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def withinBlockPart {n : ℕ} (r : Setoid (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if r i j then M i j else 0

lemma withinBlockPart_mul_left {n : ℕ} (r : Setoid (Fin n))
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, ¬ r i j → A i j = 0) :
    withinBlockPart r (A * M) = A * withinBlockPart r M := by
  ext i j
  by_cases hij : r i j
  · simp only [withinBlockPart, hij, ite_true, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : r i k
    · have hkj : r k j := r.trans (r.symm hik) hij
      simp only [hkj, ite_true]
    · simp only [hA i k hik, zero_mul]
  · simp only [withinBlockPart, hij, ite_false, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hkj : r k j
    · have hik : ¬ r i k := fun hik => hij (r.trans hik hkj)
      simp only [hA i k hik, zero_mul]
    · simp only [hkj, ite_false, mul_zero]

lemma withinBlockPart_mul_right {n : ℕ} (r : Setoid (Fin n))
    (M B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, ¬ r i j → B i j = 0) :
    withinBlockPart r (M * B) = withinBlockPart r M * B := by
  ext i j
  by_cases hij : r i j
  · simp only [withinBlockPart, hij, ite_true, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : r k j
    · have hik : r i k := r.trans hij (r.symm hkj)
      simp only [hik, ite_true]
    · simp only [hB k j hkj, mul_zero]
  · simp only [withinBlockPart, hij, ite_false, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : r i k
    · have hkj : ¬ r k j := fun hkj => hij (r.trans hik hkj)
      simp only [hB k j hkj, mul_zero]
    · simp only [hik, ite_false, zero_mul]

lemma withinBlockPart_eq_scalar_iff {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (c : ℝ) :
    withinBlockPart r g.val = Matrix.diagonal (fun _ => c) ↔
      (∀ i, g.val i i = c) ∧ (∀ i j, i ≠ j → r i j → g.val i j = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) h
      simpa only [withinBlockPart, r.refl, ite_true, Matrix.diagonal_apply_eq] using hi
    · intro i j hij hr
      have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) h
      simpa only [withinBlockPart, hr, ite_true, Matrix.diagonal_apply_ne _ hij] using hi
  · rintro ⟨hd, hz⟩
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [withinBlockPart, r.refl, ite_true, Matrix.diagonal_apply_eq, hd]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hr : r i j
      · simp only [withinBlockPart, hr, ite_true, hz i j hij hr]
      · simp only [withinBlockPart, hr, ite_false]

/-- Conjugation by any block matrix preserves the scalar within-block
part. The cross-block part cannot produce a hidden within-block limit. -/
theorem withinBlockPart_conjugate_scalar {n : ℕ} (r : Setoid (Fin n))
    (g u : G n) (hu : u ∈ blockMatrixGroup r) (c : ℝ)
    (hg : withinBlockPart r g.val = Matrix.diagonal (fun _ => c)) :
    withinBlockPart r (u * g * u⁻¹).val = Matrix.diagonal (fun _ => c) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
    withinBlockPart_mul_left r u.val _ (cross_zero_of_mem_blockMatrixGroup r u hu),
    withinBlockPart_mul_right r g.val u⁻¹.val
      (cross_zero_of_mem_blockMatrixGroup r u⁻¹ ((blockMatrixGroup r).inv_mem hu)), hg]
  have hcomm : u.val * Matrix.diagonal (fun _ => c) =
      Matrix.diagonal (fun _ => c) * u.val := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

/-- The conjugating block matrices may diverge. The scalar block part
still tends to identity, and no within-block off-diagonal entry appears. -/
theorem block_conjugation_transverse_limit_entries {n : ℕ}
    (r : Setoid (Fin n)) (g u : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hu : ∀ k, u k ∈ blockMatrixGroup r)
    (hpart : ∀ᶠ k in atTop,
      withinBlockPart r (g k).val = Matrix.diagonal (fun _ => c k))
    (h : G n)
    (hlim : Tendsto (fun k => u k * g k * (u k)⁻¹) atTop (𝓝 h)) :
    (∀ i, h.val i i = 1) ∧ (∀ i j, i ≠ j → r i j → h.val i j = 0) := by
  have hparts : ∀ᶠ k in atTop,
      (∀ i, (u k * g k * (u k)⁻¹).val i i = (g k).val i i) ∧
      (∀ i j, i ≠ j → r i j → (u k * g k * (u k)⁻¹).val i j = 0) := by
    filter_upwards [hpart] with k hk
    have hs := (withinBlockPart_eq_scalar_iff r (u k * g k * (u k)⁻¹) (c k)).mp
      (withinBlockPart_conjugate_scalar r (g k) (u k) (hu k) (c k) hk)
    have hgk := (withinBlockPart_eq_scalar_iff r (g k) (c k)).mp hk
    exact ⟨fun i => (hs.1 i).trans (hgk.1 i).symm, hs.2⟩
  have hc (i j : Fin n) : Continuous (fun a : G n => a.val i j) := by fun_prop
  constructor
  · intro i
    have hh := (hc i i).continuousAt.tendsto.comp hlim
    have he := (hc i i).continuousAt.tendsto.comp hg
    have he' : Tendsto (fun k => (g k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using he
    have hh' : Tendsto (fun k => (u k * g k * (u k)⁻¹).val i i) atTop (𝓝 (1 : ℝ)) :=
      he'.congr' (hparts.mono fun k hk => (hk.1 i).symm)
    exact tendsto_nhds_unique hh hh'
  · intro i j hij hr
    have hh := (hc i j).continuousAt.tendsto.comp hlim
    have hz : ∀ᶠ k in atTop, (u k * g k * (u k)⁻¹).val i j = 0 :=
      hparts.mono fun k hk => hk.2 i j hij hr
    exact tendsto_nhds_unique hh (tendsto_const_nhds.congr' (hz.mono fun k hk => hk.symm))

/-- In particular the existing root-shearing compactness theorem can
never return a nonidentity element already in L after this normalization. -/
theorem block_conjugation_transverse_limit_not_mem {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n))
    (hmax : ∀ (i j : Fin n) (hij : i ≠ j) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hij c ∈ L → r i j)
    (g u : ℕ → G n) (c : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 1))
    (hu : ∀ k, u k ∈ blockMatrixGroup r)
    (hpart : ∀ᶠ k in atTop,
      withinBlockPart r (g k).val = Matrix.diagonal (fun _ => c k))
    (h : G n) (hne : h ≠ 1)
    (hlim : Tendsto (fun k => u k * g k * (u k)⁻¹) atTop (𝓝 h)) : h ∉ L := by
  obtain ⟨hd, hz⟩ := block_conjugation_transverse_limit_entries r g u c hg hu hpart h hlim
  exact transverse_not_mem_of_maximal_roots L hclosed hnormal r hmax h hne hd hz

end DukePrimeDegree

end

end OAI
