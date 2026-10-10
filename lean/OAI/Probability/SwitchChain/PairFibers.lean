import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFibers

def SameFiber {n : ℕ} (a : Finset (Fin n))
    (G H : SimpleGraph (Fin n)) : Prop :=
  (∀ u v, u ∉ a → v ∉ a → (G.Adj u v ↔ H.Adj u v)) ∧
  (∀ u v, u ∈ a → v ∈ a → (G.Adj u v ↔ H.Adj u v)) ∧
  (∀ w, w ∉ a →
    (a.filter (fun u => G.Adj u w)).card = (a.filter (fun u => H.Adj u w)).card)

theorem SameFiber.refl {n : ℕ} (a : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    SameFiber a G G := by
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem SameFiber.symm {n : ℕ} {a : Finset (Fin n)} {G H : SimpleGraph (Fin n)}
    (h : SameFiber a G H) : SameFiber a H G := by
  exact ⟨fun u v hu hv => (h.1 u v hu hv).symm,
    fun u v hu hv => (h.2.1 u v hu hv).symm,
    fun w hw => (h.2.2 w hw).symm⟩

theorem SameFiber.trans {n : ℕ} {a : Finset (Fin n)} {G H K : SimpleGraph (Fin n)}
    (hGH : SameFiber a G H) (hHK : SameFiber a H K) : SameFiber a G K := by
  exact ⟨fun u v hu hv => (hGH.1 u v hu hv).trans (hHK.1 u v hu hv),
    fun u v hu hv => (hGH.2.1 u v hu hv).trans (hHK.2.1 u v hu hv),
    fun w hw => (hGH.2.2 w hw).trans (hHK.2.2 w hw)⟩

def stateSetoid {n : ℕ} (d : Fin n → ℕ) (a : Finset (Fin n)) :
    Setoid (GraphState n d) where
  r G H := SameFiber a G.val H.val
  iseqv := ⟨fun G => SameFiber.refl a G.val,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

section Partition

variable {α : Type*} [Fintype α]

def constantSubspace (R : Setoid α) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∀ x y, R.r x y → f x = f y}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x y hxy
    change f x + g x = f y + g y
    rw [hf x y hxy, hg x y hxy]
  smul_mem' := by
    intro c f hf x y hxy
    change c * f x = c * f y
    rw [hf x y hxy]

omit [Fintype α] in
@[simp] theorem mem_constantSubspace (R : Setoid α) (f : EuclideanSpace ℝ α) :
    f ∈ constantSubspace R ↔ ∀ x y, R.r x y → f x = f y := Iff.rfl

def expectation (R : Setoid α) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (constantSubspace R).starProjection

def deviation (R : Setoid α) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (constantSubspace R)ᗮ.starProjection

theorem expectation_mem (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f ∈ constantSubspace R :=
  (constantSubspace R).starProjection_apply_mem f

theorem expectation_constant (R : Setoid α) (f : EuclideanSpace ℝ α)
    {x y : α} (hxy : R.r x y) : expectation R f x = expectation R f y :=
  expectation_mem R f x y hxy

theorem expectation_eq_self_iff (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f = f ↔ ∀ x y, R.r x y → f x = f y :=
  Submodule.starProjection_eq_self_iff

theorem deviation_eq_sub (R : Setoid α) (f : EuclideanSpace ℝ α) :
    deviation R f = f - expectation R f := by
  simpa only [deviation, expectation, sub_apply,
    ContinuousLinearMap.id_apply] using
    congrArg (fun T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α => T f)
      (Submodule.starProjection_orthogonal (constantSubspace R))

theorem deviation_eq_zero_iff (R : Setoid α) (f : EuclideanSpace ℝ α) :
    deviation R f = 0 ↔ ∀ x y, R.r x y → f x = f y := by
  rw [deviation_eq_sub, sub_eq_zero, eq_comm]
  exact expectation_eq_self_iff R f

theorem expectation_idempotent (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R (expectation R f) = expectation R f := by
  exact (expectation_eq_self_iff R _).2 (expectation_mem R f)

theorem deviation_idempotent (R : Setoid α) (f : EuclideanSpace ℝ α) :
    deviation R (deviation R f) = deviation R f := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (constantSubspace R)ᗮ.starProjection_apply_mem f

theorem expectation_symmetric (R : Setoid α) :
    (expectation R).toLinearMap.IsSymmetric :=
  (constantSubspace R).starProjection_isSymmetric

theorem deviation_symmetric (R : Setoid α) :
    (deviation R).toLinearMap.IsSymmetric :=
  (constantSubspace R)ᗮ.starProjection_isSymmetric

theorem deviation_energy (R : Setoid α) (f : EuclideanSpace ℝ α) :
    inner ℝ f (deviation R f) = ‖deviation R f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := deviation_symmetric R f (deviation R f)
  simpa only [ContinuousLinearMap.coe_coe, deviation_idempotent] using h.symm

theorem deviation_energy_nonneg (R : Setoid α) (f : EuclideanSpace ℝ α) :
    0 ≤ inner ℝ f (deviation R f) := by
  rw [deviation_energy]
  exact sq_nonneg _

def cell (R : Setoid α) (x : α) : Finset α :=
  Finset.univ.filter (fun y => R.r x y)

@[simp] theorem mem_cell (R : Setoid α) (x y : α) :
    y ∈ cell R x ↔ R.r x y := by simp [cell]

theorem cell_nonempty (R : Setoid α) (x : α) : (cell R x).Nonempty :=
  ⟨x, (mem_cell R x x).2 (R.refl x)⟩

theorem cell_eq (R : Setoid α) {x y : α} (hxy : R.r x y) : cell R x = cell R y := by
  ext z
  simp only [mem_cell]
  exact ⟨fun h => R.trans (R.symm hxy) h, fun h => R.trans hxy h⟩

def cellIndicator (R : Setoid α) (x : α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun y => if R.r x y then 1 else 0)

omit [Fintype α] in
theorem cellIndicator_mem (R : Setoid α) (x : α) :
    cellIndicator R x ∈ constantSubspace R := by
  intro y z hyz
  change (if R.r x y then (1 : ℝ) else 0) = if R.r x z then 1 else 0
  have hiff : R.r x y ↔ R.r x z :=
    ⟨fun h => R.trans h hyz, fun h => R.trans h (R.symm hyz)⟩
  simp only [hiff]

theorem inner_cellIndicator (R : Setoid α) (x : α) (f : EuclideanSpace ℝ α) :
    inner ℝ f (cellIndicator R x) = ∑ y ∈ cell R x, f y := by
  simp [cellIndicator, PiLp.inner_apply, cell, Finset.sum_filter]

theorem expectation_apply (R : Setoid α) (f : EuclideanSpace ℝ α) (x : α) :
    expectation R f x = (∑ y ∈ cell R x, f y) / ((cell R x).card : ℝ) := by
  have hcNat : 0 < (cell R x).card := Finset.card_pos.mpr (cell_nonempty R x)
  have hc : (0 : ℝ) < (cell R x).card := by exact_mod_cast hcNat
  have horth := Submodule.starProjection_inner_eq_zero
    (K := constantSubspace R) f (cellIndicator R x) (cellIndicator_mem R x)
  change inner ℝ (f - expectation R f) (cellIndicator R x) = 0 at horth
  rw [inner_sub_left, inner_cellIndicator, inner_cellIndicator] at horth
  have hsum : (∑ y ∈ cell R x, expectation R f y) =
      (cell R x).card * expectation R f x := by
    calc
      (∑ y ∈ cell R x, expectation R f y) = ∑ _y ∈ cell R x, expectation R f x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (expectation_constant R f ((mem_cell R x y).1 hy)).symm
      _ = _ := by simp
  rw [hsum] at horth
  apply (eq_div_iff (ne_of_gt hc)).2
  nlinarith

end Partition

abbrev StateSpace (n : ℕ) (d : Fin n → ℕ) := EuclideanSpace ℝ (GraphState n d)

def pairExpectation {n : ℕ} (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := expectation (stateSetoid d a)

def pairDeviation {n : ℕ} (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := deviation (stateSetoid d a)

theorem pairDeviation_eq_zero_iff {n : ℕ} (d : Fin n → ℕ)
    (a : Finset (Fin n)) (f : StateSpace n d) :
    pairDeviation d a f = 0 ↔
      ∀ G H : GraphState n d, SameFiber a G.val H.val → f G = f H :=
  deviation_eq_zero_iff (stateSetoid d a) f

end Problem315.PairFibers

end

end OAI
