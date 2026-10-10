import OAI.Probability.SwitchChain.PairFibers
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CellProjectionTransport

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

def restrictedSetoid (R : Setoid α) (C : α → Prop) : Setoid {x // C x} :=
  Setoid.comap Subtype.val R

def restrict (C : α → Prop) (f : EuclideanSpace ℝ α) :
    EuclideanSpace ℝ {x // C x} := WithLp.toLp 2 (fun x => f x.val)

include sectionFintypeα in
@[simp] theorem restrict_apply (C : α → Prop) (f : EuclideanSpace ℝ α)
    (x : {x // C x}) : restrict C f x = f x.val := by
  have retainedsectionFintypeα := sectionFintypeα
  exact rfl

def classEquiv (R : Setoid α) (C : α → Prop)
    (hC : ∀ x y, R.r x y → (C x ↔ C y)) (x : {x // C x}) :
    ↥(PairFibers.cell R x.val) ≃
      ↥(PairFibers.cell (restrictedSetoid R C) x) where
  toFun y := ⟨⟨y.val, (hC x.val y.val
    ((PairFibers.mem_cell R x.val y.val).mp y.property)).mp x.property⟩,
    (PairFibers.mem_cell _ _ _).mpr ((PairFibers.mem_cell R x.val y.val).mp y.property)⟩
  invFun y := ⟨y.val.val, (PairFibers.mem_cell R x.val y.val.val).mpr
    ((PairFibers.mem_cell (restrictedSetoid R C) x y.val).mp y.property)⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

theorem expectation_restrict (R : Setoid α) (C : α → Prop)
    (hC : ∀ x y, R.r x y → (C x ↔ C y)) (f : EuclideanSpace ℝ α) :
    restrict C (PairFibers.expectation R f) =
      PairFibers.expectation (restrictedSetoid R C) (restrict C f) := by
  ext x
  simp only [restrict_apply, PairFibers.expectation_apply]
  have hc : (PairFibers.cell R x.val).card =
      (PairFibers.cell (restrictedSetoid R C) x).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (classEquiv R C hC x)
  rw [hc]
  congr 1
  calc
    (∑ y ∈ PairFibers.cell R x.val, f y) =
        ∑ y : PairFibers.cell R x.val, f y.val :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ y : PairFibers.cell (restrictedSetoid R C) x, f y.val.val :=
      (classEquiv R C hC x).sum_comp (fun y => f y.val.val)
    _ = ∑ y ∈ PairFibers.cell (restrictedSetoid R C) x, f y.val :=
      Finset.sum_coe_sort (PairFibers.cell (restrictedSetoid R C) x) (fun y => f y.val)

def pull (e : α ≃ β) (f : EuclideanSpace ℝ β) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun x => f (e x))

include sectionFintypeα sectionFintypeβ in
@[simp] theorem pull_apply (e : α ≃ β) (f : EuclideanSpace ℝ β) (x : α) :
    pull e f x = f (e x) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  exact rfl

include sectionFintypeα sectionFintypeβ in
@[simp] theorem pull_symm (e : α ≃ β) (f : EuclideanSpace ℝ α) :
    pull e (pull e.symm f) = f := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  ext x
  simp [pull]

def equivClass (e : α ≃ β) (R : Setoid α) (S : Setoid β)
    (he : ∀ x y, R.r x y ↔ S.r (e x) (e y)) (x : α) :
    ↥(PairFibers.cell R x) ≃ ↥(PairFibers.cell S (e x)) where
  toFun y := ⟨e y.val, (PairFibers.mem_cell _ _ _).mpr
    ((he x y.val).mp ((PairFibers.mem_cell _ _ _).mp y.property))⟩
  invFun y := ⟨e.symm y.val, (PairFibers.mem_cell _ _ _).mpr
    ((he x (e.symm y.val)).mpr (by
      simpa only [e.apply_symm_apply] using
        ((PairFibers.mem_cell S (e x) y.val).mp y.property)))⟩
  left_inv y := by apply Subtype.ext; exact e.symm_apply_apply y.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

theorem expectation_pull (e : α ≃ β) (R : Setoid α) (S : Setoid β)
    (he : ∀ x y, R.r x y ↔ S.r (e x) (e y)) (f : EuclideanSpace ℝ β) :
    PairFibers.expectation R (pull e f) = pull e (PairFibers.expectation S f) := by
  ext x
  simp only [pull_apply, PairFibers.expectation_apply]
  have hc : (PairFibers.cell R x).card = (PairFibers.cell S (e x)).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (equivClass e R S he x)
  rw [hc]
  congr 1
  calc
    (∑ y ∈ PairFibers.cell R x, f (e y)) =
        ∑ y : PairFibers.cell R x, f (e y.val) :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ y : PairFibers.cell S (e x), f y.val :=
      (equivClass e R S he x).sum_comp (fun y => f y.val)
    _ = ∑ y ∈ PairFibers.cell S (e x), f y :=
      Finset.sum_coe_sort _ _

theorem inner_pull (e : α ≃ β) (f g : EuclideanSpace ℝ β) :
    ⟪pull e f, pull e g⟫ = ⟪f, g⟫ := by
  simp only [PiLp.inner_apply, pull_apply]
  exact e.sum_comp (fun x => inner ℝ (f x) (g x))

@[simp] theorem norm_sq_pull (e : α ≃ β) (f : EuclideanSpace ℝ β) :
    ‖pull e f‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_pull e f f

@[simp] theorem expectation_constant (R : Setoid α) (c : ℝ) :
    PairFibers.expectation R (WithLp.toLp 2 (fun _ : α => c)) =
      WithLp.toLp 2 (fun _ : α => c) := by
  apply (PairFibers.expectation_eq_self_iff R _).mpr
  intro x y hxy
  rfl

theorem sum_expectation (R : Setoid α) (f : EuclideanSpace ℝ α) :
    (∑ x, PairFibers.expectation R f x) = ∑ x, f x := by
  let one : EuclideanSpace ℝ α := WithLp.toLp 2 (fun _ => 1)
  have h := PairFibers.expectation_symmetric R f one
  change ⟪PairFibers.expectation R f, one⟫ =
    ⟪f, PairFibers.expectation R one⟫ at h
  rw [show PairFibers.expectation R one = one from expectation_constant R 1] at h
  simpa [PiLp.inner_apply, one] using h

theorem expectation_centered (R : Setoid α) (f : EuclideanSpace ℝ α)
    (hf : ∑ x, f x = 0) : ∑ x, PairFibers.expectation R f x = 0 := by
  rw [sum_expectation, hf]

theorem sum_pull (e : α ≃ β) (f : EuclideanSpace ℝ β) :
    (∑ x, pull e f x) = ∑ y, f y := e.sum_comp f

variable {n : ℕ} {d : Fin n → ℕ}

def graphSetoid (a : Finset (Fin n)) : Setoid (GraphState n d) where
  r G H := PairResampling.SameFiber a G.val H.val
  iseqv := ⟨fun G => PairResampling.SameFiber.refl a G.val,
    fun h => h.symm, fun h k => h.trans k⟩

theorem graph_expectation (a : Finset (Fin n)) :
    PairFibers.expectation (graphSetoid (d := d) a) = PairResampling.expectation n d a := by
  have h : PairFibers.constantSubspace (graphSetoid (d := d) a) =
      PairResampling.fiberSpace n d a := by
    ext f
    rfl
  unfold PairFibers.expectation PairResampling.expectation
  simp only [h]

theorem graph_expectation_restrict (a : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : ∀ G H, PairResampling.SameFiber a G.val H.val → (C G ↔ C H))
    (f : PairResampling.StateSpace n d) :
    restrict C (PairResampling.expectation n d a f) =
      PairFibers.expectation (restrictedSetoid (graphSetoid a) C) (restrict C f) := by
  rw [← graph_expectation]
  exact expectation_restrict (graphSetoid a) C hC f

theorem graph_expectation_equiv (a : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : ∀ G H, PairResampling.SameFiber a G.val H.val → (C G ↔ C H))
    (e : {G // C G} ≃ β) (S : Setoid β)
    (he : ∀ G H : {G // C G},
      PairResampling.SameFiber a G.val.val H.val.val ↔ S.r (e G) (e H))
    (f : PairResampling.StateSpace n d) :
    restrict C (PairResampling.expectation n d a f) =
      pull e (PairFibers.expectation S (pull e.symm (restrict C f))) := by
  rw [graph_expectation_restrict a C hC]
  have h := expectation_pull e (restrictedSetoid (graphSetoid a) C) S he
    (pull e.symm (restrict C f))
  simpa only [pull_symm] using h

end Problem315.CellProjectionTransport

end

end OAI
