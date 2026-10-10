import OAI.Probability.InvariantIsing.Cavity.CavityGroupedCoordinates
import Mathlib.Logic.Equiv.Fintype

namespace OAI

/-! Completion of the selected canonical axes to a fixed orthonormal
frame in each spectral group. Only finitely many cavity axes are added. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupIndexEquiv {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) :
    Fin (k a) ≃ {i : Fin N // (e.symm i).1=a} :=
  (Equiv.sigmaSubtype a).symm.trans
    (e.subtypeEquivOfSubtype' (p := fun w => w.1=a))

lemma cavityGroupIndexEquiv_apply {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) (j : Fin (k a)) :
    ((cavityGroupIndexEquiv k e a) j).val = e ⟨a,j⟩ := rfl

lemma cavity_group_selected_embedding {N m d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (s : Fin d → Fin N) (hs : Function.Injective s) (g : Fin d → Fin m)
    (hg : ∀ j, (e.symm (s j)).1=g j) (hk : ∀ a, d ≤ k a) :
    ∃ f : (a : Fin m) → Fin d ↪ Fin (k a), ∀ j, e ⟨g j,f (g j) j⟩=s j := by
  classical
  let b (a : Fin m) : Fin d ↪ Fin (k a) := ⟨fun j => j.castLE (hk a), Fin.castLE_injective _⟩
  let t (a : Fin m) : {j : Fin d // g j=a} → Fin (k a) := fun j =>
    (cavityGroupIndexEquiv k e a).symm ⟨s j.1, (hg j.1).trans j.2⟩
  have ht a : Function.Injective (t a) := by
    intro i j hij
    apply Subtype.ext
    apply hs
    have hh := congrArg (fun z => ((cavityGroupIndexEquiv k e a) z).val) hij
    simpa only [t, Equiv.apply_symm_apply] using hh
  have hb a : Function.Injective (fun j : {j : Fin d // g j=a} => b a j.1) :=
    (b a).injective.comp Subtype.val_injective
  choose P hP using fun a => Equiv.Perm.exists_extending_pair
    (fun j : {j : Fin d // g j=a} => b a j.1) (t a) (hb a) (ht a)
  refine ⟨fun a => (b a).trans (P a).toEmbedding, ?_⟩
  intro j
  have h := hP (g j) ⟨j,rfl⟩
  have he := congrArg (fun z => ((cavityGroupIndexEquiv k e (g j)) z).val) h
  simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    cavityGroupIndexEquiv_apply, t, Equiv.apply_symm_apply] using he

def cavitySelectedGroupFrame {m d : ℕ} (k : Fin m → ℕ)
    (f : (a : Fin m) → Fin d ↪ Fin (k a)) (a : Fin m) :
    Matrix (Fin (k a)) (Fin d) ℝ := fun i j => if i=f a j then 1 else 0

lemma cavitySelectedGroupFrame_gram {m d : ℕ} (k : Fin m → ℕ)
    (f : (a : Fin m) → Fin d ↪ Fin (k a)) (a : Fin m) :
    (cavitySelectedGroupFrame k f a).transpose*cavitySelectedGroupFrame k f a=1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cavitySelectedGroupFrame,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    (f a).injective.eq_iff, Matrix.one_apply]

lemma cavitySelectedGroupFrame_columns {N m d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (g : Fin d → Fin m) (f : (a : Fin m) → Fin d ↪ Fin (k a)) :
    cavityGroupedSelectedFrame k e (fun j => (g j,j)) (cavitySelectedGroupFrame k f) =
      fun i j => if i=e ⟨g j,f (g j) j⟩ then 1 else 0 := by
  ext i j
  simp only [cavityGroupedSelectedFrame, Matrix.mul_apply, cavityGroupFrame,
    cavitySelectedGroupFrame]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end InvariantIsing

end

end OAI
