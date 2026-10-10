import OAI.Analysis.HyperbolicCones.SplitBasic

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

structure PencilSpectralSplit {m : ℕ} (A : Sym m) where
  a : ℕ
  c : ℕ
  a_pos : 0 < a
  c_pos : 0 < c
  index : (Fin a ⊕ Fin c) ≃ Fin m
  positive : ∀ i, 0 < (sym_isHermitian A).eigenvalues (index (Sum.inl i))
  nonpositive : ∀ i, ¬ 0 < (sym_isHermitian A).eigenvalues (index (Sum.inr i))

theorem pencilSpectralSplit_exists {m : ℕ} (A : Sym m)
    (hA : (A : Mat m ℝ).PosSemidef) (hne : (A : Mat m ℝ) ≠ 0)
    (hnpd : ¬ (A : Mat m ℝ).PosDef) : Nonempty (PencilSpectralSplit A) := by
  classical
  let p : Fin m → Prop := fun i => 0 < (sym_isHermitian A).eigenvalues i
  have hp : ∃ i, p i := by
    by_contra! hh
    apply hne
    apply (sym_isHermitian A).eigenvalues_eq_zero_iff.mp
    funext i
    exact le_antisymm (le_of_not_gt (hh i)) (hA.eigenvalues_nonneg i)
  have hn : ∃ i, ¬ p i := by
    by_contra! hh
    exact hnpd ((sym_isHermitian A).posDef_iff_eigenvalues_pos.mpr hh)
  let J := {i : Fin m // p i}
  let Q := {i : Fin m // ¬ p i}
  let a := Fintype.card J
  let c := Fintype.card Q
  let f : Fin a ≃ J := (Fintype.equivFin J).symm
  let g : Fin c ≃ Q := (Fintype.equivFin Q).symm
  let e : (Fin a ⊕ Fin c) ≃ Fin m := (Equiv.sumCongr f g).trans (Equiv.sumCompl p)
  have ha : 0 < a := Fintype.card_pos_iff.mpr ⟨⟨hp.choose, hp.choose_spec⟩⟩
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨⟨hn.choose, hn.choose_spec⟩⟩
  exact ⟨⟨a, c, ha, hc, e, fun i => (f i).property, fun i => (g i).property⟩⟩

def rectangularPencil {V : Type u} [AddCommGroup V] [Module ℝ V]
    {m a c : ℕ} (L : V →ₗ[ℝ] Sym m) (f : Fin a → Fin m) (g : Fin c → Fin m) :
    V →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ where
  toFun x := (L x : Mat m ℝ).submatrix f g
  map_add' x y := by ext i j; simp
  map_smul' s x := by ext i j; simp

theorem conjugatePencil_posDef {V : Type u} [AddCommGroup V] [Module ℝ V]
    {m : ℕ} (L : V →ₗ[ℝ] Sym m) (U : Mat m ℝ) (hU : IsUnit U) (x : V)
    (hx : (L x : Mat m ℝ).PosDef) : (conjugatePencil L U x : Mat m ℝ).PosDef := by
  change (Uᴴ * (L x : Mat m ℝ) * U).PosDef
  exact hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hU)

end Paper256

end

end OAI
