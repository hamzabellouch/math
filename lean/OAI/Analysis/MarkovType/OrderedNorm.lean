import OAI.Analysis.MarkovType.OrderedSequences

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

structure OrderedNorm where
  toSeminorm : Seminorm ℝ C00
  definite : ∀ x, toSeminorm x = 0 → x = 0
  spreading : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
    ∀ a : Fin m → ℝ, toSeminorm (C00.place ι a) = toSeminorm (C00.ofArray a)
  merge_le : ∀ (i : ℕ) (x : C00), toSeminorm (C00.mergeAt i x) ≤ toSeminorm x

namespace OrderedNorm

instance : CoeFun OrderedNorm (fun _ => C00 → ℝ) := ⟨fun N => N.toSeminorm⟩

@[simp] theorem coe_toSeminorm (N : OrderedNorm) (x : C00) :
    N.toSeminorm x = N x := rfl

@[simp] theorem map_zero (N : OrderedNorm) : N 0 = 0 :=
  N.toSeminorm.map_zero'

theorem nonneg (N : OrderedNorm) (x : C00) : 0 ≤ N x :=
  apply_nonneg N.toSeminorm x

@[simp] theorem eq_zero_iff (N : OrderedNorm) (x : C00) : N x = 0 ↔ x = 0 :=
  ⟨N.definite x, fun h => h ▸ N.map_zero⟩

theorem add_le (N : OrderedNorm) (x y : C00) : N (x + y) ≤ N x + N y :=
  N.toSeminorm.add_le' x y

@[simp] theorem neg (N : OrderedNorm) (x : C00) : N (-x) = N x :=
  N.toSeminorm.neg' x

@[simp] theorem smul (N : OrderedNorm) (r : ℝ) (x : C00) :
    N (r • x) = |r| * N x := by

  rw [map_smul_eq_mul, Real.norm_eq_abs]

end OrderedNorm

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

def CoordinatesRepresentable (N : OrderedNorm) : Prop :=
  ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
      N (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + ε) * N (C00.ofArray a)

end MarkovSuperreflexivity

end

end OAI
