import OAI.Analysis.MarkovType.OrderedNorm

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def NormedC00 (p : Seminorm ℝ C00) (_hp : ∀ x, p x = 0 → x = 0) := C00

namespace NormedC00

variable (p : Seminorm ℝ C00) (hp : ∀ x, p x = 0 → x = 0)

instance : AddCommGroup (NormedC00 p hp) := inferInstanceAs (AddCommGroup C00)

instance : Module ℝ (NormedC00 p hp) := inferInstanceAs (Module ℝ C00)

instance : Norm (NormedC00 p hp) := ⟨fun x => p x⟩

private theorem normCore : NormedSpace.Core ℝ (NormedC00 p hp) where
  norm_nonneg x := apply_nonneg p x
  norm_smul r x := p.smul' r x
  norm_triangle x y := p.add_le' x y
  norm_eq_zero_iff x := by
    change p x = 0 ↔ x = 0
    exact ⟨hp x, fun h => h ▸ p.map_zero'⟩

instance : NormedAddCommGroup (NormedC00 p hp) :=
  NormedAddCommGroup.ofCore (normCore p hp)

instance : NormedSpace ℝ (NormedC00 p hp) :=
  NormedSpace.ofCore (normCore p hp)

def coefficients : NormedC00 p hp ≃ₗ[ℝ] C00 := LinearEquiv.refl ℝ _

@[simp] theorem norm_eq (x : NormedC00 p hp) : ‖x‖ = p x := rfl

end NormedC00

abbrev OrderedSpace (N : OrderedNorm) := NormedC00 N.toSeminorm N.definite

end MarkovSuperreflexivity

end

end OAI
