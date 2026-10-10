import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Construction.DescendantSpacesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.OddListExtraction

namespace OAI


namespace PerfectCompleteness.DecoderContraction

open scoped TensorProduct Classical
open TensorCosetEvaluation
open PointwiseSpaces RecursiveSpaces

noncomputable section

abbrev F2 := ZMod 2

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

def chosenRow (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (hσ : σ.comp W.subtype ≠ 0) : W :=
  Classical.choose (exists_value_one (σ.comp W.subtype) hσ)

theorem chosenRow_value_one (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (hσ : σ.comp W.subtype ≠ 0) : σ (chosenRow W σ hσ).val = 1 :=
  Classical.choose_spec (exists_value_one (σ.comp W.subtype) hσ)

def contract (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) : Module.Dual F2 H :=
  if hσ : σ.comp W.subtype ≠ 0 then scalarRestriction Φ (chosenRow W σ hσ) else 0

theorem contract_eq (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hσ : σ.comp W.subtype ≠ 0) :
    contract W σ Φ = scalarRestriction Φ (chosenRow W σ hσ) := by
  simp only [contract, dite_eq_left hσ]

theorem contract_eq_zero (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hσ : σ.comp W.subtype = 0) :
    contract W σ Φ = 0 := by
  simp [contract, hσ]

def baseFrequency (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (z : Module.Dual F2 H) : Module.Dual F2 (W ⊗[F2] H) :=
  pureFrequency (σ.comp W.subtype) z

@[simp] theorem baseFrequency_tmul (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (z : Module.Dual F2 H) (w : W) (h : H) :
    baseFrequency W σ z (w ⊗ₜ[F2] h) = σ w.val * z h :=
  pureFrequency_tmul (σ.comp W.subtype) z w h

theorem contract_baseFrequency (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (z : Module.Dual F2 H) (hσ : σ.comp W.subtype ≠ 0) :
    contract W σ (baseFrequency W σ z) = z := by
  rw [contract_eq W σ _ hσ]
  change scalarRestriction (pureFrequency (σ.comp W.subtype) z) (chosenRow W σ hσ) = z
  rw [scalarRestriction_pure]
  change σ (chosenRow W σ hσ).val • z = z
  rw [chosenRow_value_one, one_smul]

def errorSpace (W : Submodule F2 K) (Q : Submodule F2 (Module.Dual F2 H)) :
    Submodule F2 (Module.Dual F2 (W ⊗[F2] H)) where
  carrier := {Ψ | ∀ w : W, scalarRestriction Ψ w ∈ Q}
  zero_mem' := by
    intro w
    rw [scalarRestriction_zero]
    exact Q.zero_mem
  add_mem' := by
    intro Φ Ψ hΦ hΨ w
    rw [scalarRestriction_add]
    exact Q.add_mem (hΦ w) (hΨ w)
  smul_mem' := by
    intro c Ψ hΨ w
    rw [scalarRestriction_smul]
    exact Q.smul_mem c (hΨ w)

@[simp] theorem mem_errorSpace (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) (Ψ : Module.Dual F2 (W ⊗[F2] H)) :
    Ψ ∈ errorSpace W Q ↔ ∀ w : W, scalarRestriction Ψ w ∈ Q := Iff.rfl

theorem equationSpace_le_errorSpace (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) : equationSpace (U := W) Q ≤ errorSpace W Q := by
  intro Ψ hΨ w
  exact scalarRestriction_mem Q Ψ hΨ w

theorem contract_sub_mem (W : Submodule F2 K) (Q : Submodule F2 (Module.Dual F2 H))
    (σ : Module.Dual F2 K) (Φ : Module.Dual F2 (W ⊗[F2] H)) (z : Module.Dual F2 H)
    (hσ : σ.comp W.subtype ≠ 0) (hΦ : Φ - baseFrequency W σ z ∈ errorSpace W Q) :
    contract W σ Φ - z ∈ Q := by
  have h := hΦ (chosenRow W σ hσ)
  rw [scalarRestriction_sub] at h
  rw [contract_eq W σ Φ hσ]
  have hbase : scalarRestriction (baseFrequency W σ z) (chosenRow W σ hσ) = z := by
    rw [← contract_eq W σ _ hσ]
    exact contract_baseFrequency W σ z hσ
  rw [hbase] at h
  exact h

theorem contract_sub_mem_of_equationSpace (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (z : Module.Dual F2 H)
    (hσ : σ.comp W.subtype ≠ 0)
    (hΦ : Φ - baseFrequency W σ z ∈ equationSpace (U := W) Q) :
    contract W σ Φ - z ∈ Q :=
  contract_sub_mem W Q σ Φ z hσ (equationSpace_le_errorSpace W Q hΦ)

theorem factored_mem_errorSpace {L : Type*} [AddCommGroup L] [Module F2 L]
    (W : Submodule F2 K) (Q : Submodule F2 (Module.Dual F2 H)) [FiniteDimensional F2 Q]
    (R : (W ⊗[F2] H) →ₗ[F2] L)
    (hR : ∀ w h, h ∈ Q.dualCoannihilator → R (w ⊗ₜ[F2] h) = 0)
    (ψ : Module.Dual F2 L) : ψ.comp R ∈ errorSpace W Q := by
  intro w
  exact scalarRestriction_factor_mem Q R hR ψ w


variable {branch : Nat → Nat} {n m : Nat}

def descendantSquareEmbedding (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n) :
    squareSpace (space F2 branch m (p.family A)) →ₗ[F2] space F2 branch n A where
  toFun f := ⟨pullback F2 (p.restriction A) f.val,
    DescendantSpaces.descendant_square_le_space p A hbranch hproper
      (Submodule.mem_map_of_mem f.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem descendantSquareEmbedding_apply (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (f : squareSpace (space F2 branch m (p.family A))) (x : Assignment A) :
    (descendantSquareEmbedding p A hbranch hproper f).val x = f.val (p.restriction A x) := rfl

theorem descendantSquareEmbedding_injective (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (hnonempty : ∀ s, Nonempty (A s)) :
    Function.Injective (descendantSquareEmbedding p A hbranch hproper) := by
  intro f g h
  apply Subtype.ext
  exact DescendantSpaces.descendant_pullback_injective p A hnonempty (congrArg Subtype.val h)

def descendantFunctional (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (z : Module.Dual F2 (space F2 branch n A)) :
    Module.Dual F2 (squareSpace (space F2 branch m (p.family A))) :=
  z.comp (descendantSquareEmbedding p A hbranch hproper)

def descendantForm (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (z : Module.Dual F2 (space F2 branch n A)) :
    space F2 branch m (p.family A) →ₗ[F2] space F2 branch m (p.family A) →ₗ[F2] F2 :=
  OddListExtraction.multiplicationForm _ (descendantFunctional p A hbranch hproper z)

theorem descendantFunctional_contract_eq (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 (space F2 branch n A)))
    (σ : Module.Dual F2 K) (Φ : Module.Dual F2 (W ⊗[F2] space F2 branch n A))
    (z : Module.Dual F2 (space F2 branch n A)) (hσ : σ.comp W.subtype ≠ 0)
    (hΦ : Φ - baseFrequency W σ z ∈ errorSpace W Q)
    (hvanish : ∀ q ∈ Q, q.comp (descendantSquareEmbedding p A hbranch hproper) = 0) :
    descendantFunctional p A hbranch hproper (contract W σ Φ) =
      descendantFunctional p A hbranch hproper z := by
  have h := hvanish (contract W σ Φ - z) (contract_sub_mem W Q σ Φ z hσ hΦ)
  apply LinearMap.ext
  intro f
  have he := LinearMap.congr_fun h f
  change contract W σ Φ (descendantSquareEmbedding p A hbranch hproper f) -
      z (descendantSquareEmbedding p A hbranch hproper f) = 0 at he
  exact sub_eq_zero.mp he


end
end PerfectCompleteness.DecoderContraction

end OAI
