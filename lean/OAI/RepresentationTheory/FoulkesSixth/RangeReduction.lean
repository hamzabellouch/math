import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.IndependentChart
import OAI.RepresentationTheory.FoulkesSixth.BlockInjection

namespace OAI

noncomputable section

namespace Foulkes
universe u

open scoped TensorProduct

def SixthPowerComparison : Prop :=
  ∀ (b : ℕ), 6 ≤ b →
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    ∃ (i : Sym 6 (Sym b V) →ₗ[ℂ] Sym b (Sym 6 V)),
      Function.Injective i ∧
        ∀ (g : V ≃ₗ[ℂ] V) (x : Sym 6 (Sym b V)),
          i (symMap 6 (symMap b g.toLinearMap) x) =
            symMap b (symMap 6 g.toLinearMap) (i x)

def normalizedAverage (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    (⨂[ℂ] (_ : Fin n), V) →ₗ[ℂ] (⨂[ℂ] (_ : Fin n), V) :=
  (n.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
    (PiTensorProduct.reindex ℂ (fun _ : Fin n => V) σ).toLinearMap

namespace PolynomialModel

abbrev P (a n : ℕ) := MvPolynomial (Fin a × Fin n) ℂ

def rowWeight (a n : ℕ) : Fin a × Fin n → (Fin a → ℕ) :=
  fun ij => Pi.single ij.1 1

def W (a n j : ℕ) : Submodule ℂ (P a n) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (rowWeight a n) (fun _ => j)

def rowInvariants (a n : ℕ) : Subalgebra ℂ (P a n) where
  carrier := {f | ∀ σ : Equiv.Perm (Fin a),
    MvPolynomial.rename (fun ij : Fin a × Fin n => (σ ij.1, ij.2)) f = f}
  zero_mem' := by intro σ; simp
  add_mem' := by intro f g hf hg σ; simp only [map_add, hf σ, hg σ]
  one_mem' := by intro σ; simp
  mul_mem' := by intro f g hf hg σ; simp only [map_mul, hf σ, hg σ]
  algebraMap_mem' := by intro c σ; simp

def R (a n j : ℕ) : Submodule ℂ (P a n) :=
  W a n j ⊓ (rowInvariants a n).toSubmodule

def A (a n : ℕ) : Subalgebra ℂ (P a n) :=
  Algebra.adjoin ℂ (R a n 1 : Set (P a n))

def AComponent (a n b : ℕ) : Submodule ℂ (P a n) :=
  W a n b ⊓ (A a n).toSubmodule

def IndependentChartBound : Prop :=
  ∀ (a n b : ℕ), 2 ≤ a → a * (a - 1)^2 ≤ b → R a n b = AComponent a n b

end PolynomialModel
theorem independent_chart : PolynomialModel.IndependentChartBound := by
  intro a n b ha hb
  exact Chart.independent_chart_bound a n b ha hb

theorem sixth_equal (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    ∃ i : Sym 6 (Sym 6 V) →ₗ[ℂ] Sym 6 (Sym 6 V), Function.Injective i ∧
      ∀ (g : V ≃ₗ[ℂ] V) (x : Sym 6 (Sym 6 V)),
        i (symMap 6 (symMap 6 g.toLinearMap) x) = symMap 6 (symMap 6 g.toLinearMap) (i x) :=
  ⟨LinearMap.id, fun _ _ h => h, fun _ _ => rfl⟩

def FiniteSixthPowerComparison : Prop :=
  ∀ (b : ℕ), 7 ≤ b → b ≤ 29 →
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    ∃ (i : Sym 6 (Sym b V) →ₗ[ℂ] Sym b (Sym 6 V)),
      Function.Injective i ∧
        ∀ (g : V ≃ₗ[ℂ] V) (x : Sym 6 (Sym b V)),
          i (symMap 6 (symMap b g.toLinearMap) x) =
            symMap b (symMap 6 g.toLinearMap) (i x)

theorem full_iff_finite : SixthPowerComparison.{u} ↔ FiniteSixthPowerComparison.{u} := by
  constructor
  · intro h b hb _ V _ _ _
    exact h b (by omega) V
  · intro h b hb V _ _ _
    by_cases he : b = 6
    · subst b
      exact sixth_equal V
    · by_cases hbig : 30 ≤ b
      · exact Injection.sixth_large b hbig V
      · exact h b (by omega) (by omega) V

def BaseSixthPowerComparison : Prop :=
  ∀ (b : ℕ), 7 ≤ b → b ≤ 24 →
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    ∃ (i : Sym 6 (Sym b V) →ₗ[ℂ] Sym b (Sym 6 V)),
      Function.Injective i ∧
        ∀ (g : V ≃ₗ[ℂ] V) (x : Sym 6 (Sym b V)),
          i (symMap 6 (symMap b g.toLinearMap) x) =
            symMap b (symMap 6 g.toLinearMap) (i x)

theorem full_iff_base : SixthPowerComparison.{u} ↔ BaseSixthPowerComparison.{u} := by
  constructor
  · intro h b hb _ V _ _ _
    exact h b (by omega) V
  · intro h b hb V _ _ _
    by_cases he : b = 6
    · subst b
      exact sixth_equal V
    · by_cases hbig : 25 ≤ b
      · exact Injection.sixth_from_25 b hbig V
      · exact h b (by omega) (by omega) V

end Foulkes

end

end OAI
