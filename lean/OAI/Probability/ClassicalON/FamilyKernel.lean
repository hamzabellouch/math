import OAI.Probability.ClassicalON.ObservableBounds

namespace OAI

universe uE uI uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON
variable {I : Type uI} {E : Type uE} [Fintype I] [Fintype E]

def familyKernel (u : I → E → ℂ) (e l : E) : ℂ := ∑ i, u i e * conj (u i l)

def rowSquare (u : I → E → ℂ) (e : E) : ℝ := ∑ l, ‖familyKernel u e l‖^2

def familyHSSquare (u : I → E → ℂ) : ℝ := ∑ e, rowSquare u e

omit [Fintype E] in
@[simp] theorem familyKernel_conj (u : I → E → ℂ) (e l : E) :
    familyKernel (fun i e => conj (u i e)) e l = conj (familyKernel u e l) := by
  simp [familyKernel]

theorem rowSquare_nonneg (u : I → E → ℂ) (e : E) : 0 ≤ rowSquare u e :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem familyHSSquare_nonneg (u : I → E → ℂ) : 0 ≤ familyHSSquare u :=
  Finset.sum_nonneg fun e _ => rowSquare_nonneg u e

theorem kernel_diag_sq_le_row (u : I → E → ℂ) (e : E) :
    ‖familyKernel u e e‖^2 ≤ rowSquare u e :=
  Finset.single_le_sum (fun l _ => sq_nonneg ‖familyKernel u e l‖) (Finset.mem_univ e)

theorem kernel_diag_norm_le_sqrt (u : I → E → ℂ) (e : E) :
    ‖familyKernel u e e‖ ≤ Real.sqrt (rowSquare u e) :=
  Real.le_sqrt_of_sq_le (kernel_diag_sq_le_row u e)

namespace SpinSystem
variable {n : ℕ} {V : Type uV} [Fintype V]

omit [Fintype V] [Fintype I] in
def coefficientObservable (S : SpinSystem n V E) (M : SpinOperator n) (e : E) :
    C((V → Spin n), ℂ) := ⟨fun σ => (S.localCoefficient M σ e : ℂ), by
  unfold localCoefficient
  fun_prop⟩

omit [Fintype V] [Fintype I] in
def currentObservable (S : SpinSystem n V E) (M : SpinOperator n) (u : E → ℂ) :
    C((V → Spin n), ℂ) := ⟨_, S.continuous_complexEnergy M u⟩

omit [Fintype V] [Fintype I] [Fintype E] in
def conjugateObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℂ) :=
  ⟨fun σ => conj (f σ), Complex.continuous_conj.comp f.continuous⟩

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem conjugateObservable_apply {Ω : Type uΩ} [TopologicalSpace Ω]
    (f : C(Ω, ℂ)) (σ : Ω) : conjugateObservable f σ = conj (f σ) := rfl

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem normObservable_conjugate {Ω : Type uΩ} [TopologicalSpace Ω]
    (f : C(Ω, ℂ)) : normObservable (conjugateObservable f) = normObservable f := by
  ext σ
  exact Complex.norm_conj (f σ)

omit [Fintype V] [Fintype I] in
@[simp] theorem currentObservable_conj (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) : S.currentObservable M (fun e => conj (u e)) =
      conjugateObservable (S.currentObservable M u) := by
  ext σ
  exact S.complexEnergy_conj M u σ

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem coefficientObservable_conj (S : SpinSystem n V E) (M : SpinOperator n)
    (e : E) : conjugateObservable (S.coefficientObservable M e) =
      S.coefficientObservable M e := by
  ext σ
  exact Complex.conj_ofReal _

omit [Fintype V] [Fintype E] in
theorem familyKernel_differential (S : SpinSystem n V E) (f : I → V → ℂ) (e : E) :
    familyKernel (fun i => S.differential (f i)) e =
      S.differential (fun x => ∑ i, S.differential (f i) e * conj (f i x)) := by
  funext l
  simp only [familyKernel, differential, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem row_current_moment [NeZero n] (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator n) (hM : M ∈ skewAdjoint (SpinOperator n)) (hMn : ‖M‖ ≤ 1)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) (e : E) :
    S.averageLinear (normObservable (S.currentObservable M
      (familyKernel (fun i => S.differential (f i)) e)) *
      normObservable (S.currentObservable M
      (familyKernel (fun i => S.differential (f i)) e))) ≤
        β * rowSquare (fun i => S.differential (f i)) e := by
  have hp : ∀ x s, S.pin x = some s →
      (∑ i, S.differential (f i) e * conj (f i x)) = 0 := by
    intro x s hs
    simp [hP _ x s hs]
  have h := S.complex_gradient_current_bound β hb M hM hMn
    (fun x => ∑ i, S.differential (f i) e * conj (f i x)) hp
  rw [← S.familyKernel_differential f e] at h
  change S.average (fun σ =>
    ‖S.complexEnergy M (familyKernel (fun i => S.differential (f i)) e) σ‖ *
    ‖S.complexEnergy M (familyKernel (fun i => S.differential (f i)) e) σ‖) ≤ _
  simpa only [rowSquare, pow_two] using h

end SpinSystem
end ClassicalON

end

end OAI
