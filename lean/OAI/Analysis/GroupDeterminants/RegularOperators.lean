import OAI.Analysis.GroupDeterminants.ModularLifting

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularAction
open scoped ENNReal
variable {G : Type} [Group G] {n : ℕ}

def reindex (e : (Fin n × G) ≃ (Fin n × G)) : Hilbert G n →ₗᵢ[ℂ] Hilbert G n where
  toFun ξ := ⟨fun a => ξ (e a), memℓp_gen
    (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩
  map_add' ξ η := by ext a; rfl
  map_smul' z ξ := by ext a; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun a => ‖ξ a‖ ^ (2 : ℝ≥0∞).toReal)

def cutComponent (i : Fin n) : Hilbert G n →L[ℂ] Hilbert G n := by
  classical
  let f : Hilbert G n →ₗ[ℂ] Hilbert G n := {
    toFun ξ := ⟨fun a => if a.1 = i then ξ a else 0,
      (lp.memℓp ξ).mono' (fun a => by split_ifs <;> simp)⟩
    map_add' ξ η := by
      ext a
      change (if a.1 = i then ξ a + η a else 0) =
        (if a.1 = i then ξ a else 0) + (if a.1 = i then η a else 0)
      split_ifs <;> simp
    map_smul' z ξ := by
      ext a
      change (if a.1 = i then z • ξ a else 0) = z • (if a.1 = i then ξ a else 0)
      split_ifs <;> simp }
  exact f.mkContinuous 1 (fun ξ => by
    simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (x := f ξ) (y := ξ) (fun a => by
        change ‖ite (a.1 = i) (ξ a) 0‖ ≤ ‖ξ a‖
        split_ifs <;> simp))

omit [Group G] in
@[simp] theorem cutComponent_apply (i : Fin n) (ξ : Hilbert G n) (a : Fin n × G) :
    cutComponent i ξ a = if a.1 = i then ξ a else 0 := rfl

def elementaryOperator (i j : Fin n) (g : G) : Hilbert G n →L[ℂ] Hilbert G n :=
  (cutComponent i).comp (reindex
    (Equiv.prodCongr (Equiv.swap i j) (Equiv.mulLeft g⁻¹))).toContinuousLinearMap

theorem elementaryOperator_apply (i j : Fin n) (g : G) (ξ : Hilbert G n)
    (a : Fin n) (h : G) :
    elementaryOperator i j g ξ (a, h) = if a = i then ξ (j, g⁻¹ * h) else 0 := by
  classical
  by_cases hi : a = i
  · subst a
    simp [elementaryOperator, reindex, cutComponent_apply]
  · simp [elementaryOperator, cutComponent_apply, hi]

def regularOperator (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    Hilbert G n →L[ℂ] Hilbert G n :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j).coeff.sum
    (fun g z => (z : ℂ) • elementaryOperator i j g)

theorem regularOperator_spec (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    IsRegularOperator A (regularOperator A) := by
  classical
  intro ξ i h
  simp only [regularOperator, Finsupp.sum, sum_apply,
    smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, elementaryOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · simp

theorem exists_regularOperator (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    ∃ T, IsRegularOperator A T := ⟨regularOperator A, regularOperator_spec A⟩

end RegularAction

end GroupRingDeterminant

end

end OAI
