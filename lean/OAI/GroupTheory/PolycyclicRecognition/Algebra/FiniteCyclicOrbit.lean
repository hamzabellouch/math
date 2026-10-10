import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicExteriorOrbitDependence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Int.Interval

namespace OAI

/-! # A dependent invertible cyclic orbit spans a finite-dimensional space -/

noncomputable section
namespace PolycyclicRecognition
variable {K : Type} [Field K]
open scoped MonoidAlgebra
variable {M : Type} [AddCommGroup M] [Module K M]

theorem finite_cyclic_invariant_all
    (ρ : Representation K (Multiplicative ℤ) M) (U : Submodule K M)
    [FiniteDimensional K U]
    (hU : ∀ x ∈ U, ρ (Multiplicative.ofAdd 1) x ∈ U) :
    ∀ g x, x ∈ U → ρ g x ∈ U := by
  let H : Subgroup (Multiplicative ℤ) :=
    { carrier := {g | ∀ x ∈ U, ρ g x ∈ U}
      one_mem' := by intro x hx; simpa using hx
      mul_mem' := by
        intro g h hg hh x hx
        simpa only [map_mul, Module.End.mul_apply] using hg _ (hh x hx)
      inv_mem' := by
        intro g hg x hx
        have hk : LinearMap.ker (ρ g) = ⊥ :=
          LinearMap.ker_eq_bot.mpr (ρ.apply_bijective g).injective
        have hc : U.comap (ρ g) = U := by
          simpa only [hk, sup_bot_eq] using
            LinearMap.comap_eq_sup_ker_of_disjoint hg (by rw [hk]; exact disjoint_bot_right)
        have hh : ρ g⁻¹ x ∈ U.comap (ρ g) := by
          change ρ g (ρ g⁻¹ x) ∈ U
          simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply] using hx
        exact hc ▸ hh }
  have ht : Multiplicative.ofAdd (1 : ℤ) ∈ H := hU
  intro g x hx
  have hp := H.zpow_mem ht g.toAdd
  have he : (Multiplicative.ofAdd (1 : ℤ)) ^ g.toAdd = g := by
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
    rfl
  rw [he] at hp
  exact hp x hx

theorem cyclic_orbit_span_finite_of_dependent
    (ρ : Representation K (Multiplicative ℤ) M) (v : M)
    (hdep : ¬LinearIndependent K (fun i : ℤ => ρ (Multiplicative.ofAdd i) v)) :
    FiniteDimensional K (Submodule.span K
      (Set.range (fun i : ℤ => ρ (Multiplicative.ofAdd i) v))) := by
  classical
  let w : ℤ → M := fun i => ρ (Multiplicative.ofAdd i) v
  have hstep (i : ℤ) : ρ (Multiplicative.ofAdd 1) (w i) = w (i + 1) := by
    change ρ (Multiplicative.ofAdd 1) (ρ (Multiplicative.ofAdd i) v) = _
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    change 1 + i = i + 1
    omega
  obtain ⟨a, ha, ha0⟩ := not_linearIndependent_iff_linearCombination.mp hdep
  have hne : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr ha0
  let m : ℤ := a.support.min' hne
  let n : ℤ := a.support.max' hne
  have hm : m ∈ a.support := Finset.min'_mem _ _
  have hn : n ∈ a.support := Finset.max'_mem _ _
  have hmn : m ≤ n := Finset.le_max' _ _ hm
  let U : Submodule K M := Submodule.span K (w '' Set.Icc m n)
  let : FiniteDimensional K U :=
    FiniteDimensional.span_of_finite K ((Set.finite_Icc m n).image w)
  have hwmem (i : ℤ) (hi : m ≤ i ∧ i ≤ n) : w i ∈ U :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  have hrel : ∑ i ∈ a.support, a i • w (i + 1) = 0 := by
    have ha' : ∑ i ∈ a.support, a i • w i = 0 := ha
    have h := congrArg (ρ (Multiplicative.ofAdd 1)) ha'
    simpa only [map_sum, map_smul, map_zero, hstep] using h
  have hsmall : (∑ i ∈ a.support.erase n, a i • w (i + 1)) ∈ U := by
    apply Submodule.sum_mem
    intro i hi
    obtain ⟨hin, his⟩ := Finset.mem_erase.mp hi
    have hmi := Finset.min'_le _ _ his
    have hin' := Finset.le_max' _ _ his
    exact U.smul_mem _ (hwmem (i + 1) ⟨by omega, by omega⟩)
  have htop : w (n + 1) ∈ U := by
    have hsum : (∑ i ∈ a.support.erase n, a i • w (i + 1)) + a n • w (n + 1) = 0 :=
      (Finset.sum_erase_add _ _ hn).trans hrel
    have ht : a n • w (n + 1) ∈ U := by
      rw [eq_neg_of_add_eq_zero_right hsum]
      exact U.neg_mem hsmall
    have hc : a n ≠ 0 := Finsupp.mem_support_iff.mp hn
    have h := U.smul_mem (a n)⁻¹ ht
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  have hstable : ∀ x ∈ U, ρ (Multiplicative.ofAdd 1) x ∈ U := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rcases hi with ⟨hil, hiu⟩
      rw [hstep]
      by_cases hin : i = n
      · simpa only [hin] using htop
      · exact hwmem (i + 1) ⟨by omega, by omega⟩
    | zero => simpa only [map_zero] using U.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using U.add_mem hx hy
    | smul r x _ hx => simpa only [map_smul] using U.smul_mem r hx
  have hall : ∀ i : ℤ, w i ∈ U := by
    intro i
    have h := finite_cyclic_invariant_all ρ U hstable
      (Multiplicative.ofAdd (i - m)) (w m) (hwmem m ⟨le_rfl, hmn⟩)
    have he : ρ (Multiplicative.ofAdd (i - m)) (w m) = w i := by
      change ρ (Multiplicative.ofAdd (i - m)) (ρ (Multiplicative.ofAdd m) v) = w i
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      change i - m + m = i
      omega
    exact he ▸ h
  have hle : Submodule.span K (Set.range w) ≤ U :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

theorem cyclic_orbit_span_finite_of_finite_exterior
    (ρ : Representation K (Multiplicative ℤ) M)
    [Module.Finite K[Multiplicative ℤ] (rationalExteriorSquareRepresentation ρ).asModule]
    (v : M) : FiniteDimensional K (Submodule.span K
      (Set.range (fun i : ℤ => ρ (Multiplicative.ofAdd i) v))) :=
  cyclic_orbit_span_finite_of_dependent ρ v (cyclic_orbit_dependent_of_finite_exterior ρ v)

end PolycyclicRecognition

end

end OAI
