import Mathlib

namespace OAI

/-!
Finite polyhedra, local perturbations, and quotient dimension bounds.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

section PolyhedralPrelude
variable {I J : Type*} [Fintype I] [Fintype J]

def finitePolyhedron (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ) : Set (J → ℝ) :=
  {x | ∀ i, L i x ≤ b i}

/-- Finite slack, with every active equation preserved, permits both signs. -/
theorem finitePolyhedron_eventually_line (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ)
    {x : J → ℝ} (hx : x ∈ finitePolyhedron L b) (u : J → ℝ)
    (hu : ∀ i, L i x = b i → L i u = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ finitePolyhedron L b := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : L i x=b i
  · apply Filter.Eventually.of_forall
    intro t
    rw [map_add, map_smul, hu i hi, smul_zero, add_zero, hi]
  · have hlt : L i x < b i := lt_of_le_of_ne (hx i) hi
    have hc : Continuous (fun t : ℝ => L i (x+t • u)) :=
      (L i).continuous_of_finiteDimensional.comp (by fun_prop)
    have hh : ∀ᶠ t : ℝ in 𝓝 0, L i (x+t • u) < b i :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa using hlt : L i (x+(0:ℝ) • u) < b i)
    exact hh.mono fun t ht => le_of_lt ht

/-- Radial expansion about x preserves every active inequality for arbitrary
nearby feasible points. Inactive inequalities are handled by finite slack. -/
theorem finitePolyhedron_eventually_expand (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ)
    {x : J → ℝ} (hx : x ∈ finitePolyhedron L b) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ y in 𝓝[finitePolyhedron L b] x, x+t⁻¹ • (y-x) ∈ finitePolyhedron L b := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : L i x=b i
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    rw [map_add, map_smul, map_sub, hi]
    change b i+t⁻¹ * (L i y-b i) ≤ b i
    have hh := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr (hy i))
    linarith
  · have hlt : L i x < b i := lt_of_le_of_ne (hx i) hi
    have hc : Continuous (fun y : J → ℝ => L i (x+t⁻¹ • (y-x))) :=
      (L i).continuous_of_finiteDimensional.comp (by fun_prop)
    have hh : ∀ᶠ y : J → ℝ in 𝓝 x, L i (x+t⁻¹ • (y-x)) < b i :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa using hlt : L i (x+t⁻¹ • (x-x)) < b i)
    exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => le_of_lt hy

omit [Fintype J] in
theorem extreme_point_direction_zero (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • u ∈ P := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0:ℝ))
    exact hc.eventually hu
  -- choose a strictly positive point using the right-hand punctured neighborhood
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x+t • u ∈ P ∧ x+(-t) • u ∈ P) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  have hseg : x ∈ openSegment ℝ (x+a • u) (x+(-a) • u) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := (mem_extremePoints.mp hx).2 _ ha _ hna hseg |>.1
  ext j
  have hj := congrFun he j
  change x j+a*u j=x j at hj
  change u j=0
  exact (mul_eq_zero.mp (by linarith : a*u j=0)).resolve_left (ne_of_gt ha0)


section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

theorem quotient_finrank_le_pair (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u))=0 := hu
    have hW : f u ∈ W := by
      have hq := congrArg Prod.fst hh
      simpa using hq
    have hZ : g u ∈ Z := by
      have hq := congrArg Prod.snd hh
      simpa using hq
    exact h u hW hZ
  simpa using quotient_finrank_le_of_ker_le U F hk

end LinearHelper
end PolyhedralPrelude

end MatchingEntropy

end

end OAI
