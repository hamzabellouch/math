import Mathlib

namespace OAI

/-!
# Compact p-adic modules

The map `1 - shift` is surjective on the product of a tower of finite abelian groups,
without any surjectivity assumption on the transition maps. A compact Hausdorff module
vanishes if a topologically nilpotent scalar acts surjectively. This implies compact
p-adic Nakayama: a compact Hausdorff `ℤ_[p]`-module with continuous operations is finitely
generated exactly when its quotient modulo `p` is finite. Finitely generated
`ℤ_[p]`-modules also have finite `p`-torsion.

These are algebraic support results. The `K(n)`-local sphere, its homotopy groups,
their p-adic topology and module structure, and their ranks are not constructed here.
-/

open Filter Topology CategoryTheory
open scoped Pointwise

namespace KnLocalSphere.IntegralRecovery

universe u v

/-- The map `1 - shift` is surjective for any tower of finite abelian groups. -/
theorem one_sub_shift_surjective (A : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Finite (A n)]
    (f : ∀ n, A (n + 1) →+ A n) :
    Function.Surjective (fun x : (n : ℕ) → A n => fun n => x n - f n (x (n + 1))) := by
  intro y
  let D : ℕᵒᵖ ⥤ Type u := CategoryTheory.Functor.ofOpSequence
    (X := A) (fun n => ↾(fun z => y n + f n z))
  have : ∀ n, Finite (D.obj n) := fun n => inferInstanceAs (Finite (A n.unop))
  have : ∀ n, Nonempty (D.obj n) := fun n => ⟨(0 : A n.unop)⟩
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system D
  refine ⟨fun n => x (Opposite.op n), ?_⟩
  funext n
  apply sub_eq_iff_eq_add.mpr
  have h := hx (CategoryTheory.homOfLE (Nat.le_add_right n 1)).op
  simp only [D, CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ] at h
  change y n + f n (x (Opposite.op (n + 1))) = x (Opposite.op n) at h
  exact h.symm

/-- A surjective topologically nilpotent scalar annihilates a compact Hausdorff module. -/
theorem eq_zero_of_surjective_smul {R : Type u} {M : Type v}
    [Semiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [CompactSpace M] [T2Space M] [ContinuousSMul R M]
    (a : R) (ha : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0))
    (hs : Function.Surjective (fun x : M => a • x)) (x : M) : x = 0 := by
  have hpow : ∀ n : ℕ, Function.Surjective (fun y : M => a ^ n • y) := by
    intro n
    induction n with
    | zero =>
      intro z
      exact ⟨z, by change a ^ 0 • z = z; simp⟩
    | succ n ih =>
      intro z
      obtain ⟨w, hw⟩ := hs z
      obtain ⟨y, hy⟩ := ih w
      refine ⟨y, ?_⟩
      change a ^ (n + 1) • y = z
      change a • w = z at hw
      change a ^ n • y = w at hy
      rw [pow_succ', mul_smul, hy, hw]
  have hx : Tendsto (fun _ : ℕ => x) atTop (𝓝 (0 : M)) := by
    intro U hU
    have hV : ∀ᶠ r in 𝓝 (0 : R), ∀ y : M, r • y ∈ U := by
      have h := (isCompact_univ : IsCompact (Set.univ : Set M)).eventually_forall_of_forall_eventually (x₀ := (0 : R))
        (P := fun r y => r • y ∈ U) (fun y _ => by
          have hy : Tendsto (fun z : R × M => z.1 • z.2) (𝓝 (0, y)) (𝓝 (0 : M)) := by
            simpa only [ContinuousAt, zero_smul] using
              (continuous_smul : Continuous (fun z : R × M => z.1 • z.2)).continuousAt (x := (0, y))
          exact hy hU)
      simpa only [Set.mem_univ, forall_true_left] using h
    obtain ⟨n, hn⟩ := (ha.eventually hV).exists
    obtain ⟨y, hy⟩ := hpow n x
    change a ^ n • y = x at hy
    have hxu : x ∈ U := by rw [← hy]; exact hn y
    change ∀ᶠ _ : ℕ in atTop, x ∈ U
    exact Filter.Eventually.of_forall (fun _ => hxu)
  exact tendsto_nhds_unique tendsto_const_nhds hx

/-- Compact p-adic Nakayama: finiteness modulo `p` implies finite generation over `ℤ_[p]`. -/
theorem finite_of_finite_mod_p (p : ℕ) [Fact p.Prime]
    (M : Type u) [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℤ_[p] M]
    [CompactSpace M] [T2Space M]
    [Finite (M ⧸ LinearMap.range (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p])))] :
    Module.Finite ℤ_[p] M := by
  classical
  let P := LinearMap.range (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p]))
  let r : M ⧸ P → M := Function.surjInv P.mkQ_surjective
  have hr : ∀ z, P.mkQ (r z) = z := Function.surjInv_eq P.mkQ_surjective
  let N : Submodule ℤ_[p] M := Submodule.span ℤ_[p] (Set.range r)
  have hN : N.FG := Submodule.fg_span (Set.finite_range r)
  have : CompactSpace (M ⧸ N) := N.mkQ_surjective.compactSpace N.continuous_mkQ
  have : IsClosed (N : Set M) := (Submodule.isCompact_of_fg hN).isClosed
  have hsurj : Function.Surjective (fun x : M ⧸ N => (p : ℤ_[p]) • x) := by
    intro z
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    have hmem : x - r (P.mkQ x) ∈ P := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change P.mkQ (x - r (P.mkQ x)) = 0
      rw [map_sub, hr, sub_self]
    obtain ⟨y, hy⟩ := hmem
    refine ⟨N.mkQ y, ?_⟩
    have hn : N.mkQ (r (P.mkQ x)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.subset_span (Set.mem_range_self _)
    change (p : ℤ_[p]) • y = x - r (P.mkQ x) at hy
    change (p : ℤ_[p]) • N.mkQ y = N.mkQ x
    rw [← map_smul, hy, map_sub, hn, sub_zero]
  have hp : Tendsto (fun n : ℕ => (p : ℤ_[p]) ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [PadicInt.norm_p]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have htop : N = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact eq_zero_of_surjective_smul (p : ℤ_[p]) hp hsurj (N.mkQ x)
  exact ⟨htop ▸ hN⟩

/-- A finitely generated `ℤ_[p]`-module has finite quotient modulo `p`. -/
theorem finite_mod_p_of_finite_module (p : ℕ) [Fact p.Prime]
    (M : Type u) [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    Finite (M ⧸ LinearMap.range (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p]))) := by
  have : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact Finite.of_injective PadicInt.residueField PadicInt.residueField.injective
  have h := Submodule.finite_quotient_smul (M := M) (Ideal.span {(p : ℤ_[p])})
    (N := ⊤) (Module.Finite.fg_top (R := ℤ_[p]) (M := M))
  have heq : Ideal.span {(p : ℤ_[p])} • (⊤ : Submodule ℤ_[p] M) =
      LinearMap.range (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p])) := by
    rw [Submodule.ideal_span_singleton_smul]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]
  exact heq ▸ h

/-- A finitely generated `ℤ_[p]`-module killed by `p` is finite. -/
theorem finite_of_finite_module_killed_by_p (p : ℕ) [Fact p.Prime]
    (M : Type u) [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (hp : ∀ x : M, (p : ℤ_[p]) • x = 0) : Finite M := by
  let P := LinearMap.range (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p]))
  have : Finite (M ⧸ P) := finite_mod_p_of_finite_module p M
  apply Finite.of_injective P.mkQ
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mkQ]
  apply LinearMap.range_eq_bot.mpr
  ext x
  exact hp x

/-- The `p`-torsion of a finitely generated `ℤ_[p]`-module is finite. -/
theorem finite_p_torsion (p : ℕ) [Fact p.Prime]
    (M : Type u) [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    Finite (LinearMap.ker (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p]))) := by
  let T := LinearMap.ker (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p]))
  have : Module.Finite ℤ_[p] T := inferInstance
  apply finite_of_finite_module_killed_by_p p T
  intro x
  apply Subtype.ext
  exact x.property

/-- A compact Hausdorff `ℤ_[p]`-module is finitely generated iff it is finite modulo `p`. -/
theorem module_finite_iff_finite_mod_p (p : ℕ) [Fact p.Prime]
    (M : Type u) [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℤ_[p] M]
    [CompactSpace M] [T2Space M] :
    Module.Finite ℤ_[p] M ↔
      Finite (M ⧸ LinearMap.range (LinearMap.lsmul ℤ_[p] M (p : ℤ_[p]))) := by
  constructor
  · intro _
    exact finite_mod_p_of_finite_module p M
  · intro _
    exact finite_of_finite_mod_p p M

end KnLocalSphere.IntegralRecovery

end OAI
