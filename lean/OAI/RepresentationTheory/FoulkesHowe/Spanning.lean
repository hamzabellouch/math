import OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear

namespace OAI

noncomputable section
open scoped BigOperators
universe u v
namespace Problem346

/-- Monomials span the symmetric power, in its subtype realization. -/
theorem span_symMonomial (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    Submodule.span ℂ (Set.range (symMonomial n V)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (symPowSubmodule n V)
    (fun x => Submodule.subset_span (Set.mem_range_self x))).2
  rfl

/-- Maps out of a symmetric power are determined by monomials. -/
theorem symPow_linearMap_ext (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W]
    (f g : SymPow n V →ₗ[ℂ] W)
    (h : ∀ x : Fin n → V, f (symMonomial n V x) = g (symMonomial n V x)) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top f g (span_symMonomial n V)).2
  rintro ⟨_, x, rfl⟩
  exact h x

/-- A multilinear map vanishing on tuples from a spanning set is zero. -/
theorem multilinear_eq_zero_of_span
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {N : Type v} [AddCommGroup N] [Module ℂ N]
    {s : Set M} (hs : Submodule.span ℂ s = ⊤) (n : ℕ) :
    ∀ F : MultilinearMap ℂ (fun _ : Fin n => M) N,
      (∀ x, (∀ i, x i ∈ s) → F x = 0) → F = 0 := by
  induction n with
  | zero =>
      intro F hF
      ext x
      exact hF x (fun i => Fin.elim0 i)
  | succ n ih =>
      intro F hF
      have hc : F.curryLeft = 0 := by
        apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top F.curryLeft hs).2
        intro x
        apply ih
        intro y hy
        apply hF
        exact Fin.cases x.property hy
      ext x
      have h := congrArg (fun f : M →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => M) N =>
        f (x 0) (Fin.tail x)) hc
      simpa using h

/-- Multilinear maps agree if they agree on tuples from a spanning set. -/
theorem multilinear_ext_of_span
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {N : Type v} [AddCommGroup N] [Module ℂ N]
    {s : Set M} (hs : Submodule.span ℂ s = ⊤) (n : ℕ)
    (F G : MultilinearMap ℂ (fun _ : Fin n => M) N)
    (h : ∀ x, (∀ i, x i ∈ s) → F x = G x) : F = G := by
  apply sub_eq_zero.mp
  apply multilinear_eq_zero_of_span hs n
  intro x hx
  simp only [sub_apply, h x hx, sub_self]

/-- Linear maps out of a plethysm are determined by double monomials. -/
theorem plethysm_linearMap_ext (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W]
    (f g : SymPow b (SymPow a V) →ₗ[ℂ] W)
    (h : ∀ x : Fin b → Fin a → V,
      f (symMonomial b (SymPow a V) (fun j => symMonomial a V (x j))) =
      g (symMonomial b (SymPow a V) (fun j => symMonomial a V (x j)))) : f = g := by
  classical
  apply symPow_linearMap_ext b (SymPow a V)
  have hm : f.compMultilinearMap (symMonomialMultilinear b (SymPow a V)) =
      g.compMultilinearMap (symMonomialMultilinear b (SymPow a V)) := by
    apply multilinear_ext_of_span (span_symMonomial a V) b
    intro x hx
    choose v hv using hx
    have hx' : x = fun j => symMonomial a V (v j) := funext (fun j => (hv j).symm)
    subst x
    exact h v
  intro x
  exact congrArg (fun F => F x) hm

/-- Double monomials span the plethysm. -/
theorem span_plethysmMonomial (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    Submodule.span ℂ (Set.range (fun x : Fin b → Fin a → V =>
      symMonomial b (SymPow a V) (fun j => symMonomial a V (x j)))) = ⊤ := by
  let p := Submodule.span ℂ (Set.range (fun x : Fin b → Fin a → V =>
    symMonomial b (SymPow a V) (fun j => symMonomial a V (x j))))
  change p = ⊤
  have hp : p.mkQ = 0 := by
    apply plethysm_linearMap_ext a b V
    intro x
    apply (Submodule.Quotient.mk_eq_zero p).mpr
    exact Submodule.subset_span (Set.mem_range_self x)
  rw [← Submodule.ker_mkQ p, hp, LinearMap.ker_zero]

/-- The defining formula determines a Foulkes map uniquely. -/
theorem IsFoulkesMap.unique (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    {f g : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hf : IsFoulkesMap a b V f) (hg : IsFoulkesMap a b V g) : f = g := by
  apply plethysm_linearMap_ext a b V
  intro x
  exact (hf x).trans (hg x).symm

end Problem346

end

end OAI
