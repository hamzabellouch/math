import OAI.Analysis.Nuclearity.UnitizedConeOperations

namespace OAI

/-! Convexity of the actual finite coefficient cone. Padding arrays by zero
allows unrelated finite coefficient sizes to be combined without changing
their maps. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B]
  (U : Ultrafilter ℕ)

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

lemma finiteUnitizedAbelianCoefficientCone_add (β : B →⋆ₙₐ[ℂ] N)
    {S T : B → N} (hS : S ∈ finiteUnitizedAbelianCoefficientCone U β)
    (hT : T ∈ finiteUnitizedAbelianCoefficientCone U β) :
    S + T ∈ finiteUnitizedAbelianCoefficientCone U β := by
  obtain ⟨n, m, V, hi, hp, hc, a, c, hv⟩ := hS
  obtain ⟨n', m', V', hi', hp', hc', a', c', hv'⟩ := hT
  let W := Fin.append V V'
  let aa := Fin.append
    (fun j => Fin.append (fun i => a (j, i)) (0 : Fin m' → Unitization ℂ N))
    (fun j => Fin.append (0 : Fin m → Unitization ℂ N) (fun i => a' (j, i)))
  let cc := Fin.append
    (fun j => Fin.append (fun i => c (j, i)) (0 : Fin m' → B))
    (fun j => Fin.append (0 : Fin m → B) (fun i => c' (j, i)))
  refine ⟨n + n', m + m', W, ?_, ?_, ?_, (fun p => aa p.1 p.2),
    (fun p => cc p.1 p.2), ?_⟩
  · intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [W, Fin.append_left] using hi k
    · simpa only [W, Fin.append_right] using hi' k
  · intro j b hb
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [W, Fin.append_left] using hp k b hb
    · simpa only [W, Fin.append_right] using hp' k b hb
  · intro j b d
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [W, Fin.append_left] using hc k b d
    · simpa only [W, Fin.append_right] using hc' k b d
  · intro b
    rw [Fin.sum_univ_add]
    simp only [W, aa, cc, Fin.append_left, Fin.append_right,
      unitizedCoefficientEnlargement_pad_left, unitizedCoefficientEnlargement_pad_right]
    exact congrArg₂ (· + ·) (hv b) (hv' b)

lemma finiteUnitizedAbelianCoefficientCone_smul (β : B →⋆ₙₐ[ℂ] N)
    {S : B → N} (hS : S ∈ finiteUnitizedAbelianCoefficientCone U β)
    {r : ℝ} (hr : 0 ≤ r) : r • S ∈ finiteUnitizedAbelianCoefficientCone U β := by
  obtain ⟨n, m, V, hi, hp, hc, a, c, hv⟩ := hS
  refine ⟨n, m, V, hi, hp, hc, (fun p => Real.sqrt r • a p), c, ?_⟩
  intro b
  simp only [unitizedCoefficientEnlargement_nonneg_smul _ _ _ _ hr,
    ← Finset.smul_sum]
  exact congrArg (fun z => r • z) (hv b)

lemma finiteUnitizedAbelianCoefficientCone_zero (β : B →⋆ₙₐ[ℂ] N) :
    (0 : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β := by
  refine ⟨0, 0, Fin.elim0, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j),
    (fun j => Fin.elim0 j), (fun p => Fin.elim0 p.1), (fun p => Fin.elim0 p.1), ?_⟩
  intro b
  simp

def unitizedCoefficientCone (β : B →⋆ₙₐ[ℂ] N) : ConvexCone ℝ (B → N) where
  carrier := finiteUnitizedAbelianCoefficientCone U β
  smul_mem' := fun _ hr _ hS => finiteUnitizedAbelianCoefficientCone_smul U β hS hr.le
  add_mem' := fun _ hS _ hT => finiteUnitizedAbelianCoefficientCone_add U β hS hT

end WeakPureInfiniteness

end

end OAI
