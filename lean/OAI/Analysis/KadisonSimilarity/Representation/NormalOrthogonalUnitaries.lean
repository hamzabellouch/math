import OAI.Analysis.KadisonSimilarity.Tracial.NormalSmallCorners

namespace OAI

/-! The diffuse normal matrix source supplies the unitary sequence used in
the free-factor center argument. The sequence consists of positive powers
of the constructed full-corner Haar unitary. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

local instance normalUnitaries_closed (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N

include M in
/-- An actual centered orthogonal unitary family in the original source. -/
theorem exists_orthogonal_unitaries_of_normal_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop) :
    ∃ u : ℕ → unitary P, (∀ n, G.trace (u n : P) = 0) ∧
      ∀ i j, G.trace ((u i : P) * star (u j : P)) = if i = j then 1 else 0 := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hdiff := G.normalRange_diffuse_of_matrix_tower M h1 hf N hN hsize
  obtain ⟨z, hz⟩ := exists_dyadicCornerHaar τ hdiff ⟨1, IsStarProjection.one _⟩
  have hhaar : HaarCornerMoments (concreteTraceLinear τ) z 1 := by
    intro k hk
    change (1 : ℂ)⁻¹ * τ.trace (haarCornerPower z k) = 0
    rw [inv_one, one_mul]
    exact hz k hk
  have htrace : concreteTraceLinear τ 1 = (1 : ℂ) := τ.trace_one
  let v : ℕ → unitary N.toStarSubalgebra := fun n =>
    ⟨haarCornerLetter z 1 n, by
      constructor
      · simpa using star_haarCornerLetter_mul_self z (by norm_num : (0 : ℝ) ≤ 1) n
      · simpa using haarCornerLetter_mul_star_self z (by norm_num : (0 : ℝ) ≤ 1) n⟩
  have hv0 (n : ℕ) : concreteTraceLinear τ (v n : N.toStarSubalgebra) = 0 :=
    haarCornerLetter_trace_zero _ z (by norm_num) htrace hhaar n
  have hv (i j : ℕ) :
      concreteTraceLinear τ ((v i : N.toStarSubalgebra) * star (v j : N.toStarSubalgebra)) =
        if i = j then 1 else 0 :=
    haarCornerLetter_mul_star_trace _ z (by norm_num) htrace hhaar i j
  have htransport (a : N.toStarSubalgebra) :
      G.trace (e.symm a) = concreteTraceLinear τ a := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm a)
    change τ.trace (e (e.symm a)) = G.trace (e.symm a) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  refine ⟨fun n => Unitary.map (StarMonoidHom.ofClass e.symm) (v n), ?_, ?_⟩
  · intro n
    change G.trace (e.symm (v n : N.toStarSubalgebra)) = 0
    rw [htransport, hv0]
  · intro i j
    change G.trace (e.symm (v i : N.toStarSubalgebra) *
      star (e.symm (v j : N.toStarSubalgebra))) = _
    have hs : e.symm (star (v j : N.toStarSubalgebra)) =
        star (e.symm (v j : N.toStarSubalgebra)) := e.symm.map_star' _
    have hm : e.symm ((v i : N.toStarSubalgebra) * star (v j : N.toStarSubalgebra)) =
        e.symm (v i : N.toStarSubalgebra) * e.symm (star (v j : N.toStarSubalgebra)) :=
      e.symm.map_mul' _ _
    rw [← hs, ← hm, htransport, hv]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
