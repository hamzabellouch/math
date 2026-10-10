import OAI.Geometry.NodalSets.Elliptic.CompactParameterEllipticityLemmas

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {ι : Type*} [Fintype ι]

lemma compact_parameter_finite_scalar_bound (f : ι → T → Yau.Jets.Coord → ℝ)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (hf : ∀ i, Continuous (fun z : T × Q ↦ f i z.1 z.2)) :
    ∃ M > 0, ∀ i t x, x ∈ Q → |f i t x| ≤ M := by
  classical
  have hb (i : ι) := compact_parameter_scalar_bound (f i) hQ (hf i)
  choose M hM hb using hb
  refine ⟨1+∑ i, |M i|,by positivity,?_⟩
  intro i t x hx
  have h := (hb i t x hx).trans ((le_abs_self (M i)).trans
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (M j)) (Finset.mem_univ i)))
  linarith

end
end Yau.Geometry

end OAI
