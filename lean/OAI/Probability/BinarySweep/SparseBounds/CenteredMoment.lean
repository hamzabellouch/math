import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.CenteredPlacement

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

lemma groupAverage_adjoint (ρ : Representation ℂ G V)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (p : G → ℂ) :
    (groupAverage ρ p).adjoint=groupAverage ρ (fun g => star (p g⁻¹)) := by
  simp only [groupAverage,map_sum,map_smulₛₗ,unitary_rep_adjoint ρ hρ,starRingEnd_apply]
  have he := Equiv.sum_comp (Equiv.inv G) (fun g => star (p g⁻¹) • ρ g)
  simpa only [Equiv.inv_apply,inv_inv] using he

lemma even_compatible_maps (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (f : V →ₗ[ℂ] W) (hf : ∀v, B (f v)=f (A v))
    (hs : ∀v, B.adjoint (f v)=f (A.adjoint v)) (q : ℕ) (v : V) :
    ((B.adjoint*B)^q) (f v)=f (((A.adjoint*A)^q) v) := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]
    rw [Module.End.mul_apply,hf,hs]
    rfl

theorem evenMoment_le_of_injective (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (f : V →ₗ[ℂ] W) (hi : Function.Injective f)
    (hf : ∀v, B (f v)=f (A v)) (hs : ∀v, B.adjoint (f v)=f (A.adjoint v)) (q : ℕ) :
    evenMoment q A ≤ evenMoment q B := by
  let S := LinearMap.range f
  let a := (A.adjoint*A)^q
  let b := (B.adjoint*B)^q
  have hb : ∀w∈S, b w∈S := by
    intro w hw
    obtain ⟨v,rfl⟩ := hw
    exact ⟨a v,(even_compatible_maps A B f hf hs q v).symm⟩
  let e : V ≃ₗ[ℂ] S := LinearEquiv.ofInjective f hi
  have he : e.symm.conj (b.restrict hb)=a := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (e.symm ((b.restrict hb) (e v)))=e (a v)
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact even_compatible_maps A B f hf hs q v
  have ht := LinearMap.trace_conj' (b.restrict hb) e.symm
  rw [he] at ht
  have hle := positive_trace_restrict_le S b
    (positive_pow (LinearMap.isPositive_adjoint_comp_self B) q) hb
  rw [← ht] at hle
  exact hle

end BinaryCoordinateSweeps.Irrep
namespace BinaryCoordinateSweeps.Young

theorem centeredHilbert_moment (μ : YoungDiagram) (s : ℝ) (hs : s≠0)
    (p : G μ → ℂ) (q : ℕ) :
    Irrep.evenMoment q (Irrep.groupAverage (hilbertSpecht μ) p) ≤
      Irrep.evenMoment q (centeredHilbert (I:=Tail μ) s p) := by
  apply Irrep.evenMoment_le_of_injective _ _ (spechtPlacementHilbert μ)
    (spechtPlacementHilbert_injective μ)
  · exact centeredHilbert_specht μ s hs p
  · intro v
    rw [centeredHilbert_adjoint,Irrep.groupAverage_adjoint _ (hilbertSpecht_unitary μ)]
    exact centeredHilbert_specht μ s hs _ v

end BinaryCoordinateSweeps.Young

end

end OAI
