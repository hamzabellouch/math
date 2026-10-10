import Mathlib
import OAI.Analysis.Commutator.FiniteFactorComparison
import OAI.Analysis.Commutator.MatrixUnits
import OAI.Analysis.Commutator.NormalTraceProjection

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_factor_equivalence_link (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (heq : τ ⟨e,heM⟩=τ ⟨f,hfM⟩) :
    ∃ v : Link M e f, v.initial=e ∧ v.final=f := by
  obtain ⟨v,hvi⟩ := finite_factor_comparison M hM τ hτ hfaith heM hfM he hf heq.le
  have hti : τ ⟨v.initial,v.initial_mem⟩=τ ⟨e,heM⟩ := congrArg τ (Subtype.ext hvi)
  have htf : τ ⟨v.final,v.final_mem⟩=τ ⟨f,hfM⟩ :=
    (v.trace_initial_final τ hτ).symm.trans (hti.trans heq)
  have hmem : f-v.final∈M := M.sub_mem hfM v.final_mem
  have hzero : τ ⟨f-v.final,hmem⟩=0 := by
    change τ ((⟨f,hfM⟩ : M)-⟨v.final,v.final_mem⟩)=0
    rw [map_sub,htf,sub_self]
  have hvf := (sub_eq_zero.mp (faithful_projection M τ hfaith hmem
    (v.residual_target_projection hf) hzero)).symm
  exact ⟨v,hvi,hvf⟩

end Kadison.PartialIsometryOrder

namespace Kadison.FiniteFactorMatrices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem partition_representation (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (p : I→M) (hp : ∀ i, IsStarProjection (p i))
    (heq : ∀ i j, τ (p i)=τ (p j))
    (horth : ∀ i j, i≠j → p i*p j=0) (hone : ∑ i,p i=1) :
    ∃ φ : Matrix I I ℂ →⋆ₐ[ℂ] M,
      ∀ i, φ (Matrix.single i i (1:ℂ))=p i := by
  let i₀ : I := Classical.choice inferInstance
  have hv : ∀ i, ∃ v : PartialIsometryOrder.Link M (p i₀) (p i),
      v.initial=p i₀ ∧ v.final=p i := by
    intro i
    exact PartialIsometryOrder.finite_factor_equivalence_link M hM τ hτ hfaith
      (p i₀).property (p i).property
      ((hp i₀).map M.toStarSubalgebra.subtype) ((hp i).map M.toStarSubalgebra.subtype)
      (heq i₀ i)
  choose v hvi hvf using hv
  let u : I→M := fun i => ⟨(v i).val,(v i).mem⟩
  have hsource : ∀ i, star (u i)*u i=p i₀ := fun i => Subtype.ext (hvi i)
  have hfinal : ∀ i, u i*star (u i)=p i := fun i => Subtype.ext (hvf i)
  have hfix : ∀ i, u i*p i₀=u i := by
    intro i
    apply Subtype.ext
    change (v i).val*(p i₀ : H →L[ℂ] H)=(v i).val
    simpa only [hvi i] using (v i).mul_initial
  have htarget : ∀ i, p i*u i=u i := by
    intro i
    apply Subtype.ext
    change (p i : H →L[ℂ] H)*(v i).val=(v i).val
    simpa only [hvf i] using (v i).final_mul
  refine ⟨MatrixUnits.ofPartialIsometries (p i₀) p u hsource hfinal hfix htarget
    (fun i => (hp i).isSelfAdjoint.star_eq) horth hone,?_⟩
  intro i
  rw [MatrixUnits.ofPartialIsometries_single,hfinal]

theorem exists_matrix_embedding (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hone : τ 1=1) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (n : ℕ) (hn : 0<n) :
    ∃ φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] M, Function.Injective φ := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have htr : (τ 1).re=(n:ℝ)*(1/(n:ℝ)) := by rw [hone,Complex.one_re]; field_simp
  obtain ⟨p,hp,horth,hpsum⟩ := NormalGNS.exists_projection_partition M τ hτ hnormal hfaith
    hdiffuse n 1 (IsStarProjection.one _) (by positivity : 0≤1/(n:ℝ)) htr
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have heq : ∀ i j, τ (p i)=τ (p j) := by
    intro i j
    apply Complex.ext
    · rw [(hp i).2.2,(hp j).2.2]
    · exact (τ.map_nonneg (hp i).1.nonneg).2.symm.trans (τ.map_nonneg (hp j).1.nonneg).2
  obtain ⟨φ,_⟩ := partition_representation M hM τ hτ hfaith p (fun i => (hp i).1)
    heq horth hpsum
  have hneq : (0:M)≠1 := by
    intro h
    have hbad := congrArg τ h
    rw [map_zero,hone] at hbad
    exact zero_ne_one hbad
  let : Nontrivial M := ⟨⟨0,1,hneq⟩⟩
  exact ⟨φ,φ.toAlgHom.toRingHom.injective⟩

end Kadison.FiniteFactorMatrices

end

end
end

end OAI
