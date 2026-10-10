import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.PolarSupport

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def supportSpace (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x}).topologicalClosure

instance (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) : CompleteSpace (supportSpace M e) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma generator_mem (M : VonNeumannAlgebra H) (e : H →L[ℂ] H)
    {a : H →L[ℂ] H} (ha : a∈M) (ξ : H) : a (e ξ)∈supportSpace M e :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,ha,ξ,rfl⟩)

lemma supportSpace_invariant (M : VonNeumannAlgebra H) (e B : H →L[ℂ] H)
    (hB : ∀ a∈M, ∀ ξ : H, B (a (e ξ))∈supportSpace M e) :
    ∀ x∈supportSpace M e, B x∈supportSpace M e := by
  intro x hx
  apply closure_minimal (t := {x | B x∈supportSpace M e}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage B.continuous) hx
  exact (Submodule.span_le.mpr (by rintro y ⟨a,ha,ξ,rfl⟩; exact hB a ha ξ) :
    Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x} ≤ (supportSpace M e).comap B.toLinearMap)

lemma invariant_of_mem (M : VonNeumannAlgebra H) (e : H →L[ℂ] H)
    {B : H →L[ℂ] H} (hB : B∈M) :
    ∀ x∈supportSpace M e, B x∈supportSpace M e := by
  apply supportSpace_invariant
  intro a ha ξ
  exact generator_mem M e (M.mul_mem hB ha) ξ

lemma invariant_of_commutant (M : VonNeumannAlgebra H) {e B : H →L[ℂ] H}
    (he : e∈M) (hB : B∈Set.centralizer (M : Set (H →L[ℂ] H))) :
    ∀ x∈supportSpace M e, B x∈supportSpace M e := by
  apply supportSpace_invariant
  intro a ha ξ
  have hba : B*a=a*B := (hB a ha).symm
  have hbe : B*e=e*B := (hB e he).symm
  change B (a (e ξ))∈supportSpace M e
  rw [show B (a (e ξ))=a (B (e ξ)) from congrArg (fun T : H →L[ℂ] H => T (e ξ)) hba,
    show B (e ξ)=e (B ξ) from congrArg (fun T : H →L[ℂ] H => T ξ) hbe]
  exact generator_mem M e ha (B ξ)

lemma projection_commutant (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) :
    (supportSpace M e).starProjection∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
  intro a ha
  exact (projection_commutes_of_invariant _ a (invariant_of_mem M e ha)
    (invariant_of_mem M e (M.star_mem' ha))).symm

lemma projection_mem (M : VonNeumannAlgebra H) {e : H →L[ℂ] H} (he : e∈M) :
    (supportSpace M e).starProjection∈M := by
  change (supportSpace M e).starProjection∈M.carrier
  rw [←M.centralizer_centralizer']
  intro a ha
  have hsa : star a∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    simpa only [star_mul,star_star] using congrArg star (ha (star b) (M.star_mem' hb)).symm
  exact (projection_commutes_of_invariant _ a (invariant_of_commutant M he ha)
    (invariant_of_commutant M he hsa)).symm

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  ∀ z∈M, z∈Set.centralizer (M : Set (H →L[ℂ] H)) → ∃ c : ℂ, z=c • (1 : H →L[ℂ] H)

lemma centralSupport_eq_one (M : VonNeumannAlgebra H) (hf : IsFactor M)
    {e : H →L[ℂ] H} (he : e∈M) (hne : e≠0) :
    (supportSpace M e).starProjection=1 := by
  obtain ⟨c,hc⟩ := hf _ (projection_mem M he) (projection_commutant M e)
  have hex : ∃ ξ : H, e ξ≠0 := by
    by_contra! h
    apply hne
    ext ξ
    exact h ξ
  obtain ⟨ξ,hξ⟩ := hex
  have hg : e ξ∈supportSpace M e := by simpa using generator_mem M e M.one_mem ξ
  have hfix := Submodule.starProjection_eq_self_iff.mpr hg
  rw [hc] at hfix
  change c • e ξ=e ξ at hfix
  have hzero : (c-1) • e ξ=0 := by rw [sub_smul,one_smul,hfix,sub_self]
  have hcone : c=1 := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hξ)
  rw [hc,hcone,one_smul]

theorem exists_nonzero_corner (M : VonNeumannAlgebra H) (hf : IsFactor M)
    {e f : H →L[ℂ] H} (he : e∈M) (hee : e≠0) (hff : f≠0) :
    ∃ a∈M, f*a*e≠0 := by
  by_contra! h
  have hz : ∀ x∈supportSpace M e, f x=0 := by
    intro x hx
    apply closure_minimal (t := {x | f x=0}) ?_
      (isClosed_eq f.continuous continuous_const) hx
    have hspan : Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x} ≤ LinearMap.ker f.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨a,ha,ξ,rfl⟩
      exact congrArg (fun T : H →L[ℂ] H => T ξ) (h a ha)
    exact hspan
  apply hff
  ext x
  have hm := (supportSpace M e).starProjection_apply_mem x
  rw [centralSupport_eq_one M hf he hee] at hm
  exact hz x hm

theorem exists_linking_partialIsometry (M : VonNeumannAlgebra H) (hf : IsFactor M)
    {e f : H →L[ℂ] H} (he : e∈M) (hfM : f∈M)
    (hpe : IsStarProjection e) (hpf : IsStarProjection f) (hne : e≠0) (hnf : f≠0) :
    ∃ v∈M, v≠0 ∧ v*star v*v=v ∧ star v*v≤e ∧ v*star v≤f := by
  obtain ⟨a,ha,hna⟩ := exists_nonzero_corner M hf he hne hnf
  let x := f*a*e
  have hx : x∈M := M.mul_mem (M.mul_mem hfM ha) he
  have hfx : f*x=x := by dsimp only [x]; rw [←mul_assoc,←mul_assoc,hpf.isIdempotentElem.eq]
  have hxe : x*e=x := by dsimp only [x]; rw [mul_assoc,hpe.isIdempotentElem.eq]
  refine ⟨Polar.partialIsometry x,Polar.partialIsometry_mem_vonNeumann M hx,?_,
    Polar.partialIsometry_triple x,?_,?_⟩
  · intro hzero
    apply hna
    have hfact := Polar.factorization x
    rw [hzero,zero_mul] at hfact
    exact hfact.symm
  · rw [Polar.partialIsometry_initial]
    exact Polar.rightSupport_le x e hpe hxe
  · exact Polar.leftSupport_le x f hpf hfx

end Kadison.FactorCorner

end

end
end

end OAI
