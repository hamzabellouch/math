import OAI.GroupTheory.FiniteLattice.CommonCoreStatement
import OAI.GroupTheory.FiniteLattice.AmbientCore
import OAI.GroupTheory.FiniteLattice.CanonicalQuotient
import OAI.GroupTheory.FiniteLattice.InnerAutomorphisms

namespace OAI

namespace FiniteLattice.CommonCore

/-- Compatible extensions with relative cores mapping over the inner automorphisms
glue uniquely over their generated group, whose core has the same image property. -/
theorem common_core (K T : Type*) [Group K] [Finite K] [Group T] [IsSimpleGroup T]
    (ι : Type*) [Finite ι] [Nonempty ι]
    (A : Subgroup K) (U : ι → Subgroup K) (hAU : ∀ i, A ≤ U i)
    (alpha : A →* MulAut T) (beta : ∀ i, U i →* MulAut T) :
    Statement K T ι A U hAU alpha beta := by
  classical
  intro hna hgen hext hcore
  let J := SimpleInnerAutomorphisms.inner T
  let : J.Normal := SimpleInnerAutomorphisms.inner_normal T
  let : Group.IsPerfect J := SimpleInnerAutomorphisms.inner_perfect hna
  obtain ⟨Q, hQN, hQ, hQKN, hLKN, _hUnorm⟩ :=
    exists_common_normal_preimage A U hAU hgen alpha beta hext J hcore
  let : Q.Normal := hQN
  let QK := Q.map A.subtype
  let LK := (Q ⊓ alpha.ker).map A.subtype
  let : QK.Normal := hQKN
  let : LK.Normal := hLKN
  have hQA : QK ≤ A := by
    rintro _ ⟨q, _, rfl⟩
    exact q.property
  have hQcore : QK ≤ A.normalCore := Subgroup.normal_le_normalCore.mpr hQA
  have hfirst : J ≤ (A.normalCore.comap A.subtype).map alpha := by
    rw [← hQ]
    apply Subgroup.map_mono
    intro q hq
    exact hQcore (show A.subtype q ∈ QK from ⟨q, hq, rfl⟩)
  refine ⟨hfirst, ?_⟩
  let e : T ≃* J := SimpleInnerAutomorphisms.innerEquiv hna
  let f : Q →* T := preimageMap alpha Q J hQ e
  let theta : (Q ⧸ f.ker) ≃* T := canonicalTheta alpha Q J hQ e
  let emb : Q ≃* QK := Q.equivMapOfInjective A.subtype Subtype.val_injective
  let action : K →* MulAut Q := transportAction
    (MulAut.conjNormal (H := QK)) emb.symm
  have hemb (z : QK) : A.subtype ((emb.symm z : Q) : A) = (z : K) := by
    have he := congrArg (fun w : QK => (w : K)) (emb.apply_symm_apply z)
    exact he
  have haction (k : K) (q : Q) : A.subtype (action k q : A) =
      k * A.subtype (q : A) * k⁻¹ := by
    change A.subtype ((emb.symm (MulAut.conjNormal k (emb q)) : Q) : A) = _
    rw [hemb, MulAut.conjNormal_apply]
    rfl
  have hfker (q : Q) : q ∈ f.ker ↔ alpha (q : A) = 1 :=
    preimageMap_ker_iff alpha Q J hQ e q
  have hker_stable (k : K) (q : Q) (hq : q ∈ f.ker) : action k q ∈ f.ker := by
    have hqL : A.subtype (q : A) ∈ LK :=
      ⟨(q : A), ⟨q.property, (hfker q).mp hq⟩, rfl⟩
    have hconj := hLKN.conj_mem _ hqL k
    rw [← haction] at hconj
    obtain ⟨z, hz, hze⟩ := hconj
    have hze' : z = (action k q : A) := Subtype.val_injective hze
    apply (hfker _).mpr
    rw [← hze']
    exact hz.2
  have hker (k : K) : f.ker.map (action k).toMonoidHom = f.ker := by
    apply le_antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact hker_stable k q hq
    · intro q hq
      refine ⟨(action k).symm q, ?_, (action k).apply_symm_apply q⟩
      have hinv : (action k).symm = action k⁻¹ := (map_inv action k).symm
      rw [hinv]
      exact hker_stable k⁻¹ q hq
  let b : K →* MulAut T := transportAction (quotientAction action f.ker hker) theta
  have htheta (q : Q) : theta (QuotientGroup.mk' f.ker q) = f q :=
    canonicalTheta_mk alpha Q J hQ e q
  have hb (k : K) (q : Q) : b k (f q) = f (action k q) := by
    rw [← htheta q]
    change theta (QuotientGroup.congr f.ker f.ker (action k) (hker k)
      (theta.symm (theta (QuotientGroup.mk' f.ker q)))) = _
    rw [theta.symm_apply_apply]
    exact htheta (action k q)
  have hfconj (q : Q) : MulAut.conj (f q) = alpha (q : A) := by
    rw [← SimpleInnerAutomorphisms.innerEquiv_apply hna (f q)]
    change ((e (e.symm _) : J) : MulAut T) = _
    rw [e.apply_symm_apply]
  have hbrestrict (i : ι) (u : U i) : b u = beta i u := by
    apply MulEquiv.ext
    intro t
    obtain ⟨q, rfl⟩ := preimageMap_surjective alpha Q J hQ e t
    rw [hb]
    apply SimpleInnerAutomorphisms.conj_injective hna
    rw [hfconj, ← SimpleInnerAutomorphisms.conjugate_conj T, hfconj]
    exact restriction_conjugation A (U i) (hAU i) alpha (beta i) (hext i)
      u (q : A) (action u q : A) (haction u q)
  refine ⟨b, hbrestrict, ?_⟩
  intro b' hb'
  apply generated_hom_unique U hgen
  intro i u
  exact (hb' i u).trans (hbrestrict i u).symm

end FiniteLattice.CommonCore

end OAI
