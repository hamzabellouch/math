import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.OrientedSubpathRefl

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma no_fixed_qualifying_path (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (hf : NoFixedForbidden w D L a) (s : S.Specification D h L) (b : ℤ)
    (hvertices : ∀ j, ∃ k, b+s.offset j=w.offset k)
    (hsupport : ∀ p : S.Index, (p:ℕ) ∈ s.primeSupport → S.IsFixed w p)
    (htests : ∀ p : S.FixedIndex w, s.ResidueTest p.val b (a p)) : False := by
  let r : S.Residues := mergeResidues w a (fun _ => 0)
  obtain ⟨n,hn⟩ := S.residue_surjective r
  have hn' : S.integerResidues (n.val:ℤ)=r := hn
  have hqual : s.QualifiesAt ((n.val:ℤ)+b) := by
    apply (s.qualifies_iff_residueTests n.val b).mpr
    intro p
    by_cases hp : S.IsFixed w p
    · have he : ((n.val:ℤ):ZMod (p:ℕ))=a ⟨p,hp⟩ := by
        have he := congrFun hn' p
        exact he.trans (merge_fixed w a (fun _ => 0) ⟨p,hp⟩)
      rw [he]
      exact htests ⟨p,hp⟩
    · exact s.test_vacuous p (fun hm => hp (hsupport p hm)) b _
  obtain ⟨t,z,ht,hor,hsup,hqual'⟩ := s.primitive_descent _ hqual
  obtain ⟨j,hj⟩ := Specification.orientedSubpath_start hor
  obtain ⟨k,hk⟩ := hvertices j
  let u : AttachedSpec w D L := ⟨k,t,ht⟩
  have hv : u.vertex=b+z := by change w.offset k=b+z; rw [←hk,←hj]
  apply hf u
  · intro p
    have he : ((n.val:ℤ):ZMod (p.val:ℕ))=a p := by
      have he := congrFun hn' p.val
      simpa only [integerResidues,r,merge_fixed] using he
    rw [←he]
    apply (t.qualifies_iff_residueTests n.val u.vertex).mp
    simpa only [hv,add_assoc] using hqual'
  · intro p hp
    exact hsupport p (hsup hp)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
