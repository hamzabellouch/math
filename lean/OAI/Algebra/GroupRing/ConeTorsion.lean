import Mathlib
import OAI.Algebra.GroupRing.ConeArea
import OAI.Algebra.GroupRing.RelationTorsion

namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeTorsion
open scoped Classical
open PortSubdivision GraphPresentation GraphConePresentation
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
local notation "letters" => ConeSigned.freeLetter ∘ label
include hl in
lemma relations_eq : AlgebraicPictures.relations (ConeArea.words Γ R label)=
    GraphConePresentation.relations Γ letters R := by
  change Set.range (fun e=>FreeGroup.mk (ConeArea.words Γ R label e))=Set.range _
  congr 1
  funext e
  exact ConeArea.words_mk Γ R label hl e
include hl in
lemma total_zero
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced)
    (ts : List (AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)))
    (he : FreeGroup.mk (AlgebraicPictures.word (ConeArea.words Γ R label) ts)=1) :
    RelationArea.total (ConeArea.words Γ R label) ts=0 := by
  have h := ConeArea.identity_zero Γ R label hl hex ts he
  unfold RelationArea.total RelationArea.term RelationArea.q RelationArea.G
  rw [relations_eq Γ R label hl]
  exact h
include hl in
theorem cone_torsion_free
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced) :
    ∀ (g : GraphConePresentation.Group Γ letters R) (n : ℕ), 0 < n → g ^ n = 1 → g = 1 := by
  have h := RelationTorsion.torsion_free (ConeArea.words Γ R label) (total_zero Γ R label hl hex)
  unfold RelationArea.G at h
  rw [relations_eq Γ R label hl] at h
  exact h
include hl in
theorem graph_torsion_free (hbase : ∀v,R.base (R.base v)=R.base v)
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced) :
    ∀ (g : GraphPresentation.Group Γ letters R) (n : ℕ), 0 < n → g ^ n = 1 → g = 1 := by
  intro g n hn he
  let e := GraphConePresentation.equivalence Γ letters R (ConeArea.letters_reverse Γ label hl) hbase
  apply e.injective
  rw [map_one]
  exact cone_torsion_free Γ R label hl hex (e g) n hn (by rw [←map_pow,he,map_one])
end
end TorsionFreeZeroDivisors.ConeTorsion

end



end OAI
