import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransport
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalarRename
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalarTree

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistorySymbolicEncoding Arithmetic.HistoryOccurrenceVariables

theorem actualRealHistoryScalar_eq_of_plan (seed : List SourceSlot)
    {l : ℕ} {V W : ℕ → ℕ} {outside : List ℕ}
    (h g : History l) (hs : h.Supported V outside) (gs : g.Supported W outside)
    (hh : TreeSourceLabels seed h) (hg : TreeSourceLabels seed g)
    (hp : plan h hs=plan g gs) (b s : ℕ) (X tb td G : ℝ) (x : Coordinate seed l → ℝ) :
    actualRealHistoryScalar b s X tb td G outside h hs
      (x ∘ (coordinateEquiv seed h hh).symm)=
    actualRealHistoryScalar b s X tb td G outside g gs
      (x ∘ (coordinateEquiv seed g hg).symm) := by
  have hc : normalizedCode seed h hs hh=normalizedCode seed g gs hg := by
    rw [normalizedCode_eq_execute,normalizedCode_eq_execute,hp]
  have he := realHistoryScalar_eq_of_code_plan seed h g hs gs
    (renameTreeExpr (coordinateEquiv seed h hh).symm h (symbolicHistory h hs))
    (renameTreeExpr (coordinateEquiv seed g hg).symm g (symbolicHistory g gs)) hh hg
    (by simpa only [treeCode_renameTreeExpr,normalizedCode] using hc) hp b s X tb td G x
  simpa only [realHistoryScalar_renameTreeExpr,actualRealHistoryScalar] using he

theorem actualRealHistoryScalar_eq_of_coordinates (seed : List SourceSlot)
    {l : ℕ} {V W : ℕ → ℕ} {outside : List ℕ}
    (h g : History l) (hs : h.Supported V outside) (gs : g.Supported W outside)
    (hh : TreeSourceLabels seed h) (hg : TreeSourceLabels seed g)
    (hp : plan h hs=plan g gs) (b s : ℕ) (X tb td G : ℝ)
    (x : Key h → ℝ) (y : Key g → ℝ)
    (hxy : ∀i,x (coordinateEquiv seed h hh i)=y (coordinateEquiv seed g hg i)) :
    actualRealHistoryScalar b s X tb td G outside h hs x=
      actualRealHistoryScalar b s X tb td G outside g gs y := by
  have hx : (y ∘ coordinateEquiv seed g hg) ∘ (coordinateEquiv seed h hh).symm=x := by
    funext i
    obtain ⟨j,rfl⟩ := (coordinateEquiv seed h hh).surjective i
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using (hxy j).symm
  have hy : (y ∘ coordinateEquiv seed g hg) ∘ (coordinateEquiv seed g hg).symm=y := by
    funext i
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  simpa only [hx,hy] using actualRealHistoryScalar_eq_of_plan seed h g hs gs hh hg hp
    b s X tb td G (y ∘ coordinateEquiv seed g hg)

theorem decoded_actualRealHistoryScalar_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a a' : State)
    (c c' : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (haa' : a.frequency=a'.frequency)
    (hcc' : historyFrequencies sources seed V l c=historyFrequencies sources seed V l c')
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hc' : (decodeHistory sources seed V l a' c').Supported V outside)
    (b s : ℕ) (X tb td G : ℝ) (x : Coordinate seed l → ℝ) :
    actualRealHistoryScalar b s X tb td G outside (decodeHistory sources seed V l a c) hc
      (x ∘ (coordinateEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha)).symm)=
    actualRealHistoryScalar b s X tb td G outside (decodeHistory sources seed V l a' c') hc'
      (x ∘ (coordinateEquiv seed _ (decoded_tree_source_labels sources seed V l a' c' ha')).symm) :=
  actualRealHistoryScalar_eq_of_plan seed _ _ hc hc'
    (decoded_tree_source_labels sources seed V l a c ha)
    (decoded_tree_source_labels sources seed V l a' c' ha')
    (decoded_plan_eq sources seed V outside l a a' c c' ha ha' haa' hcc' hc hc')
    b s X tb td G x

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
