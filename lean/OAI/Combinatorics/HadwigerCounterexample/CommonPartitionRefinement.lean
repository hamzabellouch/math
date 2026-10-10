import OAI.Combinatorics.HadwigerCounterexample.RectangleComparisons

namespace OAI

/-! # Common Partition Refinement -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}

def refines {r r':ℕ} (Y:Silhouette p N r) (Y':Silhouette p N r') :=
    ∀ l q, ∃ f:Fin r→Fin r',∀ x,Y' l q x=f (Y l q x)

theorem self_refine (Y:Silhouette p N r): refines Y Y :=
  fun _ _=> ⟨id,fun _=>rfl⟩
theorem refines_next {r s t:ℕ} {Y:Silhouette p N r} {X:Silhouette p N s}
    {Z:Silhouette p N t} (h : refines Y X) (hg : refines X Z) :
    refines Y Z := by
  intro l q
  obtain ⟨f,hf⟩:=h l q; obtain ⟨g,hg⟩:=hg l q
  refine ⟨g∘ f,fun x => ?_⟩; rw [hg,hf]; rfl

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def bouquet (f : A→ℕ) := Fintype.card ((i:A)→ Fin (f i))
def bundleY (f:A→ℕ) (w: (i:A)→ Silhouette p N (f i)) :
    Silhouette p N (bouquet f) :=
  fun l q x=> Fintype.equivFin ((i:A)→ Fin (f i)) (fun i=> w i l q x)
theorem bundle_refines (f:A→ℕ) (w:(i:A)→ Silhouette p N (f i)) :
    ∀ i,refines (bundleY f w) (w i) := by
  intro i l q
  let e:= Fintype.equivFin ((i:A)→Fin (f i))
  exact ⟨fun x=> e.symm x i,fun x=>(congr_fun (e.symm_apply_apply (fun i=> w i l q x)) i).symm⟩

def duoY {r s} (Y : Silhouette p N r) (X : Silhouette p N s) :
    Silhouette p N (r*s) :=
  open scoped Classical in fun i q x => finProdFinEquiv (Y i q x,X i q x)
theorem duo_good {r s} (Y : Silhouette p N r) (X : Silhouette p N s) :
    refines (duoY Y X) Y ∧ refines (duoY Y X) X := by
  let e : Fin r × Fin s ≃ Fin (r*s):=finProdFinEquiv
  constructor
  · intro i j; exact ⟨fun k=>(e.symm k).1,fun x=> (congrArg Prod.fst
      (e.symm_apply_apply (Y i j x,X i j x))).symm⟩
  intro i j; exact ⟨fun k=>(e.symm k).2,fun x=> (congrArg Prod.snd
    (e.symm_apply_apply (Y i j x,X i j x))).symm⟩

namespace StatusAnalysis
variable (v : Template p A)

def paletteSize (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] := Fintype.card (B × A → Bool)
theorem buildPalette (N : ℕ) (q : A → F) (w : B → Template.Paint v N) :
    ∃ Y : Silhouette p N (paletteSize A B),∀ i,pigments q Y (w i) := by
  classical
  let E := Fintype.equivFin (B × A→Bool)
  let H (l) (q:F) (x : AtomKey (p:=p) l N) (i:B) (j:A) :=
    if h:v.t j=l then decide ((w i).flies j (h ▸ x)) else false
  let Y : Silhouette p N (paletteSize A B) :=
    fun l q x=> E (fun i=> H l q x i.1 i.2)
  refine ⟨Y,fun i j=>⟨fun x=>(E.symm x (i,j)),fun x=>?_⟩⟩
  change _ ↔ E.symm (E (fun i => H (v.t j) (q j) x i.1 i.2)) (i,j)=true
  rw [Equiv.symm_apply_apply]
  unfold H; rw [dite_eq_left rfl]; simp

omit [Fintype A] [DecidableEq A] in
theorem finerPigment {v : Template p A} {r s:ℕ} (Y : Silhouette p N r)
    (Y' : Silhouette p N s) (h : refines Y' Y) {q} (w : Template.Paint v N)
    (hh : pigments q Y w) : pigments q Y' w := by
  intro i
  obtain ⟨g,hg⟩:=hh i; obtain ⟨f,hf⟩:=h (v.t i) (q i)
  exact ⟨g∘ f,fun x=> (hg x).trans (by rw [hf]; rfl)⟩

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
