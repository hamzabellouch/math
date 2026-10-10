import OAI.AlgebraicGeometry.CharacterVarieties.Seams.BoundaryWords
import OAI.AlgebraicGeometry.CharacterVarieties.Seams.InverseSolution

namespace OAI

/-!
# Surface equations for marked atomic surgery

The marked band boundary words and handle coordinates preserve every
surface equation after the ordered boundary and handle gauges.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression BoundarySurgery
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (q : S)
    (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (J T : D.BandCutUnit (A:=A) q)
private lemma surfaceTarget_eval_count_zero (P : D.Punctures R) (f : F)
    (hf : P.count f = 0) : (D.surfaceTarget P f).eval φ g = 1 := by
  let : IsEmpty (Fin (P.count f)) := by rw [hf]; infer_instance
  simp only [surfaceTarget, Term.eval, mapUnit, Finset.prod_of_isEmpty, inv_one]
  erw [scalarUnit_one, map_one]

lemma cutOldSideValues_replacement (a : Side S arity) :
    D.cutOldSideValues q (fun a=>g (.side a)) (rebaseUnit (D.seamRank q).symm J) a=
      D.bandCutReplacement q g J a := by
  rcases a with ⟨s,c⟩
  cases c with
  | none =>
    by_cases h : s=q
    · subst s
      simp only [cutOldSideValues,bandCutReplacement]
      erw [dite_eq_left rfl, dite_eq_left rfl]
    · have hn : (⟨s,none⟩ : Side S arity)≠⟨q,none⟩ := fun hh => h (congrArg Sigma.fst hh)
      simp only [cutOldSideValues,bandCutReplacement]
      erw [dite_eq_right h, dite_eq_right hn]
  | some i =>
    have hn : (⟨s,some i⟩ : Side S arity)≠⟨q,none⟩ := by
      intro h
      cases h
    simp only [cutOldSideValues,bandCutReplacement]
    erw [dite_eq_right hn]
lemma boundary_cycleWord_raw (u : D.SideValues (R:=A)) (f : F) (b : Fin (D.boundaryCount f)) :
    cycleWord D.ports.vertexAssembly.corners.boundaryNext (D.sideCoefficient u f)
      (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryLength f b)=
      (List.ofFn (fun i => rebaseUnit (congrArg D.rank (D.boundaryFacet f b i))
        (u (D.boundarySide ⟨f,b,i⟩)))).reverse.prod := by
  unfold cycleWord
  apply congrArg (fun l : List (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ => l.reverse.prod)
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [D.boundaryEntry_pow_lt f b k (by simpa using hk),D.sideCoefficient_boundary]
    rfl
lemma bandCutBoundaryWord_cycle (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) (f : F) (b : Fin (D.boundaryCount f)) :
    ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inl b))).eval φ (D.bandCutValues q g J T h)=
      cycleWord D.ports.vertexAssembly.corners.boundaryNext
        (D.sideCoefficient (D.cutOldSideValues q (fun a=>g (.side a)) (rebaseUnit (D.seamRank q).symm J)) f)
        (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryLength f b) := by
  rw [D.bandCutBoundaryWord_long,D.boundary_cycleWord_raw]
  simp_rw [D.cutOldSideValues_replacement]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression
lemma fin_sum_comparison {m n : ℕ} {G : Type*} (a b : Fin (m+n) → G)
    (hl : ∀ i,a (finSumFinEquiv (.inl i))=b (finSumFinEquiv (.inl i)))
    (hr : ∀ j,a (finSumFinEquiv (.inr j))=b (finSumFinEquiv (.inr j))) : ∀ i,a i=b i := by
  intro i
  obtain ⟨z,rfl⟩ := (finSumFinEquiv (m:=m) (n:=n)).surjective i
  cases z with
  | inl i => exact hl i
  | inr j => exact hr j
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
/-- Invertible matrix values on the generators of a marked cut. -/
def MarkedGeneratorValues : Type :=
  (e : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).Generator) →
    (Matrix (Fin ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).generatorRank e))
      (Fin ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).generatorRank e)) A)ˣ

variable (φ : R →+* A) (frames : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).PortFrames (R:=A))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (J T : D.BandCutUnit (A:=A) q)
    (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
def refinedMarkedHandles : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).HandleValues (R:=A) := by
  intro f i b
  cases f with
  | inl f => exact h f i b
  | inr x => exact Fin.elim0 i

def refinedMarkedBandValues :
    D.MarkedGeneratorValues q d hp hc hc' hproper hmax (A:=A) :=
  (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).valuesFromPorts frames
    (D.refinedCutSideValues q d hp hc hc' (fun a=>g (.side a))
      (rebaseUnit (D.seamRank q).symm J)
      (rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T)))
    (D.refinedMarkedHandles q d hp hc hc' hproper hmax h)
lemma refinedMarkedBandWord_old (f : F) (b : Fin (D.boundaryCount f)) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl f) (D.refinedOldBoundary q d f b)).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h)=
      ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inl b))).eval φ
        (D.bandCutValues q g J T h) := by
  have ha := D.refinedMarked_boundaryWord_old q d hp hc hc' hproper hmax φ frames
    (fun a=>g (.side a)) (rebaseUnit (D.seamRank q).symm J)
    (rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T))
    (D.refinedMarkedHandles q d hp hc hc' hproper hmax h) f b
  exact ha.trans (D.bandCutBoundaryWord_cycle q φ g J T h f b).symm
lemma refinedMarkedBandWord_mirror (j : Fin (D.bandCutExtra q (D.bandCutParent q))) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl (D.bandCutParent q)) (D.refinedMirrorBoundary q d)).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h)=
      ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inr j))).eval φ
        (D.bandCutValues q g J T h) := by
  have ha := D.refinedMarked_boundaryWord_mirror q d hp hc hc' hproper hmax φ frames
    (fun a=>g (.side a)) (rebaseUnit (D.seamRank q).symm J)
    (rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T))
    (D.refinedMarkedHandles q d hp hc hc' hproper hmax h)
  exact ha.trans (D.bandCutBoundaryWord_short q φ g J T h j).symm
lemma refinedMarkedBandWord_inl (f : F) (b : Fin ((D.bandCutDiagram q).boundaryCount f)) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl f) b).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h)=
      ((D.bandCutDiagram q).boundaryWord f b).eval φ (D.bandCutValues q g J T h) := by
  refine fin_sum_comparison (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)
    (fun b => ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl f) b).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h))
    (fun b => ((D.bandCutDiagram q).boundaryWord f b).eval φ (D.bandCutValues q g J T h)) ?_ ?_ b
  · intro b
    exact D.refinedMarkedBandWord_old q d hp hc hc' hproper hmax φ frames g J T h f b
  · intro j
    have hf : f=D.bandCutParent q := by
      by_contra hh
      have hj := j.isLt
      change j.val < D.bandCutExtra q _ at hj
      simp only [bandCutExtra,ite_eq_right hh] at hj
      omega
    subst f
    have he : finSumFinEquiv (.inr j)=D.refinedMirrorBoundary q d := by
      apply Fin.ext
      change D.boundaryCount (D.bandCutParent q)+j.val=D.boundaryCount (D.bandCutParent q)
      have hj := j.isLt
      change j.val < D.bandCutExtra q _ at hj
      simp only [bandCutExtra,ite_true] at hj
      omega
    exact (congrArg (fun b => ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl (D.bandCutParent q)) b).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h)) he).trans (D.refinedMarkedBandWord_mirror q d hp hc hc' hproper hmax φ frames g J T h j)
lemma refinedMarkedBandSurface_inl (f : F) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord (.inl f)).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h)=
      ((D.bandCutDiagram q).surfaceWord f).eval φ (D.bandCutValues q g J T h) := by
  have ha := (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord_eval_raw φ
    (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h) (.inl f)
  have hb := (D.bandCutDiagram q).surfaceWord_eval_raw φ (D.bandCutValues q g J T h) f
  refine ha.trans (Eq.trans ?_ hb.symm)
  congr 1
  apply congrArg (fun a : Fin ((D.bandCutDiagram q).boundaryCount f) →
        (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ => (List.ofFn a).prod)
  funext b
  exact D.refinedMarkedBandWord_inl q d hp hc hc' hproper hmax φ frames g J T h f b
lemma refinedMarkedBandSurface_fresh (x : d.atomicBand.FreshStrip) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord (.inr x)).eval φ (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h)=1 := by
  have ha := (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord_eval_raw φ
    (refinedMarkedBandValues D q d hp hc hc' hproper hmax frames g J T h) (.inr x)
  refine ha.trans ?_
  change (List.ofFn (fun k : Fin 0 => _)).prod*(List.ofFn (fun b : Fin 1 => _)).prod=1
  simp only [List.ofFn_zero,List.prod_nil,List.ofFn_succ,List.prod_cons,mul_one,one_mul]
  exact D.refinedMarked_boundaryWord_fresh q d hp hc hc' hproper hmax φ frames
    (fun a=>g (.side a)) (rebaseUnit (D.seamRank q).symm J)
    (rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T))
    (D.refinedMarkedHandles q d hp hc hc' hproper hmax h) x
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))

def refinedMarkedPunctures (P : D.Punctures R) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).Punctures R where
  count := fun f=> match f with | .inl f => P.count f | .inr _ => 0
  scalar := fun f=> match f with | .inl f => P.scalar f | .inr _ => Fin.elim0

variable (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : D.FacetUnit (A:=A) (D.bandCutParent q))
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).PortFrames (R:=A))

def refinedMarkedLiftValues :
    D.MarkedGeneratorValues q d hp hc hc' hproper hmax (A:=A) :=
  let g' := D.bandCutLiftGenerators q φ g b0 t a
  D.refinedMarkedBandValues q d hp hc hc' hproper hmax frames g'
    (D.bandCutChosenJ q φ g' b0 i0 a) (D.bandCutChosenT q φ g' b0 i0 t)
    (D.bandCutRetainedHandles q g' t)

lemma refinedMarkedLiftSurface_inl (f : F) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord (.inl f)).eval φ
      (D.refinedMarkedLiftValues q d hp hc hc' hproper hmax φ g b0 i0 t a frames)=
    ((D.bandCutDiagram q).surfaceWord f).eval φ (D.bandCutLiftValues q φ g b0 i0 t a) :=
  D.refinedMarkedBandSurface_inl q d hp hc hc' hproper hmax φ frames
    (D.bandCutLiftGenerators q φ g b0 t a)
    (D.bandCutChosenJ q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 a)
    (D.bandCutChosenT q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 t)
    (D.bandCutRetainedHandles q (D.bandCutLiftGenerators q φ g b0 t a) t) f

/-- The surface equation on a fresh strip of a marked lift. -/
def MarkedLiftFreshSurface (x : d.atomicBand.FreshStrip) : Prop :=
  ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord (.inr x)).eval φ
    (D.refinedMarkedLiftValues q d hp hc hc' hproper hmax φ g b0 i0 t a frames) = 1

lemma refinedMarkedLiftSurface_fresh (x : d.atomicBand.FreshStrip) :
    D.MarkedLiftFreshSurface q d hp hc hc' hproper hmax φ g b0 i0 t a frames x :=
  D.refinedMarkedBandSurface_fresh q d hp hc hc' hproper hmax φ frames
    (D.bandCutLiftGenerators q φ g b0 t a)
    (D.bandCutChosenJ q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 a)
    (D.bandCutChosenT q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 t)
    (D.bandCutRetainedHandles q (D.bandCutLiftGenerators q φ g b0 t a) t) x

variable [Algebra R A] (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P A)
    (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)

include hb in
/-- Atomic surgery preserves every surface equation after the ordered
boundary and handle gauges. -/
lemma refinedMarkedSolutionSurface (f : D.ports.RefinedBandFacet q d) :
    let v := D.refinedMarkedLiftValues q d hp hc hc' hproper hmax (algebraMap R A)
      x.val.val b0 i0 (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x) frames
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord f).eval (algebraMap R A) v=
      ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceTarget
         (D.refinedMarkedPunctures q d hp hc hc' hproper hmax P) f).eval (algebraMap R A) v := by
  change _ = _
  cases f with
  | inl f =>
    have hs := D.refinedMarkedLiftSurface_inl q d hp hc hc' hproper hmax
      (algebraMap R A) x.val.val b0 i0 (D.bandCutHandleT q hg P x)
      (D.bandCutHandleA q hg P x) frames f
    apply hs.trans
    exact D.bandCutSolutionSurface q hg P x b0 i0 hb f
  | inr z =>
    have hs := D.refinedMarkedLiftSurface_fresh q d hp hc hc' hproper hmax
      (algebraMap R A) x.val.val b0 i0 (D.bandCutHandleT q hg P x)
      (D.bandCutHandleA q hg P x) frames z
    have ht := surfaceTarget_eval_count_zero
      (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) (algebraMap R A)
      (D.refinedMarkedLiftValues q d hp hc hc' hproper hmax (algebraMap R A)
        x.val.val b0 i0 (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x) frames)
      (D.refinedMarkedPunctures q d hp hc hc' hproper hmax P) (.inr z) rfl
    exact hs.trans ht.symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
