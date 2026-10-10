import OAI.Probability.DilutedSpin.MarkerGeometry
import OAI.Probability.DilutedSpin.MarkerPhysicalBridge

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

lemma markerFresh_split (A : PrescribedTree n) (r : ℕ) (c d : A.Leaf) :
    splitDepth (stem (unary A) r) ((markerOldIndex A r).symm c) ((markerOldIndex A r).symm d)=
      splitDepth (stem (doubled A) r) (markerFresh A r c) (markerFresh A r d) := by
  have hS := splitDepth_stem (unary A) r (unaryLeafEquiv A c) (unaryLeafEquiv A d)
  have hQ := splitDepth_stem (doubled A) r ⟨1,c⟩ ⟨1,d⟩
  exact hS.trans ((congrArg (fun x => x+r)
    ((split_unary A c d).trans (split_doubled_same A c d 1).symm)).trans hQ.symm)

noncomputable def markerColorEquiv (A : PrescribedTree n) :
    Fin (Fintype.card A.Leaf) ≃ A.Leaf := (Fintype.equivFin A.Leaf).symm

noncomputable def markerColorTarget (A : PrescribedTree n) (r : ℕ) :
    Option (Fin (Fintype.card A.Leaf)) → (stem (markerFork A) r).Leaf :=
  markerTarget A r ∘ (Equiv.optionCongr (markerColorEquiv A))

noncomputable def markerColorFresh (A : PrescribedTree n) (r : ℕ) :
    Fin (Fintype.card A.Leaf) → (stem (doubled A) r).Leaf :=
  markerFresh A r ∘ markerColorEquiv A

noncomputable def markerColorOld (A : PrescribedTree n) (r : ℕ) :
    Fin (Fintype.card A.Leaf) ≃ (stem (unary A) r).Leaf :=
  (markerColorEquiv A).trans (markerOldIndex A r).symm

lemma markerColorTarget_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (markerColorTarget A r) :=
  (markerTarget_bijective A r).comp (Equiv.optionCongr (markerColorEquiv A)).bijective

lemma markerColorJoint_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (Sum.elim (markerOld A r) (markerColorFresh A r)) := by
  have h := (markerJoint_bijective A r).comp
    (Equiv.sumCongr (Equiv.refl (stem (unary A) r).Leaf) (markerColorEquiv A)).bijective
  convert h using 1
  funext x
  cases x <;> rfl

lemma markerColorTarget_split (A : PrescribedTree n) (r : ℕ)
    (a : (stem (unary A) r).Leaf) (x y : Option (Fin (Fintype.card A.Leaf))) :
    splitDepth (stem (markerFork A) r) (markerColorTarget A r x) (markerColorTarget A r y)=
      splitDepth (stem (doubled A) r)
        (Option.elim' (markerOld A r a) (markerColorFresh A r) x)
        (Option.elim' (markerOld A r a) (markerColorFresh A r) y) := by
  have h := markerTarget_split A r a
    (Equiv.optionCongr (markerColorEquiv A) x) (Equiv.optionCongr (markerColorEquiv A) y)
  cases x <;> cases y <;> exact h

lemma marker_spatialProduct {Ω C D : Type} [Fintype Ω] [Fintype C] [Fintype D]
    (e : C ≃ D) (V : FinitePath Ω n → Fin N → ℝ) (x : Option C → FinitePath Ω n) :
    spatialProduct (fun c y i => match c with | none => 1 | some _ => V y i) x =
      spatialProduct (fun _ : D => V) (fun d => x (some (e.symm d))) := by
  classical
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fintype.prod_option,one_mul]
  exact Fintype.prod_equiv e (fun c => V (x (some c)) i)
    (fun d => V (x (some (e.symm d))) i) (fun c => by simp)

/-- Concrete marker geometry at every preceding depth. In particular all
bijections and separation requirements of the history identity are produced,
not standing assumptions. The color count is positive for every tree. -/
theorem concrete_marker_covariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (A : PrescribedTree n) (r : ℕ) (a : (stem (unary A) r).Leaf)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r)) (m : Fin (n+1+r+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (n+1+r))=1)
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ) :
    matrixRootCovariance μ Ω (stem (markerFork A) r) (stem (unary A) r)
      (markerColorTarget A r) K m
      (List.ofFn (fun c : Fin (Fintype.card A.Leaf) => (some c : Option (Fin (Fintype.card A.Leaf))))).reverse a
      (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => V z x i))
      (fun z => treeOverlap (stem (unary A) r) (V z)) =
    partialKappa (stem (markerFork A) r) m (Finset.univ.image (markerColorTarget A r)) *
      ((∫ z, ((stem (doubled A) r).sampleLaw (K z)).expect (fun w =>
        spatialProduct (fun _ : (stem (unary A) r).Leaf => V z)
          (fun d => (stem (doubled A) r).pathAt (markerOld A r d) w) *
        spatialProduct (fun _ : (stem (unary A) r).Leaf => V z)
          (fun d => (stem (doubled A) r).pathAt
            (markerColorFresh A r ((markerColorOld A r).symm d)) w)) ∂μ) -
      (∫ z, ((stem (unary A) r).sampleLaw (K z)).expect
        (treeOverlap (stem (unary A) r) (V z)) ∂μ)^2) := by
  classical
  have h := marker_root_covariance μ Ω (stem (unary A) r) (stem (markerFork A) r)
    (stem (doubled A) r) a (markerColorOld A r) (markerColorTarget A r)
    (markerColorTarget_bijective A r) (markerOld A r) (markerColorFresh A r)
    (markerColorJoint_bijective A r) (markerOld_split A r)
    (fun c d => markerFresh_split A r (markerColorEquiv A c) (markerColorEquiv A d))
    (markerColorTarget_split A r a)
    (fun c d => marker_split_separation A r a d (markerColorEquiv A c)) K m hm hp hend
    ((List.ofFn (fun c : Fin (Fintype.card A.Leaf) => c)).reverse)
    (by
      rw [List.nodup_reverse, List.nodup_ofFn]
      exact Function.injective_id) (by
      ext c
      simp only [List.mem_toFinset,List.mem_reverse,List.mem_ofFn,Finset.mem_univ,iff_true]
      exact ⟨c,rfl⟩)
    (fun z => spatialProduct (fun _ : (stem (unary A) r).Leaf => V z))
  simp only [List.map_reverse,List.map_ofFn,Function.comp_def] at h
  simp_rw [← marker_spatialProduct (markerColorOld A r) (V _), ← treeOverlap_eq_spatialProduct] at h
  convert h using 1
  congr 2
  funext z x
  dsimp only [spatialProduct]
  congr 3
  funext i
  apply Finset.prod_congr rfl
  intro c hc
  cases c <;> rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
