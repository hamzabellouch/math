import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeAtoms
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeRetractions
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

section

/-! # Finite closed grids of cubes with controlled mesh -/

namespace Thomason.Construction.CubeGrid

open Topology

noncomputable section

def cell (n m : ℕ) (k : Fin n → Fin (m+1)) : Set (Fin n → unitInterval) :=
  Set.ofPred (fun x => ∀ i,
    (k i).val / ((m : ℝ)+1) ≤ (x i : ℝ) ∧
      (x i : ℝ) ≤ ((k i).val+1) / ((m : ℝ)+1))

theorem cell_isClosed (n m : ℕ) (k : Fin n → Fin (m+1)) : IsClosed (cell n m k) := by
  have he : cell n m k = ⋂ i : Fin n, Set.ofPred (fun x : Fin n → unitInterval =>
      (k i).val / ((m : ℝ)+1) ≤ (x i : ℝ) ∧
        (x i : ℝ) ≤ ((k i).val+1) / ((m : ℝ)+1)) := by
    ext x
    simp only [cell, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro i
  have hc : Continuous (fun x : Fin n → unitInterval => (x i : ℝ)) :=
    (continuous_apply i).subtype_val
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem cell_nonempty (n m : ℕ) (k : Fin n → Fin (m+1)) : (cell n m k).Nonempty := by
  have hm : (0 : ℝ) < (m : ℝ)+1 := by positivity
  let x : Fin n → unitInterval := fun i =>
    ⟨(k i).val / ((m : ℝ)+1), div_nonneg (by positivity) hm.le,
      (div_le_one hm).mpr (by exact_mod_cast (k i).isLt.le)⟩
  refine ⟨x, fun i => ⟨le_rfl, ?_⟩⟩
  apply div_le_div_of_nonneg_right _ hm.le
  linarith

theorem interval_mem (m : ℕ) (x : unitInterval) :
    ∃ k : Fin (m+1), k.val / ((m : ℝ)+1) ≤ (x : ℝ) ∧
      (x : ℝ) ≤ (k.val+1) / ((m : ℝ)+1) := by
  have hm : (0 : ℝ) < (m : ℝ)+1 := by positivity
  by_cases hx : (x : ℝ) = 1
  · refine ⟨⟨m, Nat.lt_succ_self m⟩, ?_, ?_⟩
    · rw [hx]
      exact (div_le_one hm).mpr (by linarith)
    · simp [hx, hm.ne']
  · have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx
    have ht : ((m : ℝ)+1) * (x : ℝ) < (m : ℝ)+1 := by nlinarith
    have hk : Nat.floor (((m : ℝ)+1) * (x : ℝ)) < m+1 := by
      apply (Nat.floor_lt (mul_nonneg hm.le x.property.1)).mpr
      simpa using ht
    refine ⟨⟨_, hk⟩, ?_, ?_⟩
    · apply (div_le_iff₀ hm).mpr
      simpa [mul_comm] using Nat.floor_le (mul_nonneg hm.le x.property.1)
    · apply (le_div_iff₀ hm).mpr
      exact le_of_lt (by simpa [mul_comm] using Nat.lt_floor_add_one (((m : ℝ)+1) * (x : ℝ)))

/-- The finite closed grid covers the entire cube. -/
theorem cover (n m : ℕ) : ⋃ k, cell n m k = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  choose k hk using fun i : Fin n => interval_mem m (x i)
  exact Set.mem_iUnion.mpr ⟨k, hk⟩

/-- In the product metric every grid cell has mesh at most `1/(m+1)`. -/
theorem cell_diam (n m : ℕ) (k : Fin n → Fin (m+1)) :
    Metric.diam (cell n m k) ≤ 1 / ((m : ℝ)+1) := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hx := hx i
  have hy := hy i
  change |(x i : ℝ) - (y i : ℝ)| ≤ 1 / ((m : ℝ)+1)
  have hw : ((k i).val+1) / ((m : ℝ)+1) - (k i).val / ((m : ℝ)+1) =
      1 / ((m : ℝ)+1) := by ring
  apply abs_le.mpr
  constructor <;> linarith

end

end Thomason.Construction.CubeGrid

end

section

/-! # Surjectivity of the actual standard realization prism -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- The maximal simplices cover the actual realization of the standard prism. -/
theorem exists_maximal_prism_simplex (n : ℕ) (x : SSet.toTop.obj (prism n)) :
    ∃ (j : Fin (n+1)) (u : StdSimplex ℝ (Fin (n+2))),
      (RealizationPrism.leg (prism n) (simplexIndex j)).hom (ULift.up u) = x := by
  have hx : x ∈ Set.range (SSet.toTop.map
      (SSet.prodStdSimplex₁.filtration (Fin.last n)).ι).hom := by
    rw [RealizationPrism.mem_range_inclusion_iff, SSet.prodStdSimplex₁.filtration_last]
    exact le_top
  rw [SSet.prodStdSimplex₁.filtration, RealizationPrism.range_iSup_inclusion] at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  let f := SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j.val).val
  have hR : Set.range (SSet.toTop.map f).hom =
      Set.range (SSet.toTop.map (SSet.Subcomplex.ofSimplex
        (SSet.prodStdSimplex₁.nonDegenerateEquiv j.val).val).ι).hom := by
    have hf : SSet.Subcomplex.range f = SSet.Subcomplex.ofSimplex
        (SSet.prodStdSimplex₁.nonDegenerateEquiv j.val).val :=
      (SSet.Subcomplex.range_eq_ofSimplex f).trans
        (congrArg SSet.Subcomplex.ofSimplex (SSet.yonedaEquiv.apply_symm_apply _))
    rw [← hf]
    exact RealizationPrism.range_realized_map f
  rw [← hR] at hj
  obtain ⟨z, hz⟩ := hj
  refine ⟨j.val, (SimplexCategory.mk (n+1)).toTopHomeo z, ?_⟩
  change (SSet.toTop.map f).hom
    ((SSet.toTopSimplex.inv.app (.mk (n+1))).hom
      (ULift.up ((SimplexCategory.mk (n+1)).toTopHomeo z))) = x
  have he : (SSet.toTopSimplex.inv.app (.mk (n+1))).hom
      (ULift.up ((SimplexCategory.mk (n+1)).toTopHomeo z)) = z :=
    (SimplexCategory.mk (n+1)).toTopHomeo.symm_apply_apply z
  rw [he]
  exact hz

/-- Every point of the standard simplicial prism is obtained by the constructed
continuous prism map, including points on degenerate and shared faces. -/
theorem standardPrism_surjective (n : ℕ) : Function.Surjective (standardPrism n) := by
  intro x
  obtain ⟨j, u, hu⟩ := exists_maximal_prism_simplex n x
  obtain ⟨p, hp⟩ := chart_surjective j u
  refine ⟨p.val, ?_⟩
  rw [standardPrism_on_region j p.val p.property]
  change (RealizationPrism.leg (prism n) (simplexIndex j)).hom (ULift.up (chart j p)) = x
  rw [hp]
  exact hu

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # The actual realization cylinder is the topological cylinder

The constructed comparison is a homeomorphism. Its inverse is given by the
first realized projection and the affine interval coordinate.
-/

namespace Thomason.Construction.RealizedCylinder

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial

noncomputable section

/-- The comparison covers every point of the actual simplicial cylinder. -/
theorem comparison_surjective (K : SSet.{0}) : Function.Surjective (comparison K).hom := by
  intro z
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation (K ⊗ Δ[1]) z
  let f := j.hom ≫ fst K Δ[1]
  let u := j.hom ≫ snd K Δ[1]
  let l : (Δ[j.left.len] : SSet.{0}) ⟶ Δ[j.left.len] ⊗ Δ[1] := lift (𝟙 _) u
  have hl : l ≫ f ▷ Δ[1] = j.hom := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  let v := (SSet.toTop.map l).hom ((SSet.toTopSimplex.inv.app j.left).hom p)
  obtain ⟨⟨x, t⟩, hxt⟩ := PrismBarycentric.standardPrism_surjective j.left.len v
  refine ⟨((RealizationPrism.leg K (CostructuredArrow.mk f)).hom (ULift.up x), t), ?_⟩
  refine (comparison_leg K (CostructuredArrow.mk f) (ULift.up x) t).trans ?_
  change (SSet.toTop.map (f ▷ Δ[1])).hom
    (PrismBarycentric.standardPrism j.left.len (x, t)) = _
  rw [hxt]
  change ((SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map l) ≫
    SSet.toTop.map (f ▷ Δ[1])).hom p = _
  rw [Category.assoc, ← SSet.toTop.map_comp, hl]
  rfl

/-- The two actual realized cylinder coordinates. -/
def coordinates (K : SSet.{0}) :
    SSet.toTop.obj (K ⊗ Δ[1]) ⟶ TopologicalInterval.cylinder.obj (SSet.toTop.obj K) :=
  TopCat.ofHom {
    toFun z := ((SSet.toTop.map (fst K Δ[1])).hom z,
      PrismBarycentric.realizationTime.hom ((SSet.toTop.map (snd K Δ[1])).hom z))
    continuous_toFun := (SSet.toTop.map (fst K Δ[1])).hom.continuous.prodMk
      (PrismBarycentric.realizationTime.hom.continuous.comp
        (SSet.toTop.map (snd K Δ[1])).hom.continuous) }

/-- The explicit coordinate map is a left inverse to the comparison. -/
theorem coordinates_comparison (K : SSet.{0}) :
    Function.LeftInverse (coordinates K).hom (comparison K).hom := by
  rintro ⟨x, t⟩
  apply Prod.ext
  · exact comparison_first K x t
  · exact comparison_time K x t

/-- Surjectivity gives the other inverse equation for the same explicit map. -/
theorem comparison_coordinates (K : SSet.{0}) :
    Function.RightInverse (coordinates K).hom (comparison K).hom :=
  (coordinates_comparison K).rightInverse_of_surjective (comparison_surjective K)

/-- The natural comparison is an actual homeomorphism, with the proved
coordinate formulas as its inverse. -/
def cylinderHomeomorph (K : SSet.{0}) :
    TopologicalInterval.cylinder.obj (SSet.toTop.obj K) ≃ₜ SSet.toTop.obj (K ⊗ Δ[1]) where
  toFun := (comparison K).hom
  invFun := (coordinates K).hom
  left_inv := coordinates_comparison K
  right_inv := comparison_coordinates K
  continuous_toFun := (comparison K).hom.continuous
  continuous_invFun := (coordinates K).hom.continuous

/-- The same cylinder comparison as an isomorphism of actual topological spaces. -/
def cylinderIso (K : SSet.{0}) :
    TopologicalInterval.cylinder.obj (SSet.toTop.obj K) ≅ SSet.toTop.obj (K ⊗ Δ[1]) :=
  TopCat.isoOfHomeo (cylinderHomeomorph K)

end

end Thomason.Construction.RealizedCylinder

end

section

/-! # Bounded lifts of all triple-cylinder atoms in the original pushout -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

theorem cylinderAtom_in_globe {n k p : ℕ} (hkn : k < n)
    (b : (cylinderOrderedAtomBasis hkn).Index p) :
    ∃ (i : Fin 3) (x : Cell (rightCylinder (DirectedGlobeComplex.complex n))),
      (rightCylinder (DirectedGlobeComplex.complex n)).realization.DimensionLE p x ∧
      (RightCylinder.map (inclusion hkn i)).realization.toFun x =
        (cylinderOrderedAtomBasis hkn).atom p b := by
  cases b with
  | endpoint a b =>
    let c : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p :=
      .endpoint a ⟨b.val.2, b.property.1⟩
    refine ⟨b.val.1, (DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p c,
      (DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom_dimension p c, ?_⟩
    have he : globeCylinderIndex hkn b.val.1 c = .endpoint a b :=
      congrArg (RightCylinderBasis.Basis.endpoint a) (embed_self hkn b)
    exact (globeCylinder_atom hkn b.val.1 c).trans
      (congrArg ((cylinderOrderedAtomBasis hkn).atom p) he)
  | @mixed q b =>
    let c : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index (q+1) :=
      .mixed ⟨b.val.2, b.property.1⟩
    refine ⟨b.val.1, (DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom (q+1) c,
      (DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom_dimension (q+1) c, ?_⟩
    have he : globeCylinderIndex hkn b.val.1 c = .mixed b :=
      congrArg RightCylinderBasis.Basis.mixed (embed_self hkn b)
    exact (globeCylinder_atom hkn b.val.1 c).trans
      (congrArg ((cylinderOrderedAtomBasis hkn).atom (q+1)) he)

end Thomason.Construction.TripleGlobeBasis

namespace Thomason.Construction.StrictOmegaCategory.TripleGlobeCylinder

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev model := GrayChainExtension.model
abbrev Source (n k : ℕ) : StrictOmegaCategory.{0} := TripleGlobe.ImageSource model n k
abbrev PieceCells (n k : ℕ) :=
  model.obj (PastingGlobe.category n n k) ⊕ model.obj (Globe.category n)

def comparison (n k : ℕ) : Source n k ⟶ model.obj (TripleGlobe.category n k) :=
  pushout.desc (model.map (TripleGlobe.pair n k)) (model.map (TripleGlobe.inclusion n k 2)) (by
    rw [← model.map_comp, ← model.map_comp]
    exact congrArg model.map (pushout.condition (f := TripleGlobe.bridge n k)
      (g := Globe.faceMap false k n)))

theorem inl_comparison (n k : ℕ) :
    pushout.inl (model.map (TripleGlobe.bridge n k)) (model.map (Globe.faceMap false k n)) ≫
      comparison n k = model.map (TripleGlobe.pair n k) := by
  unfold comparison
  exact pushout.inl_desc _ _ _

theorem inr_comparison (n k : ℕ) :
    pushout.inr (model.map (TripleGlobe.bridge n k)) (model.map (Globe.faceMap false k n)) ≫
      comparison n k = model.map (TripleGlobe.inclusion n k 2) := by
  unfold comparison
  exact pushout.inr_desc _ _ _

def basisComparison {n k : ℕ} (hkn : k < n) :
    Source n k ⟶ (rightCylinder (TripleGlobeBasis.complex n k hkn)).realization :=
  comparison n k ≫ (TripleGlobeBasis.modelIso hkn).hom

theorem comparison_imageCell (n k : ℕ) (x : PieceCells n k) :
    (comparison n k).toFun (TripleGlobe.imageCell model n k x) =
      TripleGlobe.targetCell model n k x := by
  cases x with
  | inl x => exact congrArg (fun F => F.toFun x) (inl_comparison n k)
  | inr x => exact congrArg (fun F => F.toFun x) (inr_comparison n k)

def globeChoice (n k : ℕ) (i : Fin 3) (x : model.obj (Globe.category n)) : PieceCells n k :=
  if i = 0 then .inl ((model.map (PastingGlobe.left n n k)).toFun x)
  else if i = 1 then .inl ((model.map (PastingGlobe.right n n k)).toFun x)
  else .inr x

def globeMap (n k : ℕ) (i : Fin 3) : model.obj (Globe.category n) ⟶ Source n k :=
  if i = 0 then model.map (PastingGlobe.left n n k) ≫ pushout.inl _ _
  else if i = 1 then model.map (PastingGlobe.right n n k) ≫ pushout.inl _ _
  else pushout.inr _ _

theorem globeChoice_image (n k : ℕ) (i : Fin 3) (x : model.obj (Globe.category n)) :
    TripleGlobe.imageCell model n k (globeChoice n k i x) = (globeMap n k i).toFun x := by
  fin_cases i <;> rfl

theorem globeMap_comparison (n k : ℕ) (i : Fin 3) :
    globeMap n k i ≫ comparison n k = model.map (TripleGlobe.inclusion n k i) := by
  fin_cases i
  · change (model.map (PastingGlobe.left n n k) ≫ pushout.inl _ _) ≫ comparison n k = _
    rw [Category.assoc, inl_comparison, ← model.map_comp]
    rfl
  · change (model.map (PastingGlobe.right n n k) ≫ pushout.inl _ _) ≫ comparison n k = _
    rw [Category.assoc, inl_comparison, ← model.map_comp]
    rfl
  · exact inr_comparison n k

theorem globeMap_basisComparison {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    globeMap n k i ≫ basisComparison hkn =
      (TripleGlobeBasis.globeModelIso n).hom ≫
        (RightCylinder.map (TripleGlobeBasis.inclusion hkn i)).realization := by
  rw [basisComparison, ← Category.assoc, globeMap_comparison, TripleGlobeBasis.model_globe]

theorem imageCell_eq_of_basisComparison {n k : ℕ} (hkn : k < n)
    (x y : PieceCells n k)
    (h : (basisComparison hkn).toFun (TripleGlobe.imageCell model n k x) =
      (basisComparison hkn).toFun (TripleGlobe.imageCell model n k y)) :
    TripleGlobe.imageCell model n k x = TripleGlobe.imageCell model n k y := by
  apply TripleGlobe.imageCell_eq model n k hkn.le x y
  have h' : (TripleGlobeBasis.modelIso hkn).hom.toFun
      ((comparison n k).toFun (TripleGlobe.imageCell model n k x)) =
      (TripleGlobeBasis.modelIso hkn).hom.toFun
        ((comparison n k).toFun (TripleGlobe.imageCell model n k y)) := h
  rw [comparison_imageCell, comparison_imageCell] at h'
  have hi (z : model.obj (TripleGlobe.category n k)) :
      (TripleGlobeBasis.modelIso hkn).inv.toFun
        ((TripleGlobeBasis.modelIso hkn).hom.toFun z) = z :=
    congrArg (fun F => F.toFun z) (TripleGlobeBasis.modelIso hkn).hom_inv_id
  exact (hi _).symm.trans
    ((congrArg (TripleGlobeBasis.modelIso hkn).inv.toFun h').trans (hi _))

abbrev atomBasis {n k : ℕ} (hkn : k < n) := TripleGlobeBasis.cylinderOrderedAtomBasis hkn

def representativeIndex {n k p : ℕ} (hkn : k < n) (b : (atomBasis hkn).Index p) : Fin 3 :=
  Classical.choose (TripleGlobeBasis.cylinderAtom_in_globe hkn b)

def representativeCell {n k p : ℕ} (hkn : k < n) (b : (atomBasis hkn).Index p) :
    DirectedComplex.Cell (rightCylinder (DirectedGlobeComplex.complex n)) :=
  Classical.choose (Classical.choose_spec (TripleGlobeBasis.cylinderAtom_in_globe hkn b))

theorem representative_spec {n k p : ℕ} (hkn : k < n) (b : (atomBasis hkn).Index p) :
    (rightCylinder (DirectedGlobeComplex.complex n)).realization.DimensionLE p
      (representativeCell hkn b) ∧
    (RightCylinder.map (TripleGlobeBasis.inclusion hkn (representativeIndex hkn b))).realization.toFun
      (representativeCell hkn b) = (atomBasis hkn).atom p b :=
  Classical.choose_spec (Classical.choose_spec (TripleGlobeBasis.cylinderAtom_in_globe hkn b))

def atomChoice {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) : PieceCells n k :=
  globeChoice n k (representativeIndex hkn a.2)
    ((TripleGlobeBasis.globeModelIso n).inv.toFun (representativeCell hkn a.2))

def atomLift {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) : Source n k :=
  TripleGlobe.imageCell model n k (atomChoice hkn a)

theorem atomLift_dimension {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) :
    (Source n k).DimensionLE a.1 (atomLift hkn a) := by
  change (Source n k).DimensionLE a.1
    (TripleGlobe.imageCell model n k (globeChoice n k (representativeIndex hkn a.2)
      ((TripleGlobeBasis.globeModelIso n).inv.toFun (representativeCell hkn a.2))))
  rw [globeChoice_image]
  exact (globeMap n k _).dimensionLE
    ((TripleGlobeBasis.globeModelIso n).inv.dimensionLE (representative_spec hkn a.2).1)

theorem atomLift_image {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) :
    (basisComparison hkn).toFun (atomLift hkn a) = (atomBasis hkn).atomCell a := by
  change (basisComparison hkn).toFun
    (TripleGlobe.imageCell model n k (globeChoice n k (representativeIndex hkn a.2)
      ((TripleGlobeBasis.globeModelIso n).inv.toFun (representativeCell hkn a.2)))) = _
  rw [globeChoice_image]
  have h := congrArg (fun F => F.toFun
    ((TripleGlobeBasis.globeModelIso n).inv.toFun (representativeCell hkn a.2)))
    (globeMap_basisComparison hkn (representativeIndex hkn a.2))
  have hi := congrArg (fun F => F.toFun (representativeCell hkn a.2))
    (TripleGlobeBasis.globeModelIso n).inv_hom_id
  exact h.trans ((congrArg
    (RightCylinder.map (TripleGlobeBasis.inclusion hkn (representativeIndex hkn a.2))).realization.toFun hi).trans
      (representative_spec hkn a.2).2)

end
end Thomason.Construction.StrictOmegaCategory.TripleGlobeCylinder

end

end OAI
