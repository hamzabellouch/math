import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Gray.PrismSimplexNaturality
import OAI.CategoryTheory.Thomason.Gray.RightCylinderPrism
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Strict.OrientalFiniteCells
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

namespace OAI

section

/-! # Street homotopies from concrete positive-chain cylinders

No global Gray functor or adjunction is needed here: the chain map of each
actual Street simplex is extracted from the normalized oriental presentation.
The construction uses composition generation of the simplex atoms.
-/

namespace Thomason.Construction.SimplexAtomsInput

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open _root_.OAI.Thomason.Construction.DirectedComplex SimplexComplex
open scoped Simplicial

noncomputable section

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

/-- Typed form of the explicit normalized AW map. -/
abbrev normalizedAWMap (h : NormalizedSimplexIdentities) {m : ℕ}
    (θ : Fin (m+1) →o Fin 2) :
    directedComplex m (h.squared m) ⟶ rightCylinder (directedComplex m (h.squared m)) :=
  (alexanderWhitneyInput h).chainMap θ

abbrev simplexChainMap (h : NormalizedSimplexIdentities) {l m : ℕ}
    (f : Fin (l+1) →o Fin (m+1)) :
    directedComplex l (h.squared l) ⟶ directedComplex m (h.squared m) :=
  directedMap (h.squared l) (h.squared m) f (h.naturality f)

abbrev chainCylinderMap {K L : DirectedComplex.{0}} (f : K ⟶ L) :
    rightCylinder K ⟶ rightCylinder L := RightCylinder.map f

abbrev chainEndpoint (K : DirectedComplex.{0}) (side : Bool) :
    K ⟶ rightCylinder K := RightCylinder.endpoint K side

abbrev chainProjection (K : DirectedComplex.{0}) : rightCylinder K ⟶ K :=
  RightCylinder.projection K

/-- The concrete AW map, viewed before strict realization, is natural. -/
theorem aw_naturality {l m : ℕ} (f : Fin (l+1) →o Fin (m+1))
    (θ : Fin (m+1) →o Fin 2) :
    simplexChainMap h f ≫
        (normalizedAWMap h θ) =
      (normalizedAWMap h (θ.comp f)) ≫
        chainCylinderMap (simplexChainMap h f) := by
  apply DirectedComplex.Hom.ext_app
  intro n x
  exact ((alexanderWhitneyInput h).naturality f θ n x).symm

/-- An actual simplicial cylinder map for the realization of every directed
complex. Its simplices are positive chain maps, including degenerate ones. -/
def chainNerveCylinder (K : DirectedComplex.{0}) :
    h.streetNerve.obj K.realization ⊗ Δ[1] ⟶
      h.streetNerve.obj (rightCylinder K).realization where
  app m := ↾fun x =>
    ((normalizedAWMap h
      (SSet.stdSimplex.objEquiv x.2).toOrderHom) ≫
        chainCylinderMap (a.chainOfSimplex x.1)).realization
  naturality m n f := by
    ext x
    change (h.object m.unop.len ⟶ K.realization) × (Δ[1].obj m) at x
    rcases x with ⟨F, θ⟩
    let u := simplexChainMap h f.unop.toOrderHom
    let t := (SSet.stdSimplex.objEquiv θ).toOrderHom
    change ((normalizedAWMap h (t.comp f.unop.toOrderHom)) ≫
        chainCylinderMap (a.chainOfSimplex (h.map f.unop.toOrderHom ≫ F))).realization =
      h.map f.unop.toOrderHom ≫
        ((normalizedAWMap h t) ≫
          chainCylinderMap (a.chainOfSimplex F)).realization
    rw [a.chainOfSimplex_precomp]
    have he : (normalizedAWMap h (t.comp f.unop.toOrderHom)) ≫
        chainCylinderMap (u ≫ a.chainOfSimplex F) =
      u ≫ ((normalizedAWMap h t) ≫
        chainCylinderMap (a.chainOfSimplex F)) := by
      rw [show chainCylinderMap (u ≫ a.chainOfSimplex F) =
        chainCylinderMap u ≫ chainCylinderMap (a.chainOfSimplex F) from
          rightCylinderFunctor.map_comp u (a.chainOfSimplex F)]
      rw [← Category.assoc, ← aw_naturality f.unop.toOrderHom t, Category.assoc]
    exact congrArg Hom.realization he

/-- The simplicial cylinder has the two actual strict chain endpoints. -/
theorem chainNerveCylinder_endpoint (K : DirectedComplex.{0}) (side : Bool) :
    (if side then SSet.ι₁ else SSet.ι₀) ≫ a.chainNerveCylinder K =
      h.streetNerve.map (chainEndpoint K side).realization := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  change h.object m.unop.len ⟶ K.realization at F
  have he : normalizedAWMap h
        (OrderHom.const _ (if side then 1 else 0)) ≫
      chainCylinderMap (a.chainOfSimplex F) =
      a.chainOfSimplex F ≫ chainEndpoint K side := by
    apply DirectedComplex.Hom.ext_app
    intro p x
    change (chainCylinderMap (a.chainOfSimplex F)).app p
        ((normalizedAWMap h
          (OrderHom.const _ (if side then 1 else 0))).app p x) = _
    rw [(alexanderWhitneyInput h).chainMap_const]
    exact RightCylinder.map_endpoint (a.chainOfSimplex F) side p x
  have hr : (normalizedAWMap h
        (OrderHom.const _ (if side then 1 else 0)) ≫
      chainCylinderMap (a.chainOfSimplex F)).realization =
        F ≫ (chainEndpoint K side).realization := by
    rw [he]
    change StrictOmegaCategory.Hom.comp (a.chainOfSimplex F).realization
      (chainEndpoint K side).realization = _
    rw [a.chainOfSimplex_realization]
    rfl
  cases side <;> exact hr

/-- The concrete chain projection is the simplicial cylinder projection. -/
theorem chainNerveCylinder_projection (K : DirectedComplex.{0}) :
    a.chainNerveCylinder K ≫ h.streetNerve.map (chainProjection K).realization =
      fst (h.streetNerve.obj K.realization) Δ[1] := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  change (h.object m.unop.len ⟶ K.realization) × (Δ[1].obj m) at x
  rcases x with ⟨F, θ⟩
  let t := (SSet.stdSimplex.objEquiv θ).toOrderHom
  let q := a.chainOfSimplex F
  have he : normalizedAWMap h t ≫
      chainCylinderMap q ≫ chainProjection K = q := by
    apply DirectedComplex.Hom.ext_app
    intro p z
    exact (RightCylinder.projection_map q p
      ((normalizedAWMap h t).app p z)).trans
        (congrArg (q.app p) ((alexanderWhitneyInput h).projection_chainMap t p z))
  change (normalizedAWMap h t ≫
    chainCylinderMap q ≫ chainProjection K).realization = F
  exact (congrArg Hom.realization he).trans (a.chainOfSimplex_realization F)

/-- Every strict map from the concrete chain cylinder determines an actual
homotopy of Street nerves, with no Gray model-structure premise. -/
def chainNerveHomotopy {K : DirectedComplex.{0}} {Y : StrictOmegaCategory.{0}}
    (P : (rightCylinder K).realization ⟶ Y) :
    SSet.Homotopy (h.streetNerve.map ((RightCylinder.endpoint K false).realization ≫ P))
      (h.streetNerve.map ((RightCylinder.endpoint K true).realization ≫ P)) where
  h := a.chainNerveCylinder K ≫ h.streetNerve.map P
  h₀ := by
    have he := a.chainNerveCylinder_endpoint K false
    change SSet.ι₀ ≫ a.chainNerveCylinder K = _ at he
    rw [← Category.assoc, he]
    exact (h.streetNerve.map_comp _ _).symm
  h₁ := by
    have he := a.chainNerveCylinder_endpoint K true
    change SSet.ι₁ ≫ a.chainNerveCylinder K = _ at he
    rw [← Category.assoc, he]
    exact (h.streetNerve.map_comp _ _).symm
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    change ((⊥ : (h.streetNerve.obj K.realization).Subcomplex).toSSet.obj m) ×
      (Δ[1].obj m) at x
    exact False.elim x.1.property

end

end Thomason.Construction.SimplexAtomsInput

end

section

/-! # Barycentric mass merged at a degenerate prism cut

An ordinal map can identify several source vertices with the cut vertex.
Their lower-side mass is exactly the correction to the target cut coordinate.
-/

namespace Thomason.Construction.PrismBarycentric

open Convexity

/-- Source mass before the cut that is identified with the cut vertex. -/
def lowerFiberMass {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (j : Fin (m+1)) : ℝ :=
  ∑ i : Fin (m+1), if i < j ∧ f i = f j then x.weights i else 0

/-- Cumulative source mass separates into strict target mass and merged cut mass. -/
theorem cumulative_map_decomposition {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (j : Fin (m+1)) :
    cumulative x j.val = cumulative (StdSimplex.map f x) (f j).val + lowerFiberMass f x j := by
  rw [cumulative_map]
  unfold cumulative lowerFiberMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (if i < j then x.weights i else 0) =
    (if f i < f j then x.weights i else 0) +
      (if i < j ∧ f i = f j then x.weights i else 0)
  by_cases hij : i < j
  · have hfi := f.monotone hij.le
    by_cases he : f i = f j
    · simp only [he, lt_self_iff_false, ite_false, hij, and_self, ite_true, zero_add]
    · have hlt : f i < f j := lt_of_le_of_ne hfi he
      simp only [hlt, ite_true, hij, he, and_false, ite_false, add_zero]
  · have hfi := f.monotone (le_of_not_gt hij)
    have hnot : ¬ f i < f j := not_lt_of_ge hfi
    simp only [hnot, ite_false, hij, false_and, zero_add]

/-- The target cut coordinate includes precisely the mass merged from below. -/
theorem cutMass_map {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (j : Fin (m+1)) (p : StdSimplex ℝ (Fin (m+1)) × unitInterval) :
    cutMass (f j) (StdSimplex.map f p.1, p.2) = cutMass j p + lowerFiberMass f p.1 j := by
  have h := cumulative_map_decomposition f p.1 j
  unfold cutMass
  dsimp only
  linarith

/-- On an original vertex, the prism ordinal map selects the correct copy. -/
theorem prismOrdinal_succAbove {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (j i : Fin (m+1)) :
    prismOrdinal f j (j.castSucc.succAbove i) =
      if i < j then (f i).castSucc else (f i).succ := by
  rw [prismOrdinal_apply, Fin.predAbove_succAbove]
  by_cases hi : i < j
  · rw [Fin.succAbove_castSucc_of_lt _ _ hi]
    have hle : i.castSucc ≤ j.castSucc := Fin.castSucc_le_castSucc_iff.mpr hi.le
    simp only [hle, ite_true, hi]
  · have hj : j ≤ i := le_of_not_gt hi
    rw [Fin.succAbove_castSucc_of_le _ _ hj]
    have hn : ¬ i.succ ≤ j.castSucc := by
      change ¬ i.val+1 ≤ j.val
      have hv : j.val ≤ i.val := hj
      omega
    simp only [hn, ite_false, hi]

@[simp]
theorem prismOrdinal_lower {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1)) :
    prismOrdinal f j j.castSucc = (f j).castSucc := by
  simp only [prismOrdinal_apply, le_rfl, ite_true, Fin.predAbove_castSucc_self]

@[simp]
theorem prismOrdinal_upper {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j : Fin (m+1)) :
    prismOrdinal f j j.succ = (f j).succ := by
  have hn : ¬ j.succ ≤ j.castSucc := by
    change ¬ j.val+1 ≤ j.val
    omega
  simp only [prismOrdinal_apply, hn, ite_false, Fin.predAbove_succ_self]

end Thomason.Construction.PrismBarycentric

end

section

/-! # Naturality of barycentric prism splitting

The lower-side mass merged by an ordinal map corrects both copies of the
cut vertex. Thus the actual barycentric charts commute with degeneracies
as well as faces.
-/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

/-- The image of an original vertex under the cut prism map. -/
def sideMap {m n : ℕ} (f : Fin (m+1) →o Fin (n+1)) (j i : Fin (m+1)) :
    Fin (n+2) := if i < j then (f i).castSucc else (f i).succ

/-- Only vertices merged with the cut require a correction. -/
theorem sideMap_single {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (j i : Fin (m+1)) (a : ℝ) :
    Finsupp.single (sideMap f j i) a =
      Finsupp.single ((f j).castSucc.succAbove (f i)) a +
      Finsupp.single (f j).castSucc (if i < j ∧ f i = f j then a else 0) -
      Finsupp.single (f j).succ (if i < j ∧ f i = f j then a else 0) := by
  by_cases hi : i < j
  · by_cases he : f i = f j
    · simp only [sideMap, hi, ite_true, he, and_self,
        Fin.succAbove_castSucc_of_le _ _ le_rfl]
      abel
    · have hlt : f i < f j := lt_of_le_of_ne (f.monotone hi.le) he
      simp only [sideMap, hi, ite_true, he, and_false, ite_false,
        Fin.succAbove_castSucc_of_lt _ _ hlt, Finsupp.single_zero, add_zero, sub_zero]
  · have hle : f j ≤ f i := f.monotone (le_of_not_gt hi)
    simp only [sideMap, hi, ite_false, false_and,
      Fin.succAbove_castSucc_of_le _ _ hle, Finsupp.single_zero, add_zero, sub_zero]

/-- Summing the vertex correction gives the merged lower mass. -/
theorem sideMap_weights {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (j : Fin (m+1)) :
    x.weights.mapDomain (sideMap f j) =
      (x.weights.mapDomain f).mapDomain (f j).castSucc.succAbove +
      Finsupp.single (f j).castSucc (lowerFiberMass f x j) -
      Finsupp.single (f j).succ (lowerFiberMass f x j) := by
  rw [← Finsupp.mapDomain_comp]
  simp only [Finsupp.mapDomain_fintype]
  simp_rw [sideMap_single]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  · exact (map_sum (Finsupp.singleAddHom (f j).castSucc) _ _).symm
  · exact (map_sum (Finsupp.singleAddHom (f j).succ) _ _).symm

/-- Splitting and mapping commute, with exactly the merged cut mass. -/
theorem splitWeights_map {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (x : StdSimplex ℝ (Fin (m+1))) (j : Fin (m+1)) (a : ℝ) :
    (splitWeights x j a).mapDomain (prismOrdinal f j) =
      splitWeights (StdSimplex.map f x) (f j) (a + lowerFiberMass f x j) := by
  unfold splitWeights remainder
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, prismOrdinal_lower,
    ← Finsupp.mapDomain_comp]
  have hs : (prismOrdinal f j) ∘ j.castSucc.succAbove = sideMap f j := by
    funext i
    exact prismOrdinal_succAbove f j i
  rw [hs, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hj : sideMap f j j = (f j).succ := by simp [sideMap]
  rw [hj, sideMap_weights]
  change _ = Finsupp.single (f j).castSucc (a + lowerFiberMass f x j) +
    (x.weights.mapDomain f - Finsupp.single (f j) (a + lowerFiberMass f x j)).mapDomain
      (f j).castSucc.succAbove
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Fin.succAbove_castSucc_of_le _ _ le_rfl, Finsupp.single_add, Finsupp.single_add]
  abel

/-- Full chart naturality, valid for every ordinal map. -/
theorem chart_naturality {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (j : Fin (m+1)) (p : region j) :
    StdSimplex.map (prismOrdinal f j) (chart j p) =
      chart (f j) ⟨(StdSimplex.map f p.val.1, p.val.2), region_map f j p⟩ := by
  apply StdSimplex.ext
  change (splitWeights p.val.1 j (cutMass j p.val)).mapDomain (prismOrdinal f j) =
    splitWeights (StdSimplex.map f p.val.1) (f j)
      (cutMass (f j) (StdSimplex.map f p.val.1, p.val.2))
  rw [splitWeights_map, cutMass_map]

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # Naturality of the actual standard realization prism -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory MonoidalCategory Convexity
open scoped Simplicial

noncomputable section

/-- Naturality on each closed barycentric chart. -/
theorem realizedChart_naturality {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (j : Fin (m+1)) (p : region j) :
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ▷ Δ[1])).hom
      (realizedChart j p) =
    realizedChart (f j) ⟨(StdSimplex.map f p.val.1, p.val.2), region_map f j p⟩ := by
  have hn := congrArg (fun g => g.hom (ULift.up (chart j p)))
    (RealizationPrism.leg_naturality
      (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ▷ Δ[1]) (simplexIndex j))
  have hf := congrArg (fun g => g.hom (ULift.up (chart j p)))
    ((RealizationPrism.cocone (prism n)).w (simplexNaturality f j))
  change _ = _ at hn
  change (RealizationPrism.leg (prism n) (simplexIndex (f j))).hom
    (ULift.up (StdSimplex.map (prismOrdinal f j) (chart j p))) = _ at hf
  exact hn.trans (hf.symm.trans (congrArg
    (fun x => (RealizationPrism.leg (prism n) (simplexIndex (f j))).hom (ULift.up x))
    (chart_naturality f j p)))

/-- The glued standard prism is natural under every face and degeneracy. -/
theorem standardPrism_naturality {m n : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (p : StdSimplex ℝ (Fin (m+1)) × unitInterval) :
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ▷ Δ[1])).hom
      (standardPrism m p) = standardPrism n (StdSimplex.map f p.1, p.2) := by
  have hp : p ∈ ⋃ j : Fin (m+1), region j := by rw [region_cover]; trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
  rw [standardPrism_on_region j p hj,
    standardPrism_on_region (f j) _ (region_map f j ⟨p, hj⟩)]
  exact realizedChart_naturality f j ⟨p, hj⟩

/-- Naturality in the exact simplex convention of the realization colimit. -/
theorem liftedStandardPrism_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    TopologicalInterval.cylinder.map (SimplexCategory.toTop.{0}.map f) ≫
      liftedStandardPrism n.len =
    liftedStandardPrism m.len ≫ SSet.toTop.map (SSet.stdSimplex.map f ▷ Δ[1]) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact (standardPrism_naturality f.toOrderHom (p.1.down, p.2)).symm

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # The time coordinate of the actual realization prism -/

namespace Thomason.Construction.PrismBarycentric

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial

noncomputable section

/-- On a zero-dimensional base the barycentric chart has exactly its given time. -/
theorem chart_zero_time (p : region (0 : Fin 1)) :
    StdSimplex.homeomorphI (chart 0 p) = p.val.2 := by
  apply Subtype.ext
  rw [StdSimplex.homeomorphI_apply_coe]
  change splitWeights p.val.1 0 (cutMass 0 p.val) 1 = _
  simp [splitWeights, remainder, cutMass, Finsupp.mapDomain_fintype]

/-- The ordinal map recording which side of the prism cut a vertex lies on. -/
def timeOrdinal {n : ℕ} (j : Fin (n+1)) : Fin (n+2) →o Fin 2 :=
  prismOrdinal (OrderHom.const _ (0 : Fin 1)) j

/-- Collapsing the base of a barycentric prism preserves its time coordinate. -/
theorem chart_time {n : ℕ} (j : Fin (n+1)) (p : region j) :
    StdSimplex.homeomorphI (StdSimplex.map (timeOrdinal j) (chart j p)) = p.val.2 := by
  unfold timeOrdinal
  rw [chart_naturality]
  exact chart_zero_time _

/-- The second simplicial projection records the time ordinal of each chart. -/
def secondProjectionMap {n : ℕ} (j : Fin (n+1)) :
    (CostructuredArrow.map (snd (Δ[n] : SSet.{0}) Δ[1])).obj (simplexIndex j) ⟶
      baseIndex 1 :=
  CostructuredArrow.homMk (SimplexCategory.Hom.mk (timeOrdinal j)) (by
    change SSet.stdSimplex.map _ ≫ 𝟙 _ =
      SSet.yonedaEquiv.symm (SSet.prodStdSimplex₁.nonDegenerateEquiv j).val ≫ snd _ _
    rw [Category.comp_id]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro k
    change timeOrdinal j k = if k.castSucc < j.succ.castSucc then 0 else 1
    have he : k.castSucc < j.succ.castSucc ↔ k ≤ j.castSucc := by
      change k.val < j.val + 1 ↔ k.val ≤ j.val
      omega
    simp only [timeOrdinal, prismOrdinal_apply, he]
    split_ifs <;> rfl)

/-- The usual affine coordinate on the realization of the simplicial interval. -/
def realizationTime : SSet.toTop.obj (Δ[1] : SSet.{0}) ⟶ TopCat.of unitInterval :=
  TopCat.ofHom ⟨fun x => StdSimplex.homeomorphI ((SimplexCategory.mk 1).toTopHomeo x),
    StdSimplex.homeomorphI.continuous.comp (SimplexCategory.mk 1).toTopHomeo.continuous⟩

theorem realizationTime_base (x : StdSimplex ℝ (Fin 2)) :
    realizationTime.hom ((RealizationPrism.leg (Δ[1] : SSet.{0}) (baseIndex 1)).hom
      (ULift.up x)) = StdSimplex.homeomorphI x := by
  change StdSimplex.homeomorphI
    ((SSet.toTopSimplex.hom.app (.mk 1)).hom
      ((SSet.toTopSimplex.inv.app (.mk 1) ≫ SSet.toTop.map (𝟙 _)).hom (ULift.up x))).down = _
  rw [CategoryTheory.Functor.map_id]
  have h := congrArg (fun f => f.hom (ULift.up x))
    (SSet.toTopSimplex.inv_hom_id_app (.mk 1))
  exact congrArg (fun y => StdSimplex.homeomorphI y.down) h

/-- On every chart the realized second projection is exactly the supplied time. -/
theorem realizedChart_time {n : ℕ} (j : Fin (n+1)) (p : region j) :
    realizationTime.hom ((SSet.toTop.map (snd (Δ[n] : SSet.{0}) Δ[1])).hom
      (realizedChart j p)) = p.val.2 := by
  have hn := congrArg (fun f => f.hom (ULift.up (chart j p)))
    (RealizationPrism.leg_naturality (snd (Δ[n] : SSet.{0}) Δ[1]) (simplexIndex j))
  have hf := congrArg (fun f => f.hom (ULift.up (chart j p)))
    ((RealizationPrism.cocone (Δ[1] : SSet.{0})).w (secondProjectionMap j))
  change _ = _ at hn
  change (RealizationPrism.leg (Δ[1] : SSet.{0}) (baseIndex 1)).hom
    (ULift.up (StdSimplex.map (timeOrdinal j) (chart j p))) = _ at hf
  rw [show (SSet.toTop.map (snd (Δ[n] : SSet.{0}) Δ[1])).hom (realizedChart j p) =
      (RealizationPrism.leg (Δ[1] : SSet.{0}) (baseIndex 1)).hom
        (ULift.up (StdSimplex.map (timeOrdinal j) (chart j p))) from hn.trans hf.symm]
  rw [realizationTime_base]
  exact chart_time j p

/-- The glued standard prism preserves the interval coordinate. -/
theorem standardPrism_time (n : ℕ)
    (p : StdSimplex ℝ (Fin (n+1)) × unitInterval) :
    realizationTime.hom ((SSet.toTop.map (snd (Δ[n] : SSet.{0}) Δ[1])).hom
      (standardPrism n p)) = p.2 := by
  have hp : p ∈ ⋃ j : Fin (n+1), region j := by rw [region_cover]; trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
  rw [standardPrism_on_region j p hj]
  exact realizedChart_time j ⟨p, hj⟩

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # Every maximal prism simplex comes from its barycentric region -/

namespace Thomason.Construction.PrismBarycentric

open Convexity

noncomputable section

/-- Removing the first copy of the cut vertex reverses the split weights. -/
theorem splitWeights_recover {n : ℕ} (j : Fin (n+1))
    (u : StdSimplex ℝ (Fin (n+2))) :
    splitWeights (StdSimplex.map j.predAbove u) j (u.weights j.castSucc) = u.weights := by
  classical
  have hu := congrArg (Finsupp.mapDomain j.predAbove)
    (Finsupp.single_add_erase j.castSucc u.weights)
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Fin.predAbove_castSucc_self] at hu
  have hr : u.weights.mapDomain j.predAbove - Finsupp.single j (u.weights j.castSucc) =
      (u.weights.erase j.castSucc).mapDomain j.predAbove := by
    rw [← hu]
    abel
  have he : (u.weights.erase j.castSucc).mapDomain
      (j.castSucc.succAbove ∘ j.predAbove) = u.weights.erase j.castSucc := by
    suffices hh : (u.weights.erase j.castSucc).mapDomain
        (j.castSucc.succAbove ∘ j.predAbove) =
        (u.weights.erase j.castSucc).mapDomain id from hh.trans Finsupp.mapDomain_id
    apply Finsupp.mapDomain_congr
    intro k hk
    have hne : k ≠ j.castSucc := by
      intro h
      subst k
      simp at hk
    exact Fin.succAbove_predAbove hne
  change Finsupp.single j.castSucc (u.weights j.castSucc) +
    (u.weights.mapDomain j.predAbove - Finsupp.single j (u.weights j.castSucc)).mapDomain
      j.castSucc.succAbove = u.weights
  rw [hr, ← Finsupp.mapDomain_comp, he, Finsupp.single_add_erase]

/-- The removed mass lies between zero and the mass of the collapsed vertex. -/
theorem removedMass_le {n : ℕ} (j : Fin (n+1))
    (u : StdSimplex ℝ (Fin (n+2))) :
    u.weights j.castSucc ≤ (StdSimplex.map j.predAbove u).weights j := by
  classical
  have he : 0 ≤ u.weights.erase j.castSucc := by
    intro k
    by_cases hk : k = j.castSucc
    · subst k; simp
    · simp only [Finsupp.erase_ne hk]
      exact u.weights_nonneg k
  have h := Finsupp.mapDomain_nonneg (f := j.predAbove) he
  have hu := congrArg (fun v : Fin (n+1) →₀ ℝ => v j)
    (congrArg (Finsupp.mapDomain j.predAbove) (Finsupp.single_add_erase j.castSucc u.weights))
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Fin.predAbove_castSucc_self, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hu
  change u.weights j.castSucc ≤ u.weights.mapDomain j.predAbove j
  have hj : 0 ≤ (u.weights.erase j.castSucc).mapDomain j.predAbove j := h j
  linarith only [hu, hj]

/-- Every barycentric point of a maximal prism simplex is attained by its chart. -/
theorem chart_surjective {n : ℕ} (j : Fin (n+1))
    (u : StdSimplex ℝ (Fin (n+2))) : ∃ p : region j, chart j p = u := by
  let x := StdSimplex.map j.predAbove u
  let a := u.weights j.castSucc
  have ha : 0 ≤ a := u.weights_nonneg _
  have hb : a ≤ x.weights j := removedMass_le j u
  have hc : 0 ≤ cumulative x j.val := by
    unfold cumulative
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact x.weights_nonneg i
    · exact le_rfl
  have hd : cumulative x j.val + a ≤ 1 := by
    have hh := cumulative_monotone x (show j.val+1 ≤ n+1 from j.is_lt)
    rw [cumulative_all, cumulative_step] at hh
    linarith
  let t : unitInterval := ⟨1 - cumulative x j.val - a, by constructor <;> linarith⟩
  have hp : (x, t) ∈ region j := by
    change cumulative x j.val ≤ 1 - (1 - cumulative x j.val - a) ∧
      1 - (1 - cumulative x j.val - a) ≤ cumulative x (j.val+1)
    rw [cumulative_step]
    constructor <;> linarith
  refine ⟨⟨(x, t), hp⟩, ?_⟩
  apply StdSimplex.ext
  change splitWeights x j (cutMass j (x, t)) = u.weights
  have ht : cutMass j (x, t) = a := by dsimp [cutMass, t]; ring
  rw [ht]
  exact splitWeights_recover j u

end

end Thomason.Construction.PrismBarycentric

end

section

/-! # The ordered chain basis of three composable globes

Three n-globes are pasted in succession at dimension k. Lower faces are
shared; the k-faces form a string of four cells. Above k each globe retains
its own basis. This is the concrete chain parameter for associativity.
-/

namespace Thomason.Construction.TripleGlobeBasis

open DirectedGlobeComplex

abbrev Basis (n k p : ℕ) :=
  {b : Fin 3 × Bool //
    (p < n ∨ (p = n ∧ b.2 = false)) ∧
    (p < k → b.1 = 0) ∧ (p = k → b.2 = false → b.1 = 0)}

abbrev Chains (n k p : ℕ) := Basis n k p →₀ ℤ

def predecessor (i : Fin 3) : Fin 3 := ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

/-- Normalize the source of a later globe to the preceding target. -/
def embed {n k p : ℕ} (hkn : k < n) (i : Fin 3)
    (b : DirectedGlobeComplex.Basis n p) : Basis n k p := by
  by_cases hp : p < k
  · exact ⟨(0, b.val), b.property, fun _ => rfl, fun he => by omega⟩
  · by_cases he : p = k
    · by_cases hb : b.val = false
      · by_cases hi : i = 0
        · exact ⟨(0, false), Or.inl (he ▸ hkn), fun _ => rfl, fun _ _ => rfl⟩
        · exact ⟨(predecessor i, true), Or.inl (he ▸ hkn), fun hh => (hp hh).elim,
            fun _ hh => Bool.noConfusion hh⟩
      · exact ⟨(i, b.val), b.property, fun hh => (hp hh).elim,
          fun _ hh => (hb hh).elim⟩
    · exact ⟨(i, b.val), b.property, fun hh => (hp hh).elim,
        fun hh => (he hh).elim⟩

theorem degree_le {n k p : ℕ} (b : Basis n k p) : p ≤ n := by
  rcases b.property.1 with h | ⟨h, _⟩ <;> omega

theorem embed_self {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    embed hkn b.val.1 ⟨b.val.2, b.property.1⟩ = b := by
  rcases b with ⟨⟨i, a⟩, hv, hl, hk⟩
  by_cases hp : p < k
  · have hi := hl hp
    change i = 0 at hi
    subst i
    simp [embed, hp]
  · by_cases he : p = k
    · by_cases ha : a = false
      · have hi := hk he ha
        change i = 0 at hi
        subst i
        subst a
        simp [embed, he]
      · simp [embed, he, ha]
    · simp [embed, hp, he]

def face {n k p : ℕ} (hkn : k < n) (a : Bool) (b : Basis n k (p+1)) :
    Basis n k p :=
  embed hkn b.val.1 ⟨a, Or.inl (by have := degree_le b; omega)⟩

theorem face_globular {n k p : ℕ} (hkn : k < n) (a c : Bool)
    (b : Basis n k (p+2)) :
    face hkn a (face hkn false b) = face hkn a (face hkn c b) := by
  cases c with
  | false => rfl
  | true =>
    rcases b with ⟨⟨i, t⟩, hv, hl, hk⟩
    by_cases hp : p+1 < k
    · simp [face, embed, show p < k by omega]
    · by_cases he : p+1 = k
      · simp [face, embed, show p < k by omega]
      · simp [face, embed, hp, he]

noncomputable def boundary {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    Chains n k p :=
  Finsupp.single (face hkn true b) 1 - Finsupp.single (face hkn false b) 1

noncomputable def differential {n k : ℕ} (hkn : k < n) (p : ℕ) :
    Chains n k (p+1) →ₗ[ℤ] Chains n k p :=
  Finsupp.linearCombination ℤ (boundary hkn)

@[simp] theorem differential_single {n k p : ℕ} (hkn : k < n)
    (b : Basis n k (p+1)) (z : ℤ) :
    differential hkn p (Finsupp.single b z) = z • boundary hkn b := by
  simp [differential]

@[simp] theorem differential_boundary {n k p : ℕ} (hkn : k < n)
    (b : Basis n k (p+2)) :
    differential hkn p (boundary hkn b) = 0 := by
  simp only [boundary, map_sub, differential_single, one_smul]
  rw [face_globular hkn true true b, face_globular hkn false true b]
  simp

theorem differential_squared {n k : ℕ} (hkn : k < n) (p : ℕ)
    (x : Chains n k (p+2)) : differential hkn p (differential hkn (p+1) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b z => simp

noncomputable def weight (n k p : ℕ) : Chains n k p →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem weight_single {n k p : ℕ} (b : Basis n k p) (z : ℤ) :
    weight n k p (Finsupp.single b z) = z := by simp [weight]

@[simp] theorem weight_differential {n k : ℕ} (hkn : k < n) (p : ℕ)
    (x : Chains n k (p+1)) : weight n k p (differential hkn p x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b z => simp [boundary]

def positive (n k p : ℕ) : AddSubmonoid (Chains n k p) where
  carrier := {x | ∀ b, 0 ≤ x b}
  zero_mem' := fun _ => le_rfl
  add_mem' hx hy b := add_nonneg (hx b) (hy b)

noncomputable def complex (n k : ℕ) (hkn : k < n) : DirectedComplex where
  group p := AddCommGrpCat.of (Chains n k p)
  differential p := (differential hkn p).toAddMonoidHom
  differential_squared := differential_squared hkn
  augmentation := (weight n k 0).toAddMonoidHom
  augmentation_differential := weight_differential hkn 0
  positive := positive n k

/-- The three successive intervals are placed consecutively in the height order. -/
def height {n k p : ℕ} (b : Basis n k p) : ℤ :=
  if b.val.2 then
    if p < k then 6*(n:ℤ)-4*k-p
    else 2*(b.val.1.val:ℤ)*((n:ℤ)-k)+2*n-p
  else 2*(b.val.1.val:ℤ)*((n:ℤ)-k)+p

theorem height_source_lt {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    height (face hkn false b) < height b := by
  rcases b with ⟨⟨i, a⟩, hv, hl, hk⟩
  fin_cases i <;> cases a
  all_goals
    simp_all [face, embed, predecessor, height]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

theorem height_lt_target {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    height b < height (face hkn true b) := by
  rcases b with ⟨⟨i, a⟩, hv, hl, hk⟩
  fin_cases i <;> cases a
  all_goals
    simp_all [face, embed, height]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

theorem face_ne {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    face hkn false b ≠ face hkn true b := by
  intro he
  have hs := height_source_lt hkn b
  have ht := height_lt_target hkn b
  rw [he] at hs
  omega

end Thomason.Construction.TripleGlobeBasis

end

section

/-! # The three globe inclusions in the triple chain complex -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

theorem face_embed {n k p : ℕ} (hkn : k < n) (i : Fin 3) (a : Bool)
    (b : DirectedGlobeComplex.Basis n (p+1)) :
    face hkn a (embed hkn i b) =
      embed hkn i ⟨a, Or.inl (by rcases b.property with h | ⟨h, _⟩ <;> omega)⟩ := by
  by_cases hp : p+1 < k
  · simp [embed, face, show p < k by omega]
  · by_cases he : p+1 = k
    · simp [embed, face, show p < k by omega]
    · simp [embed, hp, he, face]

def embedApp {n k : ℕ} (hkn : k < n) (i : Fin 3) (p : ℕ) :
    DirectedGlobeComplex.Chains n p →ₗ[ℤ] Chains n k p :=
  Finsupp.linearCombination ℤ (fun b => Finsupp.single (embed hkn i b) 1)

@[simp] theorem embedApp_single {n k p : ℕ} (hkn : k < n) (i : Fin 3)
    (b : DirectedGlobeComplex.Basis n p) (z : ℤ) :
    embedApp hkn i p (Finsupp.single b z) = Finsupp.single (embed hkn i b) z := by
  simp [embedApp]

theorem embedApp_differential {n k : ℕ} (hkn : k < n) (i : Fin 3) (p : ℕ)
    (u : DirectedGlobeComplex.Chains n (p+1)) :
    embedApp hkn i p (DirectedGlobeComplex.differential n p u) =
      differential hkn p (embedApp hkn i (p+1) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    have hp : p < n := by rcases b.property with h | ⟨h, _⟩ <;> omega
    simp only [DirectedGlobeComplex.differential_single, map_smul,
      DirectedGlobeComplex.boundary, dite_eq_left hp, map_sub, embedApp_single,
      differential_single, boundary, face_embed]

theorem embedApp_augmentation {n k : ℕ} (hkn : k < n) (i : Fin 3)
    (u : DirectedGlobeComplex.Chains n 0) :
    weight n k 0 (embedApp hkn i 0 u) = DirectedGlobeComplex.weight n 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z => simp

theorem embedApp_positive {n k p : ℕ} (hkn : k < n) (i : Fin 3)
    (u : DirectedGlobeComplex.Chains n p) (hu : u ∈ DirectedGlobeComplex.positive n p) :
    embedApp hkn i p u ∈ positive n k p := by
  classical
  change (u.sum fun b z => z • Finsupp.single (embed hkn i b) 1) ∈ positive n k p
  apply (positive n k p).sum_mem
  intro b hb
  change u b • Finsupp.single (embed hkn i b) 1 ∈ positive n k p
  rw [← Int.toNat_of_nonneg (hu b), natCast_zsmul]
  apply (positive n k p).nsmul_mem
  intro c
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

def inclusion {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    Hom (DirectedGlobeComplex.complex n) (complex n k hkn) where
  app p := (embedApp hkn i p).toAddMonoidHom
  differential := embedApp_differential hkn i
  augmentation := embedApp_augmentation hkn i
  positive _ _ hu := embedApp_positive hkn i _ hu

end
end Thomason.Construction.TripleGlobeBasis

end

section

/-! # Actual ordered atoms of three pasted globes and their right cylinder -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

def atom {n k p : ℕ} (hkn : k < n) (b : Basis n k p) : Cell (complex n k hkn) :=
  (inclusion hkn b.val.1).realization.toFun
    (DirectedGlobeComplex.basisAtom n p ⟨b.val.2, b.property.1⟩)

theorem atom_top {n k p : ℕ} (hkn : k < n) (b : Basis n k p) (a : Bool) :
    (atom hkn b).table a p = Finsupp.single b 1 := by
  change embedApp hkn b.val.1 p
    ((DirectedGlobeComplex.basisAtom n p ⟨b.val.2, b.property.1⟩).table a p) = _
  rw [DirectedGlobeComplex.basisAtom_top, embedApp_single, embed_self]

theorem atom_above {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hpq : p < q) (a : Bool) : (atom hkn b).table a q = 0 := by
  change embedApp hkn b.val.1 q
    ((DirectedGlobeComplex.basisAtom n p ⟨b.val.2, b.property.1⟩).table a q) = _
  rw [DirectedGlobeComplex.basisAtom_above n p _ q hpq a]
  exact map_zero _

theorem atom_below {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (a : Bool) :
    (atom hkn b).table a q = Finsupp.single
      (embed hkn b.val.1 ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩) 1 := by
  change embedApp hkn b.val.1 q
    ((DirectedGlobeComplex.basisAtom n p ⟨b.val.2, b.property.1⟩).table a q) = _
  rw [DirectedGlobeComplex.basisAtom_below n p _ q hqp a, embedApp_single]

theorem height_lower {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (a : Bool) :
    if a then height b < height (embed hkn b.val.1
      ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)
    else height (embed hkn b.val.1
      ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩) < height b := by
  rcases b with ⟨⟨i, c⟩, hv, hl, hk⟩
  fin_cases i <;> cases c <;> cases a
  all_goals
    simp_all [height, embed, predecessor]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

theorem atom_sideHeight {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (a : Bool) (c : Basis n k q)
    (hc : DFunLike.coe (F := Chains n k q) ((atom hkn b).table a q) c ≠ 0) :
    if a then height b < height c else height c < height b := by
  rw [atom_below hkn b hqp a] at hc
  have he : c = embed hkn b.val.1 ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩ := by
    by_contra he
    exact hc (Finsupp.single_eq_of_ne he)
  subst c
  exact height_lower hkn b hqp a

def orderedAtomBasis {n k : ℕ} (hkn : k < n) : OrderedAtomBasis (complex n k hkn) where
  Index p := Basis n k p
  coordinates _ := AddEquiv.refl _
  positive_iff _ _ := Iff.rfl
  augmentation := by
    change ∀ x : Chains n k 0, weight n k 0 x = x.sum (fun _ z => z)
    intro x
    simp [weight, Finsupp.linearCombination_apply]
  atom _ := atom hkn
  atom_top _ := atom_top hkn
  atom_above _ b q h a := atom_above hkn b h a
  height _ := height
  disjoint {p q r} b c hrp hrq hbc e := by
    by_cases he : DFunLike.coe (F := Chains n k r) ((atom hkn b).table false r) e = 0
    · exact Or.inl he
    · right
      by_contra hf
      have h1 := atom_sideHeight hkn b hrp false e he
      have h2 := atom_sideHeight hkn c hrq true e hf
      simp only [Bool.false_eq_true, ite_false, ite_true] at h1 h2
      exact (lt_irrefl _) (h2.trans (h1.trans_le hbc))

theorem orderedAtomBasis_sideHeight {n k : ℕ} (hkn : k < n) :
    (orderedAtomBasis hkn).SideHeight :=
  fun _ b _ h a c hc => atom_sideHeight hkn b h a c hc

def cylinderOrderedAtomBasis {n k : ℕ} (hkn : k < n) :
    OrderedAtomBasis (rightCylinder (complex n k hkn)) :=
  (orderedAtomBasis hkn).cylinderOrderedAtomBasis (orderedAtomBasis_sideHeight hkn)

end
end Thomason.Construction.TripleGlobeBasis

end

end OAI
