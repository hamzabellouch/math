import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TerminalConeUniversal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.LocallyFinite

namespace OAI

section

/-! # Weak equivalences on compatible simplicial exhaustions -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory

noncomputable section

variable {K L : SSet.{0}} (f : K ⟶ L)
  (A : ℕ → K.Subcomplex) (B : ℕ → L.Subcomplex)
  (hA : Monotone A) (hB : Monotone B)
  (g : ∀ n, (A n : SSet) ⟶ (B n : SSet))
  (hg : ∀ n, g n ≫ (B n).ι = (A n).ι ≫ f)

include f hg in
/-- Compatibility with the ambient map determines every transition square. -/
theorem exhaustion_map_naturality {m n : ℕ} (hmn : m ≤ n) :
    SSet.Subcomplex.homOfLE (hA hmn) ≫ g n =
      g m ≫ SSet.Subcomplex.homOfLE (hB hmn) := by
  apply (cancel_mono (B n).ι).mp
  calc
    (SSet.Subcomplex.homOfLE (hA hmn) ≫ g n) ≫ (B n).ι =
        SSet.Subcomplex.homOfLE (hA hmn) ≫ (g n ≫ (B n).ι) := Category.assoc _ _ _
    _ = SSet.Subcomplex.homOfLE (hA hmn) ≫ ((A n).ι ≫ f) := by rw [hg n]
    _ = (A m).ι ≫ f := rfl
    _ = g m ≫ (B m).ι := (hg m).symm
    _ = (g m ≫ SSet.Subcomplex.homOfLE (hB hmn)) ≫ (B n).ι := rfl


include hB hg in
/-- Component surjectivity passes from all stages to their exhausted target. -/
theorem exhaustion_map_components_surjective (hcoverB : iSup B = ⊤)
    (hW : ∀ n, realizationWeakEquivalences (g n)) :
    Function.Surjective (HomotopyMaps.componentsMap (SSet.toTop.map f).hom) := by
  intro z
  induction z using ZerothHomotopy.rec with
  | mk y =>
    obtain ⟨n, q, hq⟩ := compact_map_factors_stage L B hB hcoverB
      (ContinuousMap.const Unit y)
    obtain ⟨a, ha⟩ := (hW n).1.2 (ZerothHomotopy.mk (q ()))
    refine ⟨HomotopyMaps.componentsMap (SSet.toTop.map (A n).ι).hom a, ?_⟩
    have he : SSet.toTop.map (A n).ι ≫ SSet.toTop.map f =
        SSet.toTop.map (g n) ≫ SSet.toTop.map (B n).ι := by
      rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, hg]
    have hc := congrArg (fun t => HomotopyMaps.componentsMap t.hom) he
    change HomotopyMaps.componentsMap ((SSet.toTop.map f).hom.comp
        (SSet.toTop.map (A n).ι).hom) =
      HomotopyMaps.componentsMap ((SSet.toTop.map (B n).ι).hom.comp
        (SSet.toTop.map (g n)).hom) at hc
    rw [HomotopyMaps.componentsMap_comp, HomotopyMaps.componentsMap_comp] at hc
    change (HomotopyMaps.componentsMap (SSet.toTop.map f).hom ∘
      HomotopyMaps.componentsMap (SSet.toTop.map (A n).ι).hom) a = _
    rw [hc]
    change HomotopyMaps.componentsMap (SSet.toTop.map (B n).ι).hom
      (HomotopyMaps.componentsMap (SSet.toTop.map (g n)).hom a) = _
    rw [ha]
    exact congrArg ZerothHomotopy.mk (congrArg (fun t : C(_, _) => t ()) hq)

include hA hB hg in
/-- Component equality in the target is already witnessed in a common
finite stage, where the stage weak equivalence reflects it. -/
theorem exhaustion_map_components_injective
    (hcoverA : iSup A = ⊤) (hcoverB : iSup B = ⊤)
    (hW : ∀ n, realizationWeakEquivalences (g n)) :
    Function.Injective (HomotopyMaps.componentsMap (SSet.toTop.map f).hom) := by
  intro a b hab
  induction a using ZerothHomotopy.rec with
  | mk x =>
    induction b using ZerothHomotopy.rec with
    | mk y =>
      obtain ⟨n, u, v, hu, hv⟩ := compact_pair_factors_stage K A hA hcoverA
        (ContinuousMap.const Unit x) (ContinuousMap.const Unit y)
      let x' := u ()
      let y' := v ()
      have hx : (SSet.toTop.map (A n).ι).hom x' = x :=
        congrArg (fun t : C(_, _) => t ()) hu
      have hy : (SSet.toTop.map (A n).ι).hom y' = y :=
        congrArg (fun t : C(_, _) => t ()) hv
      have ef (z : SSet.toTop.obj (A n : SSet)) :
          (SSet.toTop.map (B n).ι).hom ((SSet.toTop.map (g n)).hom z) =
            (SSet.toTop.map f).hom ((SSet.toTop.map (A n).ι).hom z) := by
        have he := SSet.toTop.congr_map (hg n)
        rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
        exact congrArg (fun t => t.hom z) he
      have he : HomotopyMaps.componentsMap (SSet.toTop.map (B n).ι).hom
            (ZerothHomotopy.mk ((SSet.toTop.map (g n)).hom x')) =
          HomotopyMaps.componentsMap (SSet.toTop.map (B n).ι).hom
            (ZerothHomotopy.mk ((SSet.toTop.map (g n)).hom y')) := by
        simpa only [HomotopyMaps.componentsMap_mk, ef, hx, hy] using hab
      obtain ⟨k, hnk, hk⟩ := components_eventual_eq L B hB hcoverB n _ _ he
      let ja := SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hnk))
      let jb := SSet.toTop.map (SSet.Subcomplex.homOfLE (hB hnk))
      have hn := SSet.toTop.congr_map (exhaustion_map_naturality f A B hA hB g hg hnk)
      rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hn
      have hxg : (SSet.toTop.map (g k)).hom (ja.hom x') =
          jb.hom ((SSet.toTop.map (g n)).hom x') := congrArg (fun t => t.hom x') hn
      have hyg : (SSet.toTop.map (g k)).hom (ja.hom y') =
          jb.hom ((SSet.toTop.map (g n)).hom y') := congrArg (fun t => t.hom y') hn
      have he' : HomotopyMaps.componentsMap (SSet.toTop.map (g k)).hom
            (ZerothHomotopy.mk (ja.hom x')) =
          HomotopyMaps.componentsMap (SSet.toTop.map (g k)).hom
            (ZerothHomotopy.mk (ja.hom y')) := by
        simpa only [HomotopyMaps.componentsMap_mk, hxg, hyg] using hk
      have hr := (hW k).1.1 he'
      have hs : ja ≫ SSet.toTop.map (A k).ι = SSet.toTop.map (A n).ι := by
        rw [← SSet.toTop.map_comp]
        rfl
      have hxu : (SSet.toTop.map (A k).ι).hom (ja.hom x') = x :=
        (congrArg (fun t => t.hom x') hs).trans hx
      have hyu : (SSet.toTop.map (A k).ι).hom (ja.hom y') = y :=
        (congrArg (fun t => t.hom y') hs).trans hy
      simpa only [HomotopyMaps.componentsMap_mk, hxu, hyu] using
        congrArg (HomotopyMaps.componentsMap (SSet.toTop.map (A k).ι).hom) hr

include hA hB hg in
/-- Positive homotopy injectivity at a basepoint in a specified stage.
Only the two representatives and their target homotopy are enlarged. -/
theorem exhaustion_map_groupMap_injective_stage
    (hcoverA : iSup A = ⊤) (hcoverB : iSup B = ⊤)
    (hW : ∀ n, realizationWeakEquivalences (g n))
    (m : ℕ) (x : SSet.toTop.obj (A m : SSet)) (d : ℕ) :
    Function.Injective (HomotopyMaps.groupMap (SSet.toTop.map f).hom (d+1)
      ((SSet.toTop.map (A m).ι).hom x)) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      obtain ⟨n, hmn, p', q', hp, hq⟩ :=
        based_pair_factors_stage K A hA hcoverA m x (d+1) p q
      let gn := SSet.toTop.map (g n)
      let xn := (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hmn))).hom x
      let pB := HomotopyMaps.loopMap gn.hom p'
      let qB := HomotopyMaps.loopMap gn.hom q'
      have ef (z : SSet.toTop.obj (A n : SSet)) :
          (SSet.toTop.map (B n).ι).hom (gn.hom z) =
            (SSet.toTop.map f).hom ((SSet.toTop.map (A n).ι).hom z) := by
        have he := SSet.toTop.congr_map (hg n)
        rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
        exact congrArg (fun t => t.hom z) he
      have ep : (HomotopyMaps.loopMap (SSet.toTop.map (B n).ι).hom pB).val =
          (HomotopyMaps.loopMap (SSet.toTop.map f).hom p).val := by
        apply ContinuousMap.ext
        intro t
        exact (ef (p' t)).trans (congrArg (SSet.toTop.map f).hom (hp t))
      have eq : (HomotopyMaps.loopMap (SSet.toTop.map (B n).ι).hom qB).val =
          (HomotopyMaps.loopMap (SSet.toTop.map f).hom q).val := by
        apply ContinuousMap.ext
        intro t
        exact (ef (q' t)).trans (congrArg (SSet.toTop.map f).hom (hq t))
      obtain ⟨H⟩ : GenLoop.Homotopic (HomotopyMaps.loopMap (SSet.toTop.map f).hom p)
          (HomotopyMaps.loopMap (SSet.toTop.map f).hom q) := Quotient.exact hab
      have H' : GenLoop.Homotopic (HomotopyMaps.loopMap (SSet.toTop.map (B n).ι).hom pB)
          (HomotopyMaps.loopMap (SSet.toTop.map (B n).ι).hom qB) := by
        change Nonempty ((HomotopyMaps.loopMap _ pB).val.HomotopyRel
          (HomotopyMaps.loopMap _ qB).val _)
        rw [ep, eq]
        exact ⟨H⟩
      obtain ⟨k, hnk, hk⟩ := homotopyGroup_eventual_eq L B hB hcoverB n
        (gn.hom xn) (d+1) (Quotient.mk _ pB) (Quotient.mk _ qB) (Quotient.sound H')
      let ja := SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hnk))
      let jb := SSet.toTop.map (SSet.Subcomplex.homOfLE (hB hnk))
      let gk := SSet.toTop.map (g k)
      have hn := SSet.toTop.congr_map (exhaustion_map_naturality f A B hA hB g hg hnk)
      rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hn
      have en (z : SSet.toTop.obj (A n : SSet)) : gk.hom (ja.hom z) = jb.hom (gn.hom z) :=
        congrArg (fun t => t.hom z) hn
      obtain ⟨Hk⟩ : GenLoop.Homotopic (HomotopyMaps.loopMap jb.hom pB)
          (HomotopyMaps.loopMap jb.hom qB) := Quotient.exact hk
      have ekp : (HomotopyMaps.loopMap jb.hom pB).val =
          (HomotopyMaps.loopMap gk.hom (HomotopyMaps.loopMap ja.hom p')).val :=
        ContinuousMap.ext (fun t => (en (p' t)).symm)
      have ekq : (HomotopyMaps.loopMap jb.hom qB).val =
          (HomotopyMaps.loopMap gk.hom (HomotopyMaps.loopMap ja.hom q')).val :=
        ContinuousMap.ext (fun t => (en (q' t)).symm)
      have Hk' : GenLoop.Homotopic
          (HomotopyMaps.loopMap gk.hom (HomotopyMaps.loopMap ja.hom p'))
          (HomotopyMaps.loopMap gk.hom (HomotopyMaps.loopMap ja.hom q')) := by
        change Nonempty ((HomotopyMaps.loopMap gk.hom (HomotopyMaps.loopMap ja.hom p')).val.HomotopyRel
          (HomotopyMaps.loopMap gk.hom (HomotopyMaps.loopMap ja.hom q')).val _)
        rw [← ekp, ← ekq]
        exact ⟨Hk⟩
      have heq : HomotopyMaps.groupMap gk.hom (d+1) (ja.hom xn)
          (Quotient.mk _ (HomotopyMaps.loopMap ja.hom p')) =
          HomotopyMaps.groupMap gk.hom (d+1) (ja.hom xn)
          (Quotient.mk _ (HomotopyMaps.loopMap ja.hom q')) := Quotient.sound Hk'
      have hs := (hW k).2 d (ja.hom xn) |>.1 heq
      obtain ⟨Hs⟩ : GenLoop.Homotopic (HomotopyMaps.loopMap ja.hom p')
          (HomotopyMaps.loopMap ja.hom q') := Quotient.exact hs
      have hi : ja ≫ SSet.toTop.map (A k).ι = SSet.toTop.map (A n).ι := by
        rw [← SSet.toTop.map_comp]
        rfl
      have eip : (HomotopyMaps.loopMap (SSet.toTop.map (A k).ι).hom
            (HomotopyMaps.loopMap ja.hom p')).val = p.val := by
        apply ContinuousMap.ext
        intro t
        exact (congrArg (fun z => z.hom (p' t)) hi).trans (hp t)
      have eiq : (HomotopyMaps.loopMap (SSet.toTop.map (A k).ι).hom
            (HomotopyMaps.loopMap ja.hom q')).val = q.val := by
        apply ContinuousMap.ext
        intro t
        exact (congrArg (fun z => z.hom (q' t)) hi).trans (hq t)
      apply Quotient.sound
      change Nonempty (p.val.HomotopyRel q.val _)
      rw [← eip, ← eiq]
      exact ⟨Hs.compContinuousMap (SSet.toTop.map (A k).ι).hom⟩

include hA hB hg in
/-- Every target sphere has a preimage in some finite stage, with the
original source basepoint retained exactly. -/
theorem exhaustion_map_groupMap_surjective_stage
    (hcoverB : iSup B = ⊤) (hW : ∀ n, realizationWeakEquivalences (g n))
    (m : ℕ) (x : SSet.toTop.obj (A m : SSet)) (d : ℕ) :
    Function.Surjective (HomotopyMaps.groupMap (SSet.toTop.map f).hom (d+1)
      ((SSet.toTop.map (A m).ι).hom x)) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have ef (n : ℕ) (z : SSet.toTop.obj (A n : SSet)) :
        (SSet.toTop.map (B n).ι).hom ((SSet.toTop.map (g n)).hom z) =
          (SSet.toTop.map f).hom ((SSet.toTop.map (A n).ι).hom z) := by
      have he := SSet.toTop.congr_map (hg n)
      rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
      exact congrArg (fun t => t.hom z) he
    let p0 : GenLoop (Fin (d+1)) (SSet.toTop.obj L)
        ((SSet.toTop.map (B m).ι).hom ((SSet.toTop.map (g m)).hom x)) :=
      ⟨p.val, fun t ht => (p.property t ht).trans (ef m x).symm⟩
    obtain ⟨n, hmn, q, hq⟩ := based_cube_factors_stage L B hB hcoverB m
      ((SSet.toTop.map (g m)).hom x) (d+1) p0
    let ja := SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hmn))
    let jb := SSet.toTop.map (SSet.Subcomplex.homOfLE (hB hmn))
    let xn := ja.hom x
    let gn := SSet.toTop.map (g n)
    have hn := SSet.toTop.congr_map (exhaustion_map_naturality f A B hA hB g hg hmn)
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hn
    have en : gn.hom xn = jb.hom ((SSet.toTop.map (g m)).hom x) :=
      congrArg (fun t => t.hom x) hn
    let q' : GenLoop (Fin (d+1)) (SSet.toTop.obj (B n : SSet)) (gn.hom xn) :=
      ⟨q.val, fun t ht => (q.property t ht).trans en.symm⟩
    obtain ⟨a, ha⟩ := (hW n).2 d xn |>.2 (Quotient.mk _ q')
    have hi : ja ≫ SSet.toTop.map (A n).ι = SSet.toTop.map (A m).ι := by
      rw [← SSet.toTop.map_comp]
      rfl
    have ea : (SSet.toTop.map (A n).ι).hom xn = (SSet.toTop.map (A m).ι).hom x :=
      congrArg (fun t => t.hom x) hi
    have eb : (SSet.toTop.map (B n).ι).hom (gn.hom xn) =
        (SSet.toTop.map f).hom ((SSet.toTop.map (A m).ι).hom x) :=
      (ef n xn).trans (congrArg (SSet.toTop.map f).hom ea)
    have hc (b : HomotopyGroup.Pi (d+1) (SSet.toTop.obj (A n : SSet)) xn) :
        HomotopyMaps.basedGroupMap (SSet.toTop.map (B n).ι).hom eb (d+1)
          (HomotopyMaps.groupMap gn.hom (d+1) xn b) =
        HomotopyMaps.groupMap (SSet.toTop.map f).hom (d+1)
          ((SSet.toTop.map (A m).ι).hom x)
          (HomotopyMaps.basedGroupMap (SSet.toTop.map (A n).ι).hom ea (d+1) b) := by
      induction b using Quotient.inductionOn with
      | h b =>
        apply congrArg (Quotient.mk _)
        apply GenLoop.ext
        intro t
        exact ef n (b t)
    refine ⟨HomotopyMaps.basedGroupMap (SSet.toTop.map (A n).ι).hom ea (d+1) a, ?_⟩
    rw [← hc, ha]
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    exact hq

include hA hB hg in
/-- A compatible map of exhaustive increasing simplicial subcomplexes is
an actual weak equivalence whenever every stage map is one. No model
structure, singular comparison, or gluing theorem is assumed. -/
theorem exhaustion_map_weak (hcoverA : iSup A = ⊤) (hcoverB : iSup B = ⊤)
    (hW : ∀ n, realizationWeakEquivalences (g n)) :
    realizationWeakEquivalences f := by
  constructor
  · exact ⟨exhaustion_map_components_injective f A B hA hB g hg hcoverA hcoverB hW,
      exhaustion_map_components_surjective f A B hB g hg hcoverB hW⟩
  · intro d x
    obtain ⟨m, u, hu⟩ := compact_map_factors_stage K A hA hcoverA
      (ContinuousMap.const Unit x)
    have hx : (SSet.toTop.map (A m).ι).hom (u ()) = x :=
      congrArg (fun t : C(_, _) => t ()) hu
    rw [← hx]
    exact ⟨exhaustion_map_groupMap_injective_stage f A B hA hB g hg hcoverA hcoverB hW m (u ()) d,
      exhaustion_map_groupMap_surjective_stage f A B hA hB g hg hcoverB hW m (u ()) d⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Actual cubical sections into finite simplicial cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Only finite powers of the simplicial interval are needed for homotopy groups. -/
def obj (n : ℕ) : SSet.{0} :=
  match n with
  | 0 => Δ[0]
  | n+1 => obj n ⊗ Δ[1]

/-- Continuous coordinates on the realization of a finite simplicial cube. -/
def coordinates (n : ℕ) : C(SSet.toTop.obj (obj n), Fin n → unitInterval) :=
  match n with
  | 0 => ⟨fun _ i => Fin.elim0 i, by fun_prop⟩
  | n+1 => ⟨fun x => Fin.cons
      (PrismBarycentric.realizationTime.hom ((SSet.toTop.map (snd (obj n) Δ[1])).hom x))
      (coordinates n ((SSet.toTop.map (fst (obj n) Δ[1])).hom x)), by
        have ht := PrismBarycentric.realizationTime.hom.continuous.comp
          (SSet.toTop.map (snd (obj n) Δ[1])).hom.continuous
        have hx := (coordinates n).continuous.comp
          (SSet.toTop.map (fst (obj n) Δ[1])).hom.continuous
        apply continuous_pi
        intro i
        cases i using Fin.cases with
        | zero => exact ht
        | succ i => exact (continuous_apply i).comp hx⟩

/-- Iterated realization prisms give a continuous section of the cube coordinates. -/
def sectionMap (n : ℕ) : C((Fin n → unitInterval), SSet.toTop.obj (obj n)) :=
  match n with
  | 0 => ContinuousMap.const _ (default : SSet.toTop.obj (Δ[0] : SSet.{0}))
  | n+1 => ⟨fun p => (RealizedCylinder.comparison (obj n)).hom
      (sectionMap n (Fin.tail p), p 0), by
        apply (RealizedCylinder.comparison (obj n)).hom.continuous.comp
        fun_prop⟩

/-- The section has exactly the specified coordinates, in every dimension. -/
theorem coordinates_section (n : ℕ) (p : Fin n → unitInterval) :
    coordinates n (sectionMap n p) = p := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change Fin.cons
      (PrismBarycentric.realizationTime.hom ((SSet.toTop.map (snd (obj n) Δ[1])).hom
        ((RealizedCylinder.comparison (obj n)).hom (sectionMap n (Fin.tail p), p 0))))
      (coordinates n ((SSet.toTop.map (fst (obj n) Δ[1])).hom
        ((RealizedCylinder.comparison (obj n)).hom (sectionMap n (Fin.tail p), p 0)))) = p
    rw [RealizedCylinder.comparison_time, RealizedCylinder.comparison_first, ih]
    exact Fin.cons_self_tail p

/-- A continuous cube has an exact lift through singular evaluation after finite triangulation. -/
def singularMap {X : TopCat.{0}} (n : ℕ) (p : C((Fin n → unitInterval), X)) :
    obj n ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom (p.comp (coordinates n)))

/-- Evaluation of the realized triangulated lift recovers the original continuous cube. -/
theorem singularMap_evaluation {X : TopCat.{0}} (n : ℕ)
    (p : C((Fin n → unitInterval), X)) (t : Fin n → unitInterval) :
    (sSetTopAdj.counit.app X).hom
      ((SSet.toTop.map (singularMap n p)).hom (sectionMap n t)) = p t := by
  have h : SSet.toTop.map (singularMap n p) ≫ sSetTopAdj.counit.app X =
      TopCat.ofHom (p.comp (coordinates n)) :=
    (sSetTopAdj.homEquiv _ _).symm_apply_apply _
  have he := congrArg (fun f => f.hom (sectionMap n t)) h
  change _ = p (coordinates n (sectionMap n t)) at he
  rw [coordinates_section] at he
  exact he

end

end Thomason.Construction.RealizedCube

end

section

/-! # Face compatibility for the actual cubical realization section -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

def endpoint (e : Bool) : unitInterval := if e then 1 else 0

/-- The coordinate face of a finite simplicial cube. -/
def face (n : ℕ) (i : Fin (n+1)) (e : Bool) : obj n ⟶ obj (n+1) :=
  match n with
  | 0 => if e then SSet.ι₁ else SSet.ι₀
  | n+1 => Fin.cases (if e then SSet.ι₁ else SSet.ι₀)
      (fun j => face n j e ▷ Δ[1]) i

theorem face_zero (n : ℕ) (e : Bool) :
    face n 0 e = if e then SSet.ι₁ else SSet.ι₀ := by cases n <;> rfl

theorem face_succ (n : ℕ) (i : Fin (n+1)) (e : Bool) :
    face (n+1) i.succ e = face n i e ▷ Δ[1] := rfl

theorem coordinates_comparison (n : ℕ) (x : SSet.toTop.obj (obj n)) (t : unitInterval) :
    coordinates (n+1) ((RealizedCylinder.comparison (obj n)).hom (x, t)) =
      Fin.cons t (coordinates n x) := by
  change (Fin.cons
    (PrismBarycentric.realizationTime.hom ((SSet.toTop.map (snd (obj n) Δ[1])).hom
      ((RealizedCylinder.comparison (obj n)).hom (x, t))))
    (coordinates n ((SSet.toTop.map (fst (obj n) Δ[1])).hom
      ((RealizedCylinder.comparison (obj n)).hom (x, t)))) : Fin (n+1) → unitInterval) = _
  rw [RealizedCylinder.comparison_time, RealizedCylinder.comparison_first]

theorem face_zero_apply (n : ℕ) (e : Bool) (x : SSet.toTop.obj (obj n)) :
    (SSet.toTop.map (face n 0 e)).hom x =
      (RealizedCylinder.comparison (obj n)).hom (x, endpoint e) := by
  rw [face_zero]
  cases e
  · exact (RealizedCylinder.comparison_zero _ _).symm
  · exact (RealizedCylinder.comparison_one _ _).symm

/-- The two projections of a mapped prism are its mapped base and unchanged time. -/
theorem coordinates_whisker {K : SSet.{0}} (n : ℕ) (f : K ⟶ obj n)
    (x : SSet.toTop.obj (K ⊗ Δ[1])) :
    coordinates (n+1) ((SSet.toTop.map (f ▷ Δ[1])).hom x) =
      Fin.cons
        (PrismBarycentric.realizationTime.hom ((SSet.toTop.map (snd K Δ[1])).hom x))
        (coordinates n ((SSet.toTop.map f).hom ((SSet.toTop.map (fst K Δ[1])).hom x))) := by
  have hs := congrArg (fun g => g.hom x)
    (SSet.toTop.congr_map (whiskerRight_snd f Δ[1]))
  have hf := congrArg (fun g => g.hom x)
    (SSet.toTop.congr_map (whiskerRight_fst f Δ[1]))
  simp only [SSet.toTop.map_comp] at hs hf
  change (SSet.toTop.map (snd (obj n) Δ[1])).hom
    ((SSet.toTop.map (f ▷ Δ[1])).hom x) = (SSet.toTop.map (snd K Δ[1])).hom x at hs
  change (SSet.toTop.map (fst (obj n) Δ[1])).hom
    ((SSet.toTop.map (f ▷ Δ[1])).hom x) =
      (SSet.toTop.map f).hom ((SSet.toTop.map (fst K Δ[1])).hom x) at hf
  change (Fin.cons
    (PrismBarycentric.realizationTime.hom ((SSet.toTop.map (snd (obj n) Δ[1])).hom
      ((SSet.toTop.map (f ▷ Δ[1])).hom x)))
    (coordinates n ((SSet.toTop.map (fst (obj n) Δ[1])).hom
      ((SSet.toTop.map (f ▷ Δ[1])).hom x))) : Fin (n+1) → unitInterval) = _
  rw [hs, hf]

/-- Every realized simplicial face has the expected cubical coordinates. -/
theorem coordinates_face (n : ℕ) (i : Fin (n+1)) (e : Bool)
    (x : SSet.toTop.obj (obj n)) :
    coordinates (n+1) ((SSet.toTop.map (face n i e)).hom x) =
      Fin.insertNth i (endpoint e) (coordinates n x) := by
  induction n with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    rw [face_zero_apply, coordinates_comparison, Fin.insertNth_zero']
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rw [face_zero_apply, coordinates_comparison, Fin.insertNth_zero']
    | succ i =>
      rw [face_succ]
      have hc := coordinates_whisker (n+1) (face n i e) x
      rw [ih] at hc
      refine hc.trans ?_
      exact (Fin.insertNth_succ_cons i (endpoint e) _ _).symm

/-- The chosen section sends every topological face into the corresponding simplicial face. -/
theorem section_face (n : ℕ) (i : Fin (n+1)) (e : Bool) (p : Fin n → unitInterval) :
    sectionMap (n+1) (Fin.insertNth i (endpoint e) p) =
      (SSet.toTop.map (face n i e)).hom (sectionMap n p) := by
  induction n with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    rw [Fin.insertNth_zero', face_zero_apply]
    rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [Fin.insertNth_zero', face_zero_apply]
      rfl
    | succ i =>
      rw [face_succ, ← Fin.cons_self_tail p, Fin.insertNth_succ_cons]
      change (RealizedCylinder.comparison (obj (n+1))).hom
        (sectionMap (n+1) (Fin.insertNth i (endpoint e) (Fin.tail p)), p 0) =
        (SSet.toTop.map (face n i e ▷ Δ[1])).hom
          ((RealizedCylinder.comparison (obj n)).hom (sectionMap n (Fin.tail p), p 0))
      rw [ih]
      exact congrArg (fun f => f.hom (sectionMap n (Fin.tail p), p 0))
        (RealizedCylinder.comparison_naturality (face n i e))

end

end Thomason.Construction.RealizedCube

end

section

/-! # The topological cube boundary is a retract of the realized simplicial pair -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory Convexity Topology
open RealizationPrism
open scoped Simplicial

noncomputable section

/-- All coordinate faces of the `(n+1)`-dimensional simplicial cube. -/
def boundary (n : ℕ) : (obj (n+1)).Subcomplex :=
  ⨆ a : Fin (n+1) × Bool, SSet.Subcomplex.range (face n a.1 a.2)

theorem range_boundary_inclusion (n : ℕ) :
    Set.range (SSet.toTop.map (boundary n).ι).hom =
      ⋃ a : Fin (n+1) × Bool, Set.range (SSet.toTop.map (face n a.1 a.2)).hom := by
  rw [boundary, range_iSup_inclusion]
  congr 1
  funext a
  exact (range_realized_map (face n a.1 a.2)).symm

/-- The coordinates of every point of the realized boundary lie on a
    topological coordinate face. -/
theorem coordinates_boundary (n : ℕ)
    (x : SSet.toTop.obj (boundary n : SSet.{0})) :
    coordinates (n+1) ((SSet.toTop.map (boundary n).ι).hom x) ∈
      Cube.boundary (Fin (n+1)) := by
  have hx : (SSet.toTop.map (boundary n).ι).hom x ∈
      Set.range (SSet.toTop.map (boundary n).ι).hom := ⟨x, rfl⟩
  rw [range_boundary_inclusion] at hx
  obtain ⟨⟨i, e⟩, y, hy⟩ := Set.mem_iUnion.mp hx
  rw [← hy, coordinates_face]
  refine ⟨i, ?_⟩
  rw [Fin.insertNth_apply_same]
  cases e
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The cubical section preserves the entire boundary as a subspace. -/
theorem section_mem_boundary (n : ℕ) (x : Fin (n+1) → unitInterval)
    (hx : x ∈ Cube.boundary (Fin (n+1))) :
    sectionMap (n+1) x ∈ Set.range (SSet.toTop.map (boundary n).ι).hom := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨e, he⟩ : ∃ e : Bool, x i = endpoint e := by
    rcases hi with hi | hi
    · exact ⟨false, hi⟩
    · exact ⟨true, hi⟩
  have hx' : x = Fin.insertNth i (endpoint e) (Fin.removeNth i x) := by
    rw [← he, Fin.insertNth_self_removeNth]
  rw [range_boundary_inclusion]
  refine Set.mem_iUnion.mpr ⟨(i, e), sectionMap n (Fin.removeNth i x), ?_⟩
  exact (section_face n i e (Fin.removeNth i x)).symm.trans
    (congrArg (sectionMap (n+1)) hx'.symm)

def boundaryCoordinates (n : ℕ) :
    C(SSet.toTop.obj (boundary n : SSet.{0}), Cube.boundary (Fin (n+1))) where
  toFun x := ⟨coordinates (n+1) ((SSet.toTop.map (boundary n).ι).hom x),
    coordinates_boundary n x⟩
  continuous_toFun := ((coordinates (n+1)).continuous.comp
    (SSet.toTop.map (boundary n).ι).hom.continuous).subtype_mk _

/-- The ordinary boundary section, with values in the actual realized
    simplicial boundary. -/
def boundarySection (n : ℕ) :
    C(Cube.boundary (Fin (n+1)), SSet.toTop.obj (boundary n : SSet.{0})) :=
  let e := (inclusion_isClosedEmbedding (obj (n+1)) (boundary n)).isEmbedding.toHomeomorph
  let toRange : C(Cube.boundary (Fin (n+1)),
      Set.range (SSet.toTop.map (boundary n).ι).hom) := {
    toFun := fun x => ⟨sectionMap (n+1) x.val, section_mem_boundary n x.val x.property⟩
    continuous_toFun := ((sectionMap (n+1)).continuous.comp continuous_subtype_val).subtype_mk _ }
  (e.symm : C(_, _)).comp toRange

theorem boundarySection_inclusion (n : ℕ) (x : Cube.boundary (Fin (n+1))) :
    (SSet.toTop.map (boundary n).ι).hom (boundarySection n x) = sectionMap (n+1) x.val := by
  let e := (inclusion_isClosedEmbedding (obj (n+1)) (boundary n)).isEmbedding.toHomeomorph
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨sectionMap (n+1) x.val, section_mem_boundary n x.val x.property⟩)

theorem boundaryCoordinates_section (n : ℕ) (x : Cube.boundary (Fin (n+1))) :
    boundaryCoordinates n (boundarySection n x) = x := by
  apply Subtype.ext
  change coordinates (n+1) ((SSet.toTop.map (boundary n).ι).hom (boundarySection n x)) = x.val
  rw [boundarySection_inclusion, coordinates_section]

def boundaryInclusion (n : ℕ) :
    TopCat.of (Cube.boundary (Fin (n+1))) ⟶ TopCat.of (Fin (n+1) → unitInterval) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A retract in the actual topological arrow category, preserving both
    boundaries and ambient cubes. -/
def boundaryArrowRetract (n : ℕ) :
    RetractArrow (boundaryInclusion n) (SSet.toTop.map (boundary n).ι) where
  i := Arrow.homMk (TopCat.ofHom (boundarySection n)) (TopCat.ofHom (sectionMap (n+1))) (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact boundarySection_inclusion n)
  r := Arrow.homMk (TopCat.ofHom (boundaryCoordinates n)) (TopCat.ofHom (coordinates (n+1))) (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl)
  retract := by
    apply Arrow.hom_ext
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      exact boundaryCoordinates_section n
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      exact coordinates_section (n+1)

/-- Barycentric boundary lifting implies ordinary cubical boundary lifting,
    without a singular comparison or a Kan--Quillen model structure. -/
theorem boundary_lifting_of_barycentric {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : ∀ n, HasLiftingProperty (RealizationPrism.boundaryInclusion n) p) (n : ℕ) :
    HasLiftingProperty (boundaryInclusion n) p := by
  let := realization_mono_lifting p hp (boundary n).ι
  exact (boundaryArrowRetract n).leftLiftingProperty p

end

end Thomason.Construction.RealizedCube

end

section

/-! # Prescribing both ends and the fixed boundary of a cubical homotopy -/

namespace Thomason.Construction.CubeBoundaryValues

open Topology Convexity

noncomputable section

theorem isClosed_boundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have he : Cube.boundary (Fin n) =
      ⋃ i : Fin n, Set.ofPred (fun t => t i = 0 ∨ t i = 1) := by
    ext t
    simp [Cube.boundary]
  rw [he]
  apply isClosed_iUnion_of_finite
  intro i
  exact (isClosed_eq (continuous_apply i) continuous_const).union
    (isClosed_eq (continuous_apply i) continuous_const)

def region (n : ℕ) : Fin 3 → Set (Cube.boundary (Fin (n+1))) :=
  ![Set.ofPred (fun t => t.val 0 = 0),
    Set.ofPred (fun t => t.val 0 = 1),
    Set.ofPred (fun t => Fin.tail t.val ∈ Cube.boundary (Fin n))]

theorem region_closed (n : ℕ) (i : Fin 3) : IsClosed (region n i) := by
  fin_cases i
  · exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const
  · exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const
  · exact (isClosed_boundary n).preimage (by fun_prop)

theorem region_cover (n : ℕ) : ⋃ i, region n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨i, hi⟩ := t.property
  cases i using Fin.cases with
  | zero =>
    rcases hi with hi | hi
    · exact Set.mem_iUnion.mpr ⟨0, hi⟩
    · exact Set.mem_iUnion.mpr ⟨1, hi⟩
  | succ i => exact Set.mem_iUnion.mpr ⟨2, i, hi⟩

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

def chart (p q : GenLoop (Fin n) X x) (i : Fin 3) : C(region n i, X) :=
  if i = 0 then ⟨fun t => p (Fin.tail t.val.val), by fun_prop⟩
  else if i = 1 then ⟨fun t => q (Fin.tail t.val.val), by fun_prop⟩
  else ContinuousMap.const _ x

theorem chart_overlap (p q : GenLoop (Fin n) X x) (i j : Fin 3)
    (t : Cube.boundary (Fin (n+1))) (hi : t ∈ region n i) (hj : t ∈ region n j) :
    chart p q i ⟨t, hi⟩ = chart p q j ⟨t, hj⟩ := by
  fin_cases i <;> fin_cases j <;> simp only [chart]
  · exact (zero_ne_one (α := unitInterval) (hi.symm.trans hj)).elim
  · exact p.property _ hj
  · exact (zero_ne_one (α := unitInterval) (hj.symm.trans hi)).elim
  · exact q.property _ hj
  · exact (p.property _ hi).symm
  · exact (q.property _ hi).symm

/-- The boundary map with `p` at time zero, `q` at time one, and value `x`
    on every lateral face. -/
def map (p q : GenLoop (Fin n) X x) : C(Cube.boundary (Fin (n+1)), X) where
  toFun := Set.liftCover (region n) (fun i => chart p q i) (chart_overlap p q) (region_cover n)
  continuous_toFun := by
    apply (locallyFinite_of_finite (region n)).continuous (region_cover n) (region_closed n)
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (region n i).domRestrict
        (Set.liftCover (region n) (fun i => chart p q i) (chart_overlap p q) (region_cover n)) =
        chart p q i := by
      funext t
      exact Set.liftCover_coe t
    rw [he]
    exact (chart p q i).continuous

theorem map_zero (p q : GenLoop (Fin n) X x) (t : Cube.boundary (Fin (n+1)))
    (ht : t.val 0 = 0) : map p q t = p (Fin.tail t.val) := by
  change Set.liftCover (region n) (fun i => chart p q i) (chart_overlap p q) (region_cover n) t = _
  exact Set.liftCover_of_mem (i := 0) ht

theorem map_one (p q : GenLoop (Fin n) X x) (t : Cube.boundary (Fin (n+1)))
    (ht : t.val 0 = 1) : map p q t = q (Fin.tail t.val) := by
  change Set.liftCover (region n) (fun i => chart p q i) (chart_overlap p q) (region_cover n) t = _
  exact Set.liftCover_of_mem (i := 1) ht

theorem map_lateral (p q : GenLoop (Fin n) X x) (t : Cube.boundary (Fin (n+1)))
    (ht : Fin.tail t.val ∈ Cube.boundary (Fin n)) : map p q t = x := by
  change Set.liftCover (region n) (fun i => chart p q i) (chart_overlap p q) (region_cover n) t = _
  exact Set.liftCover_of_mem (i := 2) ht

end

end Thomason.Construction.CubeBoundaryValues

end

section

/-! # Lifting based homotopies through ordinary cubical boundary lifting -/

namespace Thomason.Construction.CubicalLifting

open CategoryTheory Topology

noncomputable section

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {x : X} {n : ℕ}
  (p q : GenLoop (Fin n) X x)
  (H : (HomotopyMaps.loopMap f.hom p).val.HomotopyRel
    (HomotopyMaps.loopMap f.hom q).val (Cube.boundary (Fin n)))

def homotopyCube : C((Fin (n+1) → unitInterval), Y) where
  toFun t := H (t 0, Fin.tail t)
  continuous_toFun := H.continuous.comp (by fun_prop)

theorem homotopyBoundarySquare :
    CommSq (TopCat.ofHom (CubeBoundaryValues.map p q)) (RealizedCube.boundaryInclusion n)
      f (TopCat.ofHom (homotopyCube f p q H)) := by
  constructor
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro t
  change f.hom (CubeBoundaryValues.map p q t) = H (t.val 0, Fin.tail t.val)
  by_cases hzero : t.val 0 = 0
  · rw [CubeBoundaryValues.map_zero p q t hzero, hzero, H.apply_zero]
    rfl
  by_cases hone : t.val 0 = 1
  · rw [CubeBoundaryValues.map_one p q t hone, hone, H.apply_one]
    rfl
  have htail : Fin.tail t.val ∈ Cube.boundary (Fin n) := by
    obtain ⟨i, hi⟩ := t.property
    cases i using Fin.cases with
    | zero => exact (hi.elim hzero hone).elim
    | succ i => exact ⟨i, hi⟩
  rw [CubeBoundaryValues.map_lateral p q t htail, H.eq_fst _ htail]
  exact congrArg f.hom (p.property _ htail).symm

structure HomotopyLift where
  homotopy : p.val.HomotopyRel q.val (Cube.boundary (Fin n))
  map_homotopy : ∀ z, f.hom (homotopy z) = H z

/-- The full homotopy lifts with both endpoints and all boundary values
    prescribed; this is stronger than lifting an unbased path. -/
def liftHomotopy (hf : ∀ m, HasLiftingProperty (RealizedCube.boundaryInclusion m) f) :
    HomotopyLift f p q H := by
  let := hf n
  let sq := homotopyBoundarySquare f p q H
  let l := sq.lift
  have hb (t : Cube.boundary (Fin (n+1))) : l.hom t.val = CubeBoundaryValues.map p q t :=
    ConcreteCategory.congr_hom sq.fac_left t
  let H' : p.val.HomotopyRel q.val (Cube.boundary (Fin n)) := {
    toFun z := l.hom (Fin.cons z.1 z.2)
    continuous_toFun := l.hom.continuous.comp (by fun_prop)
    map_zero_left t := by
      let u : Cube.boundary (Fin (n+1)) := ⟨Fin.cons 0 t, 0, Or.inl rfl⟩
      exact (hb u).trans (CubeBoundaryValues.map_zero p q u rfl)
    map_one_left t := by
      let u : Cube.boundary (Fin (n+1)) := ⟨Fin.cons 1 t, 0, Or.inr rfl⟩
      exact (hb u).trans (CubeBoundaryValues.map_one p q u rfl)
    prop' t u hu := by
      obtain ⟨i, hi⟩ := hu
      let v : Cube.boundary (Fin (n+1)) := ⟨Fin.cons t u, i.succ, hi⟩
      exact (hb v).trans ((CubeBoundaryValues.map_lateral p q v ⟨i, hi⟩).trans
        (p.property u ⟨i, hi⟩).symm) }
  refine ⟨H', ?_⟩
  intro z
  exact ConcreteCategory.congr_hom sq.fac_right (Fin.cons z.1 z.2)

end

end Thomason.Construction.CubicalLifting

end

section

/-! # Simplexes contained entirely in a sieve -/

namespace Thomason.Construction.SieveSimplex

open CategoryTheory StrictOmegaCategory

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Every cell of a simplex in the sieve belongs to its full zero fibre. -/
noncomputable def whole {m : ℕ} (s : Fin (m+1) →o A) :
    h.object m ⟶ labelFiber (label A hA ((subposetInclusion A).comp s) h) 0 where
  toFun x := ⟨x, (SimplexComplex.binaryLabel_fullCell_iff h
    ((sieveCharacteristic A hA).comp ((subposetInclusion A).comp s)) 0 x).mpr
      ⟨(sieveCharacteristic_zero_iff A hA _).mpr (s _).property,
       (sieveCharacteristic_zero_iff A hA _).mpr (s _).property⟩⟩
  map_face _ _ _ := Subtype.ext rfl
  map_comp _ _ _ _ _ := Subtype.ext rfl

omit [StrictColimitsInput] in
/-- The clamped vertex map of a simplex already in the sieve is unchanged. -/
theorem whole_cut_clamp {m : ℕ} (s : Fin (m+1) →o A)
    (c : Cut A ((subposetInclusion A).comp s)) : c.clamp = s := by
  apply DFunLike.ext
  intro i
  apply Subtype.ext
  exact c.clamp_of_mem i (s i).property

/-- On an entire sieve simplex, the clamping inverse is its original colimit leg. -/
theorem whole_back {m : ℕ} (s : Fin (m+1) →o A) :
    whole A hA h s ≫ back A hA h ((subposetInclusion A).comp s) = h.posetLeg s := by
  let c := cut A hA ((subposetInclusion A).comp s) ⟨0, (s 0).property⟩
  rw [back_eq_cut A hA h _ c]
  change (whole A hA h s ≫ labelFiberInclusion _ 0) ≫ h.posetLeg c.clamp = _
  have he : whole A hA h s ≫ labelFiberInclusion _ 0 = 𝟙 (h.object _) := by
    apply Hom.ext
    rfl
  rw [he, Category.id_comp, whole_cut_clamp A s c]

end Thomason.Construction.SieveSimplex

end

section

/-! # The standard simplex is an explicit retract of the finite cube -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Count the interval coordinates of a cube simplex, pointwise along its
ordinal parameter. This is monotone in that parameter. -/
def cubeSimplexRank (n : ℕ) : {d : SimplexCategoryᵒᵖ} →
    (RealizedCube.obj n).obj d → (Fin (d.unop.len + 1) →o Fin (n+1)) :=
  match n with
  | 0 => fun _ => OrderHom.const _ 0
  | n+1 => fun x => {
      toFun j := ⟨(cubeSimplexRank n x.1 j).val +
        ((SSet.stdSimplex.objEquiv x.2).toOrderHom j).val, by
          have h₀ := (cubeSimplexRank n x.1 j).isLt
          have h₁ := ((SSet.stdSimplex.objEquiv x.2).toOrderHom j).isLt
          change _ < 2 at h₁
          omega⟩
      monotone' := by
        intro i j hij
        exact Nat.add_le_add ((cubeSimplexRank n x.1).monotone hij)
          ((SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone hij) }

/-- Counting commutes exactly with every ordinal face and degeneracy. -/
theorem cubeSimplexRank_naturality (n : ℕ) {d e : SimplexCategoryᵒᵖ} (f : d ⟶ e)
    (x : (RealizedCube.obj n).obj d) (j : Fin (e.unop.len+1)) :
    cubeSimplexRank n ((RealizedCube.obj n).map f x) j =
      cubeSimplexRank n x (f.unop.toOrderHom j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Fin.ext
    change (cubeSimplexRank n ((RealizedCube.obj n).map f x.1) j).val +
        ((SSet.stdSimplex.objEquiv ((Δ[1] : SSet.{0}).map f x.2)).toOrderHom j).val = _
    rw [ih]
    rfl

/-- The actual simplicial map from the cube to the simplex counting its
ordered interval coordinates. -/
def cubeToSimplex (n : ℕ) : RealizedCube.obj n ⟶ (Δ[n] : SSet.{0}) where
  app d := ↾fun x => SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (cubeSimplexRank n x))
  naturality d e f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    exact cubeSimplexRank_naturality n f x j

/-- Truncate the last vertex of a standard simplex to its preceding one. -/
def simplexCubeClamp (n : ℕ) : ⦋n+1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk {
    toFun i := ⟨min i.val n, Nat.lt_succ_of_le (min_le_right _ _)⟩
    monotone' := by
      intro i j hij
      change min i.val n ≤ min j.val n
      exact min_le_min_right n (show i.val ≤ j.val from hij) }

/-- The final Boolean coordinate records exactly the final simplex vertex. -/
def simplexCubeLast (n : ℕ) : ⦋n+1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk {
    toFun i := if i.val = n+1 then 1 else 0
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj
      · exact le_rfl
      · have hj' := j.isLt
        have hi' : i.val ≤ j.val := hij
        change j.val < n + 2 at hj'
        change (1 : Fin 2) ≤ 0
        exfalso
        omega
      · decide
      · exact le_rfl }

/-- Embed the ordered simplex as the chain of cube vertices with increasing
numbers of final coordinates. -/
def simplexToCube (n : ℕ) : (Δ[n] : SSet.{0}) ⟶ RealizedCube.obj n :=
  match n with
  | 0 => 𝟙 _
  | n+1 => lift (SSet.stdSimplex.map (simplexCubeClamp n) ≫ simplexToCube n)
      (SSet.stdSimplex.map (simplexCubeLast n))

/-- Counting the embedded coordinates recovers every ordinal coordinate,
including degenerate simplices. -/
theorem cubeSimplexRank_simplexToCube (n : ℕ) {d : SimplexCategoryᵒᵖ}
    (x : (Δ[n] : SSet.{0}).obj d) (j : Fin (d.unop.len+1)) :
    cubeSimplexRank n ((simplexToCube n).app d x) j =
      (SSet.stdSimplex.objEquiv x).toOrderHom j := by
  induction n with
  | zero =>
    apply Fin.ext
    have hx := ((SSet.stdSimplex.objEquiv x).toOrderHom j).isLt
    change ((SSet.stdSimplex.objEquiv x).toOrderHom j).val < 1 at hx
    change 0 = _
    omega
  | succ n ih =>
    apply Fin.ext
    change (cubeSimplexRank n ((simplexToCube n).app d
        ((SSet.stdSimplex.map (simplexCubeClamp n)).app d x)) j).val +
      ((SSet.stdSimplex.objEquiv
        ((SSet.stdSimplex.map (simplexCubeLast n)).app d x)).toOrderHom j).val = _
    rw [ih]
    change min ((SSet.stdSimplex.objEquiv x).toOrderHom j).val n +
      (if ((SSet.stdSimplex.objEquiv x).toOrderHom j).val = n+1 then (1 : Fin 2) else 0).val =
      ((SSet.stdSimplex.objEquiv x).toOrderHom j).val
    have hj := ((SSet.stdSimplex.objEquiv x).toOrderHom j).isLt
    change ((SSet.stdSimplex.objEquiv x).toOrderHom j).val < n + 2 at hj
    split_ifs <;> simp_all only [Fin.val_one, Fin.val_zero] <;> omega

/-- The standard simplex is a genuine simplicial retract of the cube of
the same dimension. No geometric approximation is involved. -/
theorem simplexToCube_cubeToSimplex (n : ℕ) :
    simplexToCube n ≫ cubeToSimplex n = 𝟙 (Δ[n] : SSet.{0}) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  exact cubeSimplexRank_simplexToCube n x j

end

end Thomason.Construction

end

end OAI
