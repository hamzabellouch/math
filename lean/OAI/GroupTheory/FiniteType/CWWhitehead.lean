import Mathlib
import OAI.GroupTheory.FiniteType.CoveringCellGeometryHausdorff
import OAI.GroupTheory.FiniteType.CubeDisk
import OAI.GroupTheory.FiniteType.SequentialColimitRangeInclMono

namespace OAI

noncomputable section

namespace CWWhitehead
open Set Topology Metric CWExtension
open scoped unitInterval
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

structure Stage (f₀ f₁ : C(C,Y)) (n : ℕ) where
  path : C(Skel C n,C(I,Y))
  at_zero : ∀ x, path x 0 = f₀ (skelToComplex n x)
  at_one : ∀ x, path x 1 = f₁ (skelToComplex n x)

variable {f₀ f₁ : C(C,Y)} {n : ℕ}

def cellSide (H : Stage f₀ f₁ n) (i : RelCWComplex.cell C n) : C(I × Boundary n,Y) :=
  ⟨fun z => H.path (boundarySkel n i z.2) z.1,
    (H.path.continuous.comp ((boundarySkel n i).continuous.comp continuous_snd)).eval continuous_fst⟩

theorem exists_cell_extension (hfill : CWCylinder.SphereFill Y)
    (H : Stage f₀ f₁ n) (i : RelCWComplex.cell C n) :
    ∃ g : C(Disk n,C(I,Y)),
      (∀ v, g v 0 = f₀ (charMap n i v)) ∧
      (∀ v, g v 1 = f₁ (charMap n i v)) ∧
      ∀ v : Boundary n,g (CWCylinder.boundaryDisk n v) = H.path (boundarySkel n i v) := by
  have h₀ : ∀ v,cellSide H i (0,v) = (f₀.comp (charMap n i)) (CWCylinder.boundaryDisk n v) := by
    intro v
    exact H.at_zero (boundarySkel n i v)
  have h₁ : ∀ v,cellSide H i (1,v) = (f₁.comp (charMap n i)) (CWCylinder.boundaryDisk n v) := by
    intro v
    exact H.at_one (boundarySkel n i v)
  obtain ⟨F,hF₀,hF₁,hFside⟩ := CWCylinder.exists_cylinder hfill
    (f₀.comp (charMap n i)) (f₁.comp (charMap n i)) (cellSide H i) h₀ h₁
  refine ⟨(F.comp ⟨Prod.swap,continuous_swap⟩).curry,hF₀,hF₁,?_⟩
  intro v
  ext t
  exact hFside t v

theorem exists_next (hfill : CWCylinder.SphereFill Y) (H : Stage f₀ f₁ n) :
    ∃ K : Stage f₀ f₁ (n+1),∀ x,K.path (skelIncl n x) = H.path x := by
  classical
  choose g hg₀ hg₁ hgb using exists_cell_extension hfill H
  change ∀ i (v : Boundary n), g i ⟨v,sphere_subset_closedBall v.2⟩ = H.path (boundarySkel n i v) at hgb
  let Kpath := extendSkel n H.path g hgb
  have h₀ : ∀ x,Kpath x 0 = f₀ (skelToComplex (n+1) x) := by
    intro x
    obtain ⟨a,rfl⟩ := stageQuot_surjective n x
    rcases a with a | ⟨i,v⟩
    · change (extendSkel n H.path g hgb (skelIncl n a)) 0 = _
      rw [extendSkel_prior]
      exact H.at_zero a
    · change (extendSkel n H.path g hgb (charSkel n i v)) 0 = _
      rw [extendSkel_disk]
      exact hg₀ i v
  have h₁ : ∀ x,Kpath x 1 = f₁ (skelToComplex (n+1) x) := by
    intro x
    obtain ⟨a,rfl⟩ := stageQuot_surjective n x
    rcases a with a | ⟨i,v⟩
    · change (extendSkel n H.path g hgb (skelIncl n a)) 1 = _
      rw [extendSkel_prior]
      exact H.at_one a
    · change (extendSkel n H.path g hgb (charSkel n i v)) 1 = _
      rw [extendSkel_disk]
      exact hg₁ i v
  exact ⟨⟨Kpath,h₀,h₁⟩,fun x => extendSkel_prior n H.path g hgb x⟩

def next (hfill : CWCylinder.SphereFill Y) (H : Stage f₀ f₁ n) : Stage f₀ f₁ (n+1) :=
  (exists_next hfill H).choose

theorem next_compat (hfill : CWCylinder.SphereFill Y) (H : Stage f₀ f₁ n) (x : Skel C n) :
    (next hfill H).path (skelIncl n x) = H.path x :=
  (exists_next hfill H).choose_spec x

def emptyStage (f₀ f₁ : C(C,Y)) : Stage f₀ f₁ 0 := by
  letI : IsEmpty (Skel C 0) := ⟨fun x => by
    have hx := x.2
    simp only [Skel,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,mem_empty_iff_false] at hx⟩
  exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun x => isEmptyElim x⟩

def build (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) : (n : ℕ) → Stage f₀ f₁ n
  | 0 => emptyStage f₀ f₁
  | n+1 => next hfill (build hfill f₀ f₁ n)

theorem build_compat (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) (n : ℕ) (x : Skel C n) :
    (build hfill f₀ f₁ (n+1)).path (skelIncl n x) = (build hfill f₀ f₁ n).path x :=
  next_compat hfill (build hfill f₀ f₁ n) x

def allPaths (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) : C(C,C(I,Y)) :=
  unionMap (fun n => (build hfill f₀ f₁ n).path) (build_compat hfill f₀ f₁)

theorem allPaths_zero (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) (x : C) :
    allPaths hfill f₀ f₁ x 0 = f₀ x := by
  obtain ⟨⟨n,y⟩,rfl⟩ := wholeQuot_surjective (C := C) x
  change unionMap (fun k => (build hfill f₀ f₁ k).path) (build_compat hfill f₀ f₁) (skelToComplex n y) 0 = _
  rw [unionMap_skel]
  exact (build hfill f₀ f₁ n).at_zero y

theorem allPaths_one (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) (x : C) :
    allPaths hfill f₀ f₁ x 1 = f₁ x := by
  obtain ⟨⟨n,y⟩,rfl⟩ := wholeQuot_surjective (C := C) x
  change unionMap (fun k => (build hfill f₀ f₁ k).path) (build_compat hfill f₀ f₁) (skelToComplex n y) 1 = _
  rw [unionMap_skel]
  exact (build hfill f₀ f₁ n).at_one y

def homotopy (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) : f₀.Homotopy f₁ where
  toFun z := allPaths hfill f₀ f₁ z.2 z.1
  continuous_toFun := ((allPaths hfill f₀ f₁).continuous.comp continuous_snd).eval continuous_fst
  map_zero_left := allPaths_zero hfill f₀ f₁
  map_one_left := allPaths_one hfill f₀ f₁

theorem contractible_subtype [Nonempty C] (hfill : CWCylinder.SphereFill C) : ContractibleSpace C := by
  obtain ⟨x⟩ := ‹Nonempty C›
  apply (contractible_iff_id_nullhomotopic C).mpr
  exact ⟨x,⟨homotopy hfill (.id C) (.const C x)⟩⟩

end CWWhitehead

namespace SequentialCoreTower
open Set Topology Metric
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)
  [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)] [∀ n, CompactSpace (X n)]
  [∀ n, Nonempty (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))
  (hπ : ∀ n p, p ≤ n → ∀ z : (Z n).TotalSpace,
    Subsingleton (HomotopyGroup (Fin p) (Z n).TotalSpace z))

include hf hπ in

lemma sphereFill : CWCylinder.SphereFill (core X f I δ Z pot hBase hPot hCoord).TotalSpace := by
  intro n g
  obtain ⟨k,hk,h,hh⟩ := compact_map_factors_above X f I δ Z pot hBase hPot hCoord hf g n
  have hn : h.Nullhomotopic := by
    cases n with
    | zero =>
      let : IsEmpty (CWExtension.Boundary 0) := ⟨fun v => by
        have hv : ‖v.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using v.2
        have he : v.1 = 0 := Subsingleton.elim _ _
        rw [he,norm_zero] at hv
        exact zero_ne_one hv⟩
      obtain ⟨x⟩ := (inferInstance : Nonempty (X k))
      let z : (Z k).TotalSpace := ⟨x,(1:Q)⟩
      have he : h = .const (CWExtension.Boundary 0) z := by
        apply ContinuousMap.ext
        intro v
        exact isEmptyElim v
      rw [he]
      exact ContinuousMap.nullhomotopic_of_constant z
    | succ p =>
      let := hπ k p (by omega) (h (SphereQuotient.pole p))
      exact WeakSphere.sphere_nullhomotopic p h
  obtain ⟨H,hH⟩ := SphereExtension.exists_extension h hn
  exact ⟨(coverIncl X f I δ Z pot hBase hPot hCoord k).comp H,fun v => by
    change coverIncl X f I δ Z pot hBase hPot hCoord k (H _) = g v
    exact (congrArg (coverIncl X f I δ Z pot hBase hPot hCoord k) (hH v)).trans (hh v)⟩

include hf hπ in

lemma contractible [DiscreteTopology Q]
    [CWComplex (univ : Set (SequentialColimit.Space X f))] :
    ContractibleSpace (core X f I δ Z pot hBase hPot hCoord).TotalSpace := by
  let W := core X f I δ Z pot hBase hPot hCoord
  let := SequentialColimit.hausdorff X f hf
  let := CoveringCellGeometry.hausdorff (core_covering X f I δ Z pot hBase hPot hCoord)
  let := CoveringCW.cwComplex_general (core_covering X f I δ Z pot hBase hPot hCoord)
  obtain ⟨x⟩ := (inferInstance : Nonempty (X 0))
  let z : W.TotalSpace := ⟨SequentialColimit.incl X f 0 x,(1:Q)⟩
  let e := Homeomorph.Set.univ W.TotalSpace
  let H := CWWhitehead.homotopy (sphereFill X f I δ Z pot hBase hPot hCoord hf hπ)
    (⟨e,e.continuous⟩ : C((univ : Set W.TotalSpace),W.TotalSpace)) (.const _ z)
  apply (contractible_iff_id_nullhomotopic W.TotalSpace).mpr
  refine ⟨z,⟨?_⟩⟩
  exact { toFun := fun v => H (v.1,e.symm v.2)
          continuous_toFun := H.continuous.comp
            (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
          map_zero_left := fun y => (H.map_zero_left (e.symm y)).trans (e.apply_symm_apply y)
          map_one_left := fun y => H.map_one_left (e.symm y) }

end SequentialCoreTower

namespace SimpleFInftyOvergroups
universe u

def HasTypeFInfty (H : Type u) [Group H] : Prop :=
  ∃ (X : Type u) (topology : TopologicalSpace X),
    letI : TopologicalSpace X := topology
    ∃ (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      T2Space X ∧ ConnectedSpace X ∧
      Topology.CWComplex.FiniteType (Set.univ : Set X) ∧
      ∃ (x : X), Nonempty (H ≃* FundamentalGroup X x) ∧
        ∃ (E : Type u) (coverTopology : TopologicalSpace E),
          letI : TopologicalSpace E := coverTopology
          ∃ (p : E → X), IsCoveringMap p ∧ Function.Surjective p ∧ ContractibleSpace E
end SimpleFInftyOvergroups

end

end OAI
