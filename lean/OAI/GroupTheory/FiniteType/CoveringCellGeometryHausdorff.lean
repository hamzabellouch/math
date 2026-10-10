import Mathlib
import OAI.GroupTheory.FiniteType.CWCellularSkelInclHomologyIsIso
import OAI.GroupTheory.FiniteType.CoveringCellGeometry

namespace OAI

noncomputable section

section
open Set Topology unitInterval
namespace CoveringCellGeometry
open Set Topology
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [T2Space X] {p : E → X}

theorem hausdorff (cov : IsCoveringMap p) : T2Space E := by
  constructor
  intro e f hef
  by_cases hp : p e = p f
  · exact cov.isSeparatedMap e f hp hef
  · obtain ⟨U,V,hU,hV,he,hf,hUV⟩ := t2_separation hp
    exact ⟨p ⁻¹' U,p ⁻¹' V,hU.preimage cov.continuous,hV.preimage cov.continuous,
      he,hf,hUV.preimage p⟩

end CoveringCellGeometry

end

namespace PresentationGeometry.Cells
open Set Metric Topology
variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
  [CWComplex (univ : Set X)] [RelCWComplex.FiniteType (univ : Set X)]
  {k d : ℕ} (f : C(boundary k d,X))
  (hdim : ∀ n, RelCWComplex.cell (univ : Set X) n → n < d)

lemma skeleton_eq_old :
    letI := cwComplex f hdim
    (RelCWComplex.skeletonLT (univ : Set (Space f)) d : Set (Space f)) =
      Set.range (Adjunction.old f) := by
  let := cwComplex f hdim
  ext z
  constructor
  · intro hz
    obtain ⟨n,hn,c,v,hv,rfl⟩ := CWComplex.mem_skeletonLT_iff.mp hz
    rcases c with c | ⟨i,⟨rfl⟩⟩
    · exact ⟨RelCWComplex.map n c v,rfl⟩
    · exact absurd hn (lt_irrefl _)
  · rintro ⟨x,rfl⟩
    have hx : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
        RelCWComplex.openCell n i := by
      rw [CWComplex.iUnion_openCell_eq_complex]; trivial
    simp only [mem_iUnion,RelCWComplex.openCell,mem_image] at hx
    obtain ⟨n,c,v,hv,hx⟩ := hx
    exact CWComplex.mem_skeletonLT_iff.mpr
      ⟨n,by exact_mod_cast hdim n c,Sum.inl c,v,hv,congrArg (Adjunction.old f) hx⟩
end PresentationGeometry.Cells

namespace CoveringCW
open Set Topology Metric CoveringCellGeometry
variable {X E : Type} [TopologicalSpace X] [TopologicalSpace E] [T2Space X] [T2Space E]
  [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

lemma skeleton_preimage (n : ℕ) :
    letI := cwComplex_general cov
    (RelCWComplex.skeletonLT (univ : Set E) n : Set E) =
      p ⁻¹' (RelCWComplex.skeletonLT (univ : Set X) n : Set X) := by
  let := cwComplex_general cov
  ext e
  constructor
  · intro he
    obtain ⟨m,hm,c,v,hv,rfl⟩ := CWComplex.mem_skeletonLT_iff.mp he
    exact CWComplex.mem_skeletonLT_iff.mpr
      ⟨m,hm,c.1,v,hv,(chart_proj cov m c (ball_subset_closedBall hv)).symm⟩
  · intro he
    obtain ⟨m,hm,i,v,hv,hve⟩ := CWComplex.mem_skeletonLT_iff.mp he
    let z : Pullback (p := p) (baseChar m i) :=
      ⟨(⟨v,ball_subset_closedBall hv⟩,e),hve.symm⟩
    refine CWComplex.mem_skeletonLT_iff.mpr
      ⟨m,hm,⟨i,sheet cov (baseChar m i) z⟩,v,hv,?_⟩
    exact (characteristic_on_disk cov m _ ⟨v,ball_subset_closedBall hv⟩).trans
      (characteristicLift_sheet cov (baseChar m i) z)
end CoveringCW

namespace SingularChains
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
lemma homologyMap_of_homotopic {f g : C(X,Y)} (h : f.Homotopic g) (j : ℕ) :
    homologyMap (map f) j = homologyMap (map g) j :=
  (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from h.some).singularChainComplexFunctorObjMap
    (ModuleCat.of ℤ ℤ) |>.homologyMap_eq j

lemma homologyMap_const_zero (j : ℕ) (hj : j ≠ 0) (y : Y) :
    homologyMap (map (ContinuousMap.const X y)) j = 0 := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) j).obj (ModuleCat.of ℤ ℤ)
  have hz : CategoryTheory.Limits.IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) j (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hj
  change F.map (TopCat.ofHom (ContinuousMap.const X y)) = 0
  have he : TopCat.ofHom (ContinuousMap.const X y) =
      TopCat.ofHom (ContinuousMap.const X PUnit.unit) ≫
        TopCat.ofHom (ContinuousMap.const PUnit y) := rfl
  rw [he,F.map_comp,hz.eq_of_src (F.map (TopCat.ofHom (ContinuousMap.const PUnit y))) 0,comp_zero]
end SingularChains

namespace PresentationGeometry.CellCoverExtension
open Set Topology Cells CWExtension CategoryTheory HomologicalComplex SingularChains
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

lemma attaching_homology_killed {n : ℕ} (hd : d = n+3) (i : Fin k) (j : ℕ) (hj : j ≠ 0) :
    homologyMap (map (s.comp (boundarySlice i))) j ≫
      homologyMap (map (oldLift f b Z pot s hs hpot)) j = 0 := by
  obtain ⟨z,hz⟩ := attaching_lift_nullhomotopic f b Z pot s hs hpot hd i
  rw [← homologyMap_comp,← map_comp,homologyMap_of_homotopic hz,
    homologyMap_const_zero j hj z]

variable [Nonempty X] [CWComplex (univ : Set X)]
  [RelCWComplex.FiniteType (univ : Set X)]
  (hdim : ∀ m, RelCWComplex.cell (univ : Set X) m → m < d)
include hdim

lemma oldLift_skeleton :
    letI := Cells.cwComplex f hdim
    letI := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
    letI := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
    Set.range (oldLift f b Z pot s hs hpot) =
      Skel (univ : Set (coveringCore f b Z pot s hs hpot).TotalSpace) d := by
  let := Cells.cwComplex f hdim
  let := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
  let := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
  rw [range_oldLift]
  change _ = (RelCWComplex.skeletonLT (univ : Set (coveringCore f b Z pot s hs hpot).TotalSpace) d : Set (coveringCore f b Z pot s hs hpot).TotalSpace)
  rw [CoveringCW.skeleton_preimage,Cells.skeleton_eq_old f hdim]

lemma oldLift_homology_surjective (j : ℕ) (hj : j < d) :
    Function.Surjective (homologyMap (map (oldLift f b Z pot s hs hpot)) j) := by
  let := Cells.cwComplex f hdim
  let := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
  let := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
  exact CWCellular.homology_skeleton_surjective (oldLift f b Z pot s hs hpot)
    (oldLift_isEmbedding f b Z pot s hs hpot) d (oldLift_skeleton f b Z pot s hs hpot hdim) j hj

lemma oldLift_homology_bijective (j : ℕ) (hj : j+1 < d) :
    Function.Bijective (homologyMap (map (oldLift f b Z pot s hs hpot)) j) := by
  let := Cells.cwComplex f hdim
  let := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
  let := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
  exact CWCellular.homology_skeleton_bijective (oldLift f b Z pot s hs hpot)
    (oldLift_isEmbedding f b Z pot s hs hpot) d (oldLift_skeleton f b Z pot s hs hpot hdim) j hj
end PresentationGeometry.CellCoverExtension

namespace CoreDeck
open Set Topology DiscreteCoverCharts
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

def right (q : Q) (z : Z.TotalSpace) : Z.TotalSpace := ⟨z.1,@HMul.hMul Q Q Q _ z.2 q⟩

omit [DiscreteTopology Q] in
@[simp] lemma right_proj (q : Q) (z : Z.TotalSpace) : Z.proj (right Z q z) = Z.proj z := rfl

include hZ in
omit [DiscreteTopology Q] in
lemma right_chart (q : Q) (i : ι) (z : Z.TotalSpace) (hz : z.1 ∈ Z.baseSet i) :
    right Z q z = point Z i z.1 (((Z.localTriv i) z).2*q) := by
  simp only [right]
  change (⟨z.1,@HMul.hMul Q Q Q _ z.2 q⟩ : Z.TotalSpace) =
    ⟨z.1,Z.coordChange i (Z.indexAt z.1) z.1 (Z.coordChange (Z.indexAt z.1) i z.1 z.2 * q)⟩
  erw [hZ,Z.coordChange_comp (Z.indexAt z.1) i (Z.indexAt z.1) z.1
    ⟨⟨Z.mem_baseSet_at _,hz⟩,Z.mem_baseSet_at _⟩,
    Z.coordChange_self (Z.indexAt z.1) z.1 (Z.mem_baseSet_at _)]

include hZ in
lemma continuous_right (q : Q) : Continuous (right Z q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let i := Z.indexAt z.1
  have hc : ContinuousOn (fun a : Z.TotalSpace => point Z i a.1 (((Z.localTriv i) a).2*q))
      (Z.localTriv i).source := by
    apply (Z.localTriv i).toOpenPartialHomeomorph.symm.continuousOn.comp
    · exact Z.continuous_proj.continuousOn.prodMk
        ((continuous_snd.comp_continuousOn (Z.localTriv i).continuousOn).mul continuousOn_const)
    · intro a ha
      exact (Z.mem_localTriv_target i _).mpr ha
  have hc' : ContinuousOn (right Z q) (Z.localTriv i).source :=
    hc.congr (fun a ha => right_chart Z hZ q i a ha)
  exact hc'.continuousAt ((Z.localTriv i).open_source.mem_nhds (Z.mem_baseSet_at _))

def homeo (q : Q) : Z.TotalSpace ≃ₜ Z.TotalSpace where
  toFun := right Z q
  invFun := right Z q⁻¹
  left_inv z := by
    rcases z with ⟨x,a⟩
    change Q at a
    exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace))
      (show (a : Q) * q * q⁻¹ = a by simp)
  right_inv z := by
    rcases z with ⟨x,a⟩
    change Q at a
    exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace))
      (show (a : Q) * q⁻¹ * q = a by simp)
  continuous_toFun := continuous_right Z hZ q
  continuous_invFun := continuous_right Z hZ q⁻¹

omit [DiscreteTopology Q] in
lemma of_potential (pot : ι → X → Q)
    (hpot : ∀ i j x a, Z.coordChange i j x a = pot j x * (pot i x)⁻¹ * a) :
    ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q := by
  intros; simp only [hpot,mul_assoc]

instance action : MulAction Qᵐᵒᵖ Z.TotalSpace where
  smul q z := right Z q.unop z
  one_smul z := by
    change right Z (1 : Q) z = z
    rcases z with ⟨x,a⟩
    change Q at a
    exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace)) (mul_one (a : Q))
  mul_smul p q z := by
    change right Z (q.unop*p.unop) z = right Z p.unop (right Z q.unop z)
    rcases z with ⟨x,a⟩
    change Q at a
    exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace))
      (mul_assoc (a : Q) q.unop p.unop).symm

include hZ in
theorem continuousAction : @ContinuousConstSMul Qᵐᵒᵖ Z.TotalSpace _ (action Z).toSMul :=
  ⟨fun q => continuous_right Z hZ q.unop⟩

omit [DiscreteTopology Q] in
lemma transitive_fiber (a b : Z.TotalSpace) (h : Z.proj a = Z.proj b) :
    ∃ q : Q, right Z q a = b := by
  rcases a with ⟨x,a⟩; rcases b with ⟨y,b⟩
  change x = y at h; subst y
  change Q at a b
  refine ⟨@HMul.hMul Q Q Q _ (@Inv.inv Q _ a) b,?_⟩
  exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace))
    (show (a : Q) * (a⁻¹ * b) = b by simp)

omit [DiscreteTopology Q] in
lemma right_free (q : Q) (a : Z.TotalSpace) (h : right Z q a = a) : q = 1 := by
  have hh := congrArg (fun z : Z.TotalSpace => (z.2 : Q)) h
  change @HMul.hMul Q Q Q _ a.2 q = (a.2 : Q) at hh
  exact mul_left_cancel (hh.trans (mul_one _).symm)

end CoreDeck

end

end OAI
