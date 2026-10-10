import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometry
import OAI.GroupTheory.FiniteType.PresentationVanKampen

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace SphereCover
section
open Set Metric
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Sphere (E : Type) [NormedAddCommGroup E] := sphere (0 : E) 1
abbrev Cap (v : Sphere E) := ({v}ᶜ : Set (Sphere E))
abbrev Orth (v : Sphere E) := (ℝ ∙ (v : E))ᗮ

def capEquiv (v : Sphere E) : Cap v ≃ₜ Orth v :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _)

lemma cap_contractible (v : Sphere E) : ContractibleSpace (Cap v) := (capEquiv v).contractibleSpace

lemma ne_neg (v : Sphere E) : v ≠ -v := by
  intro h
  have he : (v : E) = -(v : E) := congrArg Subtype.val h
  have hv : (v : E) = 0 := by
    have hz : (2 : ℝ) • (v : E) = 0 := by
      rw [two_smul]
      exact (congrArg (fun z => (v : E) + z) he).trans (add_neg_cancel _)
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have := norm_eq_of_mem_sphere v
  simp [hv] at this

lemma cap_cover (v : Sphere E) : interior (Cap v) ∪ interior (Cap (-v)) = univ := by
  rw [isOpen_compl_singleton.interior_eq,isOpen_compl_singleton.interior_eq]
  apply eq_univ_of_forall
  intro x
  by_cases hx : x = v
  · right
    simpa [hx] using ne_neg v
  · exact Or.inl hx

abbrev Overlap (v : Sphere E) := Subtype (fun x : Cap (-v) => x.1 ∈ Cap v)

def antipode (v : Sphere E) : Cap (-v) := ⟨v,ne_neg v⟩

@[simp] lemma capEquiv_antipode (v : Sphere E) : capEquiv (-v) (antipode v) = 0 :=
  stereographic_neg_apply v

def overlapEquiv (v : Sphere E) : Overlap v ≃ₜ ({0}ᶜ : Set (Orth (-v))) :=
  (capEquiv (-v)).subtype (fun x => by
    change x.1 ≠ v ↔ capEquiv (-v) x ≠ 0
    rw [← capEquiv_antipode v, (capEquiv (-v)).injective.ne_iff]
    exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

def puncturedEquiv (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ContinuousMap.HomotopyEquiv ({0}ᶜ : Set V) (Sphere V) := by
  letI : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi (0 : ℝ)).contractibleSpace nonempty_Ioi
  let e := (ContractibleSpace.hequiv_unit (Ioi (0 : ℝ))).some
  exact (homeomorphUnitSphereProd V).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl (Sphere V)).prodCongr e).trans
      (Homeomorph.prodUnique (Sphere V) Unit).toHomotopyEquiv)

def overlapHomotopyEquiv (v : Sphere E) :
    ContinuousMap.HomotopyEquiv (Overlap v) (Sphere (Orth (-v))) :=
  (overlapEquiv v).toHomotopyEquiv.trans (puncturedEquiv _)

def overlapInterEquiv (v : Sphere E) : Overlap v ≃ₜ (Cap v ∩ Cap (-v) : Set (Sphere E)) where
  toEquiv :=
    { toFun := fun z => ⟨z.1.1,z.2,z.1.2⟩
      invFun := fun z => ⟨⟨z.1,z.2.2⟩,z.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma overlap_pathConnected [FiniteDimensional ℝ E] (n : ℕ)
    (hd : Module.finrank ℝ E = n+3) (v : Sphere E) :
    IsPathConnected (Cap v ∩ Cap (-v)) := by
  let : Fact (Module.finrank ℝ E = (n+2)+1) := ⟨hd⟩
  have hv : ((-v : Sphere E) : E) ≠ 0 := by
    intro h
    have := norm_eq_of_mem_sphere (-v)
    simp [h] at this
  have ho : Module.finrank ℝ (Orth (-v)) = n+2 :=
    Submodule.finrank_orthogonal_span_singleton hv
  have hr : 1 < Module.rank ℝ (Orth (-v)) := by
    rw [← Module.finrank_eq_rank,ho]
    exact_mod_cast (by omega : 1 < n+2)
  let : PathConnectedSpace ({0}ᶜ : Set (Orth (-v))) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank hr 0)
  let : PathConnectedSpace (Overlap v) := (overlapEquiv v).symm.surjective.pathConnectedSpace (overlapEquiv v).symm.continuous
  let : PathConnectedSpace (Cap v ∩ Cap (-v) : Set (Sphere E)) :=
    (overlapInterEquiv v).surjective.pathConnectedSpace (overlapInterEquiv v).continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem simplyConnected [FiniteDimensional ℝ E] (n : ℕ)
    (hd : Module.finrank ℝ E = n+3) : SimplyConnectedSpace (Sphere E) := by
  have hr : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank,hd]
    exact_mod_cast (by omega : 1 < n+3)
  let : PathConnectedSpace (Sphere E) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hr (0 : E) (by norm_num : (0 : ℝ) ≤ 1))
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance,fun x p => ?_⟩
  let v : Sphere E := -x
  let := cap_contractible v
  let := cap_contractible (-v)
  let b : Cap v := ⟨x,ne_neg x⟩
  have hs := PresentationVanKampen.fundamentalGroupMap_surjective_of_disjoint_open_cover
    (Cap v) (fun _ : Unit => Cap (-v)) isOpen_compl_singleton
    (fun _ => isOpen_compl_singleton) (by simpa only [iUnion_const, isOpen_compl_singleton.interior_eq] using cap_cover v)
    (fun _ _ h => False.elim (h (Subsingleton.elim _ _)))
    (fun _ => overlap_pathConnected n hd v) (fun _ => inferInstance) b
  obtain ⟨q,hq⟩ := hs (Path.Homotopic.Quotient.mk p)
  have hq' : q = 1 := Subsingleton.elim _ _
  apply Path.Homotopic.Quotient.eq.mp
  rw [← hq,hq',map_one]
  rfl
end

open Set Metric Topology
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def puncturedHomeomorph (e : E ≃L[ℝ] F) : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) :=
  e.toHomeomorph.subtype (fun x => by
    change x ≠ 0 ↔ e x ≠ 0
    exact not_congr ⟨fun h => h ▸ e.map_zero,fun h => e.injective (h.trans e.map_zero.symm)⟩)

def sphereHomotopyEquiv (e : E ≃L[ℝ] F) :
    ContinuousMap.HomotopyEquiv (Sphere E) (Sphere F) :=
  ((puncturedEquiv E).symm.trans (puncturedHomeomorph e).toHomotopyEquiv).trans (puncturedEquiv F)

lemma normed_simplyConnected [FiniteDimensional ℝ E] (n : ℕ)
    (hd : Module.finrank ℝ E = n+3) : SimplyConnectedSpace (Sphere E) := by
  let F := EuclideanSpace ℝ (Fin (n+3))
  have hdF : Module.finrank ℝ F = n+3 := finrank_euclideanSpace_fin
  let : ContinuousSMul ℝ F := IsBoundedSMul.continuousSMul
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (hd.trans hdF.symm)
  let := simplyConnected n hdF
  exact (sphereHomotopyEquiv e).simplyConnectedSpace

lemma normed_locallyPathConnected : LocallyPathConnectedSpace (Sphere E) := by
  let : LocallyPathConnectedSpace ({0}ᶜ : Set E) := isOpen_compl_singleton.locallyPathConnectedSpace
  let : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1,by norm_num⟩⟩
  exact (isQuotientMap_fst.comp (homeomorphUnitSphereProd E).isQuotientMap).locallyPathConnectedSpace
end SphereCover

namespace PresentationGeometry.Cells
open Set Metric Topology

def boundaryProductEquiv (k d : ℕ) : boundary k d ≃ₜ Fin k × SphereCover.Sphere (Fin d → ℝ) where
  toEquiv :=
    { toFun := fun z => (z.1.1,⟨z.1.2.1,z.2⟩)
      invFun := fun z => ⟨(z.1,⟨z.2.1,sphere_subset_closedBall z.2.2⟩),z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)).subtype_mk _

variable {X E : Type} [TopologicalSpace X] [TopologicalSpace E]
  {p : E → X} (cov : IsCoveringMap p) (surj : Function.Surjective p)

include cov surj in

theorem boundary_lift {k n : ℕ} (f : C(boundary k (n+3), X)) :
    ∃ s : C(boundary k (n+3),E), p ∘ s = f := by
  let A := SphereCover.Sphere (Fin (n+3) → ℝ)
  let : SimplyConnectedSpace A := SphereCover.normed_simplyConnected n (by
    simp)
  let : LocallyPathConnectedSpace A := SphereCover.normed_locallyPathConnected
  let a : A := Classical.choice (inferInstance : Nonempty A)
  let F (i : Fin k) : C(A,X) := f.comp ⟨fun z => (boundaryProductEquiv k (n+3)).symm (i,z),
    (boundaryProductEquiv k (n+3)).symm.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hl : ∀ i : Fin k, ∃ s : C(A,E), p ∘ s = F i := by
    intro i
    obtain ⟨e,he⟩ := surj (F i a)
    obtain ⟨s,hs,_⟩ := cov.existsUnique_continuousMap_lifts (F i) a e he
    exact ⟨s,hs.2⟩
  choose L hL using hl
  let s : C(Fin k × A,E) := ⟨fun z => L z.1 z.2,by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hf : ∀ᶠ w : Fin k × A in nhds z, w.1 = z.1 :=
      (continuous_fst.tendsto z).eventually (isOpen_discrete {z.1} |>.mem_nhds (by rfl))
    apply ((L z.1).continuous.comp continuous_snd).continuousAt.congr_of_eventuallyEq
    filter_upwards [hf] with w hw
    simp only [hw,Function.comp_apply]⟩
  refine ⟨s.comp ⟨boundaryProductEquiv k (n+3),(boundaryProductEquiv k (n+3)).continuous⟩,?_⟩
  funext z
  exact congrFun (hL z.1.1) ⟨z.1.2.1,z.2⟩
end PresentationGeometry.Cells

open scoped unitInterval
open Set
namespace DiscreteCoverCharts
variable {ι X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
variable (Z : FiberBundleCore ι X Q)

def point (i : ι) (x : X) (q : Q) : Z.TotalSpace :=
  (Z.localTriv i).toOpenPartialHomeomorph.symm (x,q)

@[simp] theorem point_proj (i : ι) (x : X) (q : Q) : Z.proj (point Z i x q) = x := rfl

@[simp] theorem point_val (i : ι) (x : X) (q : Q) :
    (point Z i x q).2 = Z.coordChange i (Z.indexAt x) x q := rfl

theorem point_change (i j : ι) {x : X} (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) (q : Q) :
    point Z i x q = point Z j x (Z.coordChange i j x q) := by
  change (⟨x,Z.coordChange i (Z.indexAt x) x q⟩ : Z.TotalSpace) =
    ⟨x,Z.coordChange j (Z.indexAt x) x (Z.coordChange i j x q)⟩
  rw [Z.coordChange_comp i j (Z.indexAt x) x ⟨⟨hi,hj⟩,Z.mem_baseSet_at x⟩ q]

def chartPath (i : ι) {a b : X} (p : Path a b) (hp : Set.range p ⊆ Z.baseSet i) (q : Q) :
    Path (point Z i a q) (point Z i b q) where
  toFun t := point Z i (p t) q
  continuous_toFun := (Z.localTriv i).toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
    (p.continuous.prodMk continuous_const) (fun t => (Z.mem_localTriv_target i _).mpr (hp ⟨t,rfl⟩))
  source' := by rw [p.source]
  target' := by rw [p.target]

@[simp] theorem chartPath_map (i : ι) {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ Z.baseSet i) (q : Q) :
    (chartPath Z i p hp q).map Z.continuous_proj = p := by ext t; rfl

def fiberEquiv (i : ι) (x : X) (hx : x ∈ Z.baseSet i) : Q ≃ Z.proj ⁻¹' {x} where
  toFun q := ⟨point Z i x q,rfl⟩
  invFun y := (Z.localTriv i y.1).2
  left_inv q := by
    change Z.coordChange (Z.indexAt x) i x (Z.coordChange i (Z.indexAt x) x q) = q
    rw [Z.coordChange_comp i (Z.indexAt x) i x ⟨⟨hx,Z.mem_baseSet_at x⟩,hx⟩ q,
      Z.coordChange_self i x hx q]
  right_inv y := by
    rcases y with ⟨⟨y,q⟩,hy⟩
    have he : y = x := hy
    subst y
    apply Subtype.ext
    change (⟨x,Z.coordChange i (Z.indexAt x) x (Z.coordChange (Z.indexAt x) i x q)⟩ : Z.TotalSpace) =
      ⟨x,q⟩
    rw [Z.coordChange_comp (Z.indexAt x) i (Z.indexAt x) x
      ⟨⟨Z.mem_baseSet_at x,hx⟩,Z.mem_baseSet_at x⟩ q,
      Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) q]

variable [DiscreteTopology Q]

theorem covering : IsCoveringMap Z.proj := FiberBundle.isCoveringMap

theorem monodromy_chartPath (i : ι) {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ Z.baseSet i) (q : Q) :
    (covering Z).monodromy (Path.Homotopic.Quotient.mk p)
      ⟨point Z i a q,rfl⟩ = ⟨point Z i b q,rfl⟩ := by
  apply (covering Z).monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (chartPath Z i p hp q))
  change Path.Homotopic.Quotient.mk ((chartPath Z i p hp q).map Z.continuous_proj) =
    (Path.Homotopic.Quotient.mk p).cast rfl rfl
  rw [chartPath_map]
  rfl

end DiscreteCoverCharts

end

end OAI
