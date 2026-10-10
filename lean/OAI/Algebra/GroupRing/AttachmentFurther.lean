import Mathlib
import OAI.Algebra.GroupRing.CellularFurther

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal

namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]

lemma sphere_filling_preserved {m : ℕ} (hm : m < n)
    (hX : ∀ f : C(Sphere (m+1),X), SphereTopology.Extends f)
    (f : C(Sphere (m+1),Space a)) : SphereTopology.Extends f := by
  let := SphereTopology.sphere_nonempty m
  have hdim : dimH (Set.univ : Set (Sphere (m+1))) < n :=
    (GeneralPosition.dimH_cube_boundary_subtype_le m).trans_lt (by exact_mod_cast hm)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base a f hdim
  apply SphereTopology.extends_of_homotopy H
  obtain ⟨F,hF⟩ := hX g
  refine ⟨(⟨base a,continuous_base a⟩ : C(X,Space a)).comp F,?_⟩
  ext x
  exact congrArg (base a) (ContinuousMap.congr_fun hF x)

lemma dimH_disk_subtype_le (m : ℕ) : dimH (Set.univ : Set (Disk m)) ≤ m := by
  rw [← isometry_subtype_coe.dimH_image]
  have hm := dimH_mono (Set.subset_univ (closedBall (0 : Fin m → ℝ) 1))
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq,Real.dimH_univ_pi_fin] using hm

/-- Relative cellular approximation implies that a low-dimensional sphere that
bounds after a high-dimensional attachment already bounded beforehand. -/
lemma filling_reflected {m : ℕ} (hm : m < n) (b : C(Sphere m,X))
    (hb : SphereTopology.Extends ((⟨base a,continuous_base a⟩ : C(X,Space a)).comp b)) :
    SphereTopology.Extends b := by
  obtain ⟨F,hF⟩ := hb
  have hdim : dimH (Set.univ : Set (Disk m)) < n :=
    (dimH_disk_subtype_le m).trans_lt (by exact_mod_cast hm)
  obtain ⟨g,H,hstat⟩ := exists_deformation_into_base a F hdim
  refine ⟨g,?_⟩
  ext x
  apply (base_closedEmbedding a).injective
  have hb' : F (SphereTopology.boundary m x) = base a (b x) := ContinuousMap.congr_fun hF x
  have hh := hstat 1 (SphereTopology.boundary m x) ⟨b x,hb'.symm⟩
  simpa only [ContinuousMap.Homotopy.apply_one,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hb'] using hh

end
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
variable {ι : Type*} {n : ℕ} (a : ι → C(Sphere n,X)) [Nonempty (Sphere n)]
lemma pathConnectedSpace : PathConnectedSpace (Space a) := by
  let x₀ : X := Classical.choice inferInstance
  let s₀ : Sphere n := Classical.choice inferInstance
  have hj : ∀ z : Space a, Joined (base a x₀) z := by
    intro z
    cases z with
    | inl x => exact (PathConnectedSpace.joined x₀ x).map (continuous_base a)
    | inr p =>
      have h : Joined (boundary n s₀) (interior n p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell a p.1).continuous
      rw [cell_interior,cell_boundary] at hh
      exact ((PathConnectedSpace.joined x₀ (a p.1 s₀)).map (continuous_base a)).trans hh
  exact ⟨⟨base a x₀⟩,fun x y => (hj x).symm.trans (hj y)⟩
end GroupRingTopology.Attachment

namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)

instance presentationCoverT2 : T2Space (PresentationCover s rels hrel) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y := G)))

instance presentationCoverCW : CWComplex (Set.univ : Set (PresentationCover s rels hrel)) :=
  layerCW _ (graph_dimension s)

include hs in
lemma presentationCover_pathConnected : PathConnectedSpace (PresentationCover s rels hrel) := by
  have hgen : Subgroup.closure (Set.range s) = ⊤ := by
    rw [←FreeGroup.range_lift_eq_closure,MonoidHom.range_eq_top]
    exact hs
  let := graph_pathConnected s hgen
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _

include hs hker in
lemma presentationCover_sphereFill (b : C(Sphere 2,PresentationCover s rels hrel)) : SphereTopology.Extends b := by
  let := SphereTopology.sphere_nonempty 1
  have hdim : dimH (Set.univ : Set (Sphere 2)) < 2 :=
    (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base _ b hdim
  apply SphereTopology.extends_of_homotopy H
  exact SphereTopology.extends_of_nullhomotopic
    (((presentationGraphNullhomotopy s rels hrel hs hker).compContinuousMap g).symm)

include hs hker in
lemma presentationCover_simplyConnected : SimplyConnectedSpace (PresentationCover s rels hrel) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨presentationCover_pathConnected s rels hrel hs,?_⟩
  intro x p
  obtain ⟨F,hF⟩ := presentationCover_sphereFill s rels hrel hs hker (LoopSphere.map p)
  apply LoopSphere.homotopic_of_fill p F
  intro z
  exact ContinuousMap.congr_fun hF z
end GroupRingTopology.Cayley

namespace GroupRingTopology
universe u v
variable {G : Type u} [Group G] {A : Type v} [MulAction G A]

abbrev Orbits := Quotient (MulAction.orbitRel G A)

lemma orbit_mk_smul (g : G) (a : A) : (Quotient.mk'' (g • a) : Orbits (G := G) (A := A)) = Quotient.mk'' a := by
  apply Quotient.sound
  exact ⟨g,rfl⟩

lemma orbit_out_translate (a : A) : ∃ g : G, a = g • (Quotient.mk'' a : Orbits (G := G)).out := by
  have h := Quotient.exact (Quotient.out_eq' (q := (Quotient.mk'' a : Orbits (G := G))))
  obtain ⟨g,hg⟩ := h
  refine ⟨g⁻¹,?_⟩
  rw [←hg,inv_smul_smul]

variable (hfree : ∀ (g : G) (a : A), g • a = a → g = 1)

include hfree in
lemma orbitCoordinates_bijective : Function.Bijective (fun p : G × Orbits (G := G) (A := A) => p.1 • p.2.out) := by
  constructor
  · rintro ⟨g,q⟩ ⟨h,r⟩ he
    have hqr : q = r := by
      have hh := congrArg (fun a : A => (Quotient.mk'' a : Orbits (G := G))) he
      simpa only [orbit_mk_smul,Quotient.out_eq'] using hh
    subst r
    change g • q.out = h • q.out at he
    have hh : (h⁻¹*g) • q.out = q.out := by rw [mul_smul,he,inv_smul_smul]
    have hh := hfree (h⁻¹*g) q.out hh
    have hgh : g = h := (inv_mul_eq_one.mp hh).symm
    exact Prod.ext hgh rfl
  · intro a
    obtain ⟨g,hg⟩ := orbit_out_translate (G := G) a
    exact ⟨(g,Quotient.mk'' a),hg.symm⟩

def orbitCoordinates : (G × Orbits (G := G) (A := A)) ≃ A :=
  Equiv.ofBijective _ (orbitCoordinates_bijective hfree)

lemma orbitCoordinates_apply (g : G) (q : Orbits (G := G) (A := A)) :
    orbitCoordinates hfree (g,q) = g • q.out := rfl

end GroupRingTopology

open Set Metric Topology
namespace GroupRingTopology.Cellular
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]
variable [CWComplex (univ : Set X)] {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)

def actionChart (n : ℕ) (i : G × ι n) : PartialEquiv (Fin n → ℝ) X :=
  (RelCWComplex.map n (σ n (1,i.2))).trans (Homeomorph.smul i.1).toEquiv.toPartialEquiv

lemma actionChart_apply (n : ℕ) (i : G × ι n) (x : Fin n → ℝ) :
    actionChart σ n i x = i.1 • RelCWComplex.map n (σ n (1,i.2)) x := rfl

lemma actionChart_image (n : ℕ) (i : G × ι n) (A : Set (Fin n → ℝ)) :
    actionChart σ n i '' A = (fun x : X => i.1 • x) '' (RelCWComplex.map n (σ n (1,i.2)) '' A) :=
  Set.image_comp (fun x : X => i.1 • x) (RelCWComplex.map n (σ n (1,i.2))) A

lemma actionChart_source (n : ℕ) (i : G × ι n) :
    (actionChart σ n i).source = ball 0 1 := by
  simp [actionChart,PartialEquiv.trans_source,RelCWComplex.source_eq]

lemma actionChart_continuousOn (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i) (closedBall 0 1) :=
  (continuous_const_smul i.1).comp_continuousOn (RelCWComplex.continuousOn _ _)

lemma actionChart_continuousOn_symm (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i).symm (actionChart σ n i).target := by
  change ContinuousOn (fun y => (RelCWComplex.map n (σ n (1,i.2))).symm (i.1⁻¹ • y))
    (univ ∩ (fun y : X => i.1⁻¹ • y) ⁻¹' (RelCWComplex.map n (σ n (1,i.2))).target)
  exact (RelCWComplex.continuousOn_symm _ _).comp (continuous_const_smul _).continuousOn
    (fun _ h => h.2)

variable
  (ho : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.openCell n (σ n (1,i)) = RelCWComplex.openCell n (σ n (g,i)))
  (hc : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (1,i)) = RelCWComplex.closedCell n (σ n (g,i)))

include ho in
lemma actionChart_open (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' ball 0 1 = RelCWComplex.openCell n (σ n i) := by
  rw [actionChart_image]
  exact ho n i.1 i.2

include hc in
lemma actionChart_closed (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' closedBall 0 1 = RelCWComplex.closedCell n (σ n i) := by
  rw [actionChart_image]
  exact hc n i.1 i.2

omit [ContinuousConstSMul G X] in
include hc in
lemma closedCell_smul (n : ℕ) (g h : G) (i : ι n) :
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (h,i)) =
      RelCWComplex.closedCell n (σ n (g*h,i)) := by
  rw [←hc n h i,←Set.image_comp]
  simpa only [Function.comp_def,mul_smul] using hc n (g*h) i

variable [T2Space X]

/-- A free permutation of cell orbits can be made strictly equivariant at the
level of characteristic maps. This changes neither the space nor the cells. -/
@[instance_reducible]
def actionCW : CWComplex (univ : Set X) where
  cell n := G × ι n
  map := actionChart σ
  source_eq := actionChart_source σ
  continuousOn := actionChart_continuousOn σ
  continuousOn_symm := actionChart_continuousOn_symm σ
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (actionChart σ p.1 p.2 '' ball 0 1) (actionChart σ q.1 q.2 '' ball 0 1)
    rw [actionChart_open σ ho,actionChart_open σ ho]
    apply CWComplex.disjoint_openCell_of_ne
    intro he
    apply hpq
    cases p with | mk n i =>
      cases q with | mk m j =>
        have hnm : n = m := congrArg Sigma.fst he
        subst m
        have hij : σ n i = σ n j := (Sigma.mk.inj he).2 |> eq_of_heq
        exact congrArg (Sigma.mk n) ((σ n).injective hij)
  mapsTo' := by
    classical
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n (σ n (1,i.2))
    let f (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m) : G × ι m :=
      (i.1 * ((σ m).symm j).1,((σ m).symm j).2)
    refine ⟨fun m => (I m).image (f m),?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.cellFrontier n (σ n (1,i.2)) from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hxj⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨f m j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [actionChart_closed σ hc]
    change i.1 • RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.closedCell m
      (σ m (i.1 * ((σ m).symm j).1,((σ m).symm j).2))
    rw [←closedCell_smul σ hc]
    refine ⟨_,?_,rfl⟩
    simpa only [Prod.eta,Equiv.apply_symm_apply] using hxj
  closed' := by
    intro A hA hclosed
    apply (CWComplex.closed (univ : Set X) A hA).mpr
    intro n j
    obtain ⟨i,rfl⟩ := (σ n).surjective j
    simpa only [actionChart_closed σ hc] using hclosed n i
  union' := by
    simp only [actionChart_closed σ hc]
    have he (n : ℕ) : (⋃ j : G × ι n, RelCWComplex.closedCell n (σ n j)) =
        ⋃ j : RelCWComplex.cell (univ : Set X) n, RelCWComplex.closedCell n j := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j,hj⟩; exact ⟨σ n j,hj⟩
      · rintro ⟨j,hj⟩; exact ⟨(σ n).symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
    simp_rw [he]
    exact CWComplex.union

omit [T2Space X] in
lemma actionChart_smul (n : ℕ) (g : G) (i : G × ι n) (x : Fin n → ℝ) :
    actionChart σ n (g*i.1,i.2) x = g • actionChart σ n i x := by
  exact mul_smul _ _ _
end GroupRingTopology.Cellular

namespace GroupRingTopology.Milnor
open Set Metric Topology GroupRingTopology.Simplicial
universe u
variable (G : Type u) [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

lemma vertexTranslate_injective (g : G) : Function.Injective (fun v : ℕ × G => (v.1,g*v.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change (i,g*a) = (j,g*b) at h
  apply Prod.ext
  · simpa only using congrArg (fun v : ℕ × G => v.1) h
  · exact mul_left_cancel (congrArg Prod.snd h)

lemma translate_card (g : G) (s : Finset (ℕ × G)) : (translate g s).card = s.card :=
  Finset.card_image_of_injective _ (vertexTranslate_injective G g)

abbrev StageCell (S : Shapes G) (n : ℕ) := Simplicial.Cell (stage G S) n

def cellTranslate (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) : StageCell G S n :=
  ⟨⟨translate g c.1.1,orbitSpan_invariant _ g c.1.2⟩,by rw [translate_card]; exact c.2⟩

instance cellAction (S : Shapes G) (n : ℕ) : MulAction G (StageCell G S n) where
  smul := cellTranslate G S n
  one_smul c := by apply Subtype.ext; apply Subtype.ext; exact translate_one _
  mul_smul g h c := by apply Subtype.ext; apply Subtype.ext; exact (translate_mul _ _ _).symm

lemma cell_smul_val (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (g • c).1.1 = translate g c.1.1 := rfl

lemma cellAction_free (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n)
    (h : g • c = c) : g = 1 := by
  have he : translate g c.1.1 = c.1.1 := congrArg (fun c : StageCell G S n => c.1.1) h
  obtain ⟨v,hv⟩ := c.1.2.1.1
  have ht : (v.1,g*v.2) ∈ c.1.1 := he ▸ Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have heq := c.1.2.1.2 ht hv rfl
  have hg : g * v.2 = v.2 := congrArg Prod.snd heq
  exact mul_right_cancel (hg.trans (one_mul _).symm)

abbrev CellOrbits (S : Shapes G) (n : ℕ) := Orbits (G := G) (A := StageCell G S n)

def cellCoordinates (S : Shapes G) (n : ℕ) : (G × CellOrbits G S n) ≃ StageCell G S n :=
  orbitCoordinates (cellAction_free G S n)

lemma cellCoordinates_apply (S : Shapes G) (n : ℕ) (g : G) (c : CellOrbits G S n) :
    cellCoordinates G S n (g,c) = g • c.out := rfl

instance cellOrbits_finite (S : Shapes G) (n : ℕ) : Finite (CellOrbits G S n) := by
  classical
  obtain ⟨T,hT⟩ := orbitSpan_finite_representatives (basedShapes G S)
  let R : Set (StageCell G S n) := {c | c.1.1 ∈ T}
  have hinj : Function.Injective (fun c : StageCell G S n => c.1.1) := by
    intro c d h; exact Subtype.ext (Subtype.ext h)
  have hR : R.Finite := T.finite_toSet.preimage hinj.injOn
  let := hR.fintype
  apply Finite.of_surjective (fun c : R => (Quotient.mk'' c.1 : CellOrbits G S n))
  intro q
  obtain ⟨s,hs,g,hg⟩ := hT q.out.1.1 q.out.1.2
  let c : StageCell G S n := g⁻¹ • q.out
  have hc : c ∈ R := by
    change translate g⁻¹ q.out.1.1 ∈ T
    rw [hg,translate_mul,inv_mul_cancel,translate_one]
    exact hs
  refine ⟨⟨c,hc⟩,?_⟩
  exact (orbit_mk_smul g⁻¹ q.out).trans (Quotient.out_eq' _)

lemma stage_smul_support (S : Shapes G) (g : G) (x : Stage G S) :
    (g • x).1.support = translate g x.1.support :=
  Finsupp.mapDomain_support_of_injective (vertexTranslate_injective G g) _

lemma stage_openCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support = c.1.1} :=
  Simplicial.characteristicPE_open _ _

lemma stage_closedCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support ⊆ c.1.1} := by
  change Simplicial.characteristicPE _ c '' closedBall 0 1 = _
  rw [Simplicial.characteristicPE_closed,Simplicial.range_faceMap]

lemma stage_openCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_openCell,stage_openCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support = (g • c).1.1
    rw [stage_smul_support,cell_smul_val,hy]
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support = c.1.1
    change x.1.support = translate g c.1.1 at hx
    rw [stage_smul_support,hx,translate_mul,inv_mul_cancel,translate_one]

lemma stage_closedCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_closedCell,stage_closedCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support ⊆ (g • c).1.1
    rw [stage_smul_support,cell_smul_val]
    exact translate_mono _ hy
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support ⊆ c.1.1
    rw [stage_smul_support]
    have h := translate_mono g⁻¹ hx
    simpa only [cell_smul_val,translate_mul,inv_mul_cancel,translate_one] using h

@[instance_reducible]
def stageEquivariantCW (S : Shapes G) : CWComplex (univ : Set (Stage G S)) :=
  Cellular.actionCW (cellCoordinates G S)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_openCell_smul G S n g i.out)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_closedCell_smul G S n g i.out)

end GroupRingTopology.Milnor

end

end OAI
