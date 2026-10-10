import OAI.Combinatorics.PlanarL1.LocalPersistence

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace SecondaryCell
variable {J : Set ℝ} {root : Fin (k+1)}
lemma mem_domain_iff_distance (seeds : Finset (M.Point J root)) (radius : ℝ)
    (x : M.Point J root) : x.height ∈ domain seeds radius x.column ↔ seedDistance seeds x≤radius := by
  constructor
  · intro h
    obtain ⟨z,hc,hH,hd⟩ := (mem_domain seeds radius).mp h
    exact Point.eq_of_coordinates z x hc hH ▸ hd
  · intro h
    exact (mem_domain seeds radius).mpr ⟨x,rfl,rfl,h⟩
lemma point_eq (seeds : Finset (M.Point J root)) (radius : ℝ) (x : M.Point J root)
    (h : x.height ∈ domain seeds radius x.column) : point seeds radius _ _ h=x :=
  Point.eq_of_coordinates _ _ (point_column _ _ _) (point_height _ _ _)
end SecondaryCell
namespace BState.SecondaryStep
open PlanarL1.Interpolation
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)
lemma fullNamed_at (z : M.Point J root) (hz : SecondaryCell.seedDistance U.seeds z≤U.radius) :
    U.fullNamed z.column ⟨z.height,U.sub_old z.inBand⟩=U.named z := by
  have hd := (SecondaryCell.mem_domain_iff_distance U.seeds U.radius z).mpr hz
  simp only [fullNamed,dite_eq_left hd,SecondaryCell.point_eq]

/-- A crossed seed-domain is identically old on the small ball, including its
actual deterministic branch name. No independence or pruning assumption. -/
lemma fullNamed_boundary_ball (x y : M.Point J root) {ρ : ℝ}
    (hsmall : 18*ρ≤(199/1000:ℝ)*U.radius) (hy : dist x y≤ρ)
    (hout : y.height ∉ SecondaryCell.domain U.seeds U.radius y.column)
    (z : M.Point J root) (hz : dist x z≤ρ) :
    U.fullNamed z.column ⟨z.height,U.sub_old z.inBand⟩=⟨0,U.old z⟩ := by
  by_cases hd : z.height ∈ SecondaryCell.domain U.seeds U.radius z.column
  · have hin := (SecondaryCell.mem_domain_iff_distance U.seeds U.radius z).mp hd
    rw [U.fullNamed_at z hin]
    have hyout : U.radius≤SecondaryCell.seedDistance U.seeds y := le_of_lt (lt_of_not_ge
      (fun h => hout ((SecondaryCell.mem_domain_iff_distance U.seeds U.radius y).mpr h)))
    exact SecondaryCell.namedReplacement_boundary_ball U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.seeds_nonempty U.old_lipschitz U.support_lipschitz U.zeta_eq U.radius_nonneg
      U.ordered_bound U.delta_eq U.noise_bounds U.support_le U.admitted U.shield_offset U.lo
      x y hsmall hy hyout z hz hin
  · rw [fullNamed,dite_eq_right hd]
    rfl
end BState.SecondaryStep
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
variable (hp : Tiling.Padded a₂ p x.height ρ)
variable (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
variable (positive : Bool) (C : (group A SA SB v hv i).Component)
variable {z : M.Point Set.univ A.root} (hz : dist x z≤ρ)
variable (hd : z.height ∈ SecondaryCell.domain ((group A SA SB v hv i).admittedSeeds positive C) R z.column)
include hρ hp hz hd
lemma group_touched_band : i.1.2.val.val=Tiling.index a₂ p x.height := by
  apply Tiling.near_band_unique interpolationB.2.1 hρ hp _
    (i.1.narrow_eq ▸ SecondaryCell.inBand_of_mem _ _ hd)
  rw [abs_sub_comm]
  exact (x.height_change_le z).trans hz
lemma group_touched_envelope : ∀ H, |H-x.height|≤ρ → H ∈ BandTrees.band narrow (group A SA SB v hv i).lower := by
  intro H hH
  have he := group_touched_band A SA SB v hv x hρ hp i positive C hz hd
  have hb := Tiling.near_mem_band interpolationB.2.1 hρ hp hH
  rw [←he,←i.1.narrow_eq] at hb
  exact hb
lemma group_local_center : ∃ x' : M.Point (BandTrees.band narrow (group A SA SB v hv i).lower)
    ((group A SA SB v hv i).root C), x'.column=x.column ∧ x'.height=x.height :=
  Point.local_center x z (SecondaryCell.point _ _ _ _ hd)
    (SecondaryCell.point_column _ _ _) (SecondaryCell.point_height _ _ _) hρ
      (group_touched_envelope A SA SB v hv x hρ hp i positive C hz hd) hz

lemma ball_domain_touch (b : Block (M := M) q p L U)
    (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
    (hc : c.column=x.column) (hH : c.height=x.height)
    (hC : ((group A SA SB v hv i).admittedSeeds positive C).Nonempty) (hsmall : ρ+R≤4*R) :
    Touch A SA SB v hv b c i := by
  obtain ⟨ha,w,hw,r,hr⟩ := (group A SA SB v hv i).domain_near positive C hC z.column z.height hd
  obtain ⟨s,_,hs⟩ := x.exists_shortest isClosed_univ z
  obtain ⟨t,ht⟩ := s.restrict_of_length x.height z.height x.height ρ
    (group_touched_envelope A SA SB v hv x hρ hp i positive C hz hd) (by simpa [hs] using hz)
  obtain ⟨u,hu,he⟩ := (SurvivingGroups.seed_mem
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1) i.2).mp hw
  subst w
  refine ⟨?_,u,hu,(t.cast hc.symm rfl).append r,?_⟩
  · rw [hH]
    exact group_touched_envelope A SA SB v hv x hρ hp i positive C hz hd _ (by simpa using hρ)
  · have ht' : (t.cast hc.symm rfl).length c.height z.height≤ρ := by
      rw [Path.length_cast,hH,ht,hs]
      exact hz
    exact ((t.cast hc.symm rfl).length_append_le r c.height z.height _).trans (by linarith)
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace Field
lemma ball_variation {J : Set ℝ} {r : Fin (k+1)} {K : ℝ≥0} (F : M.Field J K)
    (x z : M.Point Set.univ r) {ρ : ℝ} (hρ : 0≤ρ)
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J) (hz : dist x z≤ρ) :
    ∃ (hx : x.height ∈ J) (hZ : z.height ∈ J),
      |F.value x.column ⟨x.height,hx⟩-F.value z.column ⟨z.height,hZ⟩|≤(K:ℝ)*ρ := by
  have hx := hJ x.height (by simpa using hρ)
  have hZ := hJ z.height (by rw [abs_sub_comm]; exact (x.height_change_le z).trans hz)
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_univ z
  obtain ⟨q,hq⟩ := p.restrict_of_length x.height z.height x.height ρ hJ (by simpa [hp] using hz)
  refine ⟨hx,hZ,(F.path_bound q ⟨x.height,hx⟩ ⟨z.height,hZ⟩).trans ?_⟩
  rw [hq,hp]
  exact mul_le_mul_of_nonneg_left hz (NNReal.coe_nonneg K)
end Field
namespace BState.SecondaryStep
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root r : Fin (k+1)}
variable (U : SecondaryStep S J root)

lemma point_dist (x z : M.Point Set.univ r) {ρ : ℝ}
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J) (hz : dist x z≤ρ)
    (hx : x.height ∈ SecondaryCell.domain U.seeds U.radius x.column)
    (hZ : z.height ∈ SecondaryCell.domain U.seeds U.radius z.column) :
    dist (SecondaryCell.point U.seeds U.radius _ _ hx) (SecondaryCell.point U.seeds U.radius _ _ hZ)=dist x z := by
  obtain ⟨z',hc,hH,hd⟩ := Point.local_point x z (SecondaryCell.point _ _ _ _ hx)
    (SecondaryCell.point_column _ _ _) (SecondaryCell.point_height _ _ _) isClosed_univ
    (Set.subset_univ _) hJ hz
  have he : z'=SecondaryCell.point U.seeds U.radius _ _ hZ := Point.eq_of_coordinates _ _
    (hc.trans (SecondaryCell.point_column _ _ _).symm) (hH.trans (SecondaryCell.point_height _ _ _).symm)
  rwa [he] at hd

/-- Crossing the domain anywhere on the ambient small ball makes this actual
proposal identically old on that ball. Intrinsic paths are derived by height
padding, rather than silently identified with ambient paths. -/
lemma fullNamed_boundary_global (x y z : M.Point Set.univ r) {ρ : ℝ} (hρ : 0≤ρ)
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J)
    (hsmall : 18*ρ≤(199/1000:ℝ)*U.radius) (hy : dist x y≤ρ)
    (hout : y.height ∉ SecondaryCell.domain U.seeds U.radius y.column)
    (hz : dist x z≤ρ) (hZ : z.height ∈ U.data.band) :
    U.fullNamed z.column ⟨z.height,hZ⟩=⟨0,U.comparison.value z.column ⟨z.height,hZ⟩⟩ := by
  by_cases hd : z.height ∈ SecondaryCell.domain U.seeds U.radius z.column
  · let zp := SecondaryCell.point U.seeds U.radius _ _ hd
    obtain ⟨xp,hxc,hxh⟩ := Point.local_center x z zp
      (SecondaryCell.point_column _ _ _) (SecondaryCell.point_height _ _ _) hρ hJ hz
    obtain ⟨yp,hyc,hyh,hdy⟩ := Point.local_point x y xp hxc hxh isClosed_univ (Set.subset_univ _) hJ hy
    obtain ⟨zz,hzc,hzh,hdz⟩ := Point.local_point x z xp hxc hxh isClosed_univ (Set.subset_univ _) hJ hz
    have hout' : yp.height ∉ SecondaryCell.domain U.seeds U.radius yp.column := by rwa [hyc,hyh]
    have he := U.fullNamed_boundary_ball xp yp hsmall (hdy.le.trans hy) hout' zz (hdz.le.trans hz)
    have hzz : zz.column=z.column := hzc
    have hZZ : zz.height=z.height := hzh
    simpa only [hzz,hZZ,old] using he
  · rw [fullNamed,dite_eq_right hd]
end BState.SecondaryStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Parameters
open scoped NNReal
noncomputable def secondaryK : ℝ≥0 := max 5 ⟨3/(9*a₂/100),by norm_num [a₂]⟩
noncomputable def secondaryQ : ℝ := zetaB*(EB/8)/20
noncomputable def secondaryRadius : ℝ := zetaB*(EB/8)/1000
noncomputable def secondaryN : ℕ := 6*(⌈15/zetaB⌉₊+3+1)+3
noncomputable def secondaryTestLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (4*(secondaryK:ℝ)*ρ+secondaryQ/m)/secondaryQ+(4*(secondaryK:ℝ)*ρ+EB/m)/EB
lemma secondaryTestLoss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ secondaryTestLoss ρ m := by
  unfold secondaryTestLoss
  positivity [show 0 < secondaryQ by norm_num [secondaryQ,zetaB,EB,R],interpolationB.1]
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S) (positive : Bool) (C : G.Component)
variable (hC : (G.admittedSeeds positive C).Nonempty) {m : ℕ} (hm : 0  <  m)
abbrev Offset := Point.RadialTree.GridSample (n := k+1) (G.tree C).depthCap m × Fin (m+1) × Fin (m+1)
noncomputable def sampledStep (w : Offset G C (m := m)) :=
  G.step positive C hC ((G.tree C).gridNoise _ m w.1) ((G.tree C).gridNoise_bounds _ _ hm w.1)
    (EB/m*w.2.1.val) (EB/m*w.2.2.val) (offset_bound hm _) (offset_bound hm _)

variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0 ≤ ρ)
abbrev Ball := {z : M.Point Set.univ A.root // dist x z ≤ ρ}
noncomputable def ballCenter : Ball x (ρ := ρ) := ⟨x,by simpa using hρ⟩
variable (hBand : ∀ z : Ball x (ρ := ρ), z.val.height∈G.data.band)
noncomputable def oldOnBall (z : Ball x (ρ := ρ)) : ℝ :=
  (G.comparison positive).value z.val.column ⟨z.val.height,hBand z⟩
noncomputable def sampledOnBall (w : Offset G C (m := m)) (z : Ball x (ρ := ρ)) : NamedValue :=
  (G.sampledStep positive C hC hm w).fullNamed z.val.column ⟨z.val.height,hBand z⟩

lemma sampledStep_seeds (w : Offset G C (m := m)) :
    (G.sampledStep positive C hC hm w).seeds=G.admittedSeeds positive C := rfl
lemma sampledStep_radius (w : Offset G C (m := m)) :
    (G.sampledStep positive C hC hm w).radius=R := rfl

lemma component_local_list
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
    (hOld : ∀ z, |G.oldOnBall positive x hBand (ballCenter x hρ)-G.oldOnBall positive x hBand z| ≤ (secondaryK:ℝ)*ρ)
    (hEnv : (∃ z : Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column) →
      ∀ H, |H-x.height| ≤ ρ → H ∈ BandTrees.band narrow G.lower) :
    ∃ L : LocalList (G.oldOnBall positive x hBand) (G.sampledOnBall positive C hC hm x hBand)
      (ballCenter x hρ) ((secondaryK:ℝ)*ρ) (secondaryTestLoss ρ m),
      L.names.card ≤ secondaryN ∧
      ((¬∀ z : Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column) → L.names={0}) := by
  classical
  by_cases hfull : ∀ z : Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column
  · let lift := fun z : Ball x (ρ := ρ) => SecondaryCell.point _ _ _ _ (hfull z)
    let w0 : Offset G C (m := m) := Classical.arbitrary _
    let U := G.sampledStep positive C hC hm w0
    have hJ := hEnv ⟨ballCenter x hρ,hfull _⟩
    have hdist z : dist (lift (ballCenter x hρ)) (lift z) ≤ ρ := by
      have he := U.point_dist x z.val hJ z.property (hfull (ballCenter x hρ)) (hfull z)
      exact he.le.trans z.property
    have hrad : ρ ≤ U.tree.radius := hr
    have hex := SecondaryCell.sampled_local_list U.tree U.seeds U.old U.supportValue lift
      (ballCenter x hρ) hρ hrad hdist U.data.isOrdinary U.old_lipschitz U.support_lipschitz U.zeta_eq
      U.pc U.radius U.lo EB interpolationB.1 m hm
    have ho : (fun z => U.old (lift z))=G.oldOnBall positive x hBand := by
      funext z
      simp only [BState.SecondaryStep.old,lift,SecondaryCell.point_column,SecondaryCell.point_height]
      rfl
    have hf : (fun (w : Offset G C (m := m)) z =>
        SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue U.data.isOrdinary U.pc U.radius
          (EB/m*w.2.1.val) (EB/m*w.2.2.val) U.lo (U.tree.gridNoise U.tree.depthCap m w.1) (lift z))=
        G.sampledOnBall positive C hC hm x hBand := by
      funext w z
      unfold sampledOnBall BState.SecondaryStep.fullNamed
      split
      · rfl
      · rename_i hn
        exact False.elim (hn (hfull z))
    have heK : SecondaryCell.replacementConstant U.tree=secondaryK := rfl
    have heQ : U.tree.q=secondaryQ := rfl
    erw [ho,hf,heK,heQ] at hex
    obtain ⟨L,hh⟩ := hex
    exact ⟨L,hh,fun hn => False.elim (hn hfull)⟩
  · have he : G.sampledOnBall positive C hC hm x hBand=fun (_ : Offset G C (m := m)) z =>
        ⟨0,G.oldOnBall positive x hBand z⟩ := by
      funext w z
      obtain ⟨y,hy⟩ := not_forall.mp hfull
      by_cases hz : z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column
      · exact (G.sampledStep positive C hC hm w).fullNamed_boundary_global x y.val z.val hρ
          (hEnv ⟨z,hz⟩) hsmall y.property hy z.property (hBand z)
      · unfold sampledOnBall BState.SecondaryStep.fullNamed
        split
        · exact False.elim (hz ‹_›)
        · rfl
    rw [he]
    refine ⟨oldLocalList (G.oldOnBall positive x hBand) (ballCenter x hρ) hOld,?_,fun _ => rfl⟩
    change ({0} : Finset ℕ).card ≤ secondaryN
    simp only [Finset.card_singleton]
    unfold secondaryN
    omega
end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Interpolation
noncomputable def scaleNamed (c : ℝ) (a : NamedValue) : NamedValue := ⟨a.name,c*a.value⟩
lemma maxNamed_scale {c : ℝ} (hc : 0<c) (a b : NamedValue) :
    maxNamed (scaleNamed c a) (scaleNamed c b)=scaleNamed c (maxNamed a b) := by
  simp only [maxNamed,scaleNamed,mul_lt_mul_iff_right₀ hc,mul_right_inj' hc.ne']
  split_ifs <;> rfl
lemma maxSelection_scale {X : Type*} {c : ℝ} (hc : 0<c)
    (old : X → NamedValue) (Fs : List (X → NamedValue)) (x : X) :
    maxSelection (fun z => scaleNamed c (old z))
      (Fs.map (fun F z => scaleNamed c (F z))) x=scaleNamed c (maxSelection old Fs x) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simpa only [List.map_cons,maxSelection,ih] using maxNamed_scale hc _ _
lemma familySelection_scale {X : Type*} {k : ℕ} {c : ℝ} (hc : 0<c)
    (old : X → ℝ) (F : Fin k → X → NamedValue) (x : X) :
    familySelection (fun z => c*old z) (fun g z => scaleNamed c (F g z)) x=
      scaleNamed c (familySelection old F x) := by
  unfold familySelection
  rw [←maxSelection_scale hc]
  congr 2
  rw [List.map_ofFn]
  rfl
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
abbrev Coordinate := Σ i, (G i).Component
abbrev Offsets (m : ℕ) := ∀ u : Coordinate G, ComponentSample G u.1 u.2 m
noncomputable instance : Fintype (Coordinate G) := Fintype.ofFinite _
variable (o : Fin (S.count+1) → Bool) (c : I → Bool) {m : ℕ}
noncomputable def flatSample (w : Offsets G m) : Sample G m := (o,c,fun i C => w ⟨i,C⟩)
noncomputable def fixedSample : Sample G m := flatSample G o c (Classical.arbitrary _)
noncomputable def slot (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))) :
    Acting G (fixedSample G o c (m := m)) a := (Fintype.equivFin _).symm j
noncomputable def coord (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))) :
    Coordinate G := (slot G o c (m := m) a j).val
lemma coord_injective (a : Fin (S.count+1)) : Function.Injective (coord G o c (m := m) a) := by
  intro i j he
  apply (Fintype.equivFin (Acting G (fixedSample G o c (m := m)) a)).symm.injective
  exact Subtype.ext he

omit [Fintype I] in
lemma flat_actingStep (hm : 0 < m) (w : Offsets G m) (a : Fin (S.count+1))
    (u : Acting G (fixedSample G o c (m := m)) a) :
    actingStep G hm (flatSample G o c w) a u=
      (G u.val.1).sampledStep (o a) u.val.2 u.property.2.2 hm (w u.val) := rfl

lemma coord_index (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))) :
    (G (coord G o c (m := m) a j).1).index=a := (slot G o c (m := m) a j).property.1
lemma slot_band (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a)))
    (H : (S.chart a).band) : H.val∈(G (coord G o c (m := m) a j).1).data.band := by
  change H.val∈(S.chart (G (coord G o c (m := m) a j).1).index).band
  rw [coord_index]
  exact H.property

lemma selected_flat (hm : 0 < m) (w : Offsets G m) (a : Fin (S.count+1))
    (i : Fin (k+1)) (H : (S.chart a).band) :
    ((batch G hm (flatSample G o c w) a).selected i H).name=
      (familySelection (fun T : (S.chart a).band => ((S.chart a).comparison Group.lam Group.lam_bound (o a)).value i T)
        (fun j T => ((G (coord G o c (m := m) a j).1).sampledStep (o a) (coord G o c (m := m) a j).2
          (slot G o c (m := m) a j).property.2.2 hm (w (coord G o c (m := m) a j))).fullNamed i
            ⟨T.val,slot_band G o c (m := m) a j T⟩) H).name := by
  change (familySelection (fun T : (S.chart a).band => kappaB*((S.chart a).comparison Group.lam Group.lam_bound (o a)).value i T)
    (fun j T => scaleNamed kappaB (((G (coord G o c (m := m) a j).1).sampledStep (o a) (coord G o c (m := m) a j).2
      (slot G o c (m := m) a j).property.2.2 hm (w (coord G o c (m := m) a j))).fullNamed i
        ⟨T.val,slot_band G o c (m := m) a j T⟩)) H).name=_
  rw [familySelection_scale (by norm_num [kappaB,a₂])]
  rfl
end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Interpolation
lemma maxSelection_map {X Y : Type*} (old : Y → NamedValue)
    (Fs : List (Y → NamedValue)) (f : X → Y) (x : X) :
    maxSelection (old ∘ f) (Fs.map (fun F => F ∘ f)) x=maxSelection old Fs (f x) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp only [List.map_cons,maxSelection,Function.comp_apply,ih]
lemma familySelection_map {X Y : Type*} {k : ℕ} (old : Y → ℝ)
    (F : Fin k → Y → NamedValue) (f : X → Y) (x : X) :
    familySelection (old ∘ f) (fun g => F g ∘ f) x=familySelection old F (f x) := by
  unfold familySelection
  rw [←maxSelection_map _ _ f x,List.map_ofFn]
  rfl
lemma maxSelection_eq_fold {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (x : X) :
    maxSelection old Fs x=(Fs.map (fun F => F x)).foldr maxNamed (old x) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simpa only [maxSelection,List.map_cons,List.foldr_cons] using congrArg (maxNamed (F x)) ih
lemma familySelection_congr_at {X Y : Type*} {k : ℕ} (old : X → ℝ) (old' : Y → ℝ)
    (F : Fin k → X → NamedValue) (F' : Fin k → Y → NamedValue)
    (x : X) (y : Y) (ho : old x=old' y) (hF : ∀ g, F g x=F' g y) :
    familySelection old F x=familySelection old' F' y := by
  simp only [familySelection,maxSelection_eq_fold,List.map_ofFn,ho]
  congr 2
  funext g
  dsimp only [Function.comp_apply]
  rw [hF g]
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters PlanarL1.Interpolation FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
variable (o : Fin (S.count+1) → Bool) (c : I → Bool) {m : ℕ}
variable (a : Fin (S.count+1)) (x : M.Point Set.univ A.root) {ρ : ℝ}
abbrev Slot := Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))
variable (hBand : ∀ z : Group.Ball x (ρ := ρ), z.val.height∈(S.chart a).band)
noncomputable def ballOld (z : Group.Ball x (ρ := ρ)) : ℝ :=
  ((S.chart a).comparison Group.lam Group.lam_bound (o a)).value z.val.column ⟨z.val.height,hBand z⟩
include hBand in
lemma ball_slot_band (j : Slot G o c a (m := m)) (z : Group.Ball x (ρ := ρ)) :
    z.val.height∈(G (coord G o c (m := m) a j).1).data.band :=
  slot_band G o c (m := m) a j ⟨z.val.height,hBand z⟩
noncomputable def ballFamily (hm : 0 < m) (j : Slot G o c a (m := m))
    (w : ComponentSample G (coord G o c (m := m) a j).1 (coord G o c (m := m) a j).2 m) (z : Group.Ball x (ρ := ρ)) : NamedValue :=
  (G (coord G o c (m := m) a j).1).sampledOnBall (o a) (coord G o c (m := m) a j).2
    (slot G o c (m := m) a j).property.2.2 hm x (ball_slot_band G o c (m := m) a x hBand j) w z
lemma ballOld_eq (j : Slot G o c a (m := m)) :
    (G (coord G o c (m := m) a j).1).oldOnBall (o a) x (ball_slot_band G o c (m := m) a x hBand j)=ballOld o a x hBand := by
  funext z
  unfold Group.oldOnBall Group.comparison ballOld
  simp only [Group.data]
  have heval (b : Fin (S.count+1)) (hb : z.val.height∈(S.chart b).band) (he : b=a) :
      ((S.chart b).comparison Group.lam Group.lam_bound (o a)).value z.val.column ⟨z.val.height,hb⟩ =
      ((S.chart a).comparison Group.lam Group.lam_bound (o a)).value z.val.column ⟨z.val.height,hBand z⟩ := by
    subst b
    rfl
  exact heval _ _ (coord_index G o c (m := m) a j)
lemma selected_ball (hm : 0 < m) (w : Offsets G m) (z : Group.Ball x (ρ := ρ)) :
    ((batch G hm (flatSample G o c w) a).selected z.val.column ⟨z.val.height,hBand z⟩).name=
      (familySelection (ballOld o a x hBand) (fun j => ballFamily G o c a x hBand hm j (w (coord G o c (m := m) a j))) z).name := by
  apply (selected_flat G o c hm w a z.val.column ⟨z.val.height,hBand z⟩).trans
  apply congrArg NamedValue.name
  refine familySelection_congr_at _ _ _ _ _ _ ?_ ?_
  · rfl
  · intro j
    rfl
noncomputable def wholeBallSlots : Finset (Slot G o c a (m := m)) := Finset.univ.filter fun j =>
  ∀ z : Group.Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain
    ((G (coord G o c (m := m) a j).1).admittedSeeds (o a) (coord G o c (m := m) a j).2) R z.val.column

lemma persistence_flat [SFinite μ] (hρ : 0 ≤ ρ) (hm : 0 < m)
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
    (hOld : ∀ z, |ballOld o a x hBand (Group.ballCenter x hρ)-ballOld o a x hBand z| ≤ (secondaryK:ℝ)*ρ)
    (hold : ∀ z : Group.Ball x (ρ := ρ), S.name z.val.column z.val.height=a)
    (hEnv : ∀ j : Slot G o c a (m := m),
      (∃ z : Group.Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain
        ((G (coord G o c (m := m) a j).1).admittedSeeds (o a) (coord G o c (m := m) a j).2) R z.val.column) →
      ∀ H, |H-x.height| ≤ ρ → H ∈ BandTrees.band narrow (G (coord G o c (m := m) a j).1).lower)
    {B : ℕ} (hpack : (wholeBallSlots G o c a x (ρ := ρ) (m := m)).card ≤ B) :
    prob (fun w : Offsets G m => ∃ z : Group.Ball x (ρ := ρ),
      (result G hm (flatSample G o c w)).name z.val.column z.val.height≠
        (result G hm (flatSample G o c w)).name x.column x.height) ≤
      (1+B*secondaryN : ℕ)^2*secondaryTestLoss ρ m := by
  classical
  have hList (j : Slot G o c a (m := m)) :
      ∃ L : LocalList (ballOld o a x hBand) (ballFamily G o c a x hBand hm j)
        (Group.ballCenter x hρ) ((secondaryK:ℝ)*ρ) (secondaryTestLoss ρ m),
        L.names.card ≤ secondaryN ∧ (j∉wholeBallSlots G o c a x (ρ := ρ) (m := m) → L.names={0}) := by
    have ho := hOld
    rw [←ballOld_eq G o c (m := m) a x hBand j] at ho
    have he := (G (coord G o c (m := m) a j).1).component_local_list (o a) (coord G o c (m := m) a j).2
      (slot G o c (m := m) a j).property.2.2 hm x hρ (ball_slot_band G o c (m := m) a x hBand j)
      hsmall hr ho (hEnv j)
    erw [ballOld_eq G o c (m := m) a x hBand j] at he
    obtain ⟨L,hN,hout⟩ := he
    exact ⟨L,hN,fun hn => hout (by simpa only [wholeBallSlots,Finset.mem_filter,Finset.mem_univ,true_and] using hn)⟩
  choose L hN hout using hList
  have hprob := LocalList.family_probability (D := fun u : Coordinate G => ComponentSample G u.1 u.2 m)
    (coord G o c (m := m) a) (coord_injective G o c (m := m) a) (ballOld o a x hBand)
    (ballFamily G o c a x hBand hm) (Group.ballCenter x hρ) (secondaryTestLoss_nonneg hρ m) hOld L
    (wholeBallSlots G o c a x (ρ := ρ) (m := m)) (fun j _ => hN j)
    (fun j hj => (hout j hj).le) hpack
  apply (prob_mono (Q := fun w : Offsets G m => ∃ z : Group.Ball x (ρ := ρ),
    (familySelection (ballOld o a x hBand) (fun j => ballFamily G o c a x hBand hm j (w (coord G o c (m := m) a j))) z).name≠
      (familySelection (ballOld o a x hBand) (fun j => ballFamily G o c a x hBand hm j (w (coord G o c (m := m) a j))) (Group.ballCenter x hρ)).name) ?_).trans hprob
  rintro w ⟨z,hz⟩
  refine ⟨z,fun he => hz ?_⟩
  apply (layer G hm (flatSample G o c w)).name_eq_of_selected a (hBand z) (hBand (Group.ballCenter x hρ))
    (hold z) (hold (Group.ballCenter x hρ))
  exact (selected_ball G o c a x hBand hm w z).trans
    (he.trans (selected_ball G o c a x hBand hm w (Group.ballCenter x hρ)).symm)
end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω} {A : Ambient M}
  {S : BState M kappaB lam Ω μ} (G : SecondaryGeometry.Group A S)
lemma component_eq_of_domain (positive : Bool) (C D : G.Component) (i : Fin (k+1)) (H : ℝ)
    (hC : H ∈ SecondaryCell.domain (G.admittedSeeds positive C) R i)
    (hD : H ∈ SecondaryCell.domain (G.admittedSeeds positive D) R i) : C=D := by
  let x := SecondaryCell.point _ _ _ _ hC
  let y := SecondaryCell.point _ _ _ _ hD
  have hc : x.column=i := SecondaryCell.point_column _ _ _
  have hd : y.column=i := SecondaryCell.point_column _ _ _
  have h1 := BandTrees.reachable_mem M narrow G.lower C x.reachable
  have h2 := BandTrees.reachable_mem M narrow G.lower D y.reachable
  rw [hc] at h1
  rw [hd] at h2
  exact ((SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp h1).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff D i).mp h2)
end PlanarL1.Columns.Model.SecondaryGeometry.Group

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
variable (hp : Tiling.Padded a₁ q c.height ρ) (hn : Tiling.Padded a₂ p c.height τ)
variable {m : ℕ} (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)
variable (a : Fin (SB.count+1))

noncomputable def centerActs : Finset (Acting (group A SA SB v hv) omega a) :=
  Finset.univ.filter fun u => c.height ∈ SecondaryCell.domain
    ((group A SA SB v hv u.val.1).admittedSeeds (omega.1 a) u.val.2) R c.column

include hc hρ hτ hp hn in
lemma centerActs_card : (centerActs A SA SB v hv b c omega a).card≤SurvivingGroups.packBound := by
  let f : (centerActs A SA SB v hv b c omega a) → Hits A SA SB v hv b c
      (phaseD := phaseD) (phaseG := phaseG) := fun u =>
    ⟨u.val.val.1, domain_touch A SA SB v hv b c _ (omega.1 a) _ u.val.property.2.2
      (Finset.mem_filter.mp u.property).2⟩
  have hf : Function.Injective f := by
    intro u w he
    have hi := congrArg Subtype.val he
    change u.val.val.1=w.val.val.1 at hi
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext hi
    cases u with | mk u hu =>
      cases w with | mk w hw =>
        cases u with | mk u hu' =>
          cases w with | mk w hw' =>
            cases u with | mk i C =>
              cases w with | mk j D =>
                dsimp only at hi
                subst j
                apply heq_of_eq
                exact (group A SA SB v hv i).component_eq_of_domain (omega.1 a) C D c.column c.height
                  (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hw).2
  have he := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at he
  exact he.trans (touching_card_small A SA SB v hv b c hc hρ hτ hp hn)
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root)

lemma center_point_of_domain
    (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
    (positive : Bool) (C : (group A SA SB v hv i).Component)
    (hC : ((group A SA SB v hv i).admittedSeeds positive C).Nonempty)
    (hd : x.height∈SecondaryCell.domain ((group A SA SB v hv i).admittedSeeds positive C) R x.column) :
    ∃ z : M.Point (BandTrees.band broad i.1.lower) (BandTrees.root M broad i.1.lower i.1.1.2),
      z.column=x.column ∧ z.height=x.height ∧ z.height∈BandTrees.band narrow i.1.lower₂ := by
  obtain ⟨hH,w,_,path,_⟩ := (group A SA SB v hv i).domain_near positive C hC x.column x.height hd
  refine ⟨{ column := x.column
            height := x.height
            inBand := i.1.sub hH
            reachable := w.reachable.trans (path.widen i.1.sub).word.reachable.symm }, rfl,rfl,hH⟩

lemma wholeBallSlots_card (o : Fin (SB.count+1) → Bool)
    (coins : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) → Bool)
    (a : Fin (SB.count+1)) {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hn : Tiling.Padded a₂ p x.height ρ) :
    (wholeBallSlots (group A SA SB v hv) o coins a x (ρ := ρ) (m := m)).card ≤ SurvivingGroups.packBound := by
  classical
  let G := group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)
  let T := wholeBallSlots G o coins a x (ρ := ρ) (m := m)
  by_cases he : T.Nonempty
  · obtain ⟨j,hj⟩ := he
    have hd := (Finset.mem_filter.mp hj).2 (Group.ballCenter x hρ)
    obtain ⟨z,hzc,hzh,hzband⟩ := center_point_of_domain A SA SB v hv x (coord G o coins (m := m) a j).1
      (o a) (coord G o coins (m := m) a j).2 (slot G o coins (m := m) a j).property.2.2 hd
    let b := (coord G o coins (m := m) a j).1.1
    let omega := fixedSample G o coins (m := m)
    let f : T → centerActs A SA SB v hv b z omega a := fun t =>
      ⟨slot G o coins (m := m) a t.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        change z.height∈SecondaryCell.domain
          ((G (coord G o coins (m := m) a t.val).1).admittedSeeds (o a) (coord G o coins (m := m) a t.val).2) R z.column
        rw [hzc,hzh]
        exact (Finset.mem_filter.mp t.property).2 (Group.ballCenter x hρ)⟩⟩
    have hf : Function.Injective f := by
      intro s t he
      apply Subtype.ext
      exact (Fintype.equivFin (Acting G omega a)).symm.injective (congrArg Subtype.val he)
    have hh := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe,Fintype.card_coe] at hh
    exact hh.trans (centerActs_card A SA SB v hv b z hzband hρ hρ
      (by simpa only [hzh] using hp) (by simpa only [hzh] using hn) omega a)
  · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)).le.trans (Nat.zero_le _)
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Parameters
open scoped NNReal
noncomputable def mainK : ℝ≥0 := max 1 ⟨3/(9*a₁/100),by norm_num [a₁]⟩
noncomputable def mainQ : ℝ := zetaA*(EA/8)/20
noncomputable def mainRadius : ℝ := zetaA*(EA/8)/1000
noncomputable def mainN : ℕ := 6*(⌈15/zetaA⌉₊+3+1)+2
noncomputable def mainTestLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (4*(mainK:ℝ)*ρ+mainQ/m)/mainQ+(4*(mainK:ℝ)*ρ+EA/m)/EA
noncomputable def mainLoss (ρ : ℝ) (m : ℕ) : ℝ := (mainN:ℝ)^2*mainTestLoss ρ m
noncomputable def secondaryLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ)^2*secondaryTestLoss ρ m
lemma mainQ_pos : 0 < mainQ := by norm_num [mainQ,zetaA,EA,epsilon]
lemma mainRadius_pos : 0 < mainRadius := by norm_num [mainRadius,zetaA,EA,epsilon]
lemma secondaryQ_pos : 0 < secondaryQ := by norm_num [secondaryQ,zetaB,EB,R]
lemma secondaryRadius_pos : 0 < secondaryRadius := by norm_num [secondaryRadius,zetaB,EB,R]
noncomputable def persistenceRadius : ℝ :=
  min (EA/20) (min mainRadius (min ((199/18000:ℝ)*R) secondaryRadius))
lemma persistenceRadius_pos : 0 < persistenceRadius := by
  exact lt_min (div_pos interpolationA.1 (by norm_num))
    (lt_min mainRadius_pos (lt_min (by norm_num [R]) secondaryRadius_pos))
lemma persistence_main_small {ρ : ℝ} (h : ρ≤persistenceRadius) : 4*ρ<3*EA := by
  have h' := h.trans (min_le_left _ _)
  have hE := interpolationA.1
  linarith
lemma persistence_main_radius {ρ : ℝ} (h : ρ≤persistenceRadius) : ρ ≤ mainRadius :=
  h.trans (le_trans (min_le_right (EA/20) _) (min_le_left mainRadius _))
lemma persistence_secondary_small {ρ : ℝ} (h : ρ≤persistenceRadius) : 18*ρ≤(199/1000:ℝ)*R := by
  have h' := h.trans (le_trans (min_le_right (EA/20) _) (le_trans (min_le_right mainRadius _) (min_le_left ((199/18000:ℝ)*R) _)))
  linarith
lemma persistence_secondary_radius {ρ : ℝ} (h : ρ≤persistenceRadius) : ρ ≤ secondaryRadius :=
  h.trans (le_trans (min_le_right (EA/20) _) (le_trans (min_le_right mainRadius _) (min_le_right ((199/18000:ℝ)*R) _)))
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
variable {k : ℕ} {M : Model (k+1)} {q L U : ℝ}
variable (phase : BandComponent (M := M) q L U → ℝ)
lemma localLoss_eq (c : CellIndex q L U phase) (ρ : ℝ) (m : ℕ) :
    localLoss phase c ρ m=mainLoss ρ m := rfl
lemma radius_eq (c : CellIndex q L U phase) : (tree phase c).radius=mainRadius := rfl
end PlanarL1.Columns.Model.MainFamily

end

end OAI
