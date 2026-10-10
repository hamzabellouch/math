import Mathlib
import OAI.Algebra.GroupRing.GeneralPosition

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal

namespace GroupRingTopology.Cellular

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}

abbrev ChartDisk (n : ℕ) := Metric.ball (0 : Fin n → ℝ) 1
abbrev ChartCore (n : ℕ) := Metric.closedBall (0 : Fin n → ℝ) (1/2)

def chartCoreInclusion (n : ℕ) : C(ChartCore n,ChartDisk n) :=
  ⟨fun x => ⟨x.1, (mem_closedBall.mp x.2).trans_lt (by norm_num)⟩,
    continuous_subtype_val.subtype_mk _⟩

def chartCore (e : C(ChartDisk n,Y)) : C(ChartCore n,Y) := e.comp (chartCoreInclusion n)

lemma chartCore_closedEmbedding (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) :
    IsClosedEmbedding (chartCore e) := by
  apply (chartCore e).continuous.isClosedEmbedding
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : ChartDisk n => z.1) (he.injective h)

variable {K : Type*} [MetricSpace K]

def chartDomain (e : C(ChartDisk n,Y)) (f : C(K,Y)) : Set K := f ⁻¹' Set.range (chartCore e)

lemma chartDomain_closed (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y)) :
    IsClosed (chartDomain e f) := (chartCore_closedEmbedding e he).isClosed_range.preimage f.continuous

def coreCoordinate (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y)) :
    C(chartDomain e f,ChartCore n) :=
  ⟨fun x => (chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.symm ⟨f x,x.2⟩,
    (chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.symm.continuous.comp
      ((f.continuous.comp continuous_subtype_val).subtype_mk _)⟩

lemma coreCoordinate_fac (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (x : chartDomain e f) : chartCore e (coreCoordinate e he f x) = f x :=
  congrArg Subtype.val ((chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.apply_symm_apply _)

lemma coreCoordinate_frontier (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (x : chartDomain e f) (hx : (x:K) ∈ frontier (chartDomain e f)) :
    ‖(coreCoordinate e he f x : Fin n → ℝ)‖ = 1/2 := by
  apply le_antisymm
  · simpa only [mem_closedBall,dist_zero_right] using (coreCoordinate e he f x).2
  · by_contra! h
    let U : Set (ChartDisk n) := {z | ‖(z : Fin n → ℝ)‖ < 1/2}
    have hU : IsOpen U := isOpen_lt (continuous_subtype_val.norm) continuous_const
    have hsub : f ⁻¹' (e '' U) ⊆ chartDomain e f := by
      intro y hy
      obtain ⟨z,hz,hzy⟩ := hy
      exact ⟨⟨z.1,by simpa only [mem_closedBall,dist_zero_right] using le_of_lt hz⟩,hzy⟩
    have hxU : (x:K) ∈ f ⁻¹' (e '' U) := by
      refine ⟨chartCoreInclusion n (coreCoordinate e he f x),h,?_⟩
      exact coreCoordinate_fac e he f x
    exact hx.2 (mem_interior.mpr ⟨f ⁻¹' (e '' U),hsub,
      (he.isOpenMap U hU).preimage f.continuous,hxU⟩)

omit [T2Space Y] in
lemma chartDomain_dimH_le (e : C(ChartDisk n,Y)) (f : C(K,Y)) :
    dimH (Set.univ : Set (chartDomain e f)) ≤ dimH (Set.univ : Set K) := by
  rw [← isometry_subtype_coe.dimH_image]
  exact dimH_mono (Set.subset_univ _)

end

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}
variable {K : Type*} [MetricSpace K]

def chartCenter (e : C(ChartDisk n,Y)) : Y := e ⟨0,by simp⟩

/-- A map of smaller dimension can be homotoped off one cell centre,
without changing it outside the cell. This works for merely continuous maps,
not just piecewise linear maps. -/
lemma exists_chart_avoidance [T2Space Y] [CompactSpace K] (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ x, g x ≠ chartCenter e) ∧
      (∀ (t : unitInterval) (x : K), f x ∉ Set.range e → H (t,x) = f x) ∧
      (∀ (t : unitInterval) (x : K), H (t,x) = f x ∨ H (t,x) ∈ Set.range e) := by
  let A := chartDomain e f
  have hA : IsClosed A := chartDomain_closed e he f
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let u : C(A,Fin n → ℝ) := ⟨fun x => (coreCoordinate e he f x).1,
    continuous_subtype_val.comp (coreCoordinate e he f).continuous⟩
  obtain ⟨v,hv0,hvfix,hvdist⟩ := GeneralPosition.exists_relative_nonzero_approximation u
    ((chartDomain_dimH_le e f).trans_lt hdim) (δ := 1/8) (by norm_num)
  have hi (t : unitInterval) (x : A) : ‖u x+(t:ℝ) • (v x-u x)‖ ≤ 1/2 := by
    have hu : ‖u x‖ ≤ 4*(1/8:ℝ) := by
      simpa only [u,ContinuousMap.coe_mk,show (4:ℝ)*(1/8)=1/2 by norm_num,mem_closedBall,dist_zero_right]
        using (coreCoordinate e he f x).2
    simpa only [show (4:ℝ)*(1/8)=1/2 by norm_num] using
      GeneralPosition.relative_interpolation_bound (by norm_num : (0:ℝ)<1/8)
        hvfix hvdist x hu t
  have hvc (x : A) : v x ∈ ChartCore n := by
    have h := hi 1 x
    simpa only [Set.Icc.coe_one,one_smul,add_sub_cancel,mem_closedBall,dist_zero_right] using h
  let vcore : C(A,ChartCore n) := ⟨fun x => ⟨v x,hvc x⟩,
    v.continuous.subtype_mk hvc⟩
  let gA : C(A,Y) := (chartCore e).comp vcore
  let HA : (f.restrict A).Homotopy gA :=
    { toFun := fun tx => chartCore e ⟨u tx.2+(tx.1:ℝ) • (v tx.2-u tx.2),by
        simpa only [mem_closedBall,dist_zero_right] using hi tx.1 tx.2⟩
      continuous_toFun := (chartCore e).continuous.comp
        (((u.continuous.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).smul
            ((v.continuous.comp continuous_snd).sub (u.continuous.comp continuous_snd)))).subtype_mk
            (fun tx => by
              simpa only [ChartCore,mem_closedBall,dist_zero_right,Pi.add_apply,
                Pi.smul_apply',Pi.sub_apply,Function.comp_apply] using hi tx.1 tx.2))
      map_zero_left := fun x => by
        simp only [Set.Icc.coe_zero,zero_smul,add_zero]
        exact coreCoordinate_fac e he f x
      map_one_left := fun x => by
        simp only [Set.Icc.coe_one,one_smul,add_sub_cancel]
        rfl }
  have hboundary (t : unitInterval) (x : A) (hx : (x:K) ∈ frontier A) :
      HA (t,x) = f x := by
    have hfix : v x = u x := hvfix x (by
      change 2*(1/8:ℝ) ≤ ‖(coreCoordinate e he f x).1‖
      rw [coreCoordinate_frontier e he f x hx]
      norm_num)
    change chartCore e ⟨u x+(t:ℝ) • (v x-u x),_⟩ = f x
    simp only [hfix,sub_self,smul_zero,add_zero]
    exact coreCoordinate_fac e he f x
  let hg : ∀ x : A, (x:K) ∈ frontier A → gA x = f x :=
    fun x hx => by simpa using hboundary 1 x hx
  let g := patch hA f gA hg
  let H : f.Homotopy g := patchHomotopy hA f gA HA hboundary
  have hOn (t : unitInterval) (x : A) : H (t,(x:K)) = HA (t,x) := by
    change patchFun (Prod.snd ⁻¹' A) _ _ (t,(x:K)) = _
    rw [patchFun,dite_eq_left (show (t,(x:K)) ∈ Prod.snd ⁻¹' A from x.2)]
    rfl
  have hOff (t : unitInterval) (x : K) (hx : x ∉ A) : H (t,x) = f x := by
    change patchFun (Prod.snd ⁻¹' A) _ _ (t,x) = _
    rw [patchFun,dite_eq_right (show (t,x) ∉ Prod.snd ⁻¹' A from hx)]
    rfl
  refine ⟨g,H,?_,?_,?_⟩
  · intro x hzero
    by_cases hx : x ∈ A
    · have hv : chartCore e (vcore ⟨x,hx⟩) = chartCenter e := by
        exact (patch_on hA f gA hg ⟨x,hx⟩).symm.trans hzero
      have hu := congrArg (fun z : ChartDisk n => z.1) (he.injective hv)
      exact hv0 ⟨x,hx⟩ hu
    · have hfx : f x = chartCenter e := (patch_off hA f gA hg hx).symm.trans hzero
      apply hx
      exact ⟨⟨0,by simp⟩,hfx.symm⟩
  · intro t x hx
    apply hOff
    rintro ⟨z,hz⟩
    exact hx ⟨chartCoreInclusion n z,hz⟩
  · intro t x
    by_cases hx : x ∈ A
    · right
      rw [hOn t ⟨x,hx⟩]
      exact ⟨_,rfl⟩
    · exact Or.inl (hOff t x hx)

end

open Set Metric Topology
open scoped ENNReal NNReal
section
variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [TopologicalSpace K]

lemma homotopy_trans_pointwise {f g h : C(K,Y)} (H : f.Homotopy g) (J : g.Homotopy h)
    (P : K → Y → Prop) (hH : ∀ t x, P x (H (t,x))) (hJ : ∀ t x, P x (J (t,x))) :
    ∀ t x, P x (H.trans J (t,x)) := by
  intro t x
  erw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _ x
  · exact hJ _ x

end
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}
variable {K : Type*} [MetricSpace K] [CompactSpace K] {ι : Type*}
variable (e : ι → C(ChartDisk n,Y)) (he : ∀ i, IsOpenEmbedding (e i))
variable (hd : Pairwise (fun i j => Disjoint (Set.range (e i)) (Set.range (e j))))

omit [T2Space Y] in
lemma chartCenter_mem_range (i : ι) : chartCenter (e i) ∈ Set.range (e i) := ⟨_,rfl⟩

include he hd in
lemma exists_finite_chart_avoidance (f : C(K,Y)) (hdim : dimH (Set.univ : Set K) < n)
    (S : Finset ι) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ i ∈ S, ∀ x, g x ≠ chartCenter (e i)) ∧
      (∀ t x, H (t,x) = f x ∨ ∃ i ∈ S, H (t,x) ∈ Set.range (e i)) ∧
      (∀ t x, (∀ i ∈ S, f x ∉ Set.range (e i)) → H (t,x) = f x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨f,.refl f,by simp,(fun _ _ => Or.inl rfl),fun _ _ _ => rfl⟩
  | @insert a S ha ih =>
    obtain ⟨g,H,hg,hH,hstat⟩ := ih
    obtain ⟨g',J,hg',hJstat,hJ⟩ := exists_chart_avoidance (e a) (he a) g hdim
    refine ⟨g',H.trans J,?_,?_,?_⟩
    · intro i hi x
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hg' x
      · intro hzero
        rcases hJ 1 x with hj | hj
        · have hh : g' x = g x := by simpa using hj
          exact hg i hi x (hh.symm.trans hzero)
        · have hj : g' x ∈ Set.range (e a) := by simpa using hj
          rw [hzero] at hj
          exact (hd (by intro heq; subst i; exact ha hi)).notMem_of_mem_left hj
            (chartCenter_mem_range e i)
    · apply homotopy_trans_pointwise H J
        (fun x y => y = f x ∨ ∃ i ∈ insert a S, y ∈ Set.range (e i))
      · intro t x
        rcases hH t x with h | ⟨i,hi,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨i,Finset.mem_insert_of_mem hi,h⟩
      · intro t x
        rcases hJ t x with h | h
        · rw [h]
          have hh : g x = f x ∨ ∃ i ∈ S, g x ∈ Set.range (e i) := by simpa using hH 1 x
          rcases hh with h | ⟨i,hi,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨i,Finset.mem_insert_of_mem hi,h⟩
        · exact Or.inr ⟨a,Finset.mem_insert_self _ _,h⟩
    · intro t x hx
      have hfixed : ∀ t, H (t,x) = f x := fun t =>
        hstat t x (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      have hgx : g x = f x := by simpa using hfixed 1
      have hjfixed : ∀ t, J (t,x) = f x := fun t =>
        (hJstat t x (by rw [hgx]; exact hx a (Finset.mem_insert_self _ _))).trans hgx
      erw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hfixed _
      · exact hjfixed _

include he hd in
lemma exists_all_chart_avoidance (f : C(K,Y)) (hdim : dimH (Set.univ : Set K) < n)
    (S : Finset ι) (hs : ∀ i, i ∉ S → ∀ x, f x ∉ Set.range (e i)) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ i x, g x ≠ chartCenter (e i)) ∧
      (∀ t x, (∀ i, f x ∉ Set.range (e i)) → H (t,x) = f x) := by
  classical
  obtain ⟨g,H,hg,hH,hstat⟩ := exists_finite_chart_avoidance e he hd f hdim S
  refine ⟨g,H,?_,?_⟩
  · intro i x
    by_cases hi : i ∈ S
    · exact hg i hi x
    · intro hzero
      have hh : g x = f x ∨ ∃ j ∈ S, g x ∈ Set.range (e j) := by simpa using hH 1 x
      rcases hh with h | ⟨j,hj,h⟩
      · apply hs i hi x
        rw [← h,hzero]
        exact chartCenter_mem_range e i
      · rw [hzero] at h
        exact (hd (by intro heq; subst j; exact hi hj)).notMem_of_mem_left h
          (chartCenter_mem_range e i)
  · intro t x hx
    exact hstat t x (fun i _ => hx i)

end GroupRingTopology.Cellular

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def chart (i : ι) : C(Cellular.ChartDisk n,Space a) :=
  ⟨openCell a i,(openCell_openEmbedding a i).continuous⟩

/-- Maps of dimension below the newly attached cells can be deformed into the
old space. The deformation is stationary on the original preimage of it. -/
lemma exists_deformation_into_base (f : C(K,Space a))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,X)) (H : f.Homotopy ((⟨base a,continuous_base a⟩ : C(X,Space a)).comp g)),
      ∀ t x, f x ∈ Set.range (base a) → H (t,x) = f x := by
  classical
  let I := {i : ι | (Set.range f ∩ Set.range (openCell a i)).Nonempty}
  have hI : I.Finite := compact_finitely_many_openCells a (isCompact_range f.continuous)
  have hs : ∀ i, i ∉ hI.toFinset → ∀ x, f x ∉ Set.range (chart a i) := by
    intro i hi x hx
    apply hi
    rw [Set.Finite.mem_toFinset]
    exact ⟨f x,Set.mem_range_self x,hx⟩
  obtain ⟨g,H,hg,hstat⟩ := Cellular.exists_all_chart_avoidance (chart a)
    (fun i => openCell_openEmbedding a i) (fun i j hij => openCell_disjoint a i j hij)
    f hdim hI.toFinset hs
  have hgp (x : K) : g x ∈ punctured a := by
    rintro ⟨i,hi⟩
    exact hg i x hi.symm
  let gp : C(K,punctured a) := ⟨fun x => ⟨g x,hgp x⟩,g.continuous.subtype_mk hgp⟩
  let J := (radialHomotopy a).compContinuousMap gp
  have hJ0 : (puncturedInclusion a).comp gp = g := rfl
  let J' : g.Homotopy ((radialEnd a).comp gp) := hJ0 ▸ J
  refine ⟨(radialRetraction a).comp gp,H.trans J',?_⟩
  intro t x hx
  obtain ⟨y,hy⟩ := hx
  have hfixed (s : unitInterval) : H (s,x) = f x := by
    apply hstat s x
    intro i
    rintro ⟨d,hd⟩
    rw [← hy] at hd
    cases hd
  have hgx : g x = base a y := by simpa only [ContinuousMap.Homotopy.apply_one,← hy] using hfixed 1
  have hgp' : gp x = puncturedBase a y := Subtype.ext hgx
  have hjfixed (s : unitInterval) : J' (s,x) = f x := by
    change radialHomotopy a (s,gp x) = f x
    rw [hgp',radialHomotopy_base,hy]
  erw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hfixed _
  · exact hjfixed _

end GroupRingTopology.Attachment
open Set Metric Topology
open scoped NNReal ENNReal
namespace GroupRingTopology.GeneralPosition

lemma lipschitz_insertNth {n : ℕ} (i : Fin (n+1)) (c : ℝ) :
    LipschitzWith 1 (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → (Fin (n+1) → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same,dist_self,dist_nonneg]
  · simp only [Fin.insertNth_apply_succAbove]
    exact dist_le_pi_dist x y k

lemma sphere_subset_faces (n : ℕ) :
    Metric.sphere (0 : Fin (n+1) → ℝ) 1 ⊆
      ⋃ i : Fin (n+1), ⋃ c ∈ ({1,-1}:Set ℝ), Set.range (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → _) := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
  have hi : ∃ i, 1 ≤ ‖x i‖ := by
    by_contra! hh
    have := (pi_norm_lt_iff (by norm_num : (0:ℝ)<1)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := hi
  have heq : |x i| = 1 := le_antisymm ((norm_le_pi_norm x i).trans_eq hxnorm) hi
  have hc : x i ∈ ({1,-1}:Set ℝ) := by
    rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp heq with h | h <;> simp [h]
  refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x i,Set.mem_iUnion.mpr ⟨hc,?_⟩⟩⟩
  exact ⟨fun j => x (i.succAbove j),Fin.insertNth_self_removeNth _ _⟩

lemma dimH_cube_boundary_le (n : ℕ) :
    dimH (Metric.sphere (0 : Fin (n+1) → ℝ) 1) ≤ n := by
  apply (dimH_mono (sphere_subset_faces n)).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  rw [dimH_bUnion (Set.toFinite ({1,-1}:Set ℝ)).countable]
  apply iSup_le
  intro c
  apply iSup_le
  intro _
  exact (lipschitz_insertNth i c).dimH_range_le.trans_eq (Real.dimH_univ_pi_fin n)

lemma dimH_cube_boundary_subtype_le (n : ℕ) :
    dimH (Set.univ : Set (Metric.sphere (0 : Fin (n+1) → ℝ) 1)) ≤ n := by
  rw [← isometry_subtype_coe.dimH_image]
  simpa only [Subtype.range_coe_subtype,Set.image_univ,Set.ofPred_mem_eq] using dimH_cube_boundary_le n

end GroupRingTopology.GeneralPosition

end

end OAI
