import Mathlib
import OAI.Algebra.GroupRing.CayleyFurther

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def radialRetraction : C(punctured a,X) :=
  puncturedLift a (.id X) (fun i => (a i).comp radialSphere)
    (fun i x => by simp only [ContinuousMap.comp_apply,radialSphere_boundary,ContinuousMap.id_apply])

@[simp] lemma radialRetraction_base (x : X) : radialRetraction a (puncturedBase a x) = x := rfl
@[simp] lemma radialRetraction_cell (i : ι) (d : PuncturedDisk n) :
    radialRetraction a (puncturedCell a i d) = a i (radialSphere d) := by
  exact puncturedLift_cell _ _ _ _ _ _

def radialPaths : C(punctured a,C(unitInterval,Space a)) := by
  let f : C(X × unitInterval,Space a) := ⟨fun p => base a p.1,(continuous_base a).comp continuous_fst⟩
  let g (i : ι) : C(PuncturedDisk n × unitInterval,Space a) :=
    (cell a i).comp (radialDisk.comp ⟨Prod.swap,continuous_swap⟩)
  have h (i : ι) (x : Sphere n) : (g i).curry (puncturedBoundary x) = f.curry (a i x) := by
    ext t
    change cell a i (radialDisk (t,puncturedBoundary x)) = base a (a i x)
    rw [radialDisk_boundary,cell_boundary]
  exact puncturedLift a f.curry (fun i => (g i).curry) h

@[simp] lemma radialPaths_base (x : X) (t : unitInterval) :
    radialPaths a (puncturedBase a x) t = base a x := rfl
@[simp] lemma radialPaths_cell (i : ι) (d : PuncturedDisk n) (t : unitInterval) :
    radialPaths a (puncturedCell a i d) t = cell a i (radialDisk (t,d)) := by
  unfold radialPaths
  rw [puncturedLift_cell]
  rfl

def puncturedInclusion : C(punctured a,Space a) := ⟨Subtype.val,continuous_subtype_val⟩
def radialEnd : C(punctured a,Space a) := (⟨base a,continuous_base a⟩ : C(X,Space a)).comp (radialRetraction a)

/-- The punctured attachment deformation-retracts to the original space. -/
def radialHomotopy : (puncturedInclusion a).Homotopy (radialEnd a) where
  toFun p := radialPaths a p.2 p.1
  continuous_toFun := (radialPaths a).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_zero]
      rfl
  map_one_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_one,cell_boundary]
      change base a (a i (radialSphere d)) = base a (radialRetraction a (puncturedCell a i d))
      rw [radialRetraction_cell]

@[simp] lemma radialHomotopy_base (x : X) (t : unitInterval) :
    radialHomotopy a (t,puncturedBase a x) = base a x := rfl

lemma cell_eq_openCell_iff (i j : ι) (d : Disk n) (x : OpenDisk n) :
    cell a i d = openCell a j x ↔ i = j ∧ d.1 = x.1 := by
  classical
  constructor
  · intro h
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have hi : cell a i d = Sum.inr ⟨i,⟨d.1,hd⟩⟩ :=
        cell_interior a i ⟨d.1,hd⟩
      rw [hi] at h
      have hh : (⟨i,⟨d.1,hd⟩⟩ : Σ _ : ι, OpenDisk n) = ⟨j,x⟩ := Sum.inr_injective h
      exact ⟨congrArg Sigma.fst hh,congrArg (fun p : Σ _ : ι, OpenDisk n => p.2.1) hh⟩
    · let s : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have hi : cell a i d = base a (a i s) := cell_boundary a i s
      rw [hi] at h
      cases h
  · rintro ⟨rfl,h⟩
    have hd : d = interior n x := Subtype.ext h
    rw [hd,cell_interior]
    rfl

lemma openCell_disjoint (i j : ι) (hij : i ≠ j) :
    Disjoint (Set.range (openCell a i)) (Set.range (openCell a j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,rfl⟩ ⟨y,h⟩
  exact hij (congrArg Sigma.fst (Sum.inr_injective h)).symm

lemma openCell_selection_closed {I : Type*} (c : I → ι) (hc : Function.Injective c)
    (x : I → OpenDisk n) (S : Set (Space a))
    (hS : S ⊆ Set.range (fun i => openCell a (c i) (x i))) : IsClosed S := by
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨i,hi⟩ := hS hy
      cases hi
    rw [h]
    exact isClosed_empty
  · intro j
    suffices (cell a j ⁻¹' S).Subsingleton from this.finite.isClosed
    intro d hd e he
    obtain ⟨i,hi⟩ := hS hd
    obtain ⟨k,hk⟩ := hS he
    have hdi := (cell_eq_openCell_iff a j (c i) d (x i)).mp hi.symm
    have hek := (cell_eq_openCell_iff a j (c k) e (x k)).mp hk.symm
    have hik : i = k := hc (hdi.1.symm.trans hek.1)
    subst k
    exact Subtype.ext (hdi.2.trans hek.2.symm)

/-- The weak adjunction topology prevents compact sets from meeting infinitely
many of the new open cells. No local-finiteness assumption is needed. -/
lemma compact_finitely_many_openCells {K : Set (Space a)} (hK : IsCompact K) :
    {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}.Finite := by
  classical
  let I := {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}
  have hchoice (i : I) : ∃ x : OpenDisk n, openCell a i.1 x ∈ K := by
    obtain ⟨z,hz,⟨x,hx⟩⟩ := i.2
    exact ⟨x,hx ▸ hz⟩
  choose x hx using hchoice
  let y : I → Space a := fun i => openCell a i.1 (x i)
  have hyinj : Function.Injective y := by
    intro i j h
    apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr_injective h)
  have hclosed : ∀ S ⊆ Set.range y, IsClosed S :=
    openCell_selection_closed a Subtype.val Subtype.val_injective x
  have hcompact : IsCompact (Set.range y) := hK.of_isClosed_subset
    (hclosed _ subset_rfl) (Set.range_subset_iff.mpr hx)
  have hdisc : IsDiscrete (Set.range y) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hclosed S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdisc
  have : Finite I := (Set.finite_range_iff hyinj).mp hrange
  exact Set.toFinite I

end GroupRingTopology.Attachment

open Set Topology
namespace GroupRingTopology.Cellular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def patchFun (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : X) : Y := by
  classical
  exact if hx : x ∈ A then g ⟨x,hx⟩ else f x

lemma patchFun_on (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : A) :
    patchFun A f g x = g x := by simp only [patchFun,dite_eq_left x.2]

lemma patchFun_off (A : Set X) (f : C(X,Y)) (g : C(A,Y)) {x : X} (hx : x ∉ A) :
    patchFun A f g x = f x := by simp only [patchFun,dite_eq_right hx]

lemma continuous_patchFun {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) :
    Continuous (patchFun A f g) := by
  classical
  have hOn : ContinuousOn (patchFun A f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (patchFun A f g) = g := funext (patchFun_on A f g)
    rw [heq]
    exact g.continuous
  have h := continuous_if (p := fun x => x ∈ A) (f := patchFun A f g) (g := f)
    (fun x hx => by
      have hxa : x ∈ A := hA.closure_eq ▸ hx.1
      exact (patchFun_on A f g ⟨x,hxa⟩).trans (hboundary ⟨x,hxa⟩ hx))
    (by simpa only [Set.ofPred_mem_eq,hA.closure_eq] using hOn) f.continuous.continuousOn
  convert h using 1
  ext x
  by_cases hx : x ∈ A
  · simp only [ite_eq_left hx]
  · simp only [ite_eq_right hx,patchFun_off A f g hx]

def patch {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) : C(X,Y) :=
  ⟨patchFun A f g,continuous_patchFun hA f g hboundary⟩

lemma patch_on {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) (x : A) :
    patch hA f g hboundary x = g x := patchFun_on A f g x

lemma patch_off {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) {x : X} (hx : x ∉ A) :
    patch hA f g hboundary x = f x := patchFun_off A f g hx

/-- Homotopies on a closed subset glue to the stationary homotopy outside it,
provided they are stationary on the frontier. -/
def patchHomotopy {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (H : (f.restrict A).Homotopy g)
    (hboundary : ∀ (t : unitInterval) (x : A), (x:X) ∈ frontier A → H (t,x) = f x) :
    f.Homotopy (patch hA f g (fun x hx => by simpa using hboundary 1 x hx)) := by
  let B : Set (unitInterval × X) := Prod.snd ⁻¹' A
  let H' : C(B,Y) := ⟨fun z => H (z.1.1,⟨z.1.2,z.2⟩),
    H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩
  let hB : IsClosed B := hA.preimage continuous_snd
  let F : C(unitInterval × X,Y) := f.comp ⟨Prod.snd,continuous_snd⟩
  have hb : ∀ z : B, (z : unitInterval × X) ∈ frontier B → H' z = F z := by
    intro z hz
    exact hboundary z.1.1 ⟨z.1.2,z.2⟩ (continuous_snd.frontier_preimage_subset A hz)
  refine ⟨patch hB F H' hb,?_,?_⟩
  · intro x
    change patch hB F H' hb (0,x) = f x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(0,x),hx⟩]
      exact H.apply_zero ⟨x,hx⟩
    · exact patch_off hB F H' hb (x := (_,x)) hx
  · intro x
    change patch hB F H' hb (1,x) = patch hA f g _ x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(1,x),hx⟩,patch_on hA f g _ ⟨x,hx⟩]
      exact H.apply_one ⟨x,hx⟩
    · rw [patch_off hB F H' hb (x := (_,x)) hx,patch_off hA f g _ hx]
      rfl

end GroupRingTopology.Cellular
open Set Metric Topology
open scoped NNReal
namespace GroupRingTopology.GeneralPosition

section
variable {K : Type*} [MetricSpace K] [CompactSpace K]

lemma lipschitz_mul {f g : C(K,ℝ)} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) :
    LipschitzWith (‖f‖₊ * M + ‖g‖₊ * L) (f * g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [ContinuousMap.mul_apply,NNReal.coe_add,NNReal.coe_mul,coe_nnnorm]
  calc
    dist (f x * g x) (f y * g y)
        = ‖f x * (g x-g y) + g y * (f x-f y)‖ := by
          rw [dist_eq_norm]; congr 1; ring
    _ ≤ ‖f x * (g x-g y)‖ + ‖g y * (f x-f y)‖ := norm_add_le _ _
    _ = ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := by
      rw [norm_mul,norm_mul,dist_eq_norm,dist_eq_norm]
    _ ≤ ‖f‖ * ((M:ℝ) * dist x y) + ‖g‖ * ((L:ℝ) * dist x y) := by
      gcongr
      · exact f.norm_coe_le_norm x
      · exact hg.dist_le_mul x y
      · exact g.norm_coe_le_norm y
      · exact hf.dist_le_mul x y
    _ = (‖f‖ * M + ‖g‖ * L) * dist x y := by ring

def lipschitzAlgebra : Subalgebra ℝ C(K,ℝ) where
  carrier := {f | ∃ L, LipschitzWith L f}
  zero_mem' := ⟨0,LipschitzWith.const 0⟩
  one_mem' := ⟨0,LipschitzWith.const 1⟩
  add_mem' := by rintro f g ⟨L,hL⟩ ⟨M,hM⟩; exact ⟨L+M,hL.add hM⟩
  mul_mem' := by rintro f g ⟨L,hL⟩ ⟨M,hM⟩; exact ⟨_,lipschitz_mul hL hM⟩
  algebraMap_mem' r := ⟨0,LipschitzWith.const r⟩

lemma lipschitzAlgebra_separates : (lipschitzAlgebra (K := K)).SeparatesPoints := by
  intro x y hxy
  refine ⟨fun z => dist z y,⟨⟨fun z => dist z y,continuous_id.dist continuous_const⟩,
    ⟨1,LipschitzWith.dist_left y⟩,rfl⟩,?_⟩
  simpa using hxy

/-- Uniform Lipschitz approximation on an arbitrary compact metric space. -/
lemma exists_lipschitz_approximation (f : C(K,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,ℝ), (∃ L, LipschitzWith L g) ∧ ∀ x, ‖g x-f x‖ < ε := by
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    lipschitzAlgebra lipschitzAlgebra_separates f f.continuous ε hε
  exact ⟨g,g.2,hg⟩

end

section
open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

lemma exists_lipschitz_vector_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,Fin n → ℝ), (∃ L, LipschitzWith L g) ∧ ∀ x, ‖g x-f x‖ < ε := by
  classical
  have hex : ∀ i : Fin n, ∃ g : C(K,ℝ), (∃ L, LipschitzWith L g) ∧
      ∀ x, ‖g x-f x i‖ < ε := fun i =>
    exists_lipschitz_approximation ⟨fun x => f x i,(continuous_apply i).comp f.continuous⟩ hε
  choose g hg he using hex
  choose L hL using hg
  let H : C(K,Fin n → ℝ) := ⟨fun x i => g i x,continuous_pi (fun i => (g i).continuous)⟩
  refine ⟨H,⟨Finset.univ.sup L,?_⟩,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)]
    intro i
    exact (hL i).dist_le_mul x y |>.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.le_sup (f := L) (Finset.mem_univ i)) dist_nonneg)
  · intro x
    exact (pi_norm_lt_iff hε).mpr (fun i => he i x)

omit [CompactSpace K] in
/-- A Lipschitz image of smaller Hausdorff dimension misses points in every
positive-radius ball of Euclidean target space. -/
lemma exists_missing_point {n : ℕ} {g : K → Fin n → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hdim : dimH (Set.univ : Set K) < n)
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ a ∈ Metric.ball c r, a ∉ Set.range g := by
  by_contra! h
  have hle : dimH (Metric.ball c r) ≤ dimH (Set.range g) := dimH_mono h
  rw [Real.dimH_ball_pi_fin _ hr] at hle
  exact (not_le_of_gt hdim) (hle.trans hg.dimH_range_le)

/-- Every map from a compact metric space of dimension less than n can be
uniformly approximated by a map into punctured ℝ^n. -/
lemma exists_nonzero_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    (hdim : dimH (Set.univ : Set K) < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,Fin n → ℝ), (∀ x, g x ≠ 0) ∧ ∀ x, ‖g x-f x‖ < ε := by
  obtain ⟨h,⟨L,hL⟩,hh⟩ := exists_lipschitz_vector_approximation f (half_pos hε)
  obtain ⟨a,ha,ha'⟩ := exists_missing_point hL hdim 0 (half_pos hε)
  refine ⟨h - ContinuousMap.const K a,?_,?_⟩
  · intro x hx
    apply ha'
    exact ⟨x,sub_eq_zero.mp hx⟩
  · intro x
    have ha : ‖a‖ < ε/2 := by simpa only [Metric.mem_ball,dist_zero_right] using ha
    change ‖(h x-a)-f x‖ < ε
    have hhx := hh x
    calc
      ‖(h x-a)-f x‖ = ‖(h x-f x)-a‖ := by congr 1; abel
      _ ≤ ‖h x-f x‖+‖a‖ := norm_sub_le _ _
      _ < ε := by linarith

end

open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def cutoff (δ r : ℝ) : ℝ := min 1 (max 0 (2-r/δ))
lemma cutoff_nonneg (δ r : ℝ) : 0 ≤ cutoff δ r := le_min (by norm_num) (le_max_left _ _)
lemma cutoff_le_one (δ r : ℝ) : cutoff δ r ≤ 1 := min_le_left _ _
lemma cutoff_small {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ δ) : cutoff δ r = 1 := by
  apply min_eq_left
  apply le_max_of_le_right
  have : r/δ ≤ 1 := (div_le_one hδ).mpr hr
  linarith
lemma cutoff_large {δ r : ℝ} (hδ : 0 < δ) (hr : 2*δ ≤ r) : cutoff δ r = 0 := by
  have : 2 ≤ r/δ := (le_div_iff₀ hδ).mpr hr
  simp only [cutoff,max_eq_left (by linarith : 2-r/δ ≤ 0),min_eq_right (by norm_num : (0:ℝ)≤1)]
lemma continuous_cutoff (δ : ℝ) : Continuous (cutoff δ) :=
  continuous_const.min (continuous_const.max (continuous_const.sub (continuous_id.div_const δ)))

/-- General position relative to the region already far from the origin. -/
lemma exists_relative_nonzero_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    (hdim : dimH (Set.univ : Set K) < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C(K,Fin n → ℝ), (∀ x, g x ≠ 0) ∧
      (∀ x, 2*δ ≤ ‖f x‖ → g x = f x) ∧ ∀ x, ‖g x-f x‖ < δ/2 := by
  obtain ⟨h,hne,hh⟩ := exists_nonzero_approximation f hdim (half_pos hδ)
  let g : C(K,Fin n → ℝ) := ⟨fun x => f x + cutoff δ ‖f x‖ • (h x-f x),
    f.continuous.add (((continuous_cutoff δ).comp f.continuous.norm).smul
      (h.continuous.sub f.continuous))⟩
  have hdist (x : K) : ‖g x-f x‖ < δ/2 := by
    change ‖(f x+cutoff δ ‖f x‖ • (h x-f x))-f x‖ < δ/2
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans_lt (hh x)
  refine ⟨g,?_,?_,hdist⟩
  · intro x hx
    by_cases hnorm : ‖f x‖ ≤ δ
    · have hg : g x = h x := by
        change f x+cutoff δ ‖f x‖ • (h x-f x)=h x
        rw [cutoff_small hδ hnorm,one_smul,add_sub_cancel]
      exact hne x (hg.symm.trans hx)
    · have hd := hdist x
      rw [hx,zero_sub,norm_neg] at hd
      linarith
  · intro x hx
    change f x+cutoff δ ‖f x‖ • (h x-f x)=f x
    rw [cutoff_large hδ hx,zero_smul,add_zero]

omit [MetricSpace K] [CompactSpace K] in
/-- The straight-line homotopy from the original to the perturbed map stays
inside any disk of radius 4δ, and is stationary outside the core of radius 2δ. -/
lemma relative_interpolation_bound {n : ℕ} {f g : K → Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfix : ∀ x, 2*δ ≤ ‖f x‖ → g x = f x)
    (hdist : ∀ x, ‖g x-f x‖ < δ/2)
    (x : K) (hx : ‖f x‖ ≤ 4*δ) (t : unitInterval) :
    ‖f x+(t:ℝ) • (g x-f x)‖ ≤ 4*δ := by
  by_cases hc : 2*δ ≤ ‖f x‖
  · rw [hfix x hc,sub_self,smul_zero,add_zero]
    exact hx
  · have ht : ‖(t:ℝ) • (g x-f x)‖ ≤ ‖g x-f x‖ := by
      rw [norm_smul,Real.norm_of_nonneg t.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) t.2.2
    have hsum := norm_add_le (f x) ((t:ℝ) • (g x-f x))
    have hd := hdist x
    linarith

end GroupRingTopology.GeneralPosition

end

end OAI
