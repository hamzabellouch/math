import OAI.GroupTheory.UniversalGroup.CoveringAttachments

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology

open Set Metric Topology
open scoped NNReal
namespace UniversalFInfinity.GeneralPosition

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

lemma exists_missing_point {n : ℕ} {g : K → Fin n → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hdim : dimH (Set.univ : Set K) < n)
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ a ∈ Metric.ball c r, a ∉ Set.range g := by
  by_contra! h
  have hle : dimH (Metric.ball c r) ≤ dimH (Set.range g) := dimH_mono h
  rw [Real.dimH_ball_pi_fin _ hr] at hle
  exact (not_le_of_gt hdim) (hle.trans hg.dimH_range_le)

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

end UniversalFInfinity.GeneralPosition

namespace UniversalFInfinity.Cellular

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
  rw [ContinuousMap.Homotopy.trans_apply]
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
      rw [ContinuousMap.Homotopy.trans_apply]
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

end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def chart (i : ι) : C(Cellular.ChartDisk n,Space a) :=
  ⟨openCell a i,(openCell_openEmbedding a i).continuous⟩

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
  change (H.trans J') (t,x) = f x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hfixed _
  · exact hjfixed _

end UniversalFInfinity.Attachment

end

end OAI
