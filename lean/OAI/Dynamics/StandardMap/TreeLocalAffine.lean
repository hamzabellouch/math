import OAI.Dynamics.StandardMap.TreeAffine

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def LocallyAffineAt (d : ℝ → ℝ → ℝ) (x w : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ u∈ball x r,∀ v∈ball x r,d u v=w*|v-u|
lemma locallyAffine_speed_unique {d : ℝ → ℝ → ℝ} {x w v : ℝ}
    (hw : LocallyAffineAt d x w) (hv : LocallyAffineAt d x v) : w=v := by
  obtain ⟨r,hr,hw⟩ := hw
  obtain ⟨s,hs,hv⟩ := hv
  let a := min r s/2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r := by dsimp [a]; linarith [min_le_left r s]
  have has : a < s := by dsimp [a]; linarith [min_le_right r s]
  have hd1 := hw x (mem_ball_self hr) (x+a) (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos ha]; exact har)
  have hd2 := hv x (mem_ball_self hs) (x+a) (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos ha]; exact has)
  rw [add_sub_cancel_left,abs_of_pos ha] at hd1 hd2
  nlinarith
lemma locallyAffine_on_ball {d : ℝ → ℝ → ℝ} {x w r : ℝ} (h : ∀ u∈ball x r,∀ v∈ball x r,d u v=w*|v-u|)
    {y : ℝ} (hy : y∈ball x r) : LocallyAffineAt d y w := by
  obtain ⟨s,hs,hsr⟩ := Metric.isOpen_iff.mp isOpen_ball y hy
  exact ⟨s,hs,fun u hu v hv => h u (hsr hu) v (hsr hv)⟩
lemma locallyAffine_speed_bounds {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {x w : ℝ}
    (hw : LocallyAffineAt d x w) : 0 ≤ w ∧ w ≤ 1 := by
  obtain ⟨r,hr,hw⟩ := hw
  have he := hw x (mem_ball_self hr) (x+r/2) (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity)]; linarith)
  rw [add_sub_cancel_left,abs_of_pos (by positivity)] at he
  have h0 := hd.nonneg x (x+r/2)
  have h1 := hd.unit x (x+r/2)
  rw [add_sub_cancel_left,abs_of_pos (by positivity),he] at h1
  rw [he] at h0
  constructor  <;> nlinarith
lemma connected_local_speed {d : ℝ → ℝ → ℝ} (U : Set ℝ) (hU : IsPreconnected U) (x : U)
    (hl : ∀ y : U, ∃ w : ℝ, LocallyAffineAt d y.val w) :
    ∃ w : ℝ, ∀ y : U, LocallyAffineAt d y.val w := by
  choose w hw using hl
  have hc : IsLocallyConstant w := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro y
    obtain ⟨r,hr,hh⟩ := hw y
    have hn : {z : U | z.val∈ball y.val r}∈𝓝 y :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
    filter_upwards [hn] with z hz
    exact locallyAffine_speed_unique (hw z) (locallyAffine_on_ball hh hz)
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  exact ⟨w x,fun y => (hc.apply_eq_of_preconnectedSpace y x) ▸ hw y⟩
lemma tree_affine_of_fixed_local_speed {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (a b w : ℝ)
    (hab : a < b) (hw : 0 ≤ w) (hl : ∀ x∈Icc a b,LocallyAffineAt d x w) : d a b=w*(b-a) := by
  choose r hr hloc using (fun x : Icc a b => hl x x.property)
  let c : Icc a b → Set ℝ := fun x => ball x.val (r x)
  obtain ⟨δ,hδ,hcover⟩ := lebesgue_number_lemma_of_metric (s := Icc a b) (c := c) isCompact_Icc
    (fun x => isOpen_ball) (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr ⟨x,hx⟩)⟩)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*(b-a)/δ))
  have hNR : (0:ℝ) < N := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hN)
  have hN0 : 0 < N := by exact_mod_cast hNR
  let step : ℝ := (b-a)/(N:ℝ)
  let x : ℕ → ℝ := fun i => a+(i:ℝ)*step
  have hstep : 0 < step := div_pos (sub_pos.mpr hab) hNR
  have hstepδ : 2*step < δ := by
    have hn' : 2*(b-a)/δ < (N:ℝ) := (le_max_right _ _).trans_lt hN
    have hmul := (div_lt_iff₀ hδ).mp hn'
    dsimp [step]
    apply (mul_div_assoc 2 (b-a) (N:ℝ)).symm ▸ ((div_lt_iff₀ hNR).mpr _)
    nlinarith
  have hxt : x N=b := by dsimp [x,step]; field_simp; ring
  have hx0 : x 0=a := by simp [x]
  have hdiff (i j : ℕ) : x (i+j)-x i=(j:ℝ)*step := by dsimp [x]; push_cast; ring
  have hxmem (i : ℕ) (hi : i ≤ N) : x i∈Icc a b := by
    have hiR : (i:ℝ) ≤ N := by exact_mod_cast hi
    have hmul := mul_le_mul_of_nonneg_right hiR hstep.le
    constructor
    · dsimp [x]; nlinarith [mul_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i) hstep.le]
    · change a+(i:ℝ)*step ≤ b
      change a+(N:ℝ)*step=b at hxt
      linarith
  have hball (i j : ℕ) (hj : j ≤ 2) : x (i+j)∈ball (x i) δ := by
    rw [mem_ball,Real.dist_eq,hdiff,abs_of_nonneg (by positivity)]
    have hjR : (j:ℝ) ≤ 2 := by exact_mod_cast hj
    nlinarith
  have hedge (i : ℕ) (hi : i < N) : d (x i) (x (i+1))=w*(x (i+1)-x i) := by
    obtain ⟨z,hz⟩ := hcover (x i) (hxmem i hi.le)
    have hh := hloc z (x i) (hz (mem_ball_self hδ)) (x (i+1)) (hz (hball i 1 (by omega)))
    rw [abs_of_pos (by rw [hdiff]; simpa only [Nat.cast_one,one_mul] using hstep)] at hh
    exact hh
  have htriple (i : ℕ) (hi : i+1 < N) : d (x i) (x (i+2))=w*(x (i+2)-x i) := by
    obtain ⟨z,hz⟩ := hcover (x i) (hxmem i (by omega))
    have hh := hloc z (x i) (hz (mem_ball_self hδ)) (x (i+2)) (hz (hball i 2 le_rfl))
    rw [abs_of_pos (by rw [hdiff]; positivity)] at hh
    exact hh
  have hh := tree_chain_affine hd x N w hw (fun i hi => by have he := hdiff i 1; push_cast at he; linarith) hedge htriple
  simpa only [hx0,hxt] using hh
lemma tree_affine_on_preconnected_open {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (U : Set ℝ) (hU : IsPreconnected U) (x₀ : U)
    (hl : ∀ x∈U,∃ w,LocallyAffineAt d x w) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ x∈U,∀ y∈U,d x y=w*|y-x| := by
  obtain ⟨w,hw⟩ := connected_local_speed U hU x₀ (fun y => hl y y.property)
  have hb := locallyAffine_speed_bounds hd (hw x₀)
  refine ⟨w,hb.1,hb.2,?_⟩
  intro x hx y hy
  have hinterval : OrdConnected U := isPreconnected_iff_ordConnected.mp hU
  rcases lt_trichotomy x y with hxy|rfl|hyx
  · rw [abs_of_pos (sub_pos.mpr hxy)]
    apply tree_affine_of_fixed_local_speed hd x y w hxy hb.1
    intro z hz
    exact hw ⟨z,hinterval.out hx hy hz⟩
  · simp [hd.self]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr hyx)]
    apply tree_affine_of_fixed_local_speed hd y x w hyx hb.1
    intro z hz
    exact hw ⟨z,hinterval.out hy hx hz⟩
end StandardMapEntropy

end OAI
