import OAI.Geometry.PinnedDistances.ChartLimits

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Grid

def level (ω : FullSample) (r : ℝ) : ℤ := ⌊(-r-ω.1.1)/Real.log 2⌋

def label (ω : FullSample) (r : ℝ) (z : ℂ) : ℤ × ℤ :=
  (bin ((2:ℝ)^level ω r) (shiftZ (level ω r) ω.2.1) (rotatePair ω.1.1 ω.1.2 z).1,
   bin ((2:ℝ)^level ω r) (shiftZ (level ω r) ω.2.2) (rotatePair ω.1.1 ω.1.2 z).2)

lemma regular_pair_ae (z w : ℂ) :
    ∀ᵐ ω ∂ fullLaw,
      (∃ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) ∧
      (∀ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) →
        shareAt (m+1) ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) := by
  have hm (m : ℤ) : MeasurableSet {ω : FullSample | shareAt m ω.2
      (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)} :=
    measurableSet_shareAt_param measurable_snd
      ((measurable_rotatePair z).comp measurable_fst) ((measurable_rotatePair w).comp measurable_fst) m
  have hs : MeasurableSet {ω : FullSample |
      (∃ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) ∧
      (∀ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) →
        shareAt (m+1) ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w))} := by
    simp only [Set.ofPred_and,Set.ofPred_exists,Set.ofPred_forall]
    refine (MeasurableSet.iUnion hm).inter (MeasurableSet.iInter (fun m => ?_))
    convert (hm m).compl.union (hm (m+1)) using 1
    ext ω
    exact imp_iff_not_or
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  have hn : ∀ᵐ ω ∂ squareLaw, ∀ m, shareAt m ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) →
      shareAt (m+1) ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) := by
    exact eventually_countable_forall.mpr (fun m => shareAt_nested_ae m _ _)
  filter_upwards [share_eventually_exists (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w),hn] with ω he hn
  obtain ⟨n,he⟩ := he
  exact ⟨⟨(n:ℤ),he⟩,hn⟩

lemma label_eq_iff {ω : FullSample} {z w : ℂ} (hzw : z≠w)
    (he : ∃ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w))
    (hn : ∀ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) →
      shareAt (m+1) ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) (r : ℝ) :
    label ω r z=label ω r w ↔ r≤depth ω z w := by
  rw [show label ω r z=label ω r w ↔ shareAt (level ω r) ω.2
    (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) by simp only [label,Prod.mk.injEq,shareAt]]
  rw [shareAt_iff_minScale_le (rotatePair_ne _ _ hzw) he hn]
  unfold level depth gridDepth
  rw [Int.le_floor,le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  constructor <;> intro h <;> linarith

/-- Side length in the original (unrotated) plane, after scaling by exp m. -/
def side (ω : FullSample) (r m : ℝ) : ℝ := Real.exp (m+ω.1.1)*(2:ℝ)^level ω r

lemma side_pos (ω : FullSample) (r m : ℝ) : 0<side ω r m := by unfold side; positivity

lemma log_side (ω : FullSample) (r m : ℝ) :
    Real.log (side ω r m)=m+ω.1.1+(level ω r:ℝ)*Real.log 2 := by
  unfold side
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_zpow]

lemma side_bounds (ω : FullSample) (r m : ℝ) :
    Real.exp (m-r)/2 < side ω r m ∧ side ω r m ≤ Real.exp (m-r) := by
  have hl := Int.floor_le ((-r-ω.1.1)/Real.log 2)
  have hu := Int.lt_floor_add_one ((-r-ω.1.1)/Real.log 2)
  have hp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl' := (le_div_iff₀ hp).mp hl
  have hu' := (div_lt_iff₀ hp).mp hu
  change (level ω r:ℝ)*Real.log 2≤ -r-ω.1.1 at hl'
  change -r-ω.1.1<((level ω r:ℝ)+1)*Real.log 2 at hu'
  constructor
  · rw [← Real.exp_log (by norm_num : (0:ℝ)<2),← Real.exp_sub]
    rw [← Real.exp_log (side_pos ω r m),Real.exp_lt_exp,log_side]
    nlinarith
  · rw [← Real.exp_log (side_pos ω r m),Real.exp_le_exp,log_side]
    linarith

lemma label_diameter {ω : FullSample} {r m : ℝ} {z w : ℂ}
    (h : label ω r z=label ω r w) :
    ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖ < 2*side ω r m := by
  have h₁ := shares_gap (by positivity : 0<(2:ℝ)^level ω r) (congrArg Prod.fst h)
  have h₂ := shares_gap (by positivity : 0<(2:ℝ)^level ω r) (congrArg Prod.snd h)
  have hh := (rotatePair_gaps ω.1.1 ω.1.2 z w).1
  have hm := mul_lt_mul_of_pos_left (show Real.exp (-ω.1.1)*‖z-w‖ < 2*(2:ℝ)^level ω r by linarith)
    (Real.exp_pos (m+ω.1.1))
  have he : Real.exp (m+ω.1.1)*Real.exp (-ω.1.1)=Real.exp m := by rw [← Real.exp_add]; congr 1; ring
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold side
  rw [← mul_assoc,he] at hm
  nlinarith

end WeakPinned.Grid

namespace WeakPinned.Global
open NumberField Hierarchy
variable {P : Type u1} {K : Type u2} [Fintype P] [DecidableEq P] [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z) (v : InfinitePlace K)

omit [NumberField K] in
include hZ in
lemma arch_label_ae : ∀ᵐ ω ∂ Grid.fullLaw, ∀ r x y,
    (arch Z v ω).share r x y ↔ Grid.label ω r (v.embedding (Z x))=Grid.label ω r (v.embedding (Z y)) := by
  have hr : ∀ᵐ ω ∂ Grid.fullLaw, ∀ x y,
      (∃ m, Grid.shareAt m ω.2 (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z x))) (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z y)))) ∧
      (∀ m, Grid.shareAt m ω.2 (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z x))) (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z y))) →
        Grid.shareAt (m+1) ω.2 (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z x))) (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z y)))) := by
    simp only [Filter.eventually_all]
    exact fun x y => Grid.regular_pair_ae _ _
  filter_upwards [good_ae Z hZ v,hr] with ω hg hr
  intro r x y
  by_cases hxy : x=y
  · subst y; simp [Depth.share]
  · rw [Depth.share,or_iff_right hxy]
    change (r ≤ if good Z v ω ∧ x≠y then Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y)) else 0) ↔ _
    rw [ite_eq_left ⟨hg,hxy⟩]
    exact (Grid.label_eq_iff (embedding_ne Z hZ v hxy) (hr x y).1 (hr x y).2 r).symm

end WeakPinned.Global

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Grid

lemma bin_gap {l : ℝ} (hl : 0<l) (s x y : ℝ) :
    |(bin l s x : ℝ)-(bin l s y : ℝ)| < |x-y|/l+1 := by
  have hx := Int.floor_le ((x-s)/l)
  have hy := Int.lt_floor_add_one ((y-s)/l)
  have hx' := Int.lt_floor_add_one ((x-s)/l)
  have hy' := Int.floor_le ((y-s)/l)
  have hh : (x-s)/l-(y-s)/l=(x-y)/l := by ring
  have hle := div_le_div_of_nonneg_right (le_abs_self (x-y)) hl.le
  have hge := div_le_div_of_nonneg_right (neg_abs_le (x-y)) hl.le
  rw [neg_div] at hge
  unfold bin
  apply abs_lt.mpr
  constructor <;> linarith

lemma scaled_ratio (ω : FullSample) (r m : ℝ) (z w : ℂ) :
    Real.exp (-ω.1.1)*‖z-w‖/(2:ℝ)^level ω r =
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m := by
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold side
  have he : Real.exp (-ω.1.1)*Real.exp (m+ω.1.1)=Real.exp m := by
    rw [← Real.exp_add]; congr 1; ring
  field_simp
  nlinarith [congrArg (fun t : ℝ => ‖z-w‖*t) he]

lemma label_gap (ω : FullSample) (r m : ℝ) (z w : ℂ) :
    |((label ω r z).1:ℝ)-((label ω r w).1:ℝ)| <
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m+1 ∧
    |((label ω r z).2:ℝ)-((label ω r w).2:ℝ)| <
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m+1 := by
  have h₁ : |(rotatePair ω.1.1 ω.1.2 z).1-(rotatePair ω.1.1 ω.1.2 w).1|≤
      Real.exp (-ω.1.1)*‖z-w‖ := by
    simpa only [← norm_rotateC ω.1.1 ω.1.2 (z-w),rotateC_sub,rotatePair,Complex.sub_re] using
      Complex.abs_re_le_norm (rotateC ω.1.1 ω.1.2 z-rotateC ω.1.1 ω.1.2 w)
  have h₂ : |(rotatePair ω.1.1 ω.1.2 z).2-(rotatePair ω.1.1 ω.1.2 w).2|≤
      Real.exp (-ω.1.1)*‖z-w‖ := by
    simpa only [← norm_rotateC ω.1.1 ω.1.2 (z-w),rotateC_sub,rotatePair,Complex.sub_im] using
      Complex.abs_im_le_norm (rotateC ω.1.1 ω.1.2 z-rotateC ω.1.1 ω.1.2 w)
  have hp : 0<(2:ℝ)^level ω r := by positivity
  constructor
  · exact (bin_gap hp _ _ _).trans_le (add_le_add
      ((div_le_div_of_nonneg_right h₁ hp.le).trans_eq (scaled_ratio ω r m z w)) le_rfl)
  · exact (bin_gap hp _ _ _).trans_le (add_le_add
      ((div_le_div_of_nonneg_right h₂ hp.le).trans_eq (scaled_ratio ω r m z w)) le_rfl)

/-- A uniform bound on the number of occupied squares meeting the disk.
Only the lower bound on the actual side is needed. -/
lemma card_labels_bound {P : Type u3} [DecidableEq P] (A : Finset P) (u : P → ℂ)
    (ω : FullSample) (r m : ℝ) (b : ℂ) (R L : ℝ) (M : ℕ)
    (hR : 0≤R) (hL : 0<L) (hside : L ≤ side ω r m)
    (hM : 2*R/L+1≤M)
    (hA : ∀ x∈A, ‖(Real.exp m:ℂ)*u x+b‖≤R) :
    (A.image (fun x => label ω r (u x))).card ≤ (2*M+1)^2 := by
  classical
  rcases A.eq_empty_or_nonempty with h | ⟨x₀,hx₀⟩
  · simp [h]
  let l₀ := label ω r (u x₀)
  have hd (x : P) (hx : x∈A) :
      ‖(Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀‖≤2*R := by
    rw [show (Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀=
      ((Real.exp m:ℂ)*u x+b)-((Real.exp m:ℂ)*u x₀+b) by ring]
    exact (norm_sub_le _ _).trans (by linarith [hA x hx,hA x₀ hx₀])
  have hg (x : P) (hx : x∈A) :
      |((label ω r (u x)).1:ℝ)-(l₀.1:ℝ)|≤M ∧
      |((label ω r (u x)).2:ℝ)-(l₀.2:ℝ)|≤M := by
    have hb : ‖(Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀‖/side ω r m+1≤M := by
      apply le_trans _ hM
      apply add_le_add _ le_rfl
      exact div_le_div₀ (by positivity) (hd x hx) hL hside
    exact ⟨(label_gap ω r m _ _).1.le.trans hb,(label_gap ω r m _ _).2.le.trans hb⟩
  have hs : A.image (fun x => label ω r (u x)) ⊆
      (Finset.Icc (l₀.1-(M:ℤ)) (l₀.1+(M:ℤ))) ×ˢ
      (Finset.Icc (l₀.2-(M:ℤ)) (l₀.2+(M:ℤ))) := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    have hh := hg x hx
    rcases abs_le.mp hh.1 with ⟨ha,hb⟩
    rcases abs_le.mp hh.2 with ⟨hc,hd⟩
    simp only [Finset.mem_product,Finset.mem_Icc]
    constructor
    · constructor
      · exact_mod_cast (show (l₀.1:ℝ)-(M:ℝ)≤((label ω r (u x)).1:ℝ) by linarith)
      · exact_mod_cast (show ((label ω r (u x)).1:ℝ)≤(l₀.1:ℝ)+(M:ℝ) by linarith)
    · constructor
      · exact_mod_cast (show (l₀.2:ℝ)-(M:ℝ)≤((label ω r (u x)).2:ℝ) by linarith)
      · exact_mod_cast (show ((label ω r (u x)).2:ℝ)≤(l₀.2:ℝ)+(M:ℝ) by linarith)
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ = (2*M+1)^2 := by
      rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
      have he (z : ℤ) : (z+(M:ℤ)+1-(z-(M:ℤ))).toNat=2*M+1 := by omega
      rw [he,he,pow_two]

end WeakPinned.Grid

end
end

end OAI
