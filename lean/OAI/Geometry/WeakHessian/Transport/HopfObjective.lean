import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X]

def hopfObjective (f : X → ℝ) (t : ℝ) (x y : X) : ℝ :=
  f y + dist x y ^ 2 / (2*t)

def hopfLax (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sInf (Set.range (hopfObjective f t x))

lemma hopfObjective_bddBelow {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) :
    BddBelow (Set.range (hopfObjective f t x)) := by
  refine ⟨B, ?_⟩
  rintro r ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

lemma hopfLax_le_objective {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x y : X) :
    hopfLax f t x ≤ hopfObjective f t x y :=
  csInf_le (hopfObjective_bddBelow hf ht x) (mem_range_self y)

lemma hopfLax_le_self {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) : hopfLax f t x ≤ f x := by
  simpa only [hopfObjective, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    using hopfLax_le_objective hf ht x x

lemma lower_le_hopfLax {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) : B ≤ hopfLax f t x := by
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

lemma continuous_hopfObjective {f : X → ℝ} (hf : Continuous f) (t : ℝ) (x : X) :
    Continuous (hopfObjective f t x) := by
  unfold hopfObjective
  fun_prop

lemma hopfLax_mono_function {f g : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (hfg : ∀ y, f y ≤ g y) (ht : 0 < t) (x : X) :
    hopfLax f t x ≤ hopfLax g t x := by
  apply le_csInf ⟨hopfObjective g t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  exact (hopfLax_le_objective hf ht x y).trans (add_le_add_left (hfg y) _)

lemma hopfLax_antitone_time {f : X → ℝ} {B s t : ℝ}
    (hf : ∀ y, B ≤ f y) (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f t x ≤ hopfLax f s x := by
  apply le_csInf ⟨hopfObjective f s x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  apply (hopfLax_le_objective hf (hs.trans_le hst) x y).trans
  change f y + dist x y ^ 2 / (2*t) ≤ f y + dist x y ^ 2 / (2*s)
  gcongr

lemma exists_hopf_minimizer [ProperSpace X] {f : X → ℝ} {B t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) :
    ∃ y : X, hopfObjective f t x y = hopfLax f t x := by
  let R := Real.sqrt (2*t*(f x-B+1))
  have hnon : 0 ≤ 2*t*(f x-B+1) := by nlinarith [hlower x]
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*t*(f x-B+1) := Real.sq_sqrt hnon
  obtain ⟨y,hy,hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, by simpa using hR⟩ (continuous_hopfObjective hf t x).continuousOn
  have hyall : ∀ z : X, hopfObjective f t x y ≤ hopfObjective f t x z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall x R
    · exact hmin hz
    · have hdist : R < dist x z := by
        simpa only [Metric.mem_closedBall, not_le, dist_comm] using hz
      have hsq : R^2 < dist x z ^ 2 := sq_lt_sq₀ hR (dist_nonneg) |>.mpr hdist
      have hcost : f x < hopfObjective f t x z := by
        dsimp [hopfObjective]
        have hdiv : f x-B+1 < dist x z^2/(2*t) := by
          apply (lt_div_iff₀ (by positivity : 0 < 2*t)).mpr
          nlinarith
        linarith [hlower z]
      have hym : hopfObjective f t x y ≤ f x := by
        simpa only [hopfObjective, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div,
          add_zero] using (show hopfObjective f t x y ≤ hopfObjective f t x x from
            hmin (show x ∈ Metric.closedBall x R by simpa using hR))
      exact hym.trans hcost.le
  refine ⟨y, le_antisymm ?_ (hopfLax_le_objective hlower ht x y)⟩
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨z,rfl⟩
  exact hyall z

lemma hopf_minimizer_distance_sq {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) :
    dist x y ^ 2 ≤ 2*t*(f x-B) := by
  have H := hopfLax_le_self hlower ht x
  rw [← hy] at H
  have hdiv : dist x y^2/(2*t) ≤ f x-B := by
    dsimp [hopfObjective] at H
    linarith [hlower y]
  have H' := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hdiv
  nlinarith

lemma hopf_spatial_increment {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) (z : X) :
    hopfLax f t z - hopfLax f t x ≤
      dist x y / t * dist z x + dist z x ^ 2 / (2*t) := by
  have H := hopfLax_le_objective hlower ht z y
  rw [← hy]
  have hd := dist_triangle z x y
  have hs : dist z y ^ 2 ≤ (dist z x + dist x y) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr hd
  have hcost : dist z y^2/(2*t) - dist x y^2/(2*t) ≤
      dist x y / t * dist z x + dist z x^2/(2*t) := by
    rw [div_sub_div_same]
    have heq : dist x y / t * dist z x + dist z x ^ 2 / (2*t) =
        (2 * dist x y * dist z x + dist z x ^ 2) / (2*t) := by
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  dsimp [hopfObjective] at *
  linarith

lemma hopf_minimizer_distance_le {f : X → ℝ} {B U t R : ℝ}
    (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U) (ht : 0 < t)
    (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) : dist x y ≤ R := by
  apply (sq_le_sq₀ dist_nonneg hR).mp
  exact (hopf_minimizer_distance_sq hlower ht hy).trans
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right (hupper x) B) (by positivity)).trans hR2)

lemma hopf_spatial_abs_increment [ProperSpace X] {f : X → ℝ} {B U t R : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (ht : 0 < t) (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) (x z : X) :
    |hopfLax f t z - hopfLax f t x| ≤ R/t * dist z x + dist z x^2/(2*t) := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hlower ht x
  obtain ⟨w,hw⟩ := exists_hopf_minimizer hf hlower ht z
  have hyR := hopf_minimizer_distance_le hlower hupper ht hR hR2 hy
  have hwR := hopf_minimizer_distance_le hlower hupper ht hR hR2 hw
  have H := hopf_spatial_increment hlower ht hy z
  have H' := hopf_spatial_increment hlower ht hw x
  have I : dist x y / t * dist z x ≤ R/t * dist z x := by gcongr
  have I' : dist z w / t * dist z x ≤ R/t * dist z x := by gcongr
  rw [dist_comm x z] at H'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma hopfLax_lipschitz_radius [ProperSpace X] {f : X → ℝ} {B U t R : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) :
    LipschitzWith ⟨R/t + 1/(2*t) + (U-B), by positivity⟩ (hopfLax f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z x
  change |hopfLax f t z - hopfLax f t x| ≤ (R/t+1/(2*t)+(U-B))*dist z x
  by_cases hd : dist z x ≤ 1
  · have H := hopf_spatial_abs_increment hf hlower hupper ht hR hR2 x z
    have hs : dist z x^2 ≤ dist z x := by nlinarith [dist_nonneg (x := z) (y := x)]
    have I := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2*t)
    have J : 0 ≤ (U-B)*dist z x := by positivity
    simp only [div_eq_mul_inv, one_mul] at H I ⊢
    nlinarith
  · have hzlo := lower_le_hopfLax hlower ht z
    have hxlo := lower_le_hopfLax hlower ht x
    have hzup := (hopfLax_le_self hlower ht z).trans (hupper z)
    have hxup := (hopfLax_le_self hlower ht x).trans (hupper x)
    have H : |hopfLax f t z-hopfLax f t x| ≤ U-B := abs_le.mpr ⟨by linarith, by linarith⟩
    have I : U-B ≤ (U-B)*dist z x := by nlinarith
    have J : 0 ≤ (R/t+1/(2*t))*dist z x := by positivity
    nlinarith

lemma hopfLax_continuous [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) : Continuous (hopfLax f t) := by
  apply (hopfLax_lipschitz_radius hf hlower hupper hBU ht (Real.sqrt_nonneg (2*t*(U-B))) ?_).continuous
  exact (Real.sq_sqrt (by positivity)).ge

lemma hopf_time_increment {f : X → ℝ} {B s t : ℝ}
    (hlower : ∀ y, B ≤ f y) (hs : 0 < s) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) :
    hopfLax f s x - hopfLax f t x ≤ dist x y^2*(t-s)/(2*s*t) := by
  have H := hopfLax_le_objective hlower hs x y
  rw [← hy]
  have heq : dist x y^2/(2*s) - dist x y^2/(2*t) = dist x y^2*(t-s)/(2*s*t) := by
    field_simp
  dsimp [hopfObjective] at *
  linarith

lemma hopf_time_increment_bound [ProperSpace X] {f : X → ℝ} {B U s t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f s x - hopfLax f t x ≤ (U-B)*(t-s)/s := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hlower ht x
  apply (hopf_time_increment hlower hs ht hy).trans
  have H : dist x y^2 ≤ 2*t*(U-B) :=
    (hopf_minimizer_distance_sq hlower ht hy).trans (by gcongr; exact hupper x)
  calc
    dist x y^2*(t-s)/(2*s*t) ≤ (2*t*(U-B))*(t-s)/(2*s*t) := by gcongr
    _ = (U-B)*(t-s)/s := by field_simp

lemma hopf_time_abs_bound [ProperSpace X] {f : X → ℝ} {B U a s t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) (x : X) :
    |hopfLax f s x - hopfLax f t x| ≤ (U-B)/a * |s-t| := by
  wlog hst : s ≤ t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have hs0 := ha.trans_le hs
  have ht0 := ha.trans_le ht
  rw [abs_of_nonneg (sub_nonneg.mpr (hopfLax_antitone_time hlower hs0 hst x)),
    abs_of_nonpos (sub_nonpos.mpr hst)]
  have H := hopf_time_increment_bound hf hlower hupper hs0 hst x
  calc
    hopfLax f s x - hopfLax f t x ≤ (U-B)*(t-s)/s := H
    _ ≤ (U-B)*(t-s)/a := by gcongr
    _ = (U-B)/a * -(s-t) := by ring

lemma hopfLax_time_continuousAt [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) :
    ContinuousAt (fun s => hopfLax f s x) t := by
  have hLip : LipschitzOnWith ⟨(U-B)/(t/2), by positivity⟩
      (fun s => hopfLax f s x) (Ici (t/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    change |hopfLax f s x-hopfLax f r x| ≤ (U-B)/(t/2)*|s-r|
    exact hopf_time_abs_bound hf hlower hupper hBU (by positivity : 0 < t/2) hs hr x
  exact hLip.continuousOn.continuousAt (Ici_mem_nhds (by linarith))

lemma hopfLax_ge_lipschitz {f : X → ℝ} {L : ℝ≥0} {t : ℝ}
    (hf : LipschitzWith L f) (ht : 0 < t) (x : X) :
    f x - t*(L:ℝ)^2/2 ≤ hopfLax f t x := by
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  have H := hf.dist_le_mul x y
  rw [Real.dist_eq] at H
  have H' := (abs_le.mp H).2
  change f x - t*(L:ℝ)^2/2 ≤ f y + dist x y^2/(2*t)
  have Hsq := sq_nonneg (dist x y - t*(L:ℝ))
  have Hdiv : (L:ℝ)*dist x y - t*(L:ℝ)^2/2 ≤ dist x y^2/(2*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith
  linarith

lemma hopf_minimizer_distance_lipschitz {f : X → ℝ} {L : ℝ≥0} {B t : ℝ}
    (hf : LipschitzWith L f) (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) : dist x y ≤ 2*t*(L:ℝ) := by
  have H := hopfLax_le_self hlower ht x
  rw [← hy] at H
  have Hd := hf.dist_le_mul x y
  rw [Real.dist_eq] at Hd
  have Hd' := (abs_le.mp Hd).2
  have Hdiv : dist x y^2/(2*t) ≤ (L:ℝ)*dist x y := by
    dsimp [hopfObjective] at H
    linarith
  have Hmul := (div_le_iff₀ (by positivity : 0 < 2*t)).mp Hdiv
  by_cases hd : dist x y = 0
  · rw [hd]
    positivity
  · have hd0 : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    apply le_of_mul_le_mul_left (a := dist x y) _ hd0
    convert Hmul using 1 <;> ring

def IsFarthestHopfMinimizer (f : X → ℝ) (t : ℝ) (x y : X) : Prop :=
  hopfObjective f t x y = hopfLax f t x ∧
  ∀ z, hopfObjective f t x z = hopfLax f t x → dist x z ≤ dist x y

lemma hopf_minimizers_compact [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) :
    IsCompact {y | hopfObjective f t x y = hopfLax f t x} := by
  let R := Real.sqrt (2*t*(U-B))
  apply (isCompact_closedBall x R).of_isClosed_subset
    (isClosed_eq (continuous_hopfObjective hf t x) continuous_const)
  intro y hy
  rw [Metric.mem_closedBall, dist_comm]
  exact hopf_minimizer_distance_le hlower hupper ht (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)).ge hy

lemma exists_farthest_hopf_minimizer [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) : ∃ y, IsFarthestHopfMinimizer f t x y := by
  obtain ⟨y,hy,hmax⟩ := (hopf_minimizers_compact hf hlower hupper hBU ht x).exists_isMaxOn
    (exists_hopf_minimizer hf hlower ht x) (continuous_const.dist continuous_id).continuousOn
  exact ⟨y,hy, fun z hz => hmax hz⟩

lemma eventually_hopf_minimizer_distance_lt [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) {x y : X} (hy : IsFarthestHopfMinimizer f t x y)
    {r : ℝ} (hr : dist x y < r) :
    ∀ᶠ z in 𝓝 x, ∀ w, hopfObjective f t z w = hopfLax f t z → dist z w < r := by
  let R := Real.sqrt (2*t*(U-B))
  let C := Metric.closedBall x (R+1)
  let : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall x (R+1))
  let S : Set (X × C) := {p | hopfObjective f t p.1 p.2 = hopfLax f t p.1 ∧ r ≤ dist p.1 p.2}
  have hobj : Continuous (fun p : X × C => hopfObjective f t p.1 p.2) := by
    dsimp [hopfObjective]
    fun_prop
  have hdist : Continuous (fun p : X × C => dist p.1 p.2) := by fun_prop
  have hS : IsClosed S := (isClosed_eq hobj
    ((hopfLax_continuous hf hlower hupper hBU ht).comp continuous_fst)).inter
      (isClosed_le continuous_const hdist)
  have hclosed : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  have hx : x ∉ Prod.fst '' S := by
    rintro ⟨⟨z,w⟩,⟨hmin,hd⟩,hpair⟩
    dsimp at hpair
    subst z
    exact (not_le_of_gt (lt_of_le_of_lt (hy.2 w hmin) hr)) hd
  have hne : ∀ᶠ z in 𝓝 x, z ∉ Prod.fst '' S := hclosed.isOpen_compl.mem_nhds hx
  have hball : ∀ᶠ z in 𝓝 x, dist z x < 1 := Metric.ball_mem_nhds x (by norm_num)
  filter_upwards [hne, hball] with z hz hzx
  intro w hw
  have hwR : dist z w ≤ R := hopf_minimizer_distance_le hlower hupper ht
    (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity)).ge hw
  have hwC : w ∈ C := by
    change dist w x ≤ R+1
    calc
      dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
      _ ≤ R+1 := by rw [dist_comm w z]; linarith
  by_contra hrw
  apply hz
  exact ⟨(z, ⟨w, hwC⟩), ⟨hw, le_of_not_gt hrw⟩, rfl⟩

lemma hopf_time_derivative_at_minimizer {f : X → ℝ} {B t v : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x)
    (hv : HasDerivAt (fun s => hopfLax f s x) v t) :
    v = -(dist x y^2/(2*t^2)) := by
  have ho : HasDerivAt (fun s => hopfObjective f s x y)
      (-(dist x y^2/(2*t^2))) t := by
    convert (hasDerivAt_const t (f y)).add
      ((hasDerivAt_const t (dist x y^2)).div
        ((hasDerivAt_id t).const_mul 2) (by positivity : 2*t ≠ 0)) using 1
    <;> first | rfl | (simp only [id_eq]; ring)
  have hmax : IsLocalMax (fun s => hopfLax f s x - hopfObjective f s x y) t := by
    change ∀ᶠ s in 𝓝 t, hopfLax f s x - hopfObjective f s x y ≤
      hopfLax f t x - hopfObjective f t x y
    rw [hy, sub_self]
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact sub_nonpos.mpr (hopfLax_le_objective hlower hs x y)
  have H := hmax.hasDerivAt_eq_zero (hv.sub ho)
  linarith

lemma hopf_spatial_quotient_bound {f : X → ℝ} {B t r : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x z y w : X}
    (hy : hopfObjective f t x y = hopfLax f t x)
    (hw : hopfObjective f t z w = hopfLax f t z)
    (hyr : dist x y ≤ r) (hwr : dist z w ≤ r) (hzx : z ≠ x) :
    |hopfLax f t z - hopfLax f t x| / dist z x ≤ r/t + dist z x/(2*t) := by
  have H := hopf_spatial_increment hlower ht hy z
  have H' := hopf_spatial_increment hlower ht hw x
  have I : dist x y / t * dist z x ≤ r/t * dist z x := by gcongr
  have I' : dist z w / t * dist z x ≤ r/t * dist z x := by gcongr
  rw [dist_comm x z] at H'
  have Ha : |hopfLax f t z-hopfLax f t x| ≤ r/t*dist z x + dist z x^2/(2*t) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  apply (div_le_iff₀ (dist_pos.mpr hzx)).mpr
  apply Ha.trans_eq
  ring

lemma hopf_localSlope_le [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) {x y : X} (hy : IsFarthestHopfMinimizer f t x y) :
    Filter.limsup (fun z => ENNReal.ofReal
      (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x) ≤
      ENNReal.ofReal (dist x y/t) := by
  by_cases hbot : (𝓝[≠] x) = ⊥
  · simp [hbot]
  have : NeBot (𝓝[≠] x) := ⟨hbot⟩
  have H : ∀ r : ℝ, dist x y < r →
      Filter.limsup (fun z => ENNReal.ofReal
        (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x) ≤ ENNReal.ofReal (r/t) := by
    intro r hr
    have he := eventually_hopf_minimizer_distance_lt hf hlower hupper hBU ht hy hr
    have hb : ∀ᶠ z in 𝓝[≠] x, ENNReal.ofReal (|hopfLax f t z-hopfLax f t x|/dist z x) ≤
        ENNReal.ofReal (r/t+dist z x/(2*t)) := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzx
      obtain ⟨w,hw⟩ := exists_hopf_minimizer hf hlower ht z
      apply ENNReal.ofReal_le_ofReal
      exact hopf_spatial_quotient_bound hlower ht hy.1 hw hr.le (hz w hw).le hzx
    have hc : Tendsto (fun z => ENNReal.ofReal (r/t+dist z x/(2*t))) (𝓝[≠] x)
        (𝓝 (ENNReal.ofReal (r/t))) := by
      have hc' : ContinuousAt (fun z => ENNReal.ofReal (r/t+dist z x/(2*t))) x :=
        ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
      simpa using hc'.tendsto.mono_left nhdsWithin_le_nhds
    exact (limsup_le_limsup hb).trans_eq hc.limsup_eq
  have hc : Tendsto (fun r : ℝ => ENNReal.ofReal (r/t)) (𝓝[>] dist x y)
      (𝓝 (ENNReal.ofReal (dist x y/t))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_id.div_const t)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hc
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact H r hr

lemma hopf_hamiltonJacobi_at [ProperSpace X] {f : X → ℝ} {B U t v : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X)
    (hv : HasDerivAt (fun s => hopfLax f s x) v t) :
    v + (Filter.limsup (fun z => ENNReal.ofReal
      (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x)).toReal^2/2 ≤ 0 := by
  obtain ⟨y,hy⟩ := exists_farthest_hopf_minimizer hf hlower hupper hBU ht x
  have hd := hopf_time_derivative_at_minimizer hlower ht hy.1 hv
  have hs := hopf_localSlope_le hf hlower hupper hBU ht hy
  have hsr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist x y/t)] at hsr
  have hs2 := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity : 0 ≤ dist x y/t)).mpr hsr
  have heq : (dist x y/t)^2/2 = dist x y^2/(2*t^2) := by ring
  linarith

lemma hopf_hamiltonJacobi_ae [ProperSpace X] {f : X → ℝ} {B U : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (x : X) :
    ∀ᵐ t : ℝ, 0 < t → DifferentiableAt ℝ (fun s => hopfLax f s x) t ∧
      deriv (fun s => hopfLax f s x) t +
        (Filter.limsup (fun z => ENNReal.ofReal
          (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x)).toReal^2/2 ≤ 0 := by
  have hLip (n : ℕ) : LipschitzOnWith ⟨(U-B)/(1/(n+1:ℝ)), by positivity⟩
      (fun s => hopfLax f s x) (Ici (1/(n+1:ℝ))) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    exact hopf_time_abs_bound hf hlower hupper hBU (by positivity) hs hr x
  have ha := MeasureTheory.ae_all_iff.mpr
    (fun n => (hLip n).ae_differentiableWithinAt_of_mem_real)
  filter_upwards [ha] with t ht ht0
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt ht0
  have hd : DifferentiableAt ℝ (fun s => hopfLax f s x) t :=
    (ht n hn.le).differentiableAt (Ici_mem_nhds hn)
  exact ⟨hd, hopf_hamiltonJacobi_at hf hlower hupper hBU ht0 x hd.hasDerivAt⟩

end WeakHessianTransport

end
end InlinedFile0

end OAI
