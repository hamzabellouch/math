import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsSubgradientOn (f : E → ℝ) (s : Set E) (h zeta : E) : Prop :=
  ∀ y ∈ s, f h + inner ℝ zeta (y - h) ≤ f y

def quadraticTaylor (f0 : ℝ) (p : E) (A : E →L[ℝ] E) (h : E) : ℝ :=
  f0 + inner ℝ p h + inner ℝ (A h) h / 2

def HasQuadraticExpansion (f : E → ℝ) (p : E) (A : E →L[ℝ] E) : Prop :=
  ∀ w : ℝ, 0 < w → ∃ delta : ℝ, 0 < delta ∧
    ∀ z : E, ‖z‖ < delta →
      |f z - quadraticTaylor (f 0) p A z| ≤ w * ‖z‖ ^ 2

lemma convex_lipschitz_extension {f : E → ℝ} {s : Set E} {L : ℝ≥0}
    (hc : ConvexOn ℝ s f) (hlip : LipschitzOnWith L f s) (hs : s.Nonempty) :
    ∃ g : E → ℝ, LipschitzWith L g ∧ ConvexOn ℝ univ g ∧ EqOn f g s := by
  have : Nonempty s := hs.to_subtype
  let g := fun y : E => ⨅ x : s, f x + L * dist y x
  have hB : ∀ y : E, BddBelow (range fun x : s => f x + L * dist y x) := by
    intro y
    obtain ⟨z,hz⟩ := hs
    refine ⟨f z - L*dist y z, ?_⟩
    rintro w ⟨t,rfl⟩
    dsimp
    rw [sub_le_iff_le_add,add_assoc,← mul_add,add_comm (dist y t)]
    calc
      f z ≤ f t + L * dist z t := hlip.le_add_mul hz t.2
      _ ≤ f t + L*(dist y z + dist y t) := by
        gcongr
        exact dist_triangle_left _ _ _
  have hEq : EqOn f g s := by
    intro x hx
    refine le_antisymm (le_ciInf fun y => hlip.le_add_mul hx y.2) ?_
    simpa only [add_zero,Subtype.coe_mk,mul_zero,dist_self] using ciInf_le (hB x) ⟨x,hx⟩
  have hgL : LipschitzWith L g := by
    apply LipschitzWith.of_le_add_mul L
    intro x y
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun z => ?_
    rw [sub_le_iff_le_add]
    calc
      g x ≤ f z + L*dist x z := ciInf_le (hB x) _
      _ ≤ f z + L*dist y z + L*dist x y := by
        rw [add_assoc,← mul_add,add_comm (dist y z)]
        gcongr
        exact dist_triangle _ _ _
  refine ⟨g,hgL,⟨convex_univ,?_⟩,hEq⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨u,hu⟩ : ∃ u : s, f u + L*dist x u < g x + eps :=
    exists_lt_of_ciInf_lt (by dsimp [g]; linarith : g x < g x + eps)
  obtain ⟨v,hv⟩ : ∃ v : s, f v + L*dist y v < g y + eps :=
    exists_lt_of_ciInf_lt (by dsimp [g]; linarith : g y < g y + eps)
  have huv : a • (u:E) + b • (v:E) ∈ s := hc.1 u.2 v.2 ha hb hab
  have hcf := hc.2 u.2 v.2 ha hb hab
  have hdist : dist (a • x+b • y) (a • (u:E)+b • (v:E)) ≤
      a*dist x u + b*dist y v := by
    rw [dist_eq_norm,dist_eq_norm,dist_eq_norm]
    have heq : a • x+b • y-(a • (u:E)+b • (v:E)) =
      a • (x-u) + b • (y-v) := by simp only [smul_sub]; abel
    rw [heq]
    calc
      ‖a • (x-u)+b • (y-v)‖ ≤ ‖a • (x-u)‖+‖b • (y-v)‖ := norm_add_le _ _
      _ = a*‖x-u‖+b*‖y-v‖ := by rw [norm_smul_of_nonneg ha,norm_smul_of_nonneg hb]
  calc
    g (a • x+b • y) ≤ f (a • (u:E)+b • (v:E)) +
        L*dist (a • x+b • y) (a • (u:E)+b • (v:E)) :=
      ciInf_le (hB _) ⟨_,huv⟩
    _ ≤ a*f u+b*f v + L*(a*dist x u+b*dist y v) := by
      exact add_le_add hcf (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
    _ = a*(f u+L*dist x u)+b*(f v+L*dist y v) := by ring
    _ ≤ a*(g x+eps)+b*(g y+eps) := add_le_add
      (mul_le_mul_of_nonneg_left hu.le ha) (mul_le_mul_of_nonneg_left hv.le hb)
    _ = a*g x+b*g y+eps := by nlinarith [hab]

open MeasureTheory

lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {s : Set X} {P : X → Prop}
    (hloc : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∀ᵐ z ∂μ, z ∈ U → P z)) :
    ∀ᵐ z ∂μ, z ∈ s → P z := by
  classical
  choose U hUo hxU hUae using fun x : s => hloc x x.2
  have hcov : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨c,hc,hcover⟩ := (IsLindelof.of_coe (s := s)).elim_countable_subcover U hUo hcov
  have hnull : μ (⋃ i ∈ c, {z | z ∈ U i ∧ ¬P z}) = 0 := by
    apply (measure_biUnion_null_iff hc).mpr
    intro i _
    simpa only [Classical.not_imp] using (ae_iff.mp (hUae i))
  apply ae_iff.mpr
  apply measure_mono_null _ hnull
  intro z hz
  have hz' : z ∈ s ∧ ¬P z := by simpa only [mem_ofPred_eq,Classical.not_imp] using hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hcover hz'.1)
  exact mem_iUnion₂.mpr ⟨i,hi,hzi,hz'.2⟩

namespace ConvexProximal

def energy (f : E → ℝ) (y x : E) : ℝ := f x + ‖x-y‖^2/2

lemma norm_sq_add_real (a b : E) :
    ‖a+b‖^2 = ‖a‖^2 + 2 * inner ℝ a b + ‖b‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right]
  rw [real_inner_comm b a]
  ring

lemma energy_increment (f : E → ℝ) (y x v : E) (t : ℝ) :
    energy f y (x + t • (v-x)) - energy f y x =
      f (x + t • (v-x)) - f x +
        t * inner ℝ (x-y) (v-x) + t^2/2*‖v-x‖^2 := by
  have heq : x + t • (v-x) - y = (x-y) + t • (v-x) := by abel
  simp only [energy, heq, norm_sq_add_real, real_inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma subgradient_iff_minimizer {f : E → ℝ} (hf : ConvexOn ℝ univ f) (y x : E) :
    IsSubgradientOn f univ x (y-x) ↔ ∀ v, energy f y x ≤ energy f y v := by
  constructor
  · intro hs v
    have hh := hs v (mem_univ _)
    have hi := energy_increment f y x v 1
    have heq : x + (1:ℝ) • (v-x) = v := by simp
    rw [heq] at hi
    have hí : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
      rw [← neg_sub x y, inner_neg_left]
    rw [hí] at hh
    nlinarith [sq_nonneg ‖v-x‖]
  · intro hm v _
    have hb (t : ℝ) (ht : t ∈ Ioo 0 1) :
        f x + inner ℝ (y-x) (v-x) ≤ f v + t/2*‖v-x‖^2 := by
      have hc := hf.2 (mem_univ x) (mem_univ v) (by linarith [ht.2] : 0 ≤ 1-t)
        ht.1.le (by ring : 1-t+t=1)
      have heq : (1-t) • x + t • v = x + t • (v-x) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      rw [heq] at hc
      have hi := energy_increment f y x v t
      have hlo := hm (x + t • (v-x))
      have hinner : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
        rw [← neg_sub x y, inner_neg_left]
      rw [hinner]
      have hc' : f (x + t • (v-x)) ≤ (1-t)*f x + t*f v := by
        simpa only [smul_eq_mul] using hc
      apply (mul_le_mul_iff_left₀ ht.1).mp
      nlinarith
    have hcl : (0 : ℝ) ∈ closure (Ioo 0 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
      simp
    have hc : Continuous (fun t : ℝ => f v + t/2*‖v-x‖^2) := by fun_prop
    have hh := ContinuousWithinAt.closure_le hcl
      (continuousWithinAt_const (b := f x + inner ℝ (y-x) (v-x))) hc.continuousWithinAt hb
    simpa using hh

lemma subgradient_strong_min {f : E → ℝ} {y x : E}
    (hs : IsSubgradientOn f univ x (y-x)) (v : E) :
    energy f y x + ‖v-x‖^2/2 ≤ energy f y v := by
  have hh := hs v (mem_univ _)
  have hi := energy_increment f y x v 1
  have heq : x + (1:ℝ) • (v-x) = v := by simp
  rw [heq] at hi
  have hí : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
    rw [← neg_sub x y, inner_neg_left]
  rw [hí] at hh
  nlinarith

lemma subgradient_monotone {f : E → ℝ} {x z p q : E}
    (hp : IsSubgradientOn f univ x p) (hq : IsSubgradientOn f univ z q) :
    0 ≤ inner ℝ (p-q) (x-z) := by
  have h1 := hp z (mem_univ _)
  have h2 := hq x (mem_univ _)
  rw [← neg_sub x z, inner_neg_right] at h1
  simp only [inner_sub_left]
  linarith

lemma minimizer_unique {f : E → ℝ} (hf : ConvexOn ℝ univ f) {y x z : E}
    (hx : ∀ v, energy f y x ≤ energy f y v)
    (hz : ∀ v, energy f y z ≤ energy f y v) : x = z := by
  have hs := (subgradient_iff_minimizer hf y x).mpr hx
  have hb := subgradient_strong_min hs z
  have hh := hz x
  have hzero : ‖z-x‖ = 0 := by nlinarith [norm_nonneg (z-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

variable [FiniteDimensional ℝ E]

lemma exists_minimizer {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (y : E) :
    ∃ x, ∀ v, energy f y x ≤ energy f y v := by
  let R : ℝ := 2*(L:ℝ)+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfc := hf.continuous
  have hc : Continuous (energy f y) := by unfold energy; fun_prop
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall y R).exists_isMinOn
    ⟨y, Metric.mem_closedBall_self hR⟩ hc.continuousOn
  refine ⟨x, fun v => ?_⟩
  by_cases hv : v ∈ Metric.closedBall y R
  · exact hmin hv
  have hvR : R < ‖v-y‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hv
  have hh : f y - (L:ℝ)*‖v-y‖ ≤ f v := by
    have hl := hf.dist_le_mul v y
    rw [Real.dist_eq, dist_eq_norm] at hl
    have hl' := (abs_le.mp hl).1
    linarith
  have hpos : f y < energy f y v := by
    dsimp [R] at hvR
    unfold energy
    nlinarith [show (0:ℝ) ≤ L from L.coe_nonneg]
  have hxy : energy f y x ≤ energy f y y := hmin (Metric.mem_closedBall_self hR)
  have ey : energy f y y = f y := by simp [energy]
  rw [ey] at hxy
  exact hxy.trans hpos.le

def prox (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (y : E) : E :=
  Classical.choose (exists_minimizer hf y)

lemma prox_minimizes (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (y v : E) :
    energy f y (prox f L hf y) ≤ energy f y v :=
  Classical.choose_spec (exists_minimizer hf y) v

lemma prox_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) (y : E) :
    IsSubgradientOn f univ (prox f L hlip y) (y - prox f L hlip y) :=
  (subgradient_iff_minimizer hconv y _).mpr (prox_minimizes f L hlip y)

lemma prox_of_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) {x p : E} (hp : IsSubgradientOn f univ x p) :
    prox f L hlip (x+p) = x := by
  apply minimizer_unique hconv (prox_minimizes f L hlip (x+p))
  apply (subgradient_iff_minimizer hconv (x+p) x).mp
  simpa using hp

lemma prox_firm {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) (y z : E) :
    ‖prox f L hlip y - prox f L hlip z‖^2 ≤
      inner ℝ (prox f L hlip y - prox f L hlip z) (y-z) := by
  have hm := subgradient_monotone (prox_subgradient hlip hconv y)
    (prox_subgradient hlip hconv z)
  have heq : (y-prox f L hlip y) - (z-prox f L hlip z) =
      (y-z) - (prox f L hlip y - prox f L hlip z) := by abel
  rw [heq, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at hm
  linarith

lemma prox_lipschitz {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) : LipschitzWith 1 (prox f L hlip) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hf := prox_firm hlip hconv y z
  have hi := real_inner_le_norm (prox f L hlip y - prox f L hlip z) (y-z)
  have hnorm : ‖prox f L hlip y - prox f L hlip z‖ ≤ ‖y-z‖ := by
    nlinarith [norm_nonneg (prox f L hlip y - prox f L hlip z), norm_nonneg (y-z)]
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hnorm

omit [FiniteDimensional ℝ E] in
lemma subgradient_norm_le {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    {x p : E} (hp : IsSubgradientOn f univ x p) : ‖p‖ ≤ L := by
  have hs := hp (x+p) (mem_univ _)
  have hl := hlip.dist_le_mul (x+p) x
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  simp only [dist_eq_norm, add_sub_cancel_left] at hl
  have hh := (abs_le.mp hl).2
  nlinarith [norm_nonneg p]

lemma gradient_subgradient {f : E → ℝ} (hc : ConvexOn ℝ univ f) {x : E}
    {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    IsSubgradientOn f univ x ((InnerProductSpace.toDual ℝ E).symm f') := by
  intro v _
  rw [InnerProductSpace.toDual_symm_apply]
  have hd : HasDerivAt (fun t : ℝ => f (x + t • (v-x))) (f' (v-x)) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x + t • (v-x)) (v-x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v-x)).const_add x
    have hdf : HasFDerivAt f f' (x + (0:ℝ) • (v-x)) := by simpa using hder
    exact hdf.comp_hasDerivAt 0 hp
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ * (f (x+t • (v-x)) - f x) ≤ f v - f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hcv := hc.2 (mem_univ x) (mem_univ v) (by linarith [ht.2] : 0 ≤ 1-t)
      ht.1.le (by ring : 1-t+t=1)
    have heq : (1-t) • x + t • v = x + t • (v-x) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [heq] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div, div_le_iff₀ ht.1]
    nlinarith
  have ht : Tendsto (fun t : ℝ => t⁻¹ * (f (x+t • (v-x)) - f x))
      (𝓝[>] 0) (𝓝 (f' (v-x))) := by
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul] using hd.tendsto_slope_zero_right
  have hh := le_of_tendsto ht hb
  linarith

lemma subgradient_eq_gradient {f : E → ℝ} {x p : E} {f' : E →L[ℝ] ℝ}
    (hder : HasFDerivAt f f' x) (hp : IsSubgradientOn f univ x p) :
    p = (InnerProductSpace.toDual ℝ E).symm f' := by
  let g : E → ℝ := fun z => f z - inner ℝ p z
  have hmin : IsLocalMin g x := by
    apply Filter.Eventually.of_forall
    intro z
    have hh := hp z (mem_univ _)
    dsimp [g]
    simp only [inner_sub_right] at hh
    linarith
  have hdg : HasFDerivAt g (f' - innerSL ℝ p) x :=
    hder.sub (innerSL ℝ p).hasFDerivAt
  have hz := hmin.hasFDerivAt_eq_zero hdg
  have heq : f' = innerSL ℝ p := sub_eq_zero.mp hz
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact heq.symm

omit [FiniteDimensional ℝ E] in
lemma isClosed_subgradient_projection {f : E → ℝ} (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) :
    IsClosed {x | ∃ p ∈ K, IsSubgradientOn f univ x p} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : Set (E × K) := {z | IsSubgradientOn f univ z.1 z.2.1}
  have hC : IsClosed C := by
    simp only [C, IsSubgradientOn, ofPred_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) (by fun_prop)
  have heq : {x | ∃ p ∈ K, IsSubgradientOn f univ x p} = Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨p,hp,hpx⟩
      exact ⟨(x,⟨p,hp⟩),hpx,rfl⟩
    · rintro ⟨⟨z,p⟩,hz,rfl⟩
      exact ⟨p.1,p.2,hz⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace C hC

lemma subgradient_continuity_at_singleton {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) {x p0 : E}
    (huniq : ∀ p, IsSubgradientOn f univ x p → p = p0) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p → ‖p-p0‖ < eps := by
  intro eps heps
  let K := Metric.closedBall (0:E) (L:ℝ) \ Metric.ball p0 eps
  have hK : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hclosed := isClosed_subgradient_projection hlip.continuous hK
  have hx : x ∉ {z | ∃ p ∈ K, IsSubgradientOn f univ z p} := by
    rintro ⟨p,hp,hpx⟩
    have heq := huniq p hpx
    exact hp.2 (heq ▸ Metric.mem_ball_self heps)
  obtain ⟨delta,hd,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hx)
  refine ⟨delta,hd,?_⟩
  intro z p hz hp
  by_contra hbad
  have hpK : p ∈ K := by
    constructor
    · simpa only [Metric.mem_closedBall,dist_zero_right] using subgradient_norm_le hlip hp
    · simpa only [Metric.mem_ball,dist_eq_norm] using hbad
  exact (hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)) ⟨p,hpK,hp⟩

lemma subgradient_continuity_of_differentiable {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) {x : E} {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p →
        ‖p-(InnerProductSpace.toDual ℝ E).symm f'‖ < eps :=
  subgradient_continuity_at_singleton hlip (fun _ hp => subgradient_eq_gradient hder hp)

lemma uniform_subgradient_differential_of_regular_prox {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    {x y : E} {f' : E →L[ℝ] ℝ} (hdf : HasFDerivAt f f' x)
    (hy : prox f L hlip y = x) (B : E ≃L[ℝ] E)
    (hdP : HasFDerivAt (prox f L hlip) (B : E →L[ℝ] E) y) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p →
        ‖p - (InnerProductSpace.toDual ℝ E).symm f' -
          ((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x)‖ ≤
          eps * ‖z-x‖ := by
  let p0 := (InnerProductSpace.toDual ℝ E).symm f'
  have hyp : y = x + p0 := by
    have hs := prox_subgradient hlip hc y
    rw [hy] at hs
    have heq := subgradient_eq_gradient hdf hs
    dsimp [p0]
    rw [← heq]
    abel
  intro eps heps
  let K : ℝ := ‖(B.symm : E →L[ℝ] E)‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKbound : ‖(B.symm : E →L[ℝ] E)‖ ≤ K := by dsimp [K]; linarith
  let eta : ℝ := min (1/(2*K)) (eps/(2*K^2))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : K*eta ≤ 1/2 := by
    have hh := min_le_left (1/(2*K)) (eps/(2*K^2))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*K)).mp hh
    dsimp [eta]
    nlinarith
  have heta2 : 2*K^2*eta ≤ eps := by
    have hh := min_le_right (1/(2*K)) (eps/(2*K^2))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*K^2)).mp hh
    dsimp [eta]
    nlinarith
  obtain ⟨r,hr,hrem⟩ := Metric.mem_nhds_iff.mp (hdP.isLittleO.bound heta)
  obtain ⟨d,hd,hcont⟩ := subgradient_continuity_of_differentiable hlip hdf (r/2)
    (by positivity)
  refine ⟨min d (r/2), by positivity, ?_⟩
  intro z p hz hp
  have hpn : ‖p-p0‖ < r/2 := hcont z p (lt_of_lt_of_le hz (min_le_left _ _)) hp
  let k : E := z+p-y
  have hk : k = (z-x) + (p-p0) := by dsimp [k]; rw [hyp]; abel
  have hkr : ‖z+p-y‖ < r := by
    calc
      ‖z+p-y‖ = ‖(z-x)+(p-p0)‖ := congrArg norm hk
      _ ≤ ‖z-x‖ + ‖p-p0‖ := norm_add_le _ _
      _ < r := by have hz' := lt_of_lt_of_le hz (min_le_right _ _); linarith
  have hPz : prox f L hlip (z+p) = z := prox_of_subgradient hlip hc hp
  have hres : ‖(z-x) - B k‖ ≤ eta*‖k‖ := by
    have hh := hrem (by simpa only [Metric.mem_ball,dist_eq_norm] using hkr)
    simpa only [Set.mem_ofPred_eq, hy,hPz,k,ContinuousLinearEquiv.coe_coe] using hh
  have hinv : k = B.symm (z-x) - B.symm ((z-x)-B k) := by
    simp only [map_sub, B.symm_apply_apply]
    abel
  have hknorm : ‖k‖ ≤ 2*K*‖z-x‖ := by
    have htri : ‖k‖ ≤ ‖B.symm (z-x)‖ + ‖B.symm ((z-x)-B k)‖ := by
      conv_lhs => rw [hinv]
      exact norm_sub_le _ _
    have h1 := (B.symm : E →L[ℝ] E).le_opNorm (z-x)
    have h2 := (B.symm : E →L[ℝ] E).le_opNorm ((z-x)-B k)
    have h1' : ‖B.symm (z-x)‖ ≤ K*‖z-x‖ := h1.trans
      (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
    have h2' : ‖B.symm ((z-x)-B k)‖ ≤ K*eta*‖k‖ := by
      calc
        ‖B.symm ((z-x)-B k)‖ ≤ K*‖(z-x)-B k‖ := h2.trans
          (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
        _ ≤ K*(eta*‖k‖) := mul_le_mul_of_nonneg_left hres hK.le
        _ = K*eta*‖k‖ := by ring
    have h3 := mul_le_mul_of_nonneg_right heta1 (norm_nonneg k)
    nlinarith
  have heq : p-p0-((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x) =
      - B.symm ((z-x)-B k) := by
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, map_sub, B.symm_apply_apply]
    rw [hk]
    abel
  change ‖p-p0-((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x)‖ ≤ _
  rw [heq,norm_neg]
  calc
    ‖B.symm ((z-x)-B k)‖ ≤ K*‖(z-x)-B k‖ :=
      ((B.symm : E →L[ℝ] E).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
    _ ≤ K*(eta*‖k‖) := mul_le_mul_of_nonneg_left hres hK.le
    _ ≤ K*(eta*(2*K*‖z-x‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hknorm heta.le) hK.le
    _ = (2*K^2*eta)*‖z-x‖ := by ring
    _ ≤ eps*‖z-x‖ := mul_le_mul_of_nonneg_right heta2 (norm_nonneg _)

end ConvexProximal
end WeakMTWTransport

end

end OAI
