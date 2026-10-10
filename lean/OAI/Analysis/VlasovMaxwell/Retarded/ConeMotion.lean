import Mathlib
import OAI.Analysis.VlasovMaxwell.Model

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

lemma dot_sub_right (a b c : Vec) : dot a (b - c) = dot a b - dot a c := by
  rw [dot_comm, dot_sub_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_eq_inner (a b : Vec) : dot a b = inner ℝ a b := by
  simp [dot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma dot_self (a : Vec) : dot a a = ‖a‖ ^ 2 := by
  rw [dot_eq_inner, real_inner_self_eq_norm_sq]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma velocity_self (v : Vec) : dot (velocity v) (velocity v) = 1 - (q v)⁻¹ ^ 2 := by
  rw [velocity, dot_smul_left, dot_smul_right, dot_self]
  have hq := q_sq v
  have hn := ne_of_gt (q_pos v)
  field_simp
  nlinarith

lemma cone_angle_identity (v n : Vec) (hn : ‖n‖ = 1) :
    2 * (1 - dot n (velocity v)) = ‖n - velocity v‖ ^ 2 + (q v)⁻¹ ^ 2 := by
  rw [norm_sub_sq_real, ← dot_eq_inner, hn, ← dot_self (velocity v), velocity_self]
  ring

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

def coneMotion (a u n : Vec) : Vec :=
  ((1 - dot n u) / (1 - dot n a)) • (a - n) + n - u

def signedPrimitive (a u n : Vec) : Vec :=
  u - ((1 - dot a u) / (1 - dot n a)) • n

lemma coneMotion_dot_source (a u n : Vec) (hD : 1 - dot n a ≠ 0) :
    dot (coneMotion a u n) u -
      (1 - dot n u) * ((1 - dot n u) / (1 - dot n a) - 1) -
      (1 - dot u u) = -(1 - dot a u) * (1 - dot n u) / (1 - dot n a) := by
  simp only [coneMotion, dot_sub_left, dot_add_left, dot_smul_left]
  field_simp
  ring

lemma coneMotion_receiver_identity (a u n : Vec) (hD : 1 - dot n a ≠ 0) :
    coneMotion a u n +
      (dot (coneMotion a u n) a / (1 - dot n a)) • n + signedPrimitive a u n =
    ((1 - dot n u) / (1 - dot n a)) •
      (a - ((1 - dot a a) / (1 - dot n a)) • n) := by
  ext i
  simp only [coneMotion, signedPrimitive, dot_sub_left, dot_add_left,
    dot_smul_left, dot_comm u a]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

def signedPrimitiveRate (a u n a' u' n' : Vec) : Vec :=
  u' - (((1 - dot a u) / (1 - dot n a)) • n' +
    ((-(dot a u' + dot a' u) * (1 - dot n a) +
        (1 - dot a u) * (dot n a' + dot n' a)) / (1 - dot n a) ^ 2) • n)

lemma hasDerivAt_signedPrimitive {a u n : ℝ → Vec} {a' u' n' : Vec} {s : ℝ}
    (ha : HasDerivAt a a' s) (hu : HasDerivAt u u' s) (hn : HasDerivAt n n' s)
    (hD : 1 - dot (n s) (a s) ≠ 0) :
    HasDerivAt (fun t => signedPrimitive (a t) (u t) (n t))
      (signedPrimitiveRate (a s) (u s) (n s) a' u' n') s := by
  have he := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_dot ha hu)
  have hden := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_dot hn ha)
  have h := hu.sub ((he.div hden hD).smul hn)
  convert h using 1 <;> try rfl
  · dsimp [signedPrimitiveRate]
    congr 3
    ring

def retardedPrimitive (r : ℝ) (a u n : Vec) : Vec :=
  (r * (1 - dot n u))⁻¹ • signedPrimitive a u n

def retardedPrimitiveRate (r : ℝ) (a u n : Vec) (r' : ℝ) (a' u' n' : Vec) : Vec :=
  (r * (1 - dot n u))⁻¹ • signedPrimitiveRate a u n a' u' n' +
  (-(r' * (1 - dot n u) - r * (dot n u' + dot n' u)) /
    (r * (1 - dot n u)) ^ 2) • signedPrimitive a u n

lemma hasDerivAt_retardedPrimitive {r : ℝ → ℝ} {a u n : ℝ → Vec}
    {r' : ℝ} {a' u' n' : Vec} {s : ℝ}
    (hr : HasDerivAt r r' s) (ha : HasDerivAt a a' s)
    (hu : HasDerivAt u u' s) (hn : HasDerivAt n n' s)
    (hr0 : r s ≠ 0) (hd : 1 - dot (n s) (u s) ≠ 0)
    (hD : 1 - dot (n s) (a s) ≠ 0) :
    HasDerivAt (fun t => retardedPrimitive (r t) (a t) (u t) (n t))
      (retardedPrimitiveRate (r s) (a s) (u s) (n s) r' a' u' n') s := by
  have hden := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_dot hn hu)
  have hinv := (hr.mul hden).inv (mul_ne_zero hr0 hd)
  have h := hinv.smul (hasDerivAt_signedPrimitive ha hu hn hD)
  convert h using 1 <;> try rfl
  · dsimp [retardedPrimitiveRate]
    congr 3
    ring

def coneTransform (a n b : Vec) : Vec := b + (dot a b / (1 - dot n a)) • n

lemma coneTransform_source (a u n : Vec)
    (hd : 1 - dot n u ≠ 0) (hD : 1 - dot n a ≠ 0) :
    coneTransform a n (((1 - dot n u)⁻¹) • (u - n)) =
      ((1 - dot n u)⁻¹) • signedPrimitive a u n := by
  ext i
  simp only [coneTransform, signedPrimitive, dot_smul_right, dot_sub_right,
    dot_comm a n, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

def sourceVelocityRate (u n u' : Vec) : Vec :=
  (1 - dot n u)⁻¹ • u' + (dot n u' / (1 - dot n u)^2) • (u - n)

def signedForceKernel (r : ℝ) (a u n u' : Vec) : Vec :=
  -(r⁻¹ • coneTransform a n (sourceVelocityRate u n u')) -
    ((1 - dot u u) / (r^2 * (1 - dot n u))) •
      coneTransform a n ((1 - dot n u)⁻¹ • (u - n))

lemma signed_force_identity (r : ℝ) (a u n u' aₜ : Vec)
    (hr : r ≠ 0) (hd : 1 - dot n u ≠ 0) (hD : 1 - dot n a ≠ 0) :
    signedForceKernel r a u n u' =
      -retardedPrimitiveRate r a u n
        ((1 - dot n u) / (1 - dot n a) - 1)
        (((1 - dot n u) / (1 - dot n a)) • aₜ) u' (r⁻¹ • coneMotion a u n) +
      ((1 - dot a u) / (r^2 * (1 - dot n a)^2)) •
        (((1 - dot a a) / (1 - dot n a)) • n - a) +
      (dot aₜ (signedPrimitive a u n) / (r * (1 - dot n a)^2)) • n := by
  ext i
  simp only [signedForceKernel, retardedPrimitiveRate, signedPrimitiveRate,
    sourceVelocityRate, coneTransform, signedPrimitive, coneMotion,
    dot_add_left, dot_sub_left, dot_smul_left, dot_add_right, dot_sub_right,
    dot_smul_right, dot_comm a n, dot_comm u a, dot_comm aₜ n, dot_comm aₜ u,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
  field_simp
  ring

lemma signed_force_identity_along_branch {r : ℝ → ℝ} {a u n : ℝ → Vec}
    {u' aₜ : Vec} {s : ℝ}
    (hr : HasDerivAt r ((1 - dot (n s) (u s)) / (1 - dot (n s) (a s)) - 1) s)
    (ha : HasDerivAt a (((1 - dot (n s) (u s)) / (1 - dot (n s) (a s))) • aₜ) s)
    (hu : HasDerivAt u u' s)
    (hn : HasDerivAt n ((r s)⁻¹ • coneMotion (a s) (u s) (n s)) s)
    (hr0 : r s ≠ 0) (hd : 1 - dot (n s) (u s) ≠ 0)
    (hD : 1 - dot (n s) (a s) ≠ 0) :
    signedForceKernel (r s) (a s) (u s) (n s) u' =
      -deriv (fun t => retardedPrimitive (r t) (a t) (u t) (n t)) s +
      ((1 - dot (a s) (u s)) / ((r s)^2 * (1 - dot (n s) (a s))^2)) •
        (((1 - dot (a s) (a s)) / (1 - dot (n s) (a s))) • n s - a s) +
      (dot aₜ (signedPrimitive (a s) (u s) (n s)) /
        ((r s) * (1 - dot (n s) (a s))^2)) • n s := by
  rw [(hasDerivAt_retardedPrimitive hr ha hu hn hr0 hd hD).deriv]
  exact signed_force_identity (r s) (a s) (u s) (n s) u' aₜ hr0 hd hD

lemma unsafe_selected_actual_margins
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z + c = 1) (hΔ : Δ = (α + b + y + H) / 100000)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hfar₁ : H ≤ 2*c → b < H/2 - α + Δ)
    (hfar₂ : 2*c < H → b < H - c - α + Δ)
    (hu₁ : 2*H/3 + z/6 - Δ/3 < b) :
    0 < z ∧ Δ < z/1000 ∧ 2*c < H ∧
      (496/1000 : ℝ)*z + 3*(α+c) < H ∧
      (35/10 : ℝ)*α + (15/10 : ℝ)*c + 2*y < (753/1000 : ℝ)*z ∧
      (500/751 : ℝ) < z ∧
      y < (377/1000 : ℝ)*z - (175/100 : ℝ)*α - (75/100 : ℝ)*c ∧
      (623/1000 : ℝ) < z-y ∧ (623/1000 : ℝ) < 1-α-y := by
  have hb : b < H - α + Δ := by
    by_cases hh : H ≤ 2*c
    · have h := hfar₁ hh
      linarith
    · have h := hfar₂ (lt_of_not_ge hh)
      linarith
  have hdsmall : 99995*Δ < 4*z := by linarith
  have hzpos : 0 < z := by
    by_contra hh
    have hz0 : z = 0 := le_antisymm (le_of_not_gt hh) hz
    subst z
    have hdneg : Δ < 0 := by linarith
    linarith
  have hd : Δ < z/1000 := by linarith
  have hh : 2*c < H := by
    by_contra hh
    have hf := hfar₁ (le_of_not_gt hh)
    linarith
  have hf := hfar₂ hh
  have hlow : (496/1000 : ℝ)*z + 3*(α+c) < H := by linarith
  have hm : (35/10 : ℝ)*α + (15/10 : ℝ)*c + 2*y < (753/1000 : ℝ)*z := by
    linarith
  refine ⟨hzpos, hd, hh, hlow, hm, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma unsafe_selected_improved_window
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z + c = 1) (hΔ : Δ = (α + b + y + H) / 100000)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hfar₁ : H ≤ 2*c → b < H/2 - α + Δ)
    (hfar₂ : 2*c < H → b < H - c - α + Δ)
    (hu₁ : 2*H/3 + z/6 - Δ/3 < b)
    (hu₂ : b < H + 2*y - z/2 + Δ)
    (hactual : b < H/2 - min α c + y + (2/1000 : ℝ)*z) :
    (9/10 : ℝ) < z ∧ (895/1000 : ℝ) < 1-α ∧
      (16/100 : ℝ)*max z (1-α) < y ∧ y < (49/100 : ℝ)*min z (1-α) := by
  obtain ⟨hzpos, hd, _, hlow, hm, _, hym, _, _⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have hm0 : 0 ≤ min α c := le_min hα hc
  have hHup : H < (81/100 : ℝ)*z := by linarith
  have hac : α+c < (105/1000 : ℝ)*z := by linarith
  have hz9 : (9/10 : ℝ) < z := by linarith
  have hp : (895/1000 : ℝ) < 1-α := by linarith
  have hy19 : (19/100 : ℝ)*z < y := by linarith
  refine ⟨hz9, hp, ?_, ?_⟩
  · rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 16/100), max_lt_iff]
    constructor <;> linarith
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 49/100), lt_min_iff]
    constructor <;> linarith

lemma unsafe_selected_improved_contradiction
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 < z) (hc : 0 ≤ c)
    (hsmall : Δ < z/1000)
    (hlow : (496/1000 : ℝ)*z + 3*(α+c) < H)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hu : 2*H/3 + z/6 - Δ/3 < b)
    (himproved : b < H/2 - min α c + (29/50 : ℝ)*y + Δ) : False := by
  have hm : 0 ≤ min α c := le_min hα hc
  linarith

lemma norm_velocity_le_margin (v : Vec) {Q : ℝ} (hQ : q v ≤ Q) :
    ‖velocity v‖ ≤ 1 - 1 / (2 * Q^2) := by
  have hq := q_pos v
  have hQ0 : 0 < Q := lt_of_lt_of_le hq hQ
  have hn := norm_velocity_lt_one v
  have hs : ‖velocity v‖^2 = 1 - (q v)⁻¹^2 := by
    rw [← dot_self, velocity_self]
  have hm : (q v)⁻¹^2 / 2 ≤ 1 - ‖velocity v‖ := by
    nlinarith [sq_nonneg (1 - ‖velocity v‖)]
  have hsq : 2 * (q v)^2 ≤ 2 * Q^2 := by nlinarith
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 2 * (q v)^2) hsq
  have he : (q v)⁻¹^2 / 2 = 1 / (2 * (q v)^2) := by ring
  rw [he] at hm
  linarith

def receiverConeFunction (X : ℝ → Vec) (s : ℝ) (y : Vec) (t : ℝ) : ℝ :=
  t - s - ‖X t - y‖

lemma receiverCone_growth {X : ℝ → Vec} {D : Set ℝ} {c : ℝ}
    (hX : ∀ t₁ ∈ D, ∀ t₂ ∈ D, ‖X t₂ - X t₁‖ ≤ c * |t₂-t₁|)
    (s : ℝ) (y : Vec) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D)
    (ht : t₁ ≤ t₂) :
    (1-c)*(t₂-t₁) ≤ receiverConeFunction X s y t₂ - receiverConeFunction X s y t₁ := by
  have hdist := norm_sub_le (X t₂ - y) (X t₁ - y)
  have hnorm : ‖X t₂-y‖ ≤ ‖X t₂-X t₁‖ + ‖X t₁-y‖ := by
    calc
      ‖X t₂-y‖ = ‖(X t₂-X t₁)+(X t₁-y)‖ := by congr 1; abel
      _ ≤ ‖X t₂-X t₁‖ + ‖X t₁-y‖ := norm_add_le _ _
  have h := hX t₁ h₁ t₂ h₂
  rw [abs_of_nonneg (sub_nonneg.2 ht)] at h
  dsimp [receiverConeFunction]
  nlinarith

lemma receiverCone_strictMonoOn {X : ℝ → Vec} {D : Set ℝ} {c : ℝ}
    (hc : c < 1)
    (hX : ∀ t₁ ∈ D, ∀ t₂ ∈ D, ‖X t₂-X t₁‖ ≤ c * |t₂-t₁|)
    (s : ℝ) (y : Vec) : StrictMonoOn (receiverConeFunction X s y) D := by
  intro t₁ h₁ t₂ h₂ ht
  have hg := receiverCone_growth hX s y h₁ h₂ ht.le
  have hp : 0 < (1-c)*(t₂-t₁) := mul_pos (sub_pos.2 hc) (sub_pos.2 ht)
  linarith

lemma exists_unique_receiver_time {X : ℝ → Vec} {s T c : ℝ} {y : Vec}
    (hsT : s ≤ T) (hc : c < 1) (hcont : ContinuousOn X (Icc s T))
    (hX : ∀ t₁ ∈ Icc s T, ∀ t₂ ∈ Icc s T, ‖X t₂-X t₁‖ ≤ c * |t₂-t₁|)
    (hcone : ‖X T-y‖ ≤ T-s) :
    ∃! t : ℝ, t ∈ Icc s T ∧ t-s = ‖X t-y‖ := by
  have hfun : ContinuousOn (receiverConeFunction X s y) (Icc s T) := by
    exact (continuousOn_id.sub continuousOn_const).sub
      ((hcont.sub continuousOn_const).norm)
  have hleft : receiverConeFunction X s y s ≤ 0 := by
    simp only [receiverConeFunction, sub_self, zero_sub, neg_nonpos]
    exact norm_nonneg _
  have hright : 0 ≤ receiverConeFunction X s y T := sub_nonneg.2 hcone
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hsT hfun ⟨hleft, hright⟩
  refine ⟨t, ⟨ht, ?_⟩, ?_⟩
  · dsimp [receiverConeFunction] at hzero
    linarith
  · intro t' ht'
    apply (receiverCone_strictMonoOn hc hX s y).injOn ht'.1 ht
    rw [hzero]
    dsimp [receiverConeFunction]
    linarith [ht'.2]

lemma hit_duration_bound {F : Set ℝ} {g : ℝ → ℝ} {c R : ℝ}
    (hc : 0 < c)
    (hgrowth : ∀ x ∈ F, ∀ y ∈ F, x ≤ y → c*(y-x) ≤ g y-g x)
    (hrange : ∀ x ∈ F, |g x| ≤ R) :
    volume F ≤ ENNReal.ofReal (2*R/c) := by
  apply (Real.volume_le_diam F).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hxg := abs_le.mp (hrange x hx)
  have hyg := abs_le.mp (hrange y hy)
  rcases le_total x y with hxy | hyx
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy)]
    have h := hgrowth x hx y hy hxy
    apply (le_div_iff₀ hc).2
    nlinarith
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hyx)]
    have h := hgrowth y hy x hx hyx
    apply (le_div_iff₀ hc).2
    nlinarith

lemma projected_hit_duration {X Y : ℝ → Vec} {a u : ℝ → Vec}
    {D F : Set ℝ} {e : Vec} {c R : ℝ}
    (hD : Convex ℝ D) (hFD : F ⊆ D) (hc : 0 < c)
    (hXc : ContinuousOn X D) (hYc : ContinuousOn Y D)
    (hX : ∀ s ∈ interior D, HasDerivAt X (a s) s)
    (hY : ∀ s ∈ interior D, HasDerivAt Y (u s) s)
    (hvel : ∀ s ∈ interior D, c ≤ dot e (u s-a s))
    (hsep : ∀ s ∈ F, |dot e (Y s-X s)| ≤ R) :
    volume F ≤ ENNReal.ofReal (2*R/c) := by
  apply hit_duration_bound hc _ hsep
  have hd : ∀ s ∈ interior D, HasDerivAt (fun t => dot e (Y t-X t))
      (dot e (u s-a s)) s := by
    intro s hs
    simpa [dot] using hasDerivAt_dot (hasDerivAt_const s e) ((hY s hs).sub (hX s hs))
  have hcont : ContinuousOn (fun t => dot e (Y t-X t)) D := by
    simp only [dot_eq_inner]
    exact continuousOn_const.inner (hYc.sub hXc)
  intro x hx y hy hxy
  apply hD.mul_sub_le_image_sub_of_le_deriv hcont
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd s hs).deriv]; exact hvel s hs) x (hFD hx) y (hFD hy) hxy

lemma scalar_clm_invertible (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : L.IsInvertible := by
  let K : ℝ →L[ℝ] ℝ := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := K)
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      K, smul_apply, smul_eq_mul]
    rw [← smul_eq_mul, L.map_smul]
    have hx : L x = x * L 1 := by simpa using L.map_smul x (1 : ℝ)
    rw [smul_eq_mul, hx]
    field_simp
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      K, smul_apply, smul_eq_mul]
    have hx : L x = x * L 1 := by simpa using L.map_smul x (1 : ℝ)
    rw [hx]
    field_simp

def squaredCone (X Y : ℝ → Vec) (z : ℝ × ℝ) : ℝ :=
  (z.2-z.1)^2 - ‖X z.2 - Y z.1‖^2

lemma contDiffAt_squaredCone {X Y : ℝ → Vec} {s t : ℝ}
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s) :
    ContDiffAt ℝ 1 (squaredCone X Y) (s,t) := by
  exact (contDiffAt_snd.sub contDiffAt_fst).pow 2 |>.sub
    (((hX.comp (s,t) contDiffAt_snd).sub
      (hY.comp (s,t) contDiffAt_fst)).norm_sq ℝ)

lemma hasDerivAt_squaredCone_receiver {X Y : ℝ → Vec} {a : Vec} {s t : ℝ}
    (hX : HasDerivAt X a t) :
    HasDerivAt (fun t' => squaredCone X Y (s,t'))
      (2*(t-s) - 2*dot (X t-Y s) a) t := by
  have h := ((hasDerivAt_id t).sub_const s).pow 2 |>.sub
    ((hX.sub_const (Y s)).norm_sq)
  convert h using 1 <;> try rfl
  simp [dot_eq_inner]

lemma receiver_partial_squaredCone {X Y : ℝ → Vec} {a : Vec} {s t : ℝ}
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s)
    (hXd : HasDerivAt X a t) :
    (fderiv ℝ (squaredCone X Y) (s,t) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ) 1 = 2*(t-s) - 2*dot (X t-Y s) a := by
  have hF := (contDiffAt_squaredCone hX hY).differentiableAt one_ne_zero
  have hpair : HasFDerivAt (fun t' : ℝ => (s,t'))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) t := by
    convert (hasFDerivAt_const s t).prodMk (hasFDerivAt_id t) using 1 <;> try rfl
  exact ((hF.hasFDerivAt.comp t hpair).hasDerivAt.unique
    (hasDerivAt_squaredCone_receiver hXd))

open scoped Topology

end RVM
end

end OAI
