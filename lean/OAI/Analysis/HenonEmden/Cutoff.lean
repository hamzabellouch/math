import OAI.Analysis.HenonEmden.SphereCaps

namespace OAI

universe uE

section Cutoff

open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HenonLaneEmden.Cutoff

/-- The positive-part powers used by the compact cutoff. -/
def posPow (k : ℕ) (r : ℝ) : ℝ := (max r 0)^k
lemma continuous_posPow (k : ℕ) : Continuous (posPow k) := by unfold posPow; fun_prop
lemma hasDerivAt_posPow {k : ℕ} (hk : 2 ≤ k) (r : ℝ) :
    HasDerivAt (posPow k) ((k:ℝ)*(max r 0)^(k-1)) r := by
  rcases lt_trichotomy r 0 with hr|rfl|hr
  · have he : posPow k =ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds hr] with t ht
      simp [posPow,max_eq_right ht.le,show k ≠ 0 by omega]
    simpa [max_eq_right hr.le,show k-1 ≠ 0 by omega] using
      (hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq he
  · have hleft : HasDerivWithinAt (posPow k) 0 (Iic (0:ℝ)) 0 := by
      apply (hasDerivWithinAt_const 0 (Iic (0:ℝ)) (0:ℝ)).congr
      · intro t ht; simp [posPow,max_eq_right (mem_Iic.mp ht),show k ≠ 0 by omega]
      · simp [posPow,show k ≠ 0 by omega]
    have hright : HasDerivWithinAt (posPow k) 0 (Ici (0:ℝ)) 0 := by
      have hp : HasDerivWithinAt (fun t : ℝ => t^k) 0 (Ici (0:ℝ)) 0 := by
        simpa [show k-1 ≠ 0 by omega] using (hasDerivAt_pow k (0:ℝ)).hasDerivWithinAt (s := Ici (0:ℝ))
      apply hp.congr
      · intro t ht; simp [posPow,max_eq_left (mem_Ici.mp ht)]
      · simp [posPow]
    have hh := hleft.union hright
    rw [Iic_union_Ici,hasDerivWithinAt_univ] at hh
    simpa [show k-1 ≠ 0 by omega] using hh
  · have he : posPow k =ᶠ[𝓝 r] (fun t => t^k) := by
      filter_upwards [eventually_gt_nhds hr] with t ht
      simp [posPow,max_eq_left ht.le]
    simpa [max_eq_left hr.le] using (hasDerivAt_pow k r).congr_of_eventuallyEq he

def m (n : ℕ) := n+3
def k (n : ℕ) := n*(m n+1)
def N (n : ℕ) := k n+n+2
lemma N_ge_two (n : ℕ) : 2 ≤ N n := by unfold N; omega
lemma N_ge_three {n : ℕ} (hn : 1 ≤ n) : 3 ≤ N n := by unfold N; omega

def gapProfile (r : ℝ) : ℝ := min 1 (max (2-r) 0)
def baseProfile (r : ℝ) : ℝ := max (1-posPow 3 (r-1)) 0
def etaProfile (n : ℕ) (r : ℝ) : ℝ := posPow (N n) (1-posPow 3 (r-1))
def derivativeProfile (n : ℕ) (r : ℝ) : ℝ :=
  -(3*(N n:ℝ)*(max (r-1) 0)^2*(baseProfile r)^(N n-1))
def wProfile (n : ℕ) (r : ℝ) : ℝ := -r*derivativeProfile n r

lemma continuous_gapProfile : Continuous gapProfile := by unfold gapProfile; fun_prop
lemma continuous_baseProfile : Continuous baseProfile := by unfold baseProfile posPow; fun_prop
lemma continuous_etaProfile (n : ℕ) : Continuous (etaProfile n) := by
  unfold etaProfile posPow; fun_prop
lemma continuous_derivativeProfile (n : ℕ) : Continuous (derivativeProfile n) := by
  unfold derivativeProfile baseProfile posPow; fun_prop
lemma continuous_wProfile (n : ℕ) : Continuous (wProfile n) := by
  unfold wProfile; exact continuous_id.neg.mul (continuous_derivativeProfile n)

lemma hasDerivAt_etaProfile (n : ℕ) (r : ℝ) :
    HasDerivAt (etaProfile n) (derivativeProfile n r) r := by
  have h1 := (hasDerivAt_posPow (by omega : 2 ≤ 3) (r-1)).comp r
    ((hasDerivAt_id r).sub_const 1)
  have h2 := (hasDerivAt_posPow (N_ge_two n) (1-posPow 3 (r-1))).comp r (h1.const_sub 1)
  apply h2.congr_deriv
  simp only [derivativeProfile,baseProfile,Nat.cast_ofNat,mul_one,Nat.reduceSub]
  ring

lemma gapProfile_nonneg (r : ℝ) : 0 ≤ gapProfile r :=
  le_min (by norm_num) (le_max_right _ _)
lemma gapProfile_le_one (r : ℝ) : gapProfile r ≤ 1 := min_le_left _ _
lemma baseProfile_nonneg (r : ℝ) : 0 ≤ baseProfile r := le_max_right _ _
lemma baseProfile_le_one (r : ℝ) : baseProfile r ≤ 1 := by
  apply max_le _ (by norm_num)
  have hp : 0 ≤ posPow 3 (r-1) := pow_nonneg (le_max_right _ _) _
  linarith
lemma gapProfile_inner {r : ℝ} (hr : r ≤ 1) : gapProfile r = 1 := by
  unfold gapProfile
  rw [min_eq_left]
  exact le_trans (by linarith) (le_max_left _ _)
lemma baseProfile_inner {r : ℝ} (hr : r ≤ 1) : baseProfile r = 1 := by
  simp [baseProfile,posPow,max_eq_right (by linarith : r-1 ≤ 0)]
lemma gapProfile_outer {r : ℝ} (hr : 2 ≤ r) : gapProfile r = 0 := by
  simp [gapProfile,max_eq_right (by linarith : 2-r ≤ 0)]
lemma baseProfile_outer {r : ℝ} (hr : 2 ≤ r) : baseProfile r = 0 := by
  have hp : 1 ≤ (max (r-1) 0)^3 := one_le_pow₀ (by linarith [le_max_left (r-1) 0])
  exact max_eq_right (by dsimp [posPow]; linarith)
lemma gapProfile_middle {r : ℝ} (hr : 1 ≤ r) (hr' : r ≤ 2) : gapProfile r = 2-r := by
  unfold gapProfile
  rw [max_eq_left (by linarith),min_eq_right (by linarith)]
lemma baseProfile_middle {r : ℝ} (hr : 1 ≤ r) (hr' : r ≤ 2) :
    baseProfile r = (2-r)*(1+(r-1)+(r-1)^2) := by
  have hp : (r-1)^3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  unfold baseProfile posPow
  rw [max_eq_left (by linarith : 0 ≤ r-1),max_eq_left (by linarith)]
  ring
lemma base_gap_bounds (r : ℝ) : gapProfile r ≤ baseProfile r ∧ baseProfile r ≤ 3*gapProfile r := by
  by_cases h1 : r ≤ 1
  · rw [gapProfile_inner h1,baseProfile_inner h1]; norm_num
  by_cases h2 : 2 ≤ r
  · rw [gapProfile_outer h2,baseProfile_outer h2]; norm_num
  have hr : 1 ≤ r := (not_le.mp h1).le
  have hr' : r ≤ 2 := (not_le.mp h2).le
  rw [gapProfile_middle hr hr',baseProfile_middle hr hr']
  have hs : (r-1)^2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-r) (by positivity : 0 ≤ (r-1)^2)]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-r) (by linarith : 0 ≤ 2-((r-1)+(r-1)^2))]
lemma etaProfile_eq_power (n : ℕ) (r : ℝ) : etaProfile n r = (baseProfile r)^(N n) := rfl
lemma etaProfile_bounds (n : ℕ) (r : ℝ) :
    (gapProfile r)^(N n) ≤ etaProfile n r ∧ etaProfile n r ≤ 3^(N n)*(gapProfile r)^(N n) := by
  rw [etaProfile_eq_power,← mul_pow]
  exact ⟨pow_le_pow_left₀ (gapProfile_nonneg r) (base_gap_bounds r).1 _,
    pow_le_pow_left₀ (baseProfile_nonneg r) (base_gap_bounds r).2 _⟩
lemma derivativeProfile_inner (n : ℕ) {r : ℝ} (hr : r ≤ 1) : derivativeProfile n r = 0 := by
  simp [derivativeProfile,max_eq_right (by linarith : r-1 ≤ 0)]
lemma derivativeProfile_outer (n : ℕ) {r : ℝ} (hr : 2 ≤ r) : derivativeProfile n r = 0 := by
  simp [derivativeProfile,baseProfile_outer hr,show N n-1 ≠ 0 by have := N_ge_two n; omega]
lemma derivativeProfile_nonpos (n : ℕ) (r : ℝ) : derivativeProfile n r ≤ 0 := by
  have hb := baseProfile_nonneg r
  unfold derivativeProfile
  exact neg_nonpos.mpr (by positivity)
lemma wProfile_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ wProfile n r :=
  mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr) (derivativeProfile_nonpos n r)
lemma derivativeProfile_bound (n : ℕ) (r : ℝ) :
    |derivativeProfile n r| ≤ 3*(N n:ℝ)*3^(N n-1)*(gapProfile r)^(N n-1) := by
  have hb := baseProfile_nonneg r
  have hg := gapProfile_nonneg r
  by_cases h1 : r ≤ 1
  · rw [derivativeProfile_inner n h1,abs_zero]; positivity
  by_cases h2 : 2 ≤ r
  · rw [derivativeProfile_outer n h2,abs_zero]; positivity
  have hs : (max (r-1) 0)^2 ≤ 1 := by
    rw [max_eq_left (by linarith : 0 ≤ r-1)]
    exact pow_le_one₀ (by linarith) (by linarith)
  rw [abs_of_nonpos (derivativeProfile_nonpos n r),derivativeProfile,neg_neg]
  calc
    _ ≤ 3*(N n:ℝ)*1*(3*gapProfile r)^(N n-1) := by
      gcongr
      exact (base_gap_bounds r).2
    _ = _ := by rw [mul_pow]; ring
lemma wProfile_bound (n : ℕ) {r : ℝ} (_hr : 0 ≤ r) :
    wProfile n r ≤ 6*(N n:ℝ)*3^(N n-1)*(gapProfile r)^(N n-1) := by
  have hg := gapProfile_nonneg r
  by_cases h2 : 2 ≤ r
  · simp only [wProfile,derivativeProfile_outer n h2,mul_zero]; positivity
  calc
    _ = r*|derivativeProfile n r| := by rw [abs_of_nonpos (derivativeProfile_nonpos n r),wProfile]; ring
    _ ≤ 2*(3*(N n:ℝ)*3^(N n-1)*(gapProfile r)^(N n-1)) := by
      gcongr
      · exact le_of_lt (not_le.mp h2)
      · exact derivativeProfile_bound n r
    _ = _ := by ring
lemma gap_wProfile_bound (n : ℕ) {r : ℝ} (_hr : 0 ≤ r) :
    gapProfile r*wProfile n r ≤ 6*(N n:ℝ)*etaProfile n r := by
  have hb := baseProfile_nonneg r
  have hg := gapProfile_nonneg r
  have hη : 0 ≤ etaProfile n r := pow_nonneg hb _
  by_cases h1 : r ≤ 1
  · simp only [wProfile,derivativeProfile_inner n h1,mul_zero]; positivity
  by_cases h2 : 2 ≤ r
  · simp only [wProfile,derivativeProfile_outer n h2,mul_zero]; positivity
  have hs : (max (r-1) 0)^2 ≤ 1 := by
    rw [max_eq_left (by linarith : 0 ≤ r-1)]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hN : N n-1+1 = N n := Nat.sub_add_cancel (by have := N_ge_two n; omega)
  calc
    _ = 3*(N n:ℝ)*r*(max (r-1) 0)^2*(gapProfile r*(baseProfile r)^(N n-1)) := by
      unfold wProfile derivativeProfile; ring
    _ ≤ 3*(N n:ℝ)*2*1*(baseProfile r*(baseProfile r)^(N n-1)) := by
      gcongr
      · exact le_of_lt (not_le.mp h2)
      · exact (base_gap_bounds r).1
    _ = _ := by
      have hpow : (baseProfile r)^(N n) = (baseProfile r)^(N n-1)*baseProfile r := by
        nth_rw 1 [← hN]; rw [pow_succ]
      rw [etaProfile_eq_power,hpow]; ring

def secondProfile (n : ℕ) (r : ℝ) : ℝ :=
  -6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1) +
    9*(N n:ℝ)*(N n-1)*((max (r-1) 0)^4)*(baseProfile r)^(N n-2)

lemma continuous_secondProfile (n : ℕ) : Continuous (secondProfile n) := by
  unfold secondProfile baseProfile posPow; fun_prop

lemma hasDerivAt_derivativeProfile {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (derivativeProfile n) (secondProfile n r) r := by
  have hN := N_ge_three hn
  have h1 := (hasDerivAt_posPow (by omega : 2 ≤ 3) (r-1)).comp r
    ((hasDerivAt_id r).sub_const 1)
  have h2 := (hasDerivAt_posPow (by omega : 2 ≤ N n-1) (1-posPow 3 (r-1))).comp r
    (h1.const_sub 1)
  have h3 := (hasDerivAt_posPow (by omega : 2 ≤ 2) (r-1)).comp r
    ((hasDerivAt_id r).sub_const 1)
  have hh := ((h3.const_mul (3*(N n:ℝ))).mul h2).neg
  apply hh.congr_deriv
  simp only [Function.comp_def, id_eq, posPow,Nat.cast_ofNat,mul_one,Nat.reduceSub,pow_one,
    show N n-1-1 = N n-2 by omega]
  rw [Nat.cast_sub (by omega : 1 ≤ N n)]
  simp only [Nat.cast_one,secondProfile,baseProfile,posPow]
  ring

lemma secondProfile_inner (n : ℕ) {r : ℝ} (hr : r ≤ 1) : secondProfile n r = 0 := by
  simp [secondProfile,max_eq_right (by linarith : r-1 ≤ 0)]
lemma secondProfile_outer {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 2 ≤ r) :
    secondProfile n r = 0 := by
  have := N_ge_three hn
  simp [secondProfile,baseProfile_outer hr,show N n-1 ≠ 0 by omega,
    show N n-2 ≠ 0 by omega]

lemma secondProfile_bound {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    |secondProfile n r| ≤ (6*(N n:ℝ)+9*(N n:ℝ)*(N n-1))*
      3^(N n-2)*(gapProfile r)^(N n-2) := by
  have hN := N_ge_three hn
  have hn0 : (0:ℝ) ≤ N n-1 := by
    have : (3:ℝ) ≤ N n := by exact_mod_cast hN
    linarith
  have hb := baseProfile_nonneg r
  have hg := gapProfile_nonneg r
  by_cases h1 : r ≤ 1
  · rw [secondProfile_inner n h1,abs_zero]; positivity
  by_cases h2 : 2 ≤ r
  · rw [secondProfile_outer hn h2,abs_zero]; positivity
  have hs0 : 0 ≤ max (r-1) 0 := le_max_right _ _
  have hs1 : max (r-1) 0 ≤ 1 := by apply max_le <;> linarith
  have hs4 : (max (r-1) 0)^4 ≤ 1 := pow_le_one₀ hs0 hs1
  have hp := pow_le_pow_of_le_one hb (baseProfile_le_one r) (by omega : N n-2 ≤ N n-1)
  have hp' := pow_le_pow_left₀ hb (base_gap_bounds r).2 (N n-2)
  calc
    _ ≤ 6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1) +
        9*(N n:ℝ)*(N n-1)*(max (r-1) 0)^4*(baseProfile r)^(N n-2) := by
      unfold secondProfile
      calc
        _ ≤ |-6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1)| +
            |9*(N n:ℝ)*(N n-1)*(max (r-1) 0)^4*(baseProfile r)^(N n-2)| := abs_add_le _ _
        _ = _ := by
          rw [abs_of_nonpos (by
            have hp : 0 ≤ 6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1) := by positivity
            nlinarith),abs_of_nonneg (by positivity)]
          ring
    _ ≤ 6*(N n:ℝ)*1*((3*gapProfile r)^(N n-2)) +
        9*(N n:ℝ)*(N n-1)*1*((3*gapProfile r)^(N n-2)) := by
      gcongr
      exact hp.trans hp'
    _ = _ := by rw [mul_pow]; ring

lemma lipschitz_gapProfile : LipschitzWith 1 gapProfile := by
  have hh : LipschitzWith 1 (fun r : ℝ => 2-r) := by
    apply LipschitzWith.of_dist_le_mul
    intro r s
    simp only [NNReal.coe_one,one_mul,Real.dist_eq]
    rw [show (2-r)-(2-s) = -(r-s) by ring,abs_neg]
  exact (hh.max_const 0).const_min 1

lemma gapProfile_oscillation (r s : ℝ) : |gapProfile r-gapProfile s| ≤ |r-s| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using lipschitz_gapProfile.dist_le_mul r s

def derivativeConstant (n : ℕ) : ℝ := 3*(N n:ℝ)*3^(N n-1)
def secondConstant (n : ℕ) : ℝ := (6*(N n:ℝ)+9*(N n:ℝ)*(N n-1))*3^(N n-2)
def wDerivativeConstant (n : ℕ) : ℝ := derivativeConstant n+2*secondConstant n

def wDerivativeProfile (n : ℕ) (r : ℝ) : ℝ := -derivativeProfile n r-r*secondProfile n r

lemma hasDerivAt_wProfile {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (wProfile n) (wDerivativeProfile n r) r := by
  exact ((hasDerivAt_id r).neg.mul (hasDerivAt_derivativeProfile hn r)).congr_deriv (by
    simp only [wDerivativeProfile,Pi.neg_apply,id_eq]; ring)

lemma constants_nonneg (n : ℕ) : 0 ≤ derivativeConstant n ∧ 0 ≤ secondConstant n ∧ 0 ≤ wDerivativeConstant n := by
  have hn : (0:ℝ) ≤ N n-1 := by
    have : (2:ℝ) ≤ N n := by exact_mod_cast N_ge_two n
    linarith
  dsimp [derivativeConstant,secondConstant,wDerivativeConstant]
  constructor
  · positivity
  constructor <;> positivity

lemma wDerivativeProfile_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    |wDerivativeProfile n r| ≤ wDerivativeConstant n*(gapProfile r)^(N n-2) := by
  have hN := N_ge_three hn
  have hc := constants_nonneg n
  have hg := gapProfile_nonneg r
  by_cases h2 : 2 ≤ r
  · simp only [wDerivativeProfile,derivativeProfile_outer n h2,secondProfile_outer hn h2,
      neg_zero,mul_zero,sub_zero,abs_zero]
    exact mul_nonneg hc.2.2 (pow_nonneg hg _)
  have hp := pow_le_pow_of_le_one hg (gapProfile_le_one r) (by omega : N n-2 ≤ N n-1)
  calc
    _ ≤ |derivativeProfile n r|+r*|secondProfile n r| := by
      unfold wDerivativeProfile
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hr] using abs_sub_le (-derivativeProfile n r) 0 (r*secondProfile n r)
    _ ≤ derivativeConstant n*(gapProfile r)^(N n-2)+
        2*(secondConstant n*(gapProfile r)^(N n-2)) := by
      apply add_le_add
      · exact (derivativeProfile_bound n r).trans (mul_le_mul_of_nonneg_left hp hc.1)
      · apply mul_le_mul (by linarith) (secondProfile_bound hn r) (abs_nonneg _) (by norm_num)
    _ = _ := by unfold wDerivativeConstant; ring

lemma wProfile_oscillation {n : ℕ} (hn : 1 ≤ n) {r s D : ℝ} (_hD : 0 ≤ D)
    (hseg : ∀ t ∈ uIcc r s, 0 ≤ t ∧ gapProfile t ≤ D) :
    |wProfile n s-wProfile n r| ≤ wDerivativeConstant n*D^(N n-2)*|s-r| := by
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_wProfile hn t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖wDerivativeProfile n t‖ ≤ wDerivativeConstant n*D^(N n-2) from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (wDerivativeProfile_bound hn (hseg t ht).1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg t) (hseg t ht).2 _) (constants_nonneg n).2.2))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def d (x : E) : ℝ := gapProfile ‖x‖
def eta (n : ℕ) (x : E) : ℝ := etaProfile n ‖x‖
def w (n : ℕ) (x : E) : ℝ := -(fderiv ℝ (eta n : E → ℝ) x x)
def X (n : ℕ) (x : E) : E := eta n x • x

omit [InnerProductSpace ℝ E] in
lemma continuous_d : Continuous (d : E → ℝ) := continuous_gapProfile.comp continuous_norm
omit [InnerProductSpace ℝ E] in
lemma continuous_eta (n : ℕ) : Continuous (eta n : E → ℝ) :=
  (continuous_etaProfile n).comp continuous_norm
omit [InnerProductSpace ℝ E] in
lemma eta_eq_one {n : ℕ} {x : E} (hx : ‖x‖ ≤ 1) : eta n x = 1 := by
  simp [eta,etaProfile,posPow,max_eq_right (by linarith : ‖x‖-1 ≤ 0)]
omit [InnerProductSpace ℝ E] in
lemma eta_eq_zero {n : ℕ} {x : E} (hx : 2 ≤ ‖x‖) : eta n x = 0 := by
  have hs : 1 ≤ (max (‖x‖-1) 0)^3 := by
    exact one_le_pow₀ (by linarith [le_max_left (‖x‖-1) 0])
  simp [eta,etaProfile,posPow,max_eq_right (by linarith : 1-(max (‖x‖-1) 0)^3 ≤ 0),
    show N n ≠ 0 by have := N_ge_two n; omega]

lemma hasFDerivAt_eta (n : ℕ) (x : E) :
    HasFDerivAt (eta n) ((derivativeProfile n ‖x‖/‖x‖) • innerSL ℝ x) x := by
  by_cases hx : x = 0
  · subst x
    have he : (eta n : E → ℝ) =ᶠ[𝓝 0] (fun _ => (1:ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with y hy
      exact eta_eq_one (mem_ball_zero_iff.mp hy).le
    simpa using (hasFDerivAt_const (1:ℝ) (0:E)).congr_of_eventuallyEq he
  · exact RadialCalculus.hasFDerivAt_profile_norm hx (hasDerivAt_etaProfile n ‖x‖)

lemma w_eq_profile (n : ℕ) (x : E) : w n x = wProfile n ‖x‖ := by
  rw [w,(hasFDerivAt_eta n x).fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,real_inner_self_eq_norm_sq,wProfile]
  by_cases hx : x = 0
  · subst x; simp
  · have hn := norm_ne_zero_iff.mpr hx
    field_simp

lemma continuous_w (n : ℕ) : Continuous (w n : E → ℝ) := by
  rw [show (w n : E → ℝ) = fun x => wProfile n ‖x‖ from funext (w_eq_profile n)]
  exact (continuous_wProfile n).comp continuous_norm

end HenonLaneEmden.Cutoff
end
end Cutoff

end OAI
