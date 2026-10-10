import OAI.MathematicalPhysics.RapidForcing.RawMachine
import OAI.MathematicalPhysics.RapidForcing.ScaledSyntax

namespace OAI

section
open scoped BigOperators Topology ENNReal ContDiff
open Set Filter
namespace RapidForcing
lemma addressCurl_jetBound (M : Machine) (w : M.Input) (k : ℕ) :
    ∀ n m : ℕ, ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (fun q : ℝ × Space =>
        movingCurl (addressPath M (M.scaleData w) n m) ((M.scaleData w).δ n)
          (q.1 - 1 - (n : ℝ)) q.2) p‖ ≤
        (EffectiveProfile.Formula.curlJetBound k : ℝ) * ((M.scaleData w).b n / (M.scaleData w).δ n ^ k) := by
  let C : ℝ := EffectiveProfile.Formula.curlJetBound k
  have hbound := EffectiveProfile.Formula.curlJetBound_spec k
  intro n m p
  let d := M.scaleData w
  let η := (d.δ n)⁻¹ • addressDisplacement M d n m
  let ξ := (d.b n)⁻¹ • addressDisplacement M d n m
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (scaledCurl η ξ)) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : (Space × Space) × (ℝ × Space) => scaledCurl p.1.1 p.1.2 p.2.1 p.2.2) ∘
        (fun q : ℝ × Space => ((η, ξ), q)))
    exact scaledCurl_joint_smooth.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun q : ℝ × Space => movingCurl (addressPath M d n m) (d.δ n)
      (q.1 - 1 - (n : ℝ)) q.2) = (fun q : ℝ × Space =>
      d.b n • scaledCurl η ξ (q.1 - (1 + (n : ℝ)))
        ((d.δ n)⁻¹ • (q.2 - addressCenter d n m))) := by
    funext q
    change movingCurl (fun s => addressCenter d n m + θ s • addressDisplacement M d n m)
      (d.δ n) _ _ = _
    rw [movingCurl_normalized _ _ (d.delta_pos n).ne' (d.b_pos n).ne']
    change d.b n • scaledCurl η ξ (q.1 - 1 - (n : ℝ)) _ = _
    congr 2
    ring
  rw [heq]
  have hparam := address_parameters_bound M w n m
  have hbnd := norm_iteratedFDeriv_scaled hsm (hbound η ξ hparam.1 hparam.2)
    ((one_le_inv₀ (d.delta_pos n)).mpr (d.delta_le_one n))
    (d.b n) (1 + (n : ℝ)) (addressCenter d n m) p
  convert hbnd using 1
  · rfl
  · change C * (d.b n / d.δ n ^ k) = _
    rw [abs_of_pos (d.b_pos n), inv_pow]
    ring

lemma stepVelocity_jetBound (M : Machine) (w : M.Input) (k : ℕ) :
    ∀ n : ℕ, ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖ ≤
        (2 * (EffectiveProfile.Formula.curlJetBound k : ℝ)) * ((M.scaleData w).b n / (M.scaleData w).δ n ^ (k + 1)) := by
  let C : ℝ := EffectiveProfile.Formula.curlJetBound k
  have hC : 0 ≤ C := by dsimp [C]; exact_mod_cast EffectiveProfile.Formula.curlJetBound_nonneg k
  have hb := addressCurl_jetBound M w k
  intro n p
  let d := M.scaleData w
  have hsm (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × Space => movingCurl (addressPath M d n m) (d.δ n)
        (q.1 - 1 - (n : ℝ)) q.2) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (movingCurl (addressPath M d n m) (d.δ n)) ∘
        (fun q : ℝ × Space => (q.1 - 1 - (n : ℝ), q.2)))
    exact (movingCurl_joint_smooth (addressPath_smooth M d n m) _).comp
      ((contDiff_fst.sub contDiff_const |>.sub contDiff_const).prodMk contDiff_snd)
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := k) (x := p)
    (u := Finset.range (d.D n + 1)) (fun m _ => (hsm m |>.of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt)
  change ‖iteratedFDeriv ℝ k (fun q : ℝ × Space => ∑ m ∈ Finset.range (d.D n + 1),
    movingCurl (addressPath M d n m) (d.δ n) (q.1 - 1 - (n : ℝ)) q.2) p‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ m ∈ Finset.range (d.D n + 1),
        ‖iteratedFDeriv ℝ k (fun q : ℝ × Space => movingCurl (addressPath M d n m)
          (d.δ n) (q.1 - 1 - (n : ℝ)) q.2) p‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (d.D n + 1), C * (d.b n / d.δ n ^ k) :=
      Finset.sum_le_sum (fun m _ => hb n m p)
    _ = ((d.D n : ℝ) + 1) * (C * (d.b n / d.δ n ^ k)) := by simp
    _ ≤ (2 * (d.δ n)⁻¹) * (C * (d.b n / d.δ n ^ k)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC
        (div_nonneg (d.b_pos n).le (pow_nonneg (d.delta_nonneg n) k)))
      have hD : (d.D n : ℝ) = (d.δ n)⁻¹ := by rw [d.delta_eq_inv_D, inv_inv]
      rw [hD]
      have hi := (one_le_inv₀ (d.delta_pos n)).mpr (d.delta_le_one n)
      linarith
    _ = (2 * C) * (d.b n / d.δ n ^ (k + 1)) := by rw [pow_succ]; field_simp

namespace ScaleData
variable (d : ScaleData)

lemma s_quadratic_lower (n : ℕ) : (n+4)*n+n ≤ d.s n := by
  have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul (n+2)
  have h' : 2 ^ (2*(n+2)) ≤ 2 ^ ((n+2)^2) :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have h'' : 2 ^ ((n+2)^2) ≤ d.s n := by
    unfold s
    exact Nat.le_mul_of_pos_left _ d.C_pos
  nlinarith

lemma coefficient_tail_bound (J p n : ℕ) (hn : max J p ≤ n) :
    ((n : ℝ)+4)^J * (d.b n / d.δ n^p) ≤ (1/2:ℝ)^n := by
  have hJ : J ≤ n := (le_max_left J p).trans hn
  have hp : p ≤ n := (le_max_right J p).trans hn
  have hexp : (n+4)*J+n ≤ d.s n :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hJ) _).trans (d.s_quadratic_lower n)
  have hpoly : ((n : ℝ)+4)^J ≤ (2:ℝ)^((n+4)*J) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (Nat.lt_two_pow_self (n := n+4)).le
  have hdelta : d.δ n ≤ (1/2:ℝ)^((n+4)*J+n) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  calc
    _ ≤ ((n : ℝ)+4)^J * d.δ n :=
      mul_le_mul_of_nonneg_left (d.scaled_b_le_delta n p (by omega)) (by positivity)
    _ ≤ (2:ℝ)^((n+4)*J) * (1/2:ℝ)^((n+4)*J+n) :=
      mul_le_mul hpoly hdelta (d.delta_nonneg n) (by positivity)
    _ = _ := by rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num

def coefficientBound (J p : ℕ) : ℚ :=
  (∑ n ∈ Finset.range (max J p), ((n:ℚ)+4)^J * (d.bQ n / d.δQ n^p)) + 2

lemma coefficientBound_nonneg (J p : ℕ) : 0 ≤ d.coefficientBound J p := by
  have h : ∀ n : ℕ, (0:ℚ) ≤ ((n:ℚ)+4)^J * (d.bQ n / d.δQ n^p) := by
    intro n
    have hd : (0:ℚ) ≤ d.δQ n := by unfold δQ; positivity
    have hb : (0:ℚ) ≤ d.bQ n := by unfold bQ δQ; positivity
    positivity
  unfold coefficientBound
  exact add_nonneg (Finset.sum_nonneg (fun n _ => h n)) (by norm_num)

lemma coefficient_sum_le (J p N : ℕ) :
    (∑ n ∈ Finset.range N, ((n:ℝ)+4)^J * (d.b n / d.δ n^p)) ≤
      (d.coefficientBound J p : ℝ) := by
  let a : ℕ → ℝ := fun n => ((n:ℝ)+4)^J * (d.b n / d.δ n^p)
  have ha : ∀ n, 0 ≤ a n := fun n => mul_nonneg (by positivity)
    (div_nonneg (d.b_pos n).le (pow_nonneg (d.delta_nonneg n) _))
  have hlo : (∑ n ∈ (Finset.range N).filter (fun n => n < max J p), a n) ≤
      ∑ n ∈ Finset.range (max J p), a n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    · exact fun n _ _ => ha n
  have hhi : (∑ n ∈ (Finset.range N).filter (fun n => ¬ n < max J p), a n) ≤ 2 := by
    apply (Finset.sum_le_sum (fun n hn => d.coefficient_tail_bound J p n
      (by have := (Finset.mem_filter.mp hn).2; omega))).trans
    apply le_trans _ (sum_geometric_two_le N)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  have h := add_le_add hlo hhi
  rw [Finset.sum_filter_add_sum_filter_not] at h
  simpa only [coefficientBound, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, ScaleData.cast_bQ, ScaleData.cast_deltaQ] using h

end ScaleData

open EffectiveProfile.Formula in
lemma loadingVelocity_jetBound (M : Machine) (w : M.Input) (k : ℕ) (p : ℝ × Space) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p‖ ≤
      (curlJetBound k : ℝ) := by
  let v := vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0
  have hv : ‖v‖ ≤ 2 := by
    have hy := initial_coordinate_mem M w
    have hcoord : ∀ i : Fin 3, |v i| ≤ 1 := by
      intro i
      fin_cases i <;> dsimp [v, vec]
      · norm_num
      · exact (abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩)
      · norm_num
    simpa only [mul_one] using norm_le_two_mul_of_coord_le zero_le_one hcoord
  have he : Function.uncurry (loadingVelocity M w) = Function.uncurry (scaledCurl v v) := by
    funext q
    have h := movingCurl_normalized (0:Space) v (δ := 1) (b := 1) (by norm_num) (by norm_num) q.1 q.2
    change movingCurl (fun s => θ s • v) 1 q.1 q.2 = scaledCurl v v q.1 q.2
    simpa only [zero_add, inv_one, one_smul, sub_zero] using h
  rw [he]
  exact curlJetBound_spec k v v hv hv p

open EffectiveProfile.Formula in
lemma loadingVelocity_weighted_jetBound (M : Machine) (w : M.Input) (J k : ℕ) (p : ℝ × Space) :
    (1+‖p‖)^J * ‖iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p‖ ≤
      4^J * (curlJetBound k : ℝ) := by
  by_cases hp : p ∈ tsupport (Function.uncurry (loadingVelocity M w))
  · have hs := loadingVelocity_joint_tsupport M w hp
    have hn : ‖p‖ ≤ 3 := by
      change max ‖p.1‖ ‖p.2‖ ≤ 3
      apply max_le
      · rw [Real.norm_eq_abs, abs_of_nonneg hs.1.1]; linarith [hs.1.2]
      · exact norm_le_three_of_mem_K hs.2
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) J)
      (loadingVelocity_jetBound M w k p) (norm_nonneg _) (by positivity)
  · have hz : iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_iteratedFDeriv_subset k h))
    rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (by exact_mod_cast curlJetBound_nonneg k)

open EffectiveProfile.Formula in
lemma stepVelocity_weighted_jetBound (M : Machine) (w : M.Input) (J k n : ℕ) (p : ℝ × Space) :
    (1+‖p‖)^J * ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖ ≤
      (2 * (curlJetBound k : ℝ)) * (((n:ℝ)+4)^J *
        ((M.scaleData w).b n / (M.scaleData w).δ n^(k+1))) := by
  by_cases hp : p ∈ tsupport (Function.uncurry (stepVelocity M w n))
  · have hn := norm_le_slot (stepVelocity_joint_tsupport M w n hp)
    calc
      _ ≤ ((n:ℝ)+4)^J * ((2 * (curlJetBound k : ℝ)) *
          ((M.scaleData w).b n / (M.scaleData w).δ n^(k+1))) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) (stepVelocity_jetBound M w k n p)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_iteratedFDeriv_subset k h))
    rw [hz, norm_zero, mul_zero]
    have hC : (0:ℝ) ≤ curlJetBound k := by exact_mod_cast curlJetBound_nonneg k
    have hd := (M.scaleData w).delta_nonneg n
    have hb := (M.scaleData w).b_pos n
    positivity

def velocityJetBound (d : ScaleData) (J k : ℕ) : ℚ :=
  EffectiveProfile.Formula.curlJetBound k * (4^J + 2*d.coefficientBound J (k+1))

lemma velocityJetBound_nonneg (d : ScaleData) (J k : ℕ) : 0 ≤ velocityJetBound d J k :=
  mul_nonneg (EffectiveProfile.Formula.curlJetBound_nonneg k)
    (add_nonneg (by positivity) (mul_nonneg (by norm_num) (d.coefficientBound_nonneg J (k+1))))

lemma addressedVelocity_weighted_jetBound (M : Machine) (w : M.Input) (J k : ℕ) (p : ℝ × Space) :
    (1+‖p‖)^J * ‖iteratedFDeriv ℝ k (Function.uncurry (addressedVelocity M w)) p‖ ≤
      (velocityJetBound (M.scaleData w) J k : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt p.1
  have he : Function.uncurry (addressedVelocity M w) =ᶠ[𝓝 p]
      fun q : ℝ × Space => loadingVelocity M w q.1 q.2 +
        ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2 := by
    have hopen : IsOpen {q : ℝ × Space | q.1 < (N : ℝ) + 1} :=
      isOpen_lt continuous_fst continuous_const
    have ho : ∀ᶠ q : ℝ × Space in 𝓝 p, q.1 < (N : ℝ) + 1 :=
      hopen.mem_nhds (by change p.1 < (N : ℝ) + 1; linarith)
    filter_upwards [ho] with q hq
    simpa only [Function.uncurry, Pi.add_apply, Finset.sum_apply] using
      congrFun (addressedVelocity_eq_finite M w N hq) q.2
  have hk := finite_order k
  have hload : ContDiffAt ℝ k (Function.uncurry (loadingVelocity M w)) p :=
    ((loadingVelocity_smooth M w).of_le hk).contDiffAt
  have hstep (n : ℕ) : ContDiffAt ℝ k (Function.uncurry (stepVelocity M w n)) p :=
    ((stepVelocity_smooth M w n).of_le hk).contDiffAt
  have hsplit : iteratedFDeriv ℝ k
      (fun q : ℝ × Space => loadingVelocity M w q.1 q.2 +
        ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2) p =
      iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p +
        ∑ n ∈ Finset.range N,
          iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p := by
    calc
      _ = iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p +
          iteratedFDeriv ℝ k (fun q : ℝ × Space =>
            ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2) p :=
        fun_iteratedFDeriv_add_apply hload (ContDiffAt.sum (s := Finset.range N) (fun n _ => hstep n))
      _ = _ := congrArg (_ + ·) (iteratedFDeriv_fun_sum_apply (fun n _ => hstep n))
  let C : ℝ := EffectiveProfile.Formula.curlJetBound k
  have hC : 0 ≤ C := by dsimp [C]; exact_mod_cast EffectiveProfile.Formula.curlJetBound_nonneg k
  let d := M.scaleData w
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds, hsplit]
  calc
    _ ≤ (1+‖p‖)^J * (‖iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p‖ +
        ∑ n ∈ Finset.range N, ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = (1+‖p‖)^J * ‖iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p‖ +
        ∑ n ∈ Finset.range N, (1+‖p‖)^J *
          ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖ := by
      rw [mul_add, Finset.mul_sum]
    _ ≤ 4^J*C + ∑ n ∈ Finset.range N, 2*C * (((n:ℝ)+4)^J * (d.b n / d.δ n^(k+1))) :=
      add_le_add (loadingVelocity_weighted_jetBound M w J k p)
        (Finset.sum_le_sum (fun n _ => stepVelocity_weighted_jetBound M w J k n p))
    _ = 4^J*C + 2*C * ∑ n ∈ Finset.range N, ((n:ℝ)+4)^J * (d.b n / d.δ n^(k+1)) := by
      rw [Finset.mul_sum]
    _ ≤ 4^J*C + 2*C * (d.coefficientBound J (k+1) : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (d.coefficient_sum_le J (k+1) N) (by positivity))
    _ = _ := by simp only [velocityJetBound, Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat]; dsimp [C,d]; ring

end RapidForcing

end

end OAI
