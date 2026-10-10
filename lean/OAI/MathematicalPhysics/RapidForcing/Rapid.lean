import OAI.MathematicalPhysics.RapidForcing.Detector

namespace OAI


open scoped BigOperators ENNReal Topology
open Set MeasureTheory

namespace RapidForcing

section UniformBounds
variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_iteratedFDeriv_slice_le {f : P × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : P) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f (a, y)) x‖ ≤
      ‖iteratedFDeriv ℝ k f (a, x)‖ := by
  let L := ContinuousLinearMap.inr ℝ P E
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro y
    simp [L])
  have hf' : ContDiff ℝ (⊤ : ℕ∞) (fun z : P × E => f (z + (a, 0))) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hd := L.iteratedFDeriv_comp_right hf' x (i := k) (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hfun : (fun y => f (a, y)) = (fun z : P × E => f (z + (a, 0))) ∘ L := by
    ext y
    simp [L]
  rw [hfun, hd, iteratedFDeriv_comp_add_right]
  have hb := (iteratedFDeriv ℝ k f (L x + (a, 0))).norm_compContinuousLinearMap_le
    (fun _ : Fin k => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x + (a, 0))‖ * ‖L‖ ^ k := hb
    _ ≤ ‖iteratedFDeriv ℝ k f (L x + (a, 0))‖ * 1 :=
      mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_left₀ (norm_nonneg L) hL k)
        (norm_nonneg _)
    _ = _ := by simp [L]

lemma uniform_derivative_bound {f : P × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {A : Set P} {B : Set E}
    (hA : IsCompact A) (hB : IsCompact B)
    (hs : ∀ a ∈ A, tsupport (fun x => f (a, x)) ⊆ B) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ A, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => f (a, y)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hA.prod hB).exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (m := k) (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).continuousOn)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro a ha x
  by_cases hx : x ∈ B
  · exact (norm_iteratedFDeriv_slice_le hf a x k).trans ((hC (a, x) ⟨ha, hx⟩).trans
      (le_max_right _ _))
  · have hz : iteratedFDeriv ℝ k (fun y => f (a, y)) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hs a ha
        (tsupport_iteratedFDeriv_subset k h)))
    rw [hz, norm_zero]
    exact le_max_left _ _
end UniformBounds

noncomputable def scaledCurl (η ξ : Space) : Field Space := fun σ y =>
  curl (fun z => ζ (z - θ σ • η) •
    ((1 / 2 : ℝ) • cross (deriv θ σ • ξ) (z - θ σ • η))) y

lemma scaledCurl_joint_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : (Space × Space) × (ℝ × Space) => scaledCurl p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hθ := theta_smooth
  have hdθ : ContDiff ℝ (⊤ : ℕ∞) (deriv θ) :=
    (contDiff_infty_iff_deriv.mp theta_smooth).2
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ((Space × Space) × (ℝ × Space)) × Space =>
        ζ (p.2 - θ p.1.2.1 • p.1.1.1) •
          ((1 / 2 : ℝ) • cross (deriv θ p.1.2.1 • p.1.1.2)
            (p.2 - θ p.1.2.1 • p.1.1.1))) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i <;> dsimp [cross, vec] <;> unfold ζ <;> fun_prop (disch := assumption)
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Space × Space) × (ℝ × Space) =>
        fderiv ℝ (fun z => ζ (z - θ p.2.1 • p.1.1) •
          ((1 / 2 : ℝ) • cross (deriv θ p.2.1 • p.1.2) (z - θ p.2.1 • p.1.1))) p.2.2) :=
    h.fderiv (contDiff_snd.snd) (by simp)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [scaledCurl, curl, vec] <;> fun_prop

lemma deriv_theta_left {σ : ℝ} (hσ : σ < 1 / 4) : deriv θ σ = 0 := by
  have he : θ =ᶠ[𝓝 σ] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hσ] with s hs
    exact theta_zero hs.le
  simpa using he.deriv_eq

lemma deriv_theta_right {σ : ℝ} (hσ : 3 / 4 < σ) : deriv θ σ = 0 := by
  have he : θ =ᶠ[𝓝 σ] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds hσ] with s hs
    exact theta_one hs.le
  simpa using he.deriv_eq

lemma scaledCurl_eq_zero_of_deriv_theta (η ξ : Space) {σ : ℝ} (hσ : deriv θ σ = 0) :
    scaledCurl η ξ σ = 0 := by
  funext y
  have hc : ∀ z : Space, cross (0 : Space) z = 0 := by
    intro z
    ext i
    fin_cases i <;> simp [cross, vec]
  simp [scaledCurl, hσ, hc, curl, vec]

lemma norm_le_two_mul_of_coord_le {z : Space} {r : ℝ} (hr : 0 ≤ r)
    (hz : ∀ i : Fin 3, |z i| ≤ r) : ‖z‖ ≤ 2 * r := by
  have hs (i : Fin 3) : (z i) ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr (hz i)
  have hnorm : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 := by
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq z
  nlinarith [hs 0, hs 1, hs 2, norm_nonneg z, sq_nonneg r]

lemma scaledCurl_tsupport_subset (η ξ : Space) (hη : ‖η‖ ≤ 2) :
    tsupport (Function.uncurry (scaledCurl η ξ)) ⊆
      Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) 3 := by
  apply closure_minimal _ (isClosed_Icc.prod Metric.isClosed_closedBall)
  intro p hp
  have ht : p.1 ∈ Icc (0 : ℝ) 1 := by
    by_contra h
    have hz : scaledCurl η ξ p.1 = 0 := by
      have hor : p.1 < 0 ∨ 1 < p.1 := by
        by_cases hh : 0 ≤ p.1
        · exact Or.inr (lt_of_not_ge (fun hh' => h ⟨hh, hh'⟩))
        · exact Or.inl (lt_of_not_ge hh)
      rcases hor with h | h
      · exact scaledCurl_eq_zero_of_deriv_theta η ξ (deriv_theta_left (by linarith))
      · exact scaledCurl_eq_zero_of_deriv_theta η ξ (deriv_theta_right (by linarith))
    exact hp (congrFun hz p.2)
  refine ⟨ht, ?_⟩
  have hz : p.2 ∈ tsupport (fun z => ζ (z - θ p.1 • η) •
      ((1 / 2 : ℝ) • cross (deriv θ p.1 • ξ) (z - θ p.1 • η))) :=
    curl_tsupport_subset _ (subset_closure hp)
  have hs : tsupport (fun z => ζ (z - θ p.1 • η) •
      ((1 / 2 : ℝ) • cross (deriv θ p.1 • ξ) (z - θ p.1 • η))) ⊆
      supportBox (θ p.1 • η) (1 / 8) := by
    apply closure_minimal _ (supportBox_closed _ _)
    intro z hz i
    by_contra hi
    have hv := zeta_zero (i := i) (v := z - θ p.1 • η) (le_of_lt (not_le.mp hi))
    exact hz (by dsimp; rw [hv, zero_smul])
  have hc := hs hz
  have hn : ‖p.2 - θ p.1 • η‖ ≤ 1 := by
    have hcoord := norm_le_two_mul_of_coord_le (z := p.2 - θ p.1 • η) (by norm_num : (0 : ℝ) ≤ 1 / 8) (fun i => hc i)
    exact hcoord.trans (by norm_num)
  have hθη : ‖θ p.1 • η‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (theta_nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg η) (theta_le_one _)).trans hη
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖p.2‖ = ‖(p.2 - θ p.1 • η) + θ p.1 • η‖ := by rw [sub_add_cancel]
    _ ≤ ‖p.2 - θ p.1 • η‖ + ‖θ p.1 • η‖ := norm_add_le _ _
    _ ≤ 3 := by linarith

lemma scaledCurl_derivative_bound (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ η ξ : Space, ‖η‖ ≤ 2 → ‖ξ‖ ≤ 2 → ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (Function.uncurry (scaledCurl η ξ)) p‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_derivative_bound scaledCurl_joint_smooth
    ((isCompact_closedBall (0 : Space) 2).prod (isCompact_closedBall (0 : Space) 2))
    (isCompact_Icc.prod (isCompact_closedBall (0 : Space) 3))
    (fun a ha => scaledCurl_tsupport_subset a.1 a.2 (by simpa using ha.1)) k
  refine ⟨C, hC, ?_⟩
  intro η ξ hη hξ p
  exact hb (η, ξ) (by simpa using And.intro hη hξ) p

lemma cross_smul_left (r : ℝ) (a b : Space) : cross (r • a) b = r • cross a b := by
  ext i
  fin_cases i <;> dsimp [cross, vec] <;> ring

lemma cross_smul_right (r : ℝ) (a b : Space) : cross a (r • b) = r • cross a b := by
  ext i
  fin_cases i <;> dsimp [cross, vec] <;> ring

lemma curl_const_smul {V : Space → Space} (hV : Differentiable ℝ V) (r : ℝ) (x : Space) :
    curl (fun y => r • V y) x = r • curl V x := by
  have hd : fderiv ℝ (fun y => r • V y) x = r • fderiv ℝ V x :=
    fderiv_const_smul (hV x) r
  ext i
  fin_cases i <;> simp only [curl, hd, vec, smul_apply] <;>
    dsimp <;> ring

lemma curl_affine_scale {V : Space → Space} (hV : Differentiable ℝ V)
    (a : Space) (r : ℝ) (x : Space) :
    curl (fun y => V (r • (y - a))) x = r • curl V (r • (x - a)) := by
  have ha : HasFDerivAt (fun y : Space => r • (y - a))
      (r • ContinuousLinearMap.id ℝ Space) x :=
    ((hasFDerivAt_id x).sub_const a).const_smul r
  have hd : fderiv ℝ (fun y => V (r • (y - a))) x =
      (fderiv ℝ V (r • (x - a))).comp (r • ContinuousLinearMap.id ℝ Space) :=
    ((hV (r • (x - a))).hasFDerivAt.comp x ha).fderiv
  ext i
  fin_cases i <;> simp only [curl, hd, vec, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul] <;>
    dsimp <;> ring

lemma movingCurl_normalized (a v : Space) {δ b : ℝ} (hδ : δ ≠ 0) (hb : b ≠ 0)
    (σ : ℝ) (x : Space) :
    movingCurl (fun s => a + θ s • v) δ σ x =
      b • scaledCurl (δ⁻¹ • v) (b⁻¹ • v) σ (δ⁻¹ • (x - a)) := by
  let η := δ⁻¹ • v
  let ξ := b⁻¹ • v
  let V : Space → Space := fun z => ζ (z - θ σ • η) •
    ((1 / 2 : ℝ) • cross (deriv θ σ • ξ) (z - θ σ • η))
  have hθ := theta_smooth
  have hVsm : ContDiff ℝ (⊤ : ℕ∞) V := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i <;> dsimp [V, cross, vec] <;> unfold ζ <;> fun_prop
  have hV : Differentiable ℝ V := hVsm.differentiable (by simp)
  have hc : deriv (fun s => a + θ s • v) σ = deriv θ σ • v := by
    rw [deriv_const_add, deriv_smul_const]
    exact theta_smooth.differentiable (by simp) σ
  have hz (y : Space) : δ⁻¹ • (y - (a + θ σ • v)) = δ⁻¹ • (y - a) - θ σ • η := by
    dsimp [η]
    module
  have hz' (y : Space) : y - (a + θ σ • v) =
      δ • (δ⁻¹ • (y - a) - θ σ • η) := by
    rw [← hz, smul_inv_smul₀ hδ]
  have hv : deriv θ σ • v = b • (deriv θ σ • ξ) := by
    dsimp [ξ]
    rw [smul_comm (deriv θ σ), smul_inv_smul₀ hb]
  have hpot : (fun y => ζ (δ⁻¹ • (y - (a + θ σ • v))) •
      ((1 / 2 : ℝ) • cross (deriv (fun s => a + θ s • v) σ) (y - (a + θ σ • v)))) =
      (fun y => (b * δ) • V (δ⁻¹ • (y - a))) := by
    funext y
    rw [hc, hz, hv, hz' y, cross_smul_left, cross_smul_right]
    dsimp [V]
    module
  change curl _ x = _
  have hcomp : Differentiable ℝ (fun y => V (δ⁻¹ • (y - a))) :=
    hV.comp (((differentiable_id : Differentiable ℝ (fun y : Space => y)).sub_const a).const_smul δ⁻¹)
  rw [hpot, curl_const_smul hcomp, curl_affine_scale hV]
  change (b * δ) • (δ⁻¹ • _) = _
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hδ, mul_one]
  rfl

lemma address_parameters_bound (M : Machine) (w : M.Input) (n m : ℕ) :
    ‖((M.scaleData w).δ n)⁻¹ • addressDisplacement M (M.scaleData w) n m‖ ≤ 2 ∧
    ‖((M.scaleData w).b n)⁻¹ • addressDisplacement M (M.scaleData w) n m‖ ≤ 2 := by
  let d := M.scaleData w
  have hv := addressDisplacement_bound M w n m
  have hη (i : Fin 3) : |(d.δ n)⁻¹ * addressDisplacement M d n m i| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (d.delta_pos n))]
    exact (mul_le_mul_of_nonneg_left (hv i) (inv_nonneg.mpr (d.delta_nonneg n))).trans
      ((inv_mul_le_one₀ (d.delta_pos n)).mpr <| (d.b_lt_delta_div_eight n).le.trans
        (by linarith [d.delta_nonneg n]))
  have hξ (i : Fin 3) : |(d.b n)⁻¹ * addressDisplacement M d n m i| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (d.b_pos n))]
    exact (mul_le_mul_of_nonneg_left (hv i) (inv_nonneg.mpr (d.b_pos n).le)).trans_eq
      (inv_mul_cancel₀ (d.b_pos n).ne')
  constructor
  · simpa only [mul_one] using norm_le_two_mul_of_coord_le (r := 1) (by norm_num) hη
  · simpa only [mul_one] using norm_le_two_mul_of_coord_le (r := 1) (by norm_num) hξ

section ScaledBounds
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_scaled {g : ℝ × Space → E}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {k : ℕ} {C r : ℝ}
    (hC : ∀ p, ‖iteratedFDeriv ℝ k g p‖ ≤ C) (hr : 1 ≤ r)
    (b τ : ℝ) (a : Space) (p : ℝ × Space) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × Space =>
      b • g (q.1 - τ, r • (q.2 - a))) p‖ ≤ |b| * C * r ^ k := by
  let L : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
    (ContinuousLinearMap.fst ℝ ℝ Space).prod (r • ContinuousLinearMap.snd ℝ ℝ Space)
  have hL : ‖L‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro q
    change max ‖q.1‖ ‖r • q.2‖ ≤ r * ‖q‖
    apply max_le
    · exact (norm_fst_le q).trans (le_mul_of_one_le_left (norm_nonneg _) hr)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r)]
      exact mul_le_mul_of_nonneg_left (norm_snd_le q) (by linarith)
  have heq : (fun q : ℝ × Space => g (q.1 - τ, r • (q.2 - a))) =
      (fun q => (g ∘ L) (q - (τ, a))) := rfl
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Space =>
      g (q.1 - τ, r • (q.2 - a))) := by
    exact hg.comp ((contDiff_fst.sub contDiff_const).prodMk
      ((contDiff_snd.sub contDiff_const).const_smul r))
  rw [iteratedFDeriv_const_smul_apply' (hsm.of_le
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt, heq,
    iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hg _
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)), norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |b| * (‖iteratedFDeriv ℝ k g (L (p - (τ, a)))‖ * ‖L‖ ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using (iteratedFDeriv ℝ k g (L (p - (τ, a)))).norm_compContinuousLinearMap_le
        (fun _ : Fin k => L)
    _ ≤ |b| * (C * r ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg _) hL _)
        (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans (hC (0, 0)))
    _ = _ := by ring
end ScaledBounds

lemma addressCurl_derivative_bound (M : Machine) (w : M.Input) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (fun q : ℝ × Space =>
        movingCurl (addressPath M (M.scaleData w) n m) ((M.scaleData w).δ n)
          (q.1 - 1 - (n : ℝ)) q.2) p‖ ≤
        C * ((M.scaleData w).b n / (M.scaleData w).δ n ^ k) := by
  obtain ⟨C, hC, hbound⟩ := scaledCurl_derivative_bound k
  refine ⟨C, hC, ?_⟩
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

lemma stepVelocity_derivative_bound (M : Machine) (w : M.Input) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖ ≤
        C * ((M.scaleData w).b n / (M.scaleData w).δ n ^ (k + 1)) := by
  obtain ⟨C, hC, hb⟩ := addressCurl_derivative_bound M w k
  refine ⟨2 * C, by positivity, ?_⟩
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

end RapidForcing

end OAI
