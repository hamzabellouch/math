import OAI.MathematicalPhysics.RapidForcing.Collars

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma curl_joint_smooth {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => curl (v p.1) p.2) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Space) × Space => v p.1.1 p.2) :=
    hv.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space => fderiv ℝ (v p.1) p.2) :=
    h.fderiv contDiff_snd (by simp)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [curl, vec] <;> fun_prop

lemma movingCurl_joint_smooth {c : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (movingCurl c δ)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => curl (fun y =>
    ζ (δ⁻¹ • (y - c p.1)) • ((1 / 2 : ℝ) • cross (deriv c p.1) (y - c p.1))) p.2)
  apply curl_joint_smooth (v := fun σ y =>
    ζ (δ⁻¹ • (y - c σ)) • ((1 / 2 : ℝ) • cross (deriv c σ) (y - c σ)))
  have hdc : ContDiff ℝ (⊤ : ℕ∞) (deriv c) :=
    (contDiff_infty_iff_deriv.mp hc).2
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [cross, vec, Function.uncurry] <;> unfold ζ <;> fun_prop

noncomputable def stepVelocity (M : Machine) (w : M.Input) (n : ℕ) : Field Space :=
  fun t x => ∑ m ∈ Finset.range ((M.scaleData w).D n + 1),
    movingCurl (addressPath M (M.scaleData w) n m) ((M.scaleData w).δ n)
      (t - 1 - (n : ℝ)) x

noncomputable def loadingVelocity (M : Machine) (w : M.Input) : Field Space :=
  movingCurl (fun s => θ s • vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0) 1

lemma stepVelocity_smooth (M : Machine) (w : M.Input) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (stepVelocity M w n)) := by
  unfold stepVelocity Function.uncurry
  apply ContDiff.sum
  intro m _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (addressPath M (M.scaleData w) n m) := by
    unfold addressPath
    exact contDiff_const.add (theta_smooth.smul contDiff_const)
  have hsh : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => (p.1 - 1 - (n : ℝ), p.2)) := by
    fun_prop
  simpa only [Function.comp_def, Function.uncurry] using
    (movingCurl_joint_smooth hc ((M.scaleData w).δ n)).comp hsh

lemma loadingVelocity_smooth (M : Machine) (w : M.Input) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (loadingVelocity M w)) :=
  movingCurl_joint_smooth (theta_smooth.smul contDiff_const) 1

lemma stepVelocity_left_collar (M : Machine) (w : M.Input) (n : ℕ) {t : ℝ}
    (ht : t < 1 + (n : ℝ) + 1 / 4) : stepVelocity M w n t = 0 := by
  funext x
  apply Finset.sum_eq_zero
  intro m _
  exact congrFun (movingCurl_left_collar (addressCenter (M.scaleData w) n m)
    (addressDisplacement M (M.scaleData w) n m) _ (by linarith)) x

lemma stepVelocity_right_collar (M : Machine) (w : M.Input) (n : ℕ) {t : ℝ}
    (ht : 1 + (n : ℝ) + 3 / 4 < t) : stepVelocity M w n t = 0 := by
  funext x
  apply Finset.sum_eq_zero
  intro m _
  exact congrFun (movingCurl_right_collar (addressCenter (M.scaleData w) n m)
    (addressDisplacement M (M.scaleData w) n m) _ (by linarith)) x

lemma loadingVelocity_right_collar (M : Machine) (w : M.Input) {t : ℝ}
    (ht : 3 / 4 < t) : loadingVelocity M w t = 0 := by
  have h := movingCurl_right_collar 0
    (vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0) 1 ht
  funext x
  change movingCurl (fun s => θ s • vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0)
    1 t x = 0
  simpa only [zero_add] using congrFun h x

lemma addressedVelocity_eq_finite (M : Machine) (w : M.Input) (N : ℕ)
    {t : ℝ} (ht : t < (N : ℝ) + 1) :
    addressedVelocity M w t = loadingVelocity M w t + ∑ n ∈ Finset.range N,
      stepVelocity M w n t := by
  by_cases h : t ≤ 1
  · have hz : ∑ n ∈ Finset.range N, stepVelocity M w n t = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      apply stepVelocity_left_collar
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hz, add_zero]
    exact funext fun x => by simp [addressedVelocity, loadingVelocity, h]
  · have ht1 : 1 < t := lt_of_not_ge h
    let n := Nat.floor (t - 1)
    have hn : (n : ℝ) ≤ t - 1 := Nat.floor_le (by linarith)
    have hn' : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hnN : n < N := by
      exact_mod_cast (by linarith : (n : ℝ) < (N : ℝ))
    have hs : (∑ j ∈ Finset.range N, stepVelocity M w j t) = stepVelocity M w n t := by
      apply Finset.sum_eq_single n
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · apply stepVelocity_right_collar
          have : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hj
          linarith
        · apply stepVelocity_left_collar
          have : (n : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
          linarith
      · intro hnnot
        exact (hnnot (Finset.mem_range.mpr hnN)).elim
    rw [hs, loadingVelocity_right_collar M w (by linarith), zero_add]
    exact funext fun x => by simp [addressedVelocity, stepVelocity, h, n]

theorem addressedVelocity_joint_smooth (M : Machine) (w : M.Input) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (addressedVelocity M w)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨N, hN⟩ := exists_nat_gt p.1
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Space =>
      loadingVelocity M w q.1 q.2 + ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2) :=
    (loadingVelocity_smooth M w).add <| ContDiff.sum fun n _ => stepVelocity_smooth M w n
  apply hs.contDiffAt.congr_of_eventuallyEq
  have ho : IsOpen {q : ℝ × Space | q.1 < (N : ℝ) + 1} :=
    isOpen_lt continuous_fst continuous_const
  have he : ∀ᶠ q : ℝ × Space in 𝓝 p, q.1 < (N : ℝ) + 1 :=
    ho.mem_nhds (by change p.1 < (N : ℝ) + 1; linarith)
  filter_upwards [he] with q hq
  simpa only [Function.uncurry, Pi.add_apply, Finset.sum_apply] using
    congrFun (addressedVelocity_eq_finite M w N hq) q.2


section JointDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Field E}

lemma spatialD_joint_smooth (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v))
    (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (spatialD i v)) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Space) × Space => v p.1.1 p.2) :=
    hv.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space => fderiv ℝ (v p.1) p.2) :=
    h.fderiv contDiff_snd (by simp)
  exact hD.clm_apply contDiff_const

lemma ordinaryTimeD_joint_smooth (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => deriv (fun s => v s p.2) p.1) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Space) × ℝ => v p.2 p.1.2) :=
    hv.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space => fderiv ℝ (fun s => v s p.2) p.1) :=
    h.fderiv contDiff_fst (by simp)
  exact hD.clm_apply contDiff_const

lemma timeD_eq_ordinary (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v))
    {t : ℝ} (ht : 0 ≤ t) (x : Space) : timeD v t x = deriv (fun s => v s x) t := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun s => v s x) :=
    hv.comp (contDiff_id.prodMk contDiff_const)
  exact (h.differentiable (by simp) t).derivWithin (uniqueDiffOn_Ici 0 t ht)

end JointDerivatives

lemma advection_joint_smooth {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (advection v)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => ∑ i, (v p.1 p.2 i) • spatialD i v p.1 p.2)
  apply ContDiff.sum
  intro i _
  exact ((EuclideanSpace.proj i).contDiff.comp hv).smul (spatialD_joint_smooth hv i)

lemma laplace_joint_smooth {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (laplace v)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => ∑ i, spatialD i (spatialD i v) p.1 p.2)
  apply ContDiff.sum
  intro i _
  exact spatialD_joint_smooth (spatialD_joint_smooth hv i) i

lemma residual_smooth_of_joint_smooth {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (ν : ℝ) : Smooth (residual ν v) := by
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space =>
      deriv (fun s => v s p.2) p.1 + advection v p.1 p.2 - ν • laplace v p.1 p.2) :=
    ((ordinaryTimeD_joint_smooth hv).add (advection_joint_smooth hv)).sub
      ((laplace_joint_smooth hv).const_smul ν)
  apply hr.contDiffOn.congr
  intro p hp
  change timeD v p.1 p.2 + advection v p.1 p.2 - ν • laplace v p.1 p.2 = _
  rw [timeD_eq_ordinary hv hp.1]

theorem addressed_fields_smooth (ν : ℝ) (M : Machine) (w : M.Input) :
    Smooth (addressedVelocity M w) ∧ Smooth (addressedForce ν M w) :=
  ⟨(addressedVelocity_joint_smooth M w).contDiffOn,
    residual_smooth_of_joint_smooth (addressedVelocity_joint_smooth M w) ν⟩

end RapidForcing

end OAI
