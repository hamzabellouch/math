import OAI.MathematicalPhysics.NavierStokes.Material.Compiler

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open Filter

noncomputable section

theorem spatialD_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialD i g) := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem spatialD_twice {g : Space → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Space) :
    spatialD i (spatialD j g) x = fderiv ℝ (fderiv ℝ g) x (basisVector i) (basisVector j) := by
  change fderiv ℝ (fun y => fderiv ℝ g y (basisVector j)) x (basisVector i) = _
  rw [fderiv_clm_apply]
  · simp
  · exact (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  · fun_prop

theorem spatialD_comm {g : Space → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Space) :
    spatialD i (spatialD j g) x = spatialD j (spatialD i g) x := by
  rw [spatialD_twice hg, spatialD_twice hg]
  exact hg.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

def pairedCurl (i j : Fin 3) (g : Space → ℝ) : Space → Space :=
  fun x => spatialD j g x • basisVector i - spatialD i g x • basisVector j

theorem pairedCurl_smooth {g : Space → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (pairedCurl i j g) := by
  exact ((spatialD_smooth hg j).smul contDiff_const).sub
    ((spatialD_smooth hg i).smul contDiff_const)

theorem divergence_sub {u v : Space → Space} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (x : Space) :
    divergence (fun y => u y - v y) x = divergence u x - divergence v x := by
  simp only [divergence, spatialD, fderiv_fun_sub (hu x) (hv x),
    sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]

theorem divergence_basis_smul {g : Space → ℝ} (hg : Differentiable ℝ g)
    (j : Fin 3) (x : Space) :
    divergence (fun y => g y • basisVector j) x = spatialD j g x := by
  simp only [divergence, spatialD, fderiv_smul_const (hg x),
    ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, basisVector,
    PiLp.single_apply, smul_eq_mul]
  simp

theorem pairedCurl_divergence {g : Space → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Space) : divergence (pairedCurl i j g) x = 0 := by
  have hi := spatialD_smooth hg i
  have hj := spatialD_smooth hg j
  change divergence (fun y => spatialD j g y • basisVector i - spatialD i g y • basisVector j) x = 0
  rw [divergence_sub
    (hj.differentiable (by simp) |>.smul_const _) (hi.differentiable (by simp) |>.smul_const _),
    divergence_basis_smul (hj.differentiable (by simp)),
    divergence_basis_smul (hi.differentiable (by simp)), spatialD_comm hg, sub_self]

def spatialCutoff (x : Space) : ℝ :=
  Real.smoothTransition ((9 - ‖x‖ ^ 2) / 5)

theorem spatialCutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) spatialCutoff := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const 5)

theorem spatialCutoff_one {x : Space} (hx : ‖x‖ ≤ 2) : spatialCutoff x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hsq : ‖x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg x]
  linarith

theorem spatialCutoff_zero {x : Space} (hx : 3 ≤ ‖x‖) : spatialCutoff x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hsq : 9 ≤ ‖x‖ ^ 2 := by nlinarith
  linarith

theorem spatialCutoff_support : tsupport spatialCutoff ⊆ Metric.closedBall 0 3 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (spatialCutoff_zero (le_of_lt (lt_of_not_ge h)))

theorem spatialCutoff_compact : HasCompactSupport spatialCutoff :=
  (isCompact_closedBall (0 : Space) 3).of_isClosed_subset (isClosed_tsupport _) spatialCutoff_support

theorem spatialCutoff_one_near {x : Space} (hx : ‖x‖ < 2) :
    spatialCutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [(continuous_norm.tendsto x).eventually (gt_mem_nhds hx)] with y hy
  exact spatialCutoff_one hy.le

theorem tsupport_spatialD_subset {g : Space → ℝ} (i : Fin 3) :
    tsupport (spatialD i g) ⊆ tsupport g := by
  exact (tsupport_comp_subset (g := fun L : Space →L[ℝ] ℝ => L (basisVector i))
    (by simp) (fderiv ℝ g)).trans (tsupport_fderiv_subset ℝ)

theorem tsupport_pairedCurl_subset {g : Space → ℝ} (i j : Fin 3) :
    tsupport (pairedCurl i j g) ⊆ tsupport g := by
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact (tsupport_smul_subset_left _ _).trans (tsupport_spatialD_subset j)
  · exact (tsupport_smul_subset_left _ _).trans (tsupport_spatialD_subset i)

def localizedCurl (i j : Fin 3) (g : Space → ℝ) : Space → Space :=
  pairedCurl i j (fun x => spatialCutoff x * g x)

theorem localizedCurl_smooth {g : Space → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (localizedCurl i j g) :=
  pairedCurl_smooth (spatialCutoff_smooth.mul hg) i j

theorem localizedCurl_divergence {g : Space → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Space) : divergence (localizedCurl i j g) x = 0 :=
  pairedCurl_divergence (spatialCutoff_smooth.mul hg) i j x

theorem localizedCurl_support (i j : Fin 3) (g : Space → ℝ) :
    tsupport (localizedCurl i j g) ⊆ Metric.closedBall 0 3 :=
  (tsupport_pairedCurl_subset i j).trans (tsupport_mul_subset_left.trans spatialCutoff_support)

theorem localizedCurl_compact (i j : Fin 3) (g : Space → ℝ) :
    HasCompactSupport (localizedCurl i j g) :=
  (isCompact_closedBall (0 : Space) 3).of_isClosed_subset (isClosed_tsupport _)
    (localizedCurl_support i j g)

theorem localizedCurl_on_plateau (i j : Fin 3) (g : Space → ℝ) {x : Space}
    (hx : ‖x‖ < 2) : localizedCurl i j g x = pairedCurl i j g x := by
  have he : (fun y => spatialCutoff y * g y) =ᶠ[𝓝 x] g := by
    filter_upwards [spatialCutoff_one_near hx] with y hy
    simp [hy]
  simp only [localizedCurl, pairedCurl, spatialD, he.fderiv_eq]

theorem spatialD_sub {g h : Space → ℝ} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (i : Fin 3) (x : Space) :
    spatialD i (fun y => g y - h y) x = spatialD i g x - spatialD i h x := by
  simp [spatialD, fderiv_fun_sub (hg x) (hh x)]

theorem spatialD_mul {g h : Space → ℝ} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (i : Fin 3) (x : Space) :
    spatialD i (fun y => g y * h y) x = spatialD i g x * h x + g x * spatialD i h x := by
  simp [spatialD, fderiv_fun_mul (hg x) (hh x)]
  ring

theorem spatialD_coord (i j : Fin 3) (x : Space) :
    spatialD i (fun y : Space => y j) x = if j = i then 1 else 0 := by
  change (fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) j) x) (basisVector i) = _
  rw [ContinuousLinearMap.fderiv]
  simp [basisVector, PiLp.single_apply]

theorem spatialD_other_coord {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {i j : Fin 3} (hij : i ≠ j) (x : Space) :
    spatialD i (fun y : Space => g (y j)) x = 0 := by
  have he : HasFDerivAt (fun y : Space => g (y j))
      ((fderiv ℝ g (x j)).comp (EuclideanSpace.proj (𝕜 := ℝ) j)) x :=
    (hg (x j)).hasFDerivAt.comp x (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
  simp [spatialD, he.fderiv, basisVector, hij.symm]

def evenPotential (L E : ℝ → ℝ) (x : Space) : ℝ :=
  x 0 * L (x 1) - x 2 * E (x 1)

def oddPotential (L E : ℝ → ℝ) (x : Space) : ℝ :=
  x 1 * E (x 2) - x 0 * L (x 2)

theorem evenPotential_smooth {L E : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    (hE : ContDiff ℝ (⊤ : ℕ∞) E) : ContDiff ℝ (⊤ : ℕ∞) (evenPotential L E) := by
  have hc (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space => x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact ((hc 0).mul (hL.comp (hc 1))).sub ((hc 2).mul (hE.comp (hc 1)))

theorem oddPotential_smooth {L E : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    (hE : ContDiff ℝ (⊤ : ℕ∞) E) : ContDiff ℝ (⊤ : ℕ∞) (oddPotential L E) := by
  have hc (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space => x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact ((hc 1).mul (hE.comp (hc 2))).sub ((hc 0).mul (hL.comp (hc 2)))

theorem evenPotential_curl {L E : ℝ → ℝ} (hL : Differentiable ℝ L)
    (hE : Differentiable ℝ E) (x : Space) :
    pairedCurl 2 0 (evenPotential L E) x = E (x 1) • basisVector 0 + L (x 1) • basisVector 2 := by
  have hc (i : Fin 3) : Differentiable ℝ (fun x : Space => x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable
  have hLc : Differentiable ℝ (fun x : Space => L (x 1)) := hL.comp (hc 1)
  have hEc : Differentiable ℝ (fun x : Space => E (x 1)) := hE.comp (hc 1)
  have h (i : Fin 3) : spatialD i (evenPotential L E) x =
      (if 0 = i then 1 else 0) * L (x 1) + x 0 * spatialD i (fun y => L (y 1)) x -
      ((if 2 = i then 1 else 0) * E (x 1) + x 2 * spatialD i (fun y => E (y 1)) x) := by
    change spatialD i (fun y => y 0 * L (y 1) - y 2 * E (y 1)) x = _
    rw [spatialD_sub
      (show Differentiable ℝ (fun y : Space => y 0 * L (y 1)) from (hc 0).mul hLc)
      (show Differentiable ℝ (fun y : Space => y 2 * E (y 1)) from (hc 2).mul hEc),
      spatialD_mul (hc 0) hLc, spatialD_mul (hc 2) hEc, spatialD_coord, spatialD_coord]
  change spatialD 0 (evenPotential L E) x • basisVector 2 -
    spatialD 2 (evenPotential L E) x • basisVector 0 = _
  rw [h, h]
  simp [spatialD_other_coord hL (show (0 : Fin 3) ≠ 1 by decide),
    spatialD_other_coord hL (show (2 : Fin 3) ≠ 1 by decide),
    spatialD_other_coord hE (show (0 : Fin 3) ≠ 1 by decide),
    spatialD_other_coord hE (show (2 : Fin 3) ≠ 1 by decide), add_comm]

theorem oddPotential_curl {L E : ℝ → ℝ} (hL : Differentiable ℝ L)
    (hE : Differentiable ℝ E) (x : Space) :
    pairedCurl 0 1 (oddPotential L E) x = E (x 2) • basisVector 0 + L (x 2) • basisVector 1 := by
  have hc (i : Fin 3) : Differentiable ℝ (fun x : Space => x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable
  have hLc : Differentiable ℝ (fun x : Space => L (x 2)) := hL.comp (hc 2)
  have hEc : Differentiable ℝ (fun x : Space => E (x 2)) := hE.comp (hc 2)
  have h (i : Fin 3) : spatialD i (oddPotential L E) x =
      (if 1 = i then 1 else 0) * E (x 2) + x 1 * spatialD i (fun y => E (y 2)) x -
      ((if 0 = i then 1 else 0) * L (x 2) + x 0 * spatialD i (fun y => L (y 2)) x) := by
    change spatialD i (fun y => y 1 * E (y 2) - y 0 * L (y 2)) x = _
    rw [spatialD_sub
      (show Differentiable ℝ (fun y : Space => y 1 * E (y 2)) from (hc 1).mul hEc)
      (show Differentiable ℝ (fun y : Space => y 0 * L (y 2)) from (hc 0).mul hLc),
      spatialD_mul (hc 1) hEc, spatialD_mul (hc 0) hLc, spatialD_coord, spatialD_coord]
  change spatialD 1 (oddPotential L E) x • basisVector 0 -
    spatialD 0 (oddPotential L E) x • basisVector 1 = _
  rw [h, h]
  simp [spatialD_other_coord hL (show (0 : Fin 3) ≠ 2 by decide),
    spatialD_other_coord hL (show (1 : Fin 3) ≠ 2 by decide),
    spatialD_other_coord hE (show (0 : Fin 3) ≠ 2 by decide),
    spatialD_other_coord hE (show (1 : Fin 3) ≠ 2 by decide)]

def slotVelocity (M : Machine) (N n : ℕ) : Space → Space :=
  if n % 2 = 0 then
    localizedCurl 2 0 (evenPotential (Memory.localWrite M N n) (Memory.localSignal M N n))
  else
    localizedCurl 0 1 (oddPotential (Memory.localWrite M N n) (Memory.localSignal M N n))

theorem slotVelocity_smooth (M : Machine) (N n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (slotVelocity M N n) := by
  unfold slotVelocity
  split_ifs
  · exact localizedCurl_smooth (evenPotential_smooth
      (Memory.localWrite_smooth M N n) (Memory.localSignal_smooth M N n)) 2 0
  · exact localizedCurl_smooth (oddPotential_smooth
      (Memory.localWrite_smooth M N n) (Memory.localSignal_smooth M N n)) 0 1

theorem slotVelocity_divergence (M : Machine) (N n : ℕ) (x : Space) :
    divergence (slotVelocity M N n) x = 0 := by
  unfold slotVelocity
  split_ifs
  · exact localizedCurl_divergence (evenPotential_smooth
      (Memory.localWrite_smooth M N n) (Memory.localSignal_smooth M N n)) 2 0 x
  · exact localizedCurl_divergence (oddPotential_smooth
      (Memory.localWrite_smooth M N n) (Memory.localSignal_smooth M N n)) 0 1 x

theorem slotVelocity_support (M : Machine) (N n : ℕ) :
    tsupport (slotVelocity M N n) ⊆ Metric.closedBall 0 3 := by
  unfold slotVelocity
  split_ifs <;> exact localizedCurl_support _ _ _

theorem slotVelocity_compact (M : Machine) (N n : ℕ) :
    HasCompactSupport (slotVelocity M N n) :=
  (isCompact_closedBall (0 : Space) 3).of_isClosed_subset (isClosed_tsupport _)
    (slotVelocity_support M N n)

theorem slotVelocity_on_plateau (M : Machine) (N n : ℕ) {x : Space} (hx : ‖x‖ < 2) :
    slotVelocity M N n x = if n % 2 = 0 then
      Memory.localSignal M N n (x 1) • basisVector 0 + Memory.localWrite M N n (x 1) • basisVector 2
    else
      Memory.localSignal M N n (x 2) • basisVector 0 + Memory.localWrite M N n (x 2) • basisVector 1 := by
  have hL := (Memory.localWrite_smooth M N n).differentiable (by simp)
  have hE := (Memory.localSignal_smooth M N n).differentiable (by simp)
  unfold slotVelocity
  split_ifs
  · rw [localizedCurl_on_plateau _ _ _ hx, evenPotential_curl hL hE]
  · rw [localizedCurl_on_plateau _ _ _ hx, oddPotential_curl hL hE]

theorem slotVelocity_donor_stationary (M : Machine) (N n : ℕ) {x : Space} (hx : ‖x‖ < 2) :
    if n % 2 = 0 then slotVelocity M N n x 1 = 0 else slotVelocity M N n x 2 = 0 := by
  rw [slotVelocity_on_plateau M N n hx]
  split_ifs <;> simp [basisVector, PiLp.add_apply, PiLp.smul_apply]

end
end Alternating

end OAI
