import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledInwardLimit

namespace OAI

/-! A uniformly small local Robin error and bounded oscillatory channel
force the rescaled inward channel to vanish at the far end of a shell. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralShell_inward_limit
    (omega : ℕ → ℝ) (R B D A M : ℝ) (hRB : R < B)
    (hD : 0 ≤ D) (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hw : Tendsto omega atTop atTop)
    (q dq w : ℕ → ℝ → ℂ)
    (hc : ∀ n, ContinuousOn (q n) (Icc R B))
    (hd : ∀ n r, r ∈ Ioo R B → HasDerivAt (q n) (dq n r) r)
    (hg : ∀ᶠ n in atTop, ∃ a ∈ Icc R ((R+B)/2),
      omega n*‖q n a‖^2 ≤ M ∧ ∀ r ∈ Icc a B, omega n*‖w n r‖^2 ≤ M)
    (hs : ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, ∀ r ∈ Icc R B,
      ∃ alpha : ℂ, alpha.re ≤ -Real.sqrt (omega n)/48 ∧
        ‖alpha‖ ≤ A*Real.sqrt (omega n) ∧
        ‖dq n r-alpha*q n r‖ ≤ delta*D*Real.sqrt (omega n)*(‖q n r‖+‖w n r‖)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (Real.sqrt (omega (φ n)) : ℂ)*q (φ n) B) atTop (𝓝 0) ∧
      Tendsto (fun n => dq (φ n) B) atTop (𝓝 0) := by
  classical
  let delta := fun n : ℕ => 1/((n : ℝ)+1)
  have hdelta : ∀ n, 0 < delta n := by intro n; dsimp only [delta]; positivity
  have hdelta0 : Tendsto delta atTop (𝓝 0) := by
    simpa only [delta] using tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ,hφ,hall⟩ := extraction_forall_of_eventually (fun n =>
    (hw.eventually (eventually_gt_atTop 0)).and (hg.and (hs (delta n) (hdelta n))))
  choose a ha hqa hwa using fun n => (hall n).2.1
  let nu := fun n => Real.sqrt (omega (φ n))
  have hnu : ∀ n, 0 < nu n := fun n => Real.sqrt_pos.mpr (hall n).1
  have hnu2 : ∀ n, (nu n)^2 = omega (φ n) := fun n => Real.sq_sqrt (hall n).1.le
  have hnulim : Tendsto nu atTop atTop := Real.tendsto_sqrt_atTop.comp (hw.comp hφ.tendsto_atTop)
  have hals : ∀ n r, r ∈ Icc R B → ∃ alpha : ℂ,
      alpha.re ≤ -nu n/48 ∧ ‖alpha‖ ≤ A*nu n ∧
      ‖dq (φ n) r-alpha*q (φ n) r‖ ≤ delta n*D*nu n*(‖q (φ n) r‖+‖w (φ n) r‖) :=
    fun n => (hall n).2.2
  let alpha := fun n r => if hr : r ∈ Icc R B then (hals n r hr).choose else 0
  have halpha n r (hr : r ∈ Icc R B) :
      (alpha n r).re ≤ -nu n/48 ∧ ‖alpha n r‖ ≤ A*nu n ∧
      ‖dq (φ n) r-alpha n r*q (φ n) r‖ ≤ delta n*D*nu n*(‖q (φ n) r‖+‖w (φ n) r‖) := by
    simpa only [alpha,dite_eq_left hr] using (hals n r hr).choose_spec
  let Q := fun n r => (nu n : ℂ)*q (φ n) r
  let dQ := fun n r => (nu n : ℂ)*dq (φ n) r
  let W := fun n r => (nu n : ℂ)*w (φ n) r
  have hQnorm n r : ‖Q n r‖ = nu n*‖q (φ n) r‖ := by
    simp only [Q,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hnu n)]
  have hWnorm n r : ‖W n r‖ = nu n*‖w (φ n) r‖ := by
    simp only [W,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hnu n)]
  have hinit n : ‖Q n (a n)‖ ≤ Real.sqrt M := by
    apply (Real.le_sqrt (norm_nonneg _) hM).mpr
    rw [hQnorm,mul_pow,hnu2]
    exact hqa n
  have hbound n r (hr : r ∈ Icc (a n) B) : ‖W n r‖ ≤ Real.sqrt M := by
    apply (Real.le_sqrt (norm_nonneg _) hM).mpr
    rw [hWnorm,mul_pow,hnu2]
    exact hwa n r hr
  have hscaled n r (hr : r ∈ Icc R B) :
      ‖dQ n r-alpha n r*Q n r‖ ≤ (48*D*delta n)*(nu n/48)*(‖Q n r‖+‖W n r‖) := by
    have heq : dQ n r-alpha n r*Q n r =
        (nu n : ℂ)*(dq (φ n) r-alpha n r*q (φ n) r) := by dsimp only [dQ,Q]; ring
    rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hnu n)]
    calc
      _ ≤ nu n*(delta n*D*nu n*(‖q (φ n) r‖+‖w (φ n) r‖)) :=
        mul_le_mul_of_nonneg_left (halpha n r hr).2.2 (hnu n).le
      _ = _ := by rw [hQnorm,hWnorm]; ring
  have hlimit : Tendsto (fun n => Q n B) atTop (𝓝 0) := by
    apply spectralComplex_coupled_inward_limit a (fun n => nu n/48) (fun n => 48*D*delta n)
      B ((B-R)/2) (Real.sqrt M) (by linarith) (Real.sqrt_nonneg _)
      (hnulim.atTop_div_const (by norm_num)) (by simpa using hdelta0.const_mul (48*D)) Q dQ W alpha
    apply Eventually.of_forall
    intro n
    refine ⟨by linarith [(ha n).2],by positivity,?_,hinit n,?_,?_,?_,?_⟩
    · exact continuousOn_const.mul ((hc (φ n)).mono (by intro r hr; exact ⟨(ha n).1.trans hr.1,hr.2⟩))
    · intro r hr
      exact (hd (φ n) r ⟨lt_of_le_of_lt (ha n).1 hr.1,hr.2⟩).const_mul _
    · intro r hr
      simpa only [neg_div] using (halpha n r ⟨(ha n).1.trans hr.1.le,hr.2.le⟩).1
    · intro r hr
      exact hscaled n r ⟨(ha n).1.trans hr.1.le,hr.2.le⟩
    · intro r hr
      exact hbound n r ⟨hr.1.le,hr.2.le⟩
  refine ⟨φ,hφ,hlimit,?_⟩
  have hBn : B ∈ Icc R B := ⟨hRB.le,le_rfl⟩
  have hBbound n : ‖W n B‖ ≤ Real.sqrt M := hbound n B ⟨by linarith [(ha n).2],le_rfl⟩
  have hnormlim := tendsto_zero_iff_norm_tendsto_zero.mp hlimit
  have hrhs : Tendsto (fun n => A*‖Q n B‖+delta n*D*(‖Q n B‖+Real.sqrt M)) atTop (𝓝 0) := by
    convert (hnormlim.const_mul A).add ((hdelta0.mul_const D).mul (hnormlim.add_const (Real.sqrt M))) using 1
    simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hrhs
  apply Eventually.of_forall
  intro n
  calc
    ‖dq (φ n) B‖ ≤ ‖alpha n B*q (φ n) B‖+‖dq (φ n) B-alpha n B*q (φ n) B‖ := norm_le_insert' _ _
    _ ≤ (A*nu n)*‖q (φ n) B‖+delta n*D*nu n*(‖q (φ n) B‖+‖w (φ n) B‖) :=
      add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (halpha n B hBn).2.1 (norm_nonneg _))
        (halpha n B hBn).2.2
    _ = A*‖Q n B‖+delta n*D*(‖Q n B‖+‖W n B‖) := by rw [hQnorm,hWnorm]; ring
    _ ≤ _ := by gcongr; exact hBbound n

end DefocusingNLS

end OAI
