import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSlabGluing
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelRestart
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingGlobalTrajectory

namespace OAI

/-! # From adjacent mild equations to the global similarity equation

The exact restart identity transports the actual forcing at each successive
radius.  Consequently a continuous path satisfying the equation on every
equal slab satisfies the original mild equation on every finite interval.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

@[simp] theorem expandingPicard_initial (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    expandingPicard a b k L T ha hk hL hT F u₀ u ⟨0, le_rfl, hT⟩ = u₀ := by
  change expandingFreeStep a b k L 0 ha hk hL le_rfl u₀ +
    expandingDuhamel a b k L ha hk hL 0 _ = u₀
  rw [expandingFreeStep_zero]
  simp [expandingDuhamel]

theorem expandingDuhamel_congr_on (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (r q : ℝ → FourierL2)
    (heq : EqOn r q (Icc 0 t)) :
    expandingDuhamel a b k L ha hk hL t r =
      expandingDuhamel a b k L ha hk hL t q := by
  unfold expandingDuhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  simp only [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hs, heq hs]

theorem expandingMild_global_of_local (a b k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 < M)
    (u r : ℝ → FourierL2) (hr : ContinuousOn r (Ici 0))
    (hloc : ∀ (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 M),
      u ((n : ℝ) * M + s) =
        expandingFreeStep a b k (expandingRadius L ((n : ℝ) * M)) s ha hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) hs.1
          (u ((n : ℝ) * M)) +
        expandingDuhamel a b k (expandingRadius L ((n : ℝ) * M)) ha hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) s
          (fun τ => r ((n : ℝ) * M + τ)))
    (t : ℝ) (ht : 0 ≤ t) :
    u t = expandingFreeStep a b k L t ha hk hL ht (u 0) +
      expandingDuhamel a b k L ha hk hL t r := by
  have hgrid (n : ℕ) :
      u ((n : ℝ) * M) =
        expandingFreeStep a b k L ((n : ℝ) * M) ha hk hL (by positivity) (u 0) +
          expandingDuhamel a b k L ha hk hL ((n : ℝ) * M) r := by
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, expandingFreeStep_zero,
          ContinuousLinearMap.id_apply]
        simp [expandingDuhamel]
    | succ n ih =>
        have hn : 0 ≤ (n : ℝ) * M := by positivity
        have hrestart := expandingMild_restart a b k L ((n : ℝ) * M) M
          ha hk hL hn hM.le r (hr.mono (fun _ hx => hx.1)) (u 0)
        have he := hloc n M ⟨hM.le, le_rfl⟩
        rw [ih] at he
        have hresult := he.trans hrestart.symm
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hresult
  let n := ⌊t / M⌋₊
  let s := t - (n : ℝ) * M
  have hn : 0 ≤ (n : ℝ) * M := by positivity
  have hinterval := equalSlabInterval_floor M hM t ht
  have hs : s ∈ Icc 0 M := by
    constructor <;> dsimp [s, n] <;> linarith [hinterval.1, hinterval.2]
  have he : (n : ℝ) * M + s = t := by dsimp [s]; ring
  have hrestart := expandingMild_restart a b k L ((n : ℝ) * M) s ha hk hL hn hs.1 r
    (hr.mono (fun _ hx => hx.1)) (u 0)
  have hresult := hloc n s hs
  rw [hgrid n] at hresult
  simpa only [he] using hresult.trans hrestart.symm

noncomputable def expandingGlobalReaction (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (u : ℝ → FourierL2) (t : ℝ) : FourierL2 :=
  (-Complex.I) • expandingOddPower a k (expandingRadius L (max 0 t)) ha ha1 hk
    (hL.trans (expandingRadius_ge L _ hL (le_max_left _ _))) m (u t)

theorem continuousOn_expandingGlobalReaction (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (u : ℝ → FourierL2) (hu : ContinuousOn u (Ici 0)) :
    ContinuousOn (expandingGlobalReaction a k L ha ha1 hk hL m u) (Ici 0) := by
  let R : ℝ → {R : ℝ // 1 ≤ R} := fun t =>
    ⟨expandingRadius L (max 0 t),
      hL.trans (expandingRadius_ge L _ hL (le_max_left _ _))⟩
  have hR : Continuous R := by
    apply Continuous.subtype_mk
    unfold expandingRadius
    fun_prop
  exact ((continuous_expandingOddPower_scale a k ha ha1 hk m).comp_continuousOn
    (hR.continuousOn.prodMk hu)).const_smul (-Complex.I)

theorem expandingGlobalReaction_history (a k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (m : ℕ) (u : ℝ → FourierL2) (hu : ContinuousOn u (Ici 0))
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    expandingGlobalReaction a k L ha ha1 hk hL m u t =
      expandingReactionHistory S hS
        (expandingNonlinearReaction a k L S ha ha1 hk hL m)
        (expandingSlabRestriction u hu S) t := by
  simp only [expandingReactionHistory, projIcc_of_mem _ ht]
  change (-Complex.I) • expandingOddPower a k (expandingRadius L (max 0 t))
    ha ha1 hk _ m (u t) =
      (-Complex.I) • expandingOddPower a k (expandingRadius L t) ha ha1 hk _ m (u t)
  simp only [max_eq_right ht.1]

theorem expandingGlobal_picard_of_local (a b k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 < M)
    (m : ℕ) (u : ℝ → FourierL2) (hu : ContinuousOn u (Ici 0))
    (hloc : ∀ (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 M),
      u ((n : ℝ) * M + s) =
        expandingFreeStep a b k (expandingRadius L ((n : ℝ) * M)) s ha hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) hs.1
          (u ((n : ℝ) * M)) +
        expandingDuhamel a b k (expandingRadius L ((n : ℝ) * M)) ha hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) s
          (fun τ => expandingGlobalReaction a k L ha ha1 hk hL m u ((n : ℝ) * M + τ)))
    (S : ℝ) (hS : 0 < S) :
    expandingSlabRestriction u hu S =
      expandingPicard a b k L S ha hk hL hS.le
        (expandingNonlinearReaction a k L S ha ha1 hk hL m) (u 0)
        (expandingSlabRestriction u hu S) := by
  apply ContinuousMap.ext
  intro t
  change u t = expandingFreeStep a b k L t ha hk hL t.2.1 (u 0) + _
  rw [expandingMild_global_of_local a b k L M ha hk hL hM u
    (expandingGlobalReaction a k L ha ha1 hk hL m u)
    (continuousOn_expandingGlobalReaction a k L ha ha1 hk hL m u hu) hloc t t.2.1]
  congr 1
  apply expandingDuhamel_congr_on
  intro τ hτ
  exact expandingGlobalReaction_history a k L S ha ha1 hk hL hS.le m u hu τ
    ⟨hτ.1, hτ.2.trans t.2.2⟩

end DefocusingNLS

end OAI
