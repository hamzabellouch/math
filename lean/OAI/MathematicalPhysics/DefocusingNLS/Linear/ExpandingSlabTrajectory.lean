import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSlabMild

namespace OAI

/-! # Joining actual nonlinear similarity slabs

The finite paths here solve the polynomial equation at the correctly
advanced radius.  Their endpoint identity produces a global path solving
that same equation on every finite interval.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep gluedSlabPath

theorem expandingGluedSlabs_local (a b k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 < M)
    (m : ℕ) (W : ℕ → C(Icc (0 : ℝ) M, FourierL2))
    (hjoin : ∀ n, W n ⟨M, hM.le, le_rfl⟩ = W (n + 1) ⟨0, le_rfl, hM.le⟩)
    (hsol : ∀ n,
      W n = expandingPicard a b k (expandingRadius L ((n : ℝ) * M)) M ha hk
        (hL.trans (expandingRadius_ge L _ hL (by positivity))) hM.le
        (expandingNonlinearReaction a k (expandingRadius L ((n : ℝ) * M)) M ha ha1 hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) m)
        (W n ⟨0, le_rfl, hM.le⟩) (W n))
    (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 M) :
    let u := gluedSlabPath M hM W hjoin
    u ((n : ℝ) * M + s) =
      expandingFreeStep a b k (expandingRadius L ((n : ℝ) * M)) s ha hk
        (hL.trans (expandingRadius_ge L _ hL (by positivity))) hs.1
        (u ((n : ℝ) * M)) +
      expandingDuhamel a b k (expandingRadius L ((n : ℝ) * M)) ha hk
        (hL.trans (expandingRadius_ge L _ hL (by positivity))) s
        (fun τ => expandingGlobalReaction a k L ha ha1 hk hL m u ((n : ℝ) * M + τ)) := by
  intro u
  let Ln := expandingRadius L ((n : ℝ) * M)
  have hLn : 1 ≤ Ln := hL.trans (expandingRadius_ge L _ hL (by positivity))
  let r := expandingReactionHistory M hM.le
    (expandingNonlinearReaction a k Ln M ha ha1 hk hLn m) (W n)
  have he := congrArg (fun f : C(Icc (0 : ℝ) M, FourierL2) => f ⟨s, hs⟩) (hsol n)
  change W n ⟨s, hs⟩ = expandingFreeStep a b k Ln s ha hk hLn hs.1
    (W n ⟨0, le_rfl, hM.le⟩) + expandingDuhamel a b k Ln ha hk hLn s r at he
  have hzero : u ((n : ℝ) * M) = W n ⟨0, le_rfl, hM.le⟩ := by
    simpa only [add_zero] using gluedSlabPath_at M hM W hjoin n ⟨0, le_rfl, hM.le⟩
  rw [show u ((n : ℝ) * M + s) = W n ⟨s, hs⟩ from
    gluedSlabPath_at M hM W hjoin n ⟨s, hs⟩, hzero, he]
  congr 1
  apply expandingDuhamel_congr_on
  intro τ hτ
  have hτM : τ ∈ Icc 0 M := ⟨hτ.1, hτ.2.trans hs.2⟩
  have hpos : 0 ≤ (n : ℝ) * M + τ := add_nonneg (by positivity) hτ.1
  have huτ : u ((n : ℝ) * M + τ) = W n ⟨τ, hτM⟩ :=
    gluedSlabPath_at M hM W hjoin n ⟨τ, hτM⟩
  dsimp only [r, expandingReactionHistory]
  rw [projIcc_of_mem _ hτM]
  change (-Complex.I) • expandingOddPower a k (expandingRadius Ln τ) ha ha1 hk _ m
    (W n ⟨τ, hτM⟩) = _
  simp only [expandingGlobalReaction, max_eq_right hpos, huτ]
  simp only [Ln, expandingRadius_add]

theorem expandingGluedSlabs_picard (a b k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 < M)
    (m : ℕ) (W : ℕ → C(Icc (0 : ℝ) M, FourierL2))
    (hjoin : ∀ n, W n ⟨M, hM.le, le_rfl⟩ = W (n + 1) ⟨0, le_rfl, hM.le⟩)
    (hsol : ∀ n,
      W n = expandingPicard a b k (expandingRadius L ((n : ℝ) * M)) M ha hk
        (hL.trans (expandingRadius_ge L _ hL (by positivity))) hM.le
        (expandingNonlinearReaction a k (expandingRadius L ((n : ℝ) * M)) M ha ha1 hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) m)
        (W n ⟨0, le_rfl, hM.le⟩) (W n))
    (S : ℝ) (hS : 0 < S) :
    let u := gluedSlabPath M hM W hjoin
    expandingSlabRestriction u (continuousOn_gluedSlabPath M hM W hjoin) S =
      expandingPicard a b k L S ha hk hL hS.le
        (expandingNonlinearReaction a k L S ha ha1 hk hL m) (u 0)
        (expandingSlabRestriction u (continuousOn_gluedSlabPath M hM W hjoin) S) := by
  exact expandingGlobal_picard_of_local a b k L M ha ha1 hk hL hM m _
    (continuousOn_gluedSlabPath M hM W hjoin)
    (expandingGluedSlabs_local a b k L M ha ha1 hk hL hM m W hjoin hsol) S hS

end DefocusingNLS

end OAI
