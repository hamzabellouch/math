import OAI.Geometry.EinsteinFour.ScalarPoissonKernelLocalRepresentative

namespace OAI

/-! A smooth zeroth-order potential does not obstruct the local bootstrap.
Only the principal and first-order perturbations need to be small. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

private theorem scalarPotential_multipliers_commute (c ψ : S) (u : T) :
    M ψ (M c u) = M c (M ψ u) := by
  rw [smulLeftCLM_smulLeftCLM_apply c.hasTemperateGrowth ψ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth c.hasTemperateGrowth,
    mul_comm (c : V → ℂ) (ψ : V → ℂ)]

variable (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
  (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
  (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
  (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
  (hb : ∀ i x, ‖b i x‖ ≤ δ)
  (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
  (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)

include hδ ha ha1 ha2 hb hb1 hsmall

/-- The potential times u has the needed order from the outer cutoff; it
is not required to be smooth before the bootstrap. -/
theorem scalar_nested_cutoff_gain_of_potential (c ψ χ : S)
    (hnest : ScalarCutoffNested ψ χ) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M χ u))
    (hf : MemSobolev (n : ℝ) 2
      (M ψ (scalarPerturbedOperator a b u - u - M c u))) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M ψ u) := by
  have hi : MemSobolev (n : ℝ) 2 (M ψ u) := by
    rw [← scalarCutoffNested_mul ψ χ hnest]
    exact (scalar_memSobolev_schwartz_multiplier (n + 1) ψ _ hu).mono
      (by exact_mod_cast Nat.le_succ n)
  have hp : MemSobolev (n : ℝ) 2 (M c (M ψ u)) :=
    scalar_memSobolev_schwartz_multiplier n c _ hi
  have heq : M ψ (scalarPerturbedOperator a b u) =
      M ψ u + M c (M ψ u) +
        M ψ (scalarPerturbedOperator a b u - u - M c u) := by
    rw [map_sub, map_sub, scalarPotential_multipliers_commute]
    abel
  have hsource : MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u)) := by
    rw [heq]
    exact (hi.add hp).add hf
  exact scalar_nested_cutoff_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall ψ χ hnest n u hu hsource

theorem scalar_finite_cutoff_chain_gain_of_potential (c : S) (u : T)
    (n : ℕ) (ψ : ℕ → S)
    (hnest : ∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1)))
    (hu : MemSobolev 1 2 (M (ψ n) u))
    (hf : ∀ k ≤ n, MemSobolev (n : ℝ) 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u))) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 0) u) := by
  induction n generalizing ψ with
  | zero => simpa using hu
  | succ n ih =>
      have ht : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 1) u) := by
        apply ih (fun k => ψ (k + 1))
        · intro k hk
          exact hnest (k + 1) (Nat.succ_lt_succ hk)
        · simpa only [Nat.succ_eq_add_one] using hu
        · intro k hk
          exact (hf (k + 1) (Nat.succ_le_succ hk)).mono
            (by exact_mod_cast Nat.le_succ n)
      have hs : MemSobolev (n : ℝ) 2
          (M (ψ 0) (scalarPerturbedOperator a b u - u - M c u)) :=
        (hf 0 (Nat.zero_le _)).mono (by exact_mod_cast Nat.le_succ n)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
          c (ψ 0) (ψ 1) (hnest 0 (Nat.zero_lt_succ n)) n u ht hs

/-- Local H1 and a smooth potential-source remainder give every Sobolev
order on each smaller compactly supported localization. -/
theorem scalar_ball_local_sobolev_of_potential (c : S) (u : T)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ u))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
        MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u - u - M c u)))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hφc hφ
  intro n
  have hgain := scalar_finite_cutoff_chain_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c u n ψ (fun k _ => hnest k) (hH1 (ψ n) (hsupp n).1 (hsupp n).2)
      (fun k _ => hforce n (ψ k) (hsupp k).1 (hsupp k).2)
  rw [hψ] at hgain
  exact hgain.mono (by exact_mod_cast Nat.le_succ n)

omit hδ ha ha1 ha2 hb hb1 hsmall

private def scalarPotentialInnerBump : ContDiffBump (0 : V) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def scalarPotentialInnerCutoff : S :=
  (scalarPotentialInnerBump.hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp scalarPotentialInnerBump.contDiff)

private theorem scalarPotentialInnerCutoff_apply (x : V) :
    scalarPotentialInnerCutoff x = (scalarPotentialInnerBump x : ℂ) := rfl

private theorem scalarPotentialInnerCutoff_tsupport :
    tsupport (scalarPotentialInnerCutoff : V → ℂ) = closedBall 0 (1 / 2) := by
  have hs : Function.support (scalarPotentialInnerCutoff : V → ℂ) =
      Function.support (scalarPotentialInnerBump : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarPotentialInnerCutoff_apply,
      ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact scalarPotentialInnerBump.tsupport_eq

private theorem scalarPotentialInnerCutoff_one {x : V} (hx : x ∈ ball 0 (1 / 4)) :
    scalarPotentialInnerCutoff x = 1 := by
  rw [scalarPotentialInnerCutoff_apply]
  have h := scalarPotentialInnerBump.one_of_mem_closedBall (ball_subset_closedBall hx)
  simp only [h, Complex.ofReal_one]

include hδ ha ha1 ha2 hb hb1 hsmall

/-- No smallness or prior regularity of the potential term times u is
assumed.  The original L2 solution has a smooth local representative. -/
theorem scalar_small_elliptic_potential_local_representative (c : S) (u : L2)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ (u : T)))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev (n : ℝ) 2
        (M ψ (scalarPerturbedOperator a b (u : T) - (u : T) - M c (u : T)))) :
    ∃ f : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (u : V → ℂ) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  have hc : HasCompactSupport (scalarPotentialInnerCutoff : V → ℂ) := by
    change IsCompact (tsupport (scalarPotentialInnerCutoff : V → ℂ))
    rw [scalarPotentialInnerCutoff_tsupport]
    exact isCompact_closedBall _ _
  have hr : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M scalarPotentialInnerCutoff (u : T)) :=
    scalar_ball_local_sobolev_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall c (u : T)
      hH1 hforce (1 / 2) (by norm_num) (by norm_num) scalarPotentialInnerCutoff hc
      (by rw [scalarPotentialInnerCutoff_tsupport])
  exact scalar_L2_cutoff_smooth_on u scalarPotentialInnerCutoff (ball 0 (1 / 4))
    isOpen_ball.measurableSet (fun _ hx => scalarPotentialInnerCutoff_one hx) hr

theorem scalar_small_elliptic_potential_local_real_representative (c : S) (u : L2)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ (u : T)))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev (n : ℝ) 2
        (M ψ (scalarPerturbedOperator a b (u : T) - (u : T) - M c (u : T)))) :
    ∃ f : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (fun x : V => (u x).re) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  obtain ⟨f, hf, heq⟩ := scalar_small_elliptic_potential_local_representative
    a b δ hδ ha ha1 ha2 hb hb1 hsmall c u hH1 hforce
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  change (u x).re = (f x).re
  rw [hx]

end
end PositiveEinsteinFour.Geometry

end OAI
