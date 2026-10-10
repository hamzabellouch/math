import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanScaleTransition

namespace OAI

/-! # Comparing the actual Cartan profiles at two physical scales -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {EG G W I L : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.N.carrier] [Finite L] [Nonempty L] [Fintype I] [DecidableEq I]

omit [IsTopologicalGroup F.N.carrier] in
theorem CartanFactorModel.adjacent_scale_labels_of_approximation
    (hD : Continuous F.ExpD) (height : H →ₗ[ℝ] W)
    (hheight : Function.Surjective height) (hkill : ∀ u v : H, height ⁅u, v⁆ = 0)
    (labels : L → W ≃ₗ[ℝ] W) (hlabels : Function.Injective labels)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (μ ν : ℕ → ProbabilityMeasure F.N.carrier) (C D : ℕ → Set F.N.carrier)
    (hC : ∀ n, IsCompact (C n)) (hDset : ∀ n, IsCompact (D n))
    (hμ : ∀ n, ∀ᵐ k ∂(μ n : Measure F.N.carrier), k ∈ C n)
    (hν : ∀ n, ∀ᵐ k ∂(ν n : Measure F.N.carrier), k ∈ D n)
    (r t : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (hrt : ∀ n, r n ≤ t n)
    {K : ℝ} (hK : 0 < K) (hbound : ∀ n, t n ≤ K * r n)
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (center : ℕ → G)
    (raw raw' : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
    (hraw : ∀ n k z, raw n k z = rescaledMapProfile (J n) (center n) (F.inclusionN k)
      (max (Real.log (r n)) 0) (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X S β)
        (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ))
        (max (Real.log (r n)) 0))) z)
    (hraw' : ∀ n k z, raw' n k z = rescaledMapProfile (J n) (center n) (F.inclusionN k)
      (max (Real.log (t n)) 0) (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X S β)
        (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ))
        (max (Real.log (t n)) 0))) z)
    (R : ℝ) (hR : 0 < R) :
    let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
    let bD := WordBasisSelections.basis X S β
    let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
    let A := fun l => (⟨fun z => labels l (q z),
      (labels l).toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
        C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
    let b := fun n => ∫ k, raw n k 0 ∂(μ n : Measure F.N.carrier)
    let b' := fun n => ∫ k, raw' n k 0 ∂(ν n : Measure F.N.carrier)
    (∃ a : ℕ → L, Tendsto (fun n => ∫ k, dist ((raw n k).restrict Z)
      (A (a n) + ContinuousMap.const Z (b n)) ∂(μ n : Measure F.N.carrier)) atTop (𝓝 0)) →
    (∃ a : ℕ → L, Tendsto (fun n => ∫ k, dist ((raw' n k).restrict Z)
      (A (a n) + ContinuousMap.const Z (b' n)) ∂(ν n : Measure F.N.carrier)) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n : Measure F.N.carrier).prod
      (ν n : Measure F.N.carrier) {p | ε ≤ dist ((raw n p.1).restrict Z)
        ((raw n p.2).restrict Z)}) atTop (𝓝 0)) →
    let label := fun n => canonicalAffineLabel (μ n : Measure F.N.carrier)
      (fun k => (raw n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b n))
    let label' := fun n => canonicalAffineLabel (ν n : Measure F.N.carrier)
      (fun k => (raw' n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b' n))
    (∀ᶠ n in atTop, label n = label' n) ∧
      Tendsto (fun n => dist (b n) ((t n / r n) • b' n)) atTop (𝓝 0) := by
  classical
  dsimp only
  intro hmean hmean' hpair
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X S β
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let A := fun l => (⟨fun z => labels l (q z),
    (labels l).toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
      C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
  let b := fun n => ∫ k, raw n k 0 ∂(μ n : Measure F.N.carrier)
  let b' := fun n => ∫ k, raw' n k 0 ∂(ν n : Measure F.N.carrier)
  let label := fun n => canonicalAffineLabel (μ n : Measure F.N.carrier)
    (fun k => (raw n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b n))
  let label' := fun n => canonicalAffineLabel (ν n : Measure F.N.carrier)
    (fun k => (raw' n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b' n))
  have hleft := canonicalAffineLabel_mean_tendsto_zero
    (fun n => (μ n : Measure F.N.carrier)) (fun n k => (raw n k).restrict Z)
    (fun n l => A l + ContinuousMap.const Z (b n)) hmean
  have hright := canonicalAffineLabel_mean_tendsto_zero
    (fun n => (ν n : Measure F.N.carrier)) (fun n k => (raw' n k).restrict Z)
    (fun n l => A l + ContinuousMap.const Z (b' n)) hmean'
  let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
  let φ := fun n => wordBallScaleTransition X S β R (zero_lt_one.trans_le (hr n)) (hrt n)
  have hprofile (s : ℕ → ℝ)
      (u : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
      (hu : ∀ n k z, u n k z = rescaledMapProfile (J n) (center n) (F.inclusionN k)
        (max (Real.log (s n)) 0)
        (F.profileChart (exponentialRescaleBasis bD cost (max (Real.log (s n)) 0))) z) :
      ∀ n, Continuous (fun k => (u n k).restrict Z) := by
    intro n
    have he : u n = fun k => rescaledContinuousProfile (J n) (hJ n) (center n) (F.inclusionN k)
        (max (Real.log (s n)) 0)
        (F.profileChart (exponentialRescaleBasis bD cost (max (Real.log (s n)) 0)))
        (F.continuous_profileChart hD _) := by
      funext k
      ext z
      exact hu n k z
    rw [he]
    exact (ContinuousMap.continuous_restrict Z).comp
      ((continuous_rescaledContinuousProfile (J n) (hJ n) (center n)
        (max (Real.log (s n)) 0)
        (F.profileChart (exponentialRescaleBasis bD cost (max (Real.log (s n)) 0)))
        (F.continuous_profileChart hD _)).comp F.closedN.continuous)
  have hmatch n k : (raw n k).restrict Z = rescaleCompactProfile
      (t n / r n) (φ n) ((raw' n k).restrict Z) := by
    have he := F.wordBall_profile_scale_eq hD (J n) (hJ n) (center n) X S β R (hr n) (hrt n) k
    ext z
    have hh := congrArg (fun f : C(Z, W) => f z) he
    simpa only [rescaledContinuousProfile, ContinuousMap.coe_mk, rescaleCompactProfile,
      ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.restrict_apply,
      ← hraw, ← hraw', φ, bD, cost] using hh
  have hq : Function.Surjective q := hheight.comp bD.equivFun.symm.surjective
  have hA : Function.Injective A := by
    intro l l' he
    apply hlabels
    have he' : linearBallProfile q (labels l).toContinuousLinearEquiv.toContinuousLinearMap R =
        linearBallProfile q (labels l').toContinuousLinearEquiv.toContinuousLinearMap R := by
      exact he
    have hh := linearBallProfile_injective q hq hR he'
    ext w
    exact DFunLike.congr_fun hh w
  let : Fintype L := Fintype.ofFinite L
  apply affine_scale_labels_and_offsets μ ν C D hC hDset hμ hν
    (fun n k => (raw n k).restrict Z) (fun n k => (raw' n k).restrict Z)
    (hprofile r raw hraw) (hprofile t raw' hraw')
    (fun n => t n / r n) φ hK
    (fun n => by
      rw [abs_of_pos (div_pos (zero_lt_one.trans_le ((hr n).trans (hrt n)))
        (zero_lt_one.trans_le (hr n)))]
      exact (div_le_iff₀ (zero_lt_one.trans_le (hr n))).mpr (hbound n))
    hmatch A hA ⟨0, Metric.mem_closedBall_self hR.le⟩
    (fun l => by simp [A, q]) _ label label' b b' hleft hright hpair
  intro n l z
  change (t n / r n) • labels l (q (φ n z)) = labels l (q z)
  rw [← map_smul]
  congr 1
  exact wordBallScaleTransition_height X S β height hkill R
    (zero_lt_one.trans_le (hr n)) (hrt n) z

end PolycyclicRecognition

end

end OAI
