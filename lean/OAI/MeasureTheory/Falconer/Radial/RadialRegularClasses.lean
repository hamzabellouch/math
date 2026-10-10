import OAI.MeasureTheory.Falconer.Geometry.DyadicScaleBallBounds
import OAI.MeasureTheory.Falconer.Estimates.RegularClasses

namespace OAI

/-! # Actual radial regularization classes from the finite-scale ball hypothesis -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem radial_regular_classes (hd : 2 ≤ d) (Q : DyadicCube d) (hQ : Q.side = 1)
    {ε lam : ℝ} (hε : 0 ≤ ε) (hεlam : ε < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
        (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧ ∀ N ≥ N₀,
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], μ Q.carrierᶜ = 0 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^((d:ℝ)-1))) →
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (regularizationIndex Q μ N B t).card ≤ N^(4*H+2) ∧
      μ (⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T)ᶜ ≤
        ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*t ∧
      ∀ T ∈ regularizationIndex Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ p ∈ regularizationLeaves Q μ N, regularizationLabel Q μ N B p = T ∧
          RegularizedProfileData Q (normalizedClass Q μ L F T)
            N ((d:ℝ)-1) lam (sourceUnitProfile Q μ N B p) := by
  have hlam : 0 < lam := hε.trans_lt hεlam
  have hs : 0 ≤ (d:ℝ)-1 := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨H,N₁,hH,hHb,hscales⟩ := PlanarFalconer.exists_bounded_regularization_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed (sub_pos.mpr hεlam) ((2*Real.sqrt d)^((d:ℝ)-1))
  obtain ⟨N₃,hN₃⟩ := exists_nat_gt ((d:ℝ)/lam)
  refine ⟨H,max (max H (d+3)) (max N₁ (max N₂ N₃)),hH,hHb,?_,?_⟩
  · intro N hN
    have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hh := hscales N hN₁
    exact ⟨hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
  intro N hN μ _ hcarry hball
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hdN : d+3 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃' : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hscale := hscales N hN₁
  have hsmall : ((d:ℝ)-1)/(N:ℝ) ≤ lam := by
    apply (div_le_iff₀ (by exact_mod_cast hscale.1 : 0 < (N:ℝ))).mpr
    have hh : (d:ℝ)/lam < (N:ℝ) := hN₃.trans_le (by exact_mod_cast hN₃')
    have hh' := (div_lt_iff₀ hlam).mp hh
    nlinarith
  have hcell : ∀ j ≤ N, ∀ P : CellPath d, P.length = j →
      (μ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^lam*((2:ℝ)^N)^(-((d:ℝ)-1)*(j:ℝ)/(N:ℝ)) := by
    intro j hj P hP
    have hh := dyadic_scale_cell_bound (by omega : 0 < d) Q hQ μ hscale.1 hε hs hball hj P hP
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (((2:ℝ)^N)^(lam-ε))*(((2:ℝ)^N)^ε) :=
        mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  refine ⟨regularization_count_polynomial Q μ hH hNH hdN _,
    regularization_discarded_global Q hside μ hcarry hH hNH hdN _,?_⟩
  intro T hT
  refine ⟨(Finset.mem_filter.mp hT).2,?_⟩
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
  subst T
  refine ⟨p,hp,rfl,?_⟩
  apply sourceClass_profile_data Q hside μ hscale.1 hscale.2.1 hs hsmall
    hscale.2.2.2.1 hscale.2.2.2.2 hp
  intro j hj
  exact sourceProfile_frostman_lower Q hside μ hscale.1 hscale.2.1
    hscale.2.2.2.1 hscale.2.2.2.2 hp (retained_label_real_mass_lower Q μ hT) hcell hj

end Falconer.Regularization

end OAI
