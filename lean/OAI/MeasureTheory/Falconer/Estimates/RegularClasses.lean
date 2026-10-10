import OAI.MeasureTheory.Falconer.Estimates.RegularizationProperties
import OAI.MeasureTheory.Falconer.Estimates.RegularizationCount

namespace OAI

/-!
# Regular classes of an original Frostman law in arbitrary dimension

This proves the application-level form of Lemma `reg:regularization`.
The classes are unions of the original half-open leaves.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

structure RegularizedProfileData (Q : DyadicCube d) (ρ : Measure (Space d))
    (N : ℕ) (s lam : ℝ) (m : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure ρ
  continuous : Continuous m
  zero : m 0 = 0
  monotone : MonotoneOn m (Icc 0 1)
  lipschitz : LipschitzOnWith (d : NNReal) m (Icc 0 1)
  range : ∀ u ∈ Icc (0:ℝ) 1, m u ∈ Icc (0:ℝ) d
  cells : ∀ j ≤ N, ∀ P : CellPath d, P.length = j → 0 < ρ (Q.descendant P).carrier →
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-m ((j:ℝ)/N)) ≤
        (ρ (Q.descendant P).carrier).toReal ∧
      (ρ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-m ((j:ℝ)/N))
  envelope : ∀ u ∈ Icc (0:ℝ) 1, s*u-((d:ℝ)+4)*lam ≤ m u

theorem sourceClass_profile_data (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {s lam : ℝ} (hs : 0 ≤ s)
    (hsmall : s/(N:ℝ) ≤ lam) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    (hgrid : ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N B p j) :
    RegularizedProfileData Q (sourceClass Q μ N B p) N s lam (sourceUnitProfile Q μ N B p) := by
  obtain ⟨hc,hz,hm,hl,hr⟩ := sourceUnitProfile_properties Q μ hN hB p
  refine ⟨regularization_class_probability Q hQ μ N B hp,hc,hz,hm,hl,hr,?_,?_⟩
  · intro j hj P hP hpos
    simpa only [sourceUnitProfile_at_depth Q μ hN B p j] using
      sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp hj hP hpos
  · intro u hu
    have hh := sourceUnitProfile_lower_from_grid Q μ hN hB p hs hgrid hu
    linarith

theorem actual_regular_classes (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {s C lam : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) (hC : 0 ≤ C)
    (hlam : 0 < lam)
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (regularizationIndex Q μ N B t).card ≤ N^(4*H+2) ∧
      μ (⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T)ᶜ ≤
        ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t ∧
      ∀ T ∈ regularizationIndex Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ m : ℝ → ℝ, RegularizedProfileData Q (normalizedClass Q μ L F T) N s lam m := by
  classical
  obtain ⟨H,N₁,hH,hHb,hscales⟩ := PlanarFalconer.exists_bounded_regularization_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(2*Real.sqrt d*Q.side)^s)
  obtain ⟨N₃,hN₃⟩ := exists_nat_gt ((d:ℝ)/lam)
  refine ⟨H,max (max H (d+3)) (max N₁ (max N₂ N₃)),hH,hHb,?_⟩
  intro N hN
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hdN : d+3 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃' : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hscale := hscales N hN₁
  have hsmall : s/(N:ℝ) ≤ lam := by
    apply (div_le_iff₀ (by exact_mod_cast hscale.1 : 0 < (N:ℝ))).mpr
    have hh : (d:ℝ)/lam < (N:ℝ) := hN₃.trans_le (by exact_mod_cast hN₃')
    have hh' := (div_lt_iff₀ hlam).mp hh
    nlinarith
  refine ⟨regularization_count_polynomial Q μ hH hNH hdN _,
    regularization_discarded_global Q hQ μ hcarry hH hNH hdN _,?_⟩
  intro T hT
  refine ⟨(Finset.mem_filter.mp hT).2,?_⟩
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
  subst T
  refine ⟨sourceUnitProfile Q μ N (N/H) p,?_⟩
  apply sourceClass_profile_data Q hQ μ hscale.1 hscale.2.1 hs hsmall
    hscale.2.2.2.1 hscale.2.2.2.2 hp
  intro j hj
  apply sourceProfile_frostman_lower Q hQ μ hscale.1 hscale.2.1
    hscale.2.2.2.1 hscale.2.2.2.2 hp (retained_label_real_mass_lower Q μ hT) _ hj
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound hd Q hQ μ hC hball hscale.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity))

end Falconer.Regularization

end OAI
