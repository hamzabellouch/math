import OAI.MeasureTheory.Falconer.Frostman.FrostmanProfileCells
import OAI.MeasureTheory.Falconer.Estimates.ProfilePacking
import OAI.MeasureTheory.Falconer.Estimates.ProfileAffine
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSubpower
import OAI.MeasureTheory.Falconer.Estimates.RegularizationQuantifiers

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

structure RegularizedProfileData (Q : DyadicSquare) (ν : Measure Plane)
    (N B : ℕ) (δ lam : ℝ) (m : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure ν
  continuous : Continuous m
  zero : m 0 = 0
  slope : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ N → 0 ≤ m v-m u ∧ m v-m u ≤ 2*(v-u)/(N:ℝ)
  affine : ∀ i < N/B+1, ∃ a b : ℝ, ∀ u : ℝ,
    (blockDepth N B (i+1):ℝ) ≤ u → u ≤ (blockDepth N B i:ℝ) → m u = a*u+b
  cells : ∀ n ≤ N, ∀ P : CellPath, P.length = n → 0 < ν (Q.descendant P).carrier →
    ((2:ℝ)^N)^(-3*lam)*((2:ℝ)^N)^(-m n) ≤ (ν (Q.descendant P).carrier).toReal ∧
    (ν (Q.descendant P).carrier).toReal ≤ ((2:ℝ)^N)^(3*lam)*((2:ℝ)^N)^(-m n)
  envelope : ∀ n ≤ N, δ*(n:ℝ)/(N:ℝ)-5*lam ≤ m n-(n:ℝ)/(N:ℝ) ∧
    m n-(n:ℝ)/(N:ℝ) ≤ (n:ℝ)/(N:ℝ)
  adjusted : ∀ u v : ℝ, 0 ≤ u → u ≤ N → 0 ≤ v → v ≤ N →
    |(m v-v/(N:ℝ))-(m u-u/(N:ℝ))| ≤ |v-u|/(N:ℝ)
  packing : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ x : Plane, ∀ C₀ : ℝ, 0 ≤ C₀ →
    ((occupiedCenterCells Q ν p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
      (4*(C₀/Q.side+1)^2)*((2:ℝ)^N)^(m p-m g+6*lam)

theorem actual_profile_regularization (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {δ C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (retainedClassLabels Q μ N B t).card ≤ (4*N+1)^(2*H+1) ∧
      μ (retainedClassUnion Q μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        (((4*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
      ∀ T ∈ retainedClassLabels Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ m : ℝ → ℝ, RegularizedProfileData Q (normalizedClass Q μ L F T) N B δ lam m := by
  classical
  obtain ⟨H,N₁,hH,hHbound,hscales⟩ := exists_bounded_regularization_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(3*Q.side)^(1+δ))
  refine ⟨H,max H (max N₁ N₂),hH,hHbound,?_⟩
  intro N hN
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hs := hscales N hN₁
  have hc : (2*N+1)^(N/(N/H)+1)*(4*N+1) ≤ (4*N+1)^(2*H+1) := by
    rw [pow_succ (4*N+1) (2*H)]
    apply Nat.mul_le_mul_right
    exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hs.2.2.1)
  refine ⟨(retainedClassLabels_count Q μ N (N/H) _).trans hc,?_,?_⟩
  · have hh := retainedClass_discard_mass Q hQ μ hcarry N (N/H)
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    rw [thin_leaf_loss_identity] at hh
    apply hh.trans
    apply add_le_add_right
    apply mul_le_mul_left
    exact_mod_cast hc
  · intro T hT
    refine ⟨retainedClass_mass_lower Q μ hT,?_⟩
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
    subst T
    refine ⟨sourceProfile Q μ N (N/H) p,?_⟩
    refine ⟨regularization_class_probability Q hQ μ N (N/H) hp,
      regularizedProfile_continuous _ _ _ _ _ _,regularizedProfile_zero _ _ _ _ _ _,
      ?_,?_,?_,?_,?_,?_⟩
    · intro u v hu huv hv
      exact regularizedProfile_increment hs.1
        (show regularizationLeaves Q μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
        (regularizationLabel Q μ N (N/H)) hs.2.1 p hu huv hv
    · exact fun i hi => sourceProfile_affine_on_blocks Q μ N (N/H) p hi
    · intro n hn P hP hpos
      exact sourceClass_occupied_comparison Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp hn hP hpos
    · intro n hn
      refine ⟨?_,sourceProfile_upper Q μ hs.1 hs.2.1 p (Nat.cast_nonneg n) (Nat.cast_le.mpr hn)⟩
      apply sourceProfile_frostman_lower Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
        (retained_label_real_mass_lower Q μ hT) _ hn
      intro k hk P hP
      have hh := dyadic_cell_frostman_profile_bound Q hQ μ hC hball hs.1 P
      rw [hP] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity))
    · exact fun u v hu huN hv hvN => sourceProfile_adjusted_lipschitz Q μ hs.1 hs.2.1 p hu huN hv hvN
    · exact fun g p' hgp hpN x C₀ hC₀ =>
        sourceClass_local_count Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp hgp hpN x hC₀

end PlanarFalconer

end OAI
