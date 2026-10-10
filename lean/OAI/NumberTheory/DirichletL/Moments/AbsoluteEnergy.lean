import OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one_all (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem radial_weight_lattice_bound_all (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O, ‖Φ (‖eisEmbedding z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤B := by dsimp [B]; positivity
  have hp (z : O) : ‖Φ (‖eisEmbedding z‖^2/K)‖ ≤
      B*((1+1*‖eisEmbedding z‖^2)^2)⁻¹ := by
    have hq : 0≤‖eisEmbedding z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖eisEmbedding z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖eisEmbedding z‖^2/K)^2*‖Φ (‖eisEmbedding z‖^2/K)‖≤B at hh
    have hq' : ‖eisEmbedding z‖^2≤‖eisEmbedding z‖^2/K := by
      apply (le_div_iff₀ hK).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) hsmall
    have hden : (1+1*‖eisEmbedding z‖^2)^2≤(1+‖eisEmbedding z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

theorem finite_hecke_polynomial_norm (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem finite_hecke_energy_summable (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : O => (∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

theorem finite_hecke_energy_absolute (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    ‖finiteHeckeEnergy η m A t S c Φ K‖ ≤
      diagonalControl Φ*max 1 K*(∑ I∈S,‖c I‖)^2 := by
  have hs := (finite_hecke_energy_summable η m A t S c Φ K hK).norm
  calc
    _ ≤ ∑' z : O, ‖((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
        Φ (‖eisEmbedding z‖^2/K)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' z : O,(∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖ := by
      apply hs.tsum_le_tsum _ ((radial_norm_summable Φ K hK).mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
        (norm_nonneg _)
    _ = (∑ I∈S,‖c I‖)^2*(∑' z : O,‖Φ (‖eisEmbedding z‖^2/K)‖) := tsum_mul_left
    _ ≤ (∑ I∈S,‖c I‖)^2*(diagonalControl Φ*max 1 K) :=
      mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg _)
    _ = _ := by ring

theorem smooth_subset_source_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨D,hD,hm⟩ := smooth_subset_source_mass_uniform F Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  let C := (diagonalControl Φ+1)*D^2
  have hd := diagonalControl_nonneg Φ
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S K hK H E
  have hmass := (hm J hJ 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S).2
  have hmass' : (∑ I∈finiteColumns S,‖finiteColumnCoefficient S
      (profileCoefficient R (fun j : J => ν j.val) (fun j : J => Wslot j.val)
        (fun j : J => P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖)≤D*H := by
    simpa only [finiteColumnCoefficient,profileCoefficient_eq_original,H,mul_assoc] using hmass
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hNB₁ : 0<(Ideal.absNorm B₁:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hNB₂ : 0<(Ideal.absNorm B₂:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hprod : 0<∏ j∈J,P j := Finset.prod_pos hP
  have hH : 0<H := by dsimp only [H]; positivity
  have hmax : 0≤max 1 K := le_trans zero_le_one (le_max_left _ _)
  have he : ‖E‖≤C*max 1 K*H^2 := by
    apply (finite_hecke_energy_absolute η m A t (finiteColumns S) _ Φ K hK).trans
    calc
      _ ≤ diagonalControl Φ*max 1 K*(D*H)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass' 2)
          (mul_nonneg hd hmax)
      _ ≤ (diagonalControl Φ+1)*max 1 K*(D*H)^2 := by gcongr; linarith
      _ = C*max 1 K*H^2 := by dsimp only [C]; ring
  refine ⟨he,?_⟩
  apply (div_le_iff₀ hH).mpr
  convert he using 1; ring

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI
