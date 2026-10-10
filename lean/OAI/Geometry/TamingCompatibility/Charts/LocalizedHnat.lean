import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UniformScaledJet
import OAI.Geometry.TamingCompatibility.Charts.CriticalLocalJet
import OAI.Geometry.TamingCompatibility.DifferentialForms.ParameterScaledJet

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartzToH_add (s : ℝ) (f g : 𝓢(E,F)) :
    schwartzToH s (f+g) = schwartzToH s f + schwartzToH s g := by
  apply toDistribution_injective s
  simp only [map_add,schwartzToH_spec]

lemma schwartzToH_real_smul (s r : ℝ) (f : 𝓢(E,F)) :
    schwartzToH s (r • f) = r • schwartzToH s f := by
  apply toDistribution_injective s
  simp only [ContinuousLinearMap.map_smul_of_tower,schwartzToH_spec]

theorem cutoff_source_Hnat (n : ℕ) (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M) →
      ‖schwartzToH n (SchwartzMap.smulLeftCLM F χ f)‖ ≤ C*M := by
  classical
  induction n generalizing χ with
  | zero =>
    obtain ⟨R,hR⟩ := hχ.isBounded.subset_ball (0:E)
    let T := SchwartzMap.seminorm ℂ 0 0 χ
    have hT : 0 ≤ T := apply_nonneg _ _
    refine ⟨T * (volume (Metric.ball (0:E) R)).toReal^(1/2:ℝ),by positivity,?_⟩
    intro f M hM hb
    rw [Nat.cast_zero,schwartzToH_zero]
    have hs : tsupport (SchwartzMap.smulLeftCLM F χ f) ⊆ Metric.ball 0 R := by
      rw [SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth]
      exact (tsupport_smul_subset_left (⇑χ) (⇑f)).trans hR
    have hf (x : E) : ‖SchwartzMap.smulLeftCLM F χ f x‖ ≤ T*M := by
      rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,norm_smul]
      exact mul_le_mul (SchwartzMap.norm_le_seminorm ℂ χ x)
        (hb 0 le_rfl (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) x)
        (norm_nonneg _) hT
    exact (schwartz_L2_support_bound R (mul_nonneg hT hM) _ hs hf).trans_eq (by ring)
  | succ n ih =>
    obtain ⟨C,hC,hh⟩ := ih χ hχ
    have hder (i : basisIndex E) : HasCompactSupport (⇑(∂_{stdOrthonormalBasis ℝ E i} χ : 𝓢(E,ℂ))) :=
      hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
    choose B hB hbound using (fun i : basisIndex E => ih _ (hder i))
    let D := fun i : basisIndex E => ‖derivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)‖
    let K := |((2*Real.pi)^2)⁻¹|
    refine ⟨C+K*∑ i, D i*(B i+C), ?_, ?_⟩
    · exact add_nonneg hC (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
        (fun i _ => mul_nonneg (norm_nonneg _) (add_nonneg (hB i) hC))))
    intro f M hM hb
    have h0 := hh f M hM (fun k hk => hb k (by omega))
    have h1 (i : basisIndex E) :
        ‖schwartzToH n (∂_{stdOrthonormalBasis ℝ E i} (SchwartzMap.smulLeftCLM F χ f))‖ ≤ (B i+C)*M := by
      rw [schwartz_derivative_smul,schwartzToH_add]
      apply (norm_add_le _ _).trans
      have hb0 := hbound i f M hM (fun k hk => hb k (by omega))
      have hb1 : ‖schwartzToH n (SchwartzMap.smulLeftCLM F χ (∂_{stdOrthonormalBasis ℝ E i} f))‖ ≤ C*M := by
        apply hh _ M hM
        intro k hk m hm x
        have h := hb (k+1) (by omega) (Fin.snoc m (stdOrthonormalBasis ℝ E i))
          (by intro j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [hm]) x
        simpa only [iteratedLineDerivOp_succ_right,Fin.init_snoc,Fin.snoc_last] using h
      exact (add_le_add hb0 hb1).trans_eq (by ring)
    rw [Nat.cast_succ]
    apply (schwartz_Hsucc_norm_le (n:ℝ) _).trans
    calc
      _ ≤ C*M + K*∑ i, D i*((B i+C)*M) := by
        apply add_le_add h0
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        exact fun i _ => mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg _)
      _ = (C+K*∑ i, D i*(B i+C))*M := by
        simp_rw [← mul_assoc,← Finset.sum_mul]
        ring

theorem localized_normalized_source_Hnat (n : ℕ) (χ : 𝓢(E,ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r M : ℝ) (hr : 0 < r), 0 ≤ M →
      ∀ f : 𝓢(E,F),
      (∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      ‖schwartzToH n (SchwartzMap.smulLeftCLM F χ (r^2 • rescaleSchwartz p r hr.ne' f))‖ ≤ C*M*r^2 := by
  obtain ⟨C,hC,hbound⟩ := cutoff_source_Hnat (E := E) (F := F) n χ hχ
  refine ⟨C,hC,fun p r M hr hM f hb => ?_⟩
  have hder : ∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
      ‖(∂^{m} (r^2 • rescaleSchwartz p r hr.ne' f)) x‖ ≤ M*r^2 := by
    intro k hk m hm x
    rw [iteratedLineDerivOp_smul,rescaleSchwartz_iterated]
    simp only [smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le 2),abs_of_nonneg (pow_nonneg hr.le k),rescaleSchwartz_apply]
    calc
      r^2*(r^k*‖(∂^{m} f) (r•x+p)‖) ≤ r^2*(r^k*(M/r^k)) := by
        gcongr; exact hb k hk m hm _
      _ = M*r^2 := by field_simp
  exact (hbound _ (M*r^2) (by positivity) hder).trans_eq (by ring)
end TamingCompatibility.HilbertSobolev

end
end

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [TopologicalSpace P]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

theorem parameter_local_source_two_jet (p₀ : P) (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (E₀ : ℝ) (hE : 0 ≤ E₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (p : E) (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      (‖u.toLp 4 (volume : Measure E)‖ + ∑ i,
        ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖ ≤ E₀*M*r^3) →
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (r^2 • rescaleSchwartz p r hr.ne' f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        ‖u (r • x+p)‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤ C*M := by
  classical
  obtain ⟨J,hJ,hjet⟩ := parameter_scaled_two_jet p₀ hdim a ha hac b L d c K hb hc χ hχ
  obtain ⟨N,hN,hsource⟩ := localized_normalized_source_Hnat (E := E) (F := F) 3 ζ hζ
  refine ⟨J*(N+E₀),by positivity,?_⟩
  filter_upwards [hjet] with t hj
  intro r hr hr1 p u f M hM hf he heq x hx
  let fH := schwartzToH 3 (SchwartzMap.smulLeftCLM F ζ (r^2 • rescaleSchwartz p r hr.ne' f))
  have hfn : ‖fH‖ ≤ N*M*r^2 := hsource p r M hr hM f hf
  have h := hj r hr p u fH (fun n hn => by
    rw [show toDistribution E F 3 fH = (SchwartzMap.smulLeftCLM F ζ
      (r^2 • rescaleSchwartz p r hr.ne' f) : 𝓢'(E,F)) from schwartzToH_spec _ _]
    rw [← ComplexMatrix.product_schwartz,local_cutoff_one ζ (χ (n+1)) (hζχ n hn)]
    simpa only [ContinuousLinearMap.map_smul_of_tower] using heq n hn) x
  dsimp only at h
  rw [rescale_cutoff_two_jet (χ 4) p hr u x hx] at h
  let A₀ := ‖u (r • x+p)‖
  let A₁ := ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖
  let A₂ := ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖
  have h0 : 0 ≤ A₀ := norm_nonneg _
  have h1 : 0 ≤ A₁ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h2 : 0 ≤ A₂ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hbound : A₀ + r*A₁ + r^2*A₂ ≤ (J*(N+E₀)*M)*r^2 := by
    apply h.trans
    calc
      _ ≤ J*(N*M*r^2 + r⁻¹*(E₀*M*r^3)) := by gcongr
      _ = _ := by field_simp
  have hscaled : (A₀+A₁+A₂)*r^2 ≤ A₀+r*A₁+r^2*A₂ := by
    have hrr : r^2 ≤ r := by nlinarith
    have hr2 : r^2 ≤ 1 := hrr.trans hr1
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hr2),mul_nonneg h1 (sub_nonneg.mpr hrr)]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp (hscaled.trans hbound)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
