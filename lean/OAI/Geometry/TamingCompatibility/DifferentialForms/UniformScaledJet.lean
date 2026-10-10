import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalRescaleH1
import OAI.Geometry.TamingCompatibility.Elliptic.UniformBootstrap

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

theorem uniform_scaled_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 0) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) 0)
    (b : ℝ → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : ℝ → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) 0)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) 0)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝 (0:ℝ), ∀ (hr : 0 < r) (p : E)
      (u : 𝓢(E,F)) (f : H E F 3),
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a r) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b r) L d (c r) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (toDistribution E F 3 f)) →
      ∀ x : E, let w := SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)
        ‖w x‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} w) x‖ +
          ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} w)) x‖ ≤
        C * (‖f‖ + r⁻¹ * (‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖)) := by
  classical
  obtain ⟨B,hB,hbound⟩ := uniform_finite_bootstrap 3 a ha hac b L d c K hb hc χ hχ
  obtain ⟨T,hT,hscale⟩ := cutoff_rescale_H1 (F := F) hdim (χ 0)
  obtain ⟨J,hJ,hjet⟩ := schwartz_two_jet_bound (F := F) (stdOrthonormalBasis ℝ E) 5
    (by rw [hdim]; norm_num)
  refine ⟨J*B*(1+T),by positivity,?_⟩
  filter_upwards [hbound] with r hrbound
  intro hr p u f heq x
  let v := fun n : ℕ => schwartzToH ((n:ℝ)+1)
    (SchwartzMap.smulLeftCLM F (χ n) (rescaleSchwartz p r hr.ne' u))
  have hv (n : ℕ) (_hn : n ≤ 3+1) : toDistribution E F ((n:ℝ)+1) (v n) =
      smulLeftCLM F (χ n) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) := by
    dsimp only [v]
    rw [schwartzToH_spec,ComplexMatrix.product_schwartz]
  have h := hrbound (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) f v hv heq
  let S := ‖u.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖
  have hS : 0 ≤ S := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hv0 : ‖v 0‖ ≤ T*r⁻¹*S := by
    have he : ((0:ℕ):ℝ)+1 = 1 := by norm_num
    dsimp only [v]
    rw [he]
    exact hscale p r hr u
  have hv4 : schwartzToH 5 (SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)) = v 4 := by
    have he : ((4:ℕ):ℝ)+1 = 5 := by norm_num
    dsimp only [v]
    rw [he]
  change _ ≤ J*B*(1+T) * (‖f‖ + r⁻¹*S)
  apply (hjet (SchwartzMap.smulLeftCLM F (χ 4) (rescaleSchwartz p r hr.ne' u)) x).trans
  rw [hv4]
  calc
    J*‖v 4‖ ≤ J*(B*(‖f‖+‖v 0‖)) := mul_le_mul_of_nonneg_left h hJ
    _ ≤ J*(B*(‖f‖+T*r⁻¹*S)) := by gcongr
    _ ≤ J*B*(1+T)*(‖f‖+r⁻¹*S) := by
      have h₀ : 0 ≤ T*‖f‖ := mul_nonneg hT (norm_nonneg f)
      have h₁ : 0 ≤ r⁻¹*S := mul_nonneg (inv_nonneg.mpr hr.le) hS
      nlinarith [mul_nonneg (mul_nonneg hJ hB.le) (add_nonneg h₀ h₁)]
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_Hsucc_norm_le (s : ℝ) (f : 𝓢(E,F)) :
    ‖schwartzToH (s+1) f‖ ≤ ‖schwartzToH s f‖ + |((2*Real.pi)^2)⁻¹| *
      ∑ i, ‖derivative (F := F) s (stdOrthonormalBasis ℝ E i)‖ *
        ‖schwartzToH s (∂_{stdOrthonormalBasis ℝ E i} f)‖ := by
  have h := norm_le_gradient s (schwartzToH (s+1) f)
  rw [schwartzToH_inclusion] at h
  have hd (i : basisIndex E) : derivative (s+1) (stdOrthonormalBasis ℝ E i) (schwartzToH (s+1) f) =
      schwartzToH s (∂_{stdOrthonormalBasis ℝ E i} f) := by
    have h' := schwartzToH_derivative (s+1) (stdOrthonormalBasis ℝ E i) f
    rw [add_sub_cancel_right] at h'
    exact h'.symm
  simpa only [hd] using h

omit [CompleteSpace F] in
lemma schwartz_L2_support_bound (R : ℝ) {M : ℝ} (hM : 0 ≤ M) (f : 𝓢(E,F))
    (hs : tsupport f ⊆ Metric.ball 0 R) (hb : ∀ x, ‖f x‖ ≤ M) :
    ‖f.toLp 2 (volume : Measure E)‖ ≤ M * (volume (Metric.ball (0:E) R)).toReal^(1/2:ℝ) := by
  have h := eLpNorm_sub_le_of_dist_bdd (volume : Measure E)
    (p := 2) (by norm_num) measurableSet_ball.nullMeasurableSet hM
    (f := (f : E → F)) (g := 0)
    (f.continuous.aestronglyMeasurable.sub aestronglyMeasurable_zero)
    (fun x => by simpa using hb x)
    ((subset_tsupport _).trans hs) (by simp)
  norm_num at h
  have hfin : ENNReal.ofReal M * volume (Metric.ball (0:E) R) ^ (1/2:ℝ) ≠ ⊤ := by finiteness
  have hh := ENNReal.toReal_mono hfin h
  rw [SchwartzMap.norm_toLp]
  simpa only [ENNReal.toReal_mul,← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hM] using hh

theorem schwartz_Hnat_support_bound (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      tsupport f ⊆ Metric.ball 0 R →
      (∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M) →
      ‖schwartzToH n f‖ ≤ C*M := by
  classical
  induction n with
  | zero =>
    refine ⟨(volume (Metric.ball (0:E) R)).toReal^(1/2:ℝ),by positivity,fun f M hM hs hb => ?_⟩
    rw [Nat.cast_zero,schwartzToH_zero]
    exact (schwartz_L2_support_bound R hM f hs (hb 0 le_rfl (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))).trans_eq (mul_comm _ _)
  | succ n ih =>
    obtain ⟨C,hC,hh⟩ := ih
    let D := |((2*Real.pi)^2)⁻¹| * ∑ i, ‖derivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)‖
    have hD : 0 ≤ D := by positivity
    refine ⟨(1+D)*C,by positivity,fun f M hM hs hb => ?_⟩
    have h0 := hh f M hM hs (fun k hk => hb k (by omega))
    have h1 (i : basisIndex E) : ‖schwartzToH n (∂_{stdOrthonormalBasis ℝ E i} f)‖ ≤ C*M := by
      apply hh _ M hM ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hs)
      intro k hk m hm x
      have hb' := hb (k+1) (by omega) (Fin.snoc m (stdOrthonormalBasis ℝ E i))
        (by intro j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [hm]) x
      simpa only [iteratedLineDerivOp_succ_right,Fin.init_snoc,Fin.snoc_last] using hb'
    rw [Nat.cast_succ]
    apply (schwartz_Hsucc_norm_le (n:ℝ) f).trans
    calc
      _ ≤ C*M + |((2*Real.pi)^2)⁻¹| *
          ∑ i, ‖derivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)‖ * (C*M) := by
        gcongr with i; exact h1 i
      _ = ((1+D)*C)*M := by dsimp [D]; rw [← Finset.sum_mul]; ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_iterated (p : E) (r : ℝ) (hr : r ≠ 0) (f : 𝓢(E,F))
    {k : ℕ} (m : Fin k → E) :
    ∂^{m} (rescaleSchwartz p r hr f) = r^k • rescaleSchwartz p r hr (∂^{m} f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left,ih,lineDerivOp_smul,rescaleSchwartz_derivative,
      ← smul_assoc,smul_eq_mul,← pow_succ,iteratedLineDerivOp_succ_left]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
