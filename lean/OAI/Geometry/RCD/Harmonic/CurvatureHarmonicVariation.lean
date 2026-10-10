import OAI.Geometry.RCD.Sobolev.UniformEventualLowerEnergy
import OAI.Geometry.RCD.Sobolev.SupportedGammaIntegral
import OAI.Geometry.RCD.Sobolev.RescaledLocalEnergyBound
import OAI.Geometry.RCD.Sobolev.DirichletTestRecoverySequence
import OAI.Geometry.RCD.Sobolev.CorrectionInteriorEnergy

namespace OAI

/-! # The variational lower bound for actual harmonic perturbations

The test is in the original Dirichlet space. Its compact support makes the
mixed source energy vanish on any containing interior ball.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.curvature_harmonic_variation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R c : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S) (hcR : c<R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (g ψ : Euclidean n → ℝ)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    {L : ℝ≥0} (hψ : LipschitzWith L ψ)
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (q : ∀ k, SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball (p k) (S*r k)))
    (hqconv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k).val x-ψ (v k x)|≤δ)
    (hqzero : ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p k) (c*r k) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k).val x=0)
    {M Q P : ℝ} (hM : 0≤M) (hQ : 0≤Q)
    (hwb : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    (hqb : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k).val (q k).val x≤Q)
    (hqupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))*
        (∫ x in ball (p k) (S*r k), localGamma (hausdorff n X) hX.quadratic
          (q k).val (q k).val x ∂hausdorff n X)≤P+δ)
    (t : ℝ) :
    (∫ z in ball 0 ρ, ‖fderiv ℝ (fun y => g y+t*ψ y) z‖^2)≤
      volume.real (ball (0:Euclidean n) S)*(M+t^2*P) := by
  let μ := hausdorff n X
  let F := fun k => w k+t • (q k).val
  have hFconv (W : ℝ) (hW : 0<W) (hWS : W<S) (δ : ℝ) (hδ : 0<δ) :
      ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hX.quadratic (F k) x-(g (v k x)+t*ψ (v k x))|≤δ := by
    let a := δ/(2*(1+|t|))
    have ha : 0<a := div_pos hδ (by positivity)
    have hsub (k : ℕ) : ball (p k) (W*r k)⊆ball (p k) (S*r k) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right hWS.le (hr k).le)
    filter_upwards [hconv W hW hWS a ha,hqconv a ha] with k hk hqk
    have hqk' := ae_mono (Measure.restrict_mono (hsub k) le_rfl) hqk
    filter_upwards [hk,hqk',ae_restrict_of_ae (Lp.coeFn_add
      (SobolevSpace.toLp μ hX.quadratic (w k))
      (SobolevSpace.toLp μ hX.quadratic (t • (q k).val))),
      ae_restrict_of_ae (Lp.coeFn_smul t (SobolevSpace.toLp μ hX.quadratic (q k).val))]
      with x hx hqx hadd hsmul
    have he : SobolevSpace.toLp μ hX.quadratic (F k) x=
        SobolevSpace.toLp μ hX.quadratic (w k) x+t*SobolevSpace.toLp μ hX.quadratic (q k).val x := by
      simpa only [F,map_add,map_smul,smul_eq_mul,Pi.add_apply,Pi.smul_apply] using hadd.trans (congrArg
        (fun z => SobolevSpace.toLp μ hX.quadratic (w k) x+z) hsmul)
    rw [he]
    calc
      _ = |(SobolevSpace.toLp μ hX.quadratic (w k) x-g (v k x))+
          t*(SobolevSpace.toLp μ hX.quadratic (q k).val x-ψ (v k x))| := by congr 1; ring
      _ ≤ |SobolevSpace.toLp μ hX.quadratic (w k) x-g (v k x)|+
          |t| * |SobolevSpace.toLp μ hX.quadratic (q k).val x-ψ (v k x)| :=
        (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ a+|t| * a := add_le_add hx (mul_le_mul_of_nonneg_left hqx (abs_nonneg _))
      _ ≤ δ := by dsimp only [a]; field_simp; nlinarith [abs_nonneg t]
  have hFlip : ∀ W<S, ∃ B : ℝ≥0, LipschitzOnWith B (fun y => g y+t*ψ y) (closedBall 0 W) := by
    intro W hWS
    obtain ⟨B,hB⟩ := hg W hWS
    exact ⟨_,hB.add ((lipschitzWith_smul t).comp hψ).lipschitzOnWith⟩
  have hFb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma μ hX.quadratic (F k) (F k) x≤2*M+2*t^2*Q := by
    filter_upwards [hqb] with k hk
    filter_upwards [hwb k,ae_restrict_of_ae hk,
      ae_restrict_of_ae (localGamma_add_self_le μ hX.quadratic (w k) (t • (q k).val)),
      ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic t (q k).val (t • (q k).val)),
      ae_restrict_of_ae (localGamma_smul_right μ hX.quadratic t (q k).val (q k).val)]
      with x hwx hqx hx hl hr'
    have ht : localGamma μ hX.quadratic (t • (q k).val) (t • (q k).val) x=
        t^2*localGamma μ hX.quadratic (q k).val (q k).val x := by rw [hl,hr']; ring
    rw [ht] at hx
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (r k))
    nlinarith [mul_le_mul_of_nonneg_left hqx (sq_nonneg t)]
  have hFupper (δ : ℝ) (hδ : 0<δ) : ∀ᶠ k in atTop,
      (r k^2/μ.real (ball (p k) (S*r k)))*
        (∫ x in closedBall (p k) (R*r k), localGamma μ hX.quadratic (F k) (F k) x ∂μ)≤
          (M+t^2*P)+δ := by
    let a := δ/(1+t^2)
    have ha : 0<a := div_pos hδ (by positivity)
    filter_upwards [hqupper a ha] with k hk
    have hsub : closedBall (p k) (R*r k)⊆ball (p k) (S*r k) :=
      closedBall_subset_ball (mul_lt_mul_of_pos_right hRS (hr k))
    have hzeroA : ∀ᵐ x ∂μ, x∉closedBall (p k) (R*r k) → SobolevSpace.toLp μ hX.quadratic (q k).val x=0 :=
      (hqzero k).mono fun x hx hn => hx (fun hm => hn (ball_subset_closedBall
        ((ball_subset_ball (mul_le_mul_of_nonneg_right hcR.le (hr k).le)) hm)))
    have hzeroU : ∀ᵐ x ∂μ, x∉ball (p k) (S*r k) → SobolevSpace.toLp μ hX.quadratic (q k).val x=0 :=
      hzeroA.mono fun x hx hn => hx (fun hm => hn (hsub hm))
    have horth : (∫ x in closedBall (p k) (R*r k), localGamma μ hX.quadratic (w k) (q k).val x ∂μ)=0 := by
      rw [supported_gamma_integral μ hX.quadratic _ _ _ hzeroA,
        ← supported_gamma_integral μ hX.quadratic _ _ _ hzeroU]
      exact recovered_dirichlet_harmonic_pairing_zero μ hX.quadratic measurableSet_ball (hw k) (q k)
    have hqe : (∫ x in closedBall (p k) (R*r k), localGamma μ hX.quadratic (q k).val (q k).val x ∂μ)=
        ∫ x in ball (p k) (S*r k), localGamma μ hX.quadratic (q k).val (q k).val x ∂μ := by
      rw [supported_gamma_integral μ hX.quadratic _ _ _ hzeroA,
        supported_gamma_integral μ hX.quadratic _ _ _ hzeroU]
    have hpos : 0<μ.real (ball (p k) (S*r k)) := ENNReal.toReal_pos
      (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hX.finiteOnBounded _ isBounded_ball).ne
    have hb := rescaled_local_energy_bound μ hX.quadratic (w k) hsub
      (hX.finiteOnBounded _ isBounded_ball).ne hpos hM (hwb k)
    change _≤P+a at hk
    change _≤M at hb
    dsimp only [F]
    rw [integral_harmonic_perturbation μ hX.quadratic _ _ t _ horth,hqe,mul_add]
    have he : (r k^2/μ.real (ball (p k) (S*r k)))*
        (t^2*∫ x in ball (p k) (S*r k), localGamma μ hX.quadratic (q k).val (q k).val x ∂μ)=
        t^2*((r k^2/μ.real (ball (p k) (S*r k)))*
          ∫ x in ball (p k) (S*r k), localGamma μ hX.quadratic (q k).val (q k).val x ∂μ) := by ring
    rw [he]
    have hh := add_le_add hb (mul_le_mul_of_nonneg_left hk (sq_nonneg t))
    apply hh.trans
    have he' : a*(1+t^2)=δ := by dsimp only [a]; field_simp
    nlinarith [ha.le]
  exact (hX.gradient_energy_lower_of_curvature_eventual_sequence hn hS hτ hρτ hτR hRS p r ε v
    hr hcurv hε hε1 hεlim hv F (fun y => g y+t*ψ y) hFlip hFconv
    (by positivity : 0≤2*M+2*t^2*Q) hFb hFupper).2

end RegularPointCoordinates

end

end OAI
