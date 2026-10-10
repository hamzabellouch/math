import Mathlib
import OAI.Analysis.Conductivity.Walls.WallMomentIndependence
import OAI.Analysis.Conductivity.Variational.CompactMomentPerturbation
import OAI.Analysis.Conductivity.Variational.HarmonicRankAffine
import OAI.Analysis.Conductivity.Geometry.MatrixPerturbInverse
import OAI.Analysis.Conductivity.Fourier.SmoothHarmonicAnalytic

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

lemma compact_weak_harmonic_laplacian {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f)
    (hw : WeaklyHarmonicOn f U) (hU : IsOpen U) {x : WeylSpace} (hx : x∈U) :
    Δ f x=0 := by
  let F := hc.toSchwartzMap hf
  have hcont : Continuous (Δ f) := by
    change Continuous (fun y => Δ (F : WeylSpace → ℝ) y)
    simpa only [←SchwartzMap.laplacian_apply] using (Δ F).continuous
  have hz : ∀ᵐ y∂volume, y∈U → Δ f y=0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hcont.locallyIntegrable.locallyIntegrableOn U) (by
      intro ψ hψ hcψ hs
      let G := hcψ.toSchwartzMap hψ
      have he := SchwartzMap.integral_mul_laplacian_right_eq_left (μ := volume) F G
      have hwψ := hw ψ hψ hcψ hs
      have he' : (∫ y, f y*Δ ψ y)=(∫ y, Δ f y*ψ y) := by
        have hF : (F : WeylSpace → ℝ) = f := rfl
        have hG : (G : WeylSpace → ℝ) = ψ := rfl
        simp only [SchwartzMap.laplacian_apply] at he
        rw [hF, hG] at he
        exact he
      simpa only [smul_eq_mul,mul_comm] using he'.symm.trans hwψ)
  have he : (fun y => Δ f y) =ᵐ[volume.restrict U] (fun _ => (0:ℝ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hz
  exact Measure.eqOn_open_of_ae_eq he hU hcont.continuousOn continuous_const.continuousOn hx

lemma smooth_weak_harmonic_laplacian {f : WeylSpace → ℝ} {U : Set WeylSpace}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hw : WeaklyHarmonicOn f U)
    (hU : IsOpen U) {x : WeylSpace} (hx : x∈U) : Δ f x=0 := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := {
    rIn := r/2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : WeylSpace → ℝ := fun y => b y*f y
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have he : EqOn f g (Metric.ball x (r/2)) := by
    intro y hy
    have hb : b y=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [g,hb]
  have hwg : WeaklyHarmonicOn g (Metric.ball x (r/2)) :=
    .congr_restrict Metric.isOpen_ball.measurableSet
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (ae_of_all _ he))
      (hw.mono ((Metric.ball_subset_ball (by linarith)).trans hsub))
  have hh := compact_weak_harmonic_laplacian hg hc hwg Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity : 0<r/2))
  have he' : f =ᶠ[𝓝 x] g := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0<r/2)] with y hy
    exact he hy
  rw [(laplacian_congr_nhds he').eq_of_nhds]
  exact hh

theorem weakWeyl_pair_ae_regular {f g : WholeL2} {U : Set WeylSpace}
    (hf : WeaklyHarmonicOn f U) (hg : WeaklyHarmonicOn g U)
    {a : WeylSpace} {R : ℝ} (hR : 0<R) (hball : Metric.closedBall a R⊆U) :
    ∀ᵐ x∂volume, x∈Metric.ball a (R/4) → ∃ r>0,
      Metric.ball x r⊆Metric.ball a (R/4) ∧
      HarmonicPairRegularOn (radialMollify f (R/4)) (radialMollify g (R/4)) (Metric.ball x r) := by
  obtain ⟨hfA,hfe⟩ := weakWeyl_analytic_local hf hR hball
  obtain ⟨hgA,hge⟩ := weakWeyl_analytic_local hg hR hball
  have hb : Metric.ball a (R/4)⊆U :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall).trans hball
  have hfw := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet hfe (hf.mono hb)
  have hgw := WeaklyHarmonicOn.congr_restrict Metric.isOpen_ball.measurableSet hge (hg.mono hb)
  exact analytic_harmonic_ae_regular (EuclideanSpace.basisFun (Fin 3) ℝ) volume
    (analyticNull_euclidean 3) Metric.isOpen_ball (convex_ball _ _).isPreconnected hfA hgA
    (fun x hx => smooth_weak_harmonic_laplacian (weakWeyl_local hf hR hball).1 hfw Metric.isOpen_ball hx)
    (fun x hx => smooth_weak_harmonic_laplacian (weakWeyl_local hg hR hball).1 hgw Metric.isOpen_ball hx)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {ι P : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

omit [DecidableEq ι] in
lemma compactCrossMoment_eval {χ : ℝ → ℝ} {w v : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,Continuous (fun s => w s j)) (hv : ∀ i,Continuous (fun s => v s i))
    (a : ι → ℝ) (i : ι) :
    (∫ s,χ s*(a ⬝ᵥ w s)*v s i)=(compactCrossMoment χ w v*ᵥa) i := by
  change (∫ s,χ s*(a ⬝ᵥ w s)*v s i)=∑ j,compactCrossMoment χ w v i j*a j
  calc
    _ = ∫ s,∑ j,(χ s*w s j*v s i)*a j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [dotProduct,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by
      have hi (j : ι) : Integrable (fun s => (χ s*w s j*v s i)*a j) :=
        (((hc.mul (hw j)).mul (hv i)).integrable_of_hasCompactSupport
          (hs.mul_right.mul_right)).mul_const _
      rw [integral_finsetSum _ (fun j _ => hi j)]
      simp only [integral_mul_const,compactCrossMoment]

theorem compactMoment_uniform_inverse {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    {v : P → ℝ → ι → ℝ} {p₀ : P}
    (hc : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => w s j))
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i))
    (hlim : v p₀=w) (hG : (compactMomentGram χ w).PosDef) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀, ∀ b : ι → ℝ,
      ∃ a : ι → ℝ, (∀ i,‖a i‖≤C*‖b‖) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => χ s*(a ⬝ᵥ w s)) ∧
        HasCompactSupport (fun s => χ s*(a ⬝ᵥ w s)) ∧
        tsupport (fun s => χ s*(a ⬝ᵥ w s))⊆tsupport χ ∧
        (∀ i,(∫ s,χ s*(a ⬝ᵥ w s)*v p s i)=b i) := by
  have hM := compactCrossMoment_continuous hc.continuous hs (fun j => (hw j).continuous) hv
  have hM₀ : IsUnit (compactCrossMoment χ w (v p₀)) := by
    rw [hlim,compactCrossMoment_self]
    exact hG.isUnit
  obtain ⟨C,hC,hne⟩ := matrix_inverse_locally_bounded hM.continuousAt hM₀
  refine ⟨C,hC,?_⟩
  filter_upwards [hne] with p hp
  intro b
  let a := (compactCrossMoment χ w (v p))⁻¹*ᵥb
  obtain ⟨ha,hb⟩ := hp.2 b
  refine ⟨a,hb,hc.mul (ContDiff.sum fun j _ => contDiff_const.mul (hw j)),
    hs.mul_right,tsupport_mul_subset_left,?_⟩
  intro i
  have hvp (j : ι) : Continuous (fun s => v p s j) :=
    (hv j).comp (continuous_const.prodMk continuous_id)
  rw [compactCrossMoment_eval hc.continuous hs (fun j => (hw j).continuous) hvp]
  exact congrFun ha i

theorem wall_moment_uniform_inverse {l r σ lam : ℝ} (hlr : l<r)
    (hσ : σ≠0) (hlam : lam≠0) {v : P → ℝ → Fin 3 → ℝ} {p₀ : P}
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i))
    (hlim : v p₀=wallMomentBasis σ lam) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆Icc l r ∧ ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,∀ b : Fin 3 → ℝ,
        ∃ a : Fin 3 → ℝ, (∀ i,‖a i‖≤C*‖b‖) ∧
          ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => χ s*(a ⬝ᵥ wallMomentBasis σ lam s)) ∧
          HasCompactSupport (fun s => χ s*(a ⬝ᵥ wallMomentBasis σ lam s)) ∧
          tsupport (fun s => χ s*(a ⬝ᵥ wallMomentBasis σ lam s))⊆Icc l r ∧
          (∀ i,(∫ s,χ s*(a ⬝ᵥ wallMomentBasis σ lam s)*v p s i)=b i) := by
  obtain ⟨χ,hc,hs,hn,hp,hsub⟩ := positive_interval_bump hlr
  have hG := compactMomentGram_posDef hc.continuous hs
    (fun i => (wallMomentBasis_smooth σ lam i).continuous) hn hp
    (wallMomentBasis_independent hlr hσ hlam)
  obtain ⟨C,hC,he⟩ := compactMoment_uniform_inverse hc hs (wallMomentBasis_smooth σ lam) hv hlim hG
  refine ⟨χ,hc,hs,hsub,C,hC,?_⟩
  filter_upwards [he] with p hpe
  intro b
  obtain ⟨a,ha,hsmo,hcs,ht,hi⟩ := hpe b
  exact ⟨a,ha,hsmo,hcs,ht.trans hsub,hi⟩

end ScalarConductivity

end

end OAI
