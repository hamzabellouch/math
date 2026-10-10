import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma curve_deriv_eq_active_pairing {v : M → ℝ} (hv : Continuous v)
    {γ : ℝ → M} {t d : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    (hd : HasDerivAt (fun s => cTransform v (γ s)) d t)
    {p : TangentSpace 𝓘(ℝ,Model n) (γ t)} (hp : p∈activeLogs v (γ t)) :
    d=inner ℝ p (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1) := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun s : ℝ => cTransform v (γ s)+2*cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))
  have hmin : IsLocalMin f t := by
    apply Filter.Eventually.of_forall
    intro s
    have H := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (γ s)
    dsimp [f]
    linarith
  have hc : HasDerivAt
      (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p)))
      (inner ℝ (-((1/2:ℝ) • p)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1)) t := by
    let D : ℝ →L[ℝ] ℝ := (innerSL ℝ (-((1/2:ℝ) • p))).comp
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) t D :=
      (cost_start_gradient_of_injectivityDomain hID).comp t hγ.hasMFDerivAt
    have hfd : HasFDerivAt
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) D t :=
      hcomp.hasFDerivAt
    exact hfd.hasDerivAt
  have H := hmin.hasDerivAt_eq_zero (hd.add (hc.const_mul (2:ℝ)))
  simp only [inner_neg_left,real_inner_smul_left] at H
  linarith only [H]

lemma curve_neg_cost_deriv_eq_pairing {γ : ℝ → M} {t d : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    {p : TangentSpace 𝓘(ℝ,Model n) (γ t)} (hp : p∈minimizingVectors (γ t))
    (hd : HasDerivAt (fun s => -cost (γ s) (riemannianExp (γ t) p)) d t) :
    d=inner ℝ p (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1) := by
  have hID := contracted_minimizer_mem_injectivityDomain hp
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun s : ℝ => -cost (γ s) (riemannianExp (γ t) p)+
    2*cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))
  have hmin : IsLocalMin f t := by
    apply Filter.Eventually.of_forall
    intro s
    have H := minimizing_split_upper_support hp
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (γ s)
    have H0 := minimizing_split_contact hp
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
    dsimp [f]
    linarith only [H,H0]
  have hc : HasDerivAt
      (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p)))
      (inner ℝ (-((1/2:ℝ) • p)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1)) t := by
    let D : ℝ →L[ℝ] ℝ := (innerSL ℝ (-((1/2:ℝ) • p))).comp
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) t D :=
      (cost_start_gradient_of_injectivityDomain hID).comp t hγ.hasMFDerivAt
    have hfd : HasFDerivAt
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) D t :=
      hcomp.hasFDerivAt
    exact hfd.hasDerivAt
  have H := hmin.hasDerivAt_eq_zero (hd.add (hc.const_mul (2:ℝ)))
  simp only [inner_neg_left,real_inner_smul_left] at H
  linarith only [H]

lemma spray_neg_cost_deriv_le {z : TangentBundle 𝓘(ℝ,Model n) M} {t d : ℝ} {y : M}
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t) :
    d ≤ dist (sprayFlow t z).1 y*‖z.2‖ := by
  obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) (sprayFlow t z).1 y
  have hproj := hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt t)
  have H := curve_neg_cost_deriv_eq_pairing hproj.mdifferentiableAt hp (by simpa only [he] using hd)
  have hvel : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) (fun s => (sprayFlow s z).1) t (1:ℝ)=
      (sprayFlow t z).2 := spray_velocity_eq_mfderiv ((sprayFlow_curve z).isMIntegralCurveAt t)
  have H' : d=inner ℝ p (sprayFlow t z).2 :=
    H.trans (congrArg (fun q => inner ℝ p q) hvel)
  rw [H']
  have hn : dist (sprayFlow t z).1 y=‖p‖ := by
    change dist (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p)=‖p‖ at hp
    rwa [he] at hp
  rw [hn]
  exact (real_inner_le_norm _ _).trans_eq (by rw [sprayFlow_speed])

lemma curve_deriv_le_active_norm {v : M → ℝ} (hv : Continuous v)
    {γ : ℝ → M} {t d : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    (hd : HasDerivAt (fun s => cTransform v (γ s)) d t)
    {p : TangentSpace 𝓘(ℝ,Model n) (γ t)} (hp : p∈activeLogs v (γ t)) :
    d ≤ ‖p‖*‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1‖ := by
  rw [curve_deriv_eq_active_pairing hv hγ hd hp]
  exact real_inner_le_norm _ _

lemma spray_deriv_le_active_norm {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} {t d : ℝ}
    (hd : HasDerivAt (fun s => cTransform v (sprayFlow s z).1) d t)
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs v (sprayFlow t z).1) : d ≤ ‖p‖*‖z.2‖ := by
  have hproj := hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt t)
  have H := curve_deriv_le_active_norm hv hproj.mdifferentiableAt hd hp
  have hvel : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) (fun s => (sprayFlow s z).1) t (1:ℝ)=
      (sprayFlow t z).2 := spray_velocity_eq_mfderiv ((sprayFlow_curve z).isMIntegralCurveAt t)
  exact H.trans_eq (congrArg (fun q => ‖p‖*‖q‖) hvel |>.trans (by rw [sprayFlow_speed]))

end WeakMTWTransport

end

end OAI
