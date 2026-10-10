import OAI.Geometry.RCD.Sobolev.ContinuousLocalGradientBound
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives
import OAI.Geometry.RCD.Harmonic.GramDirectionalError

namespace OAI

/-! # Exact metric contraction from an orthonormal Sobolev Gram matrix -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem localGamma_column_orthonormal (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (S : Set X)
    (hgram : ∀ i j, localGamma μ hQ (u i) (u j) =ᵐ[μ.restrict S]
      fun _ => if i=j then 1 else 0) (a : Euclidean n) :
    localGamma μ hQ (sobolevColumnMap μ hQ u a) (sobolevColumnMap μ hQ u a)
      =ᵐ[μ.restrict S] fun _ => ‖a‖^2 := by
  classical
  have hall : ∀ᵐ x ∂μ.restrict S, ∀ i j, localGamma μ hQ (u i) (u j) x=
      if i=j then 1 else 0 := by
    exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hgram i j
  filter_upwards [hall,ae_restrict_of_ae (localGamma_column_pair μ hQ u a a)] with x hx he
  rw [he]
  simp_rw [hx]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial] using
    (real_inner_self_eq_norm_sq a)

include X in
theorem NoncollapsedRCD.orthonormal_coordinates_lipschitz {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (p : X) {R : ℝ} (hR : 0<R)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hv : ContinuousOn v (ball p (8*R)))
    (hu : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i)
      =ᵐ[(hausdorff n X).restrict (ball p (8*R))] fun x => v x i)
    (hgram : ∀ i j, localGamma (hausdorff n X) hX.quadratic (u i) (u j)
      =ᵐ[(hausdorff n X).restrict (ball p (8*R))] fun _ => if i=j then 1 else 0) :
    LipschitzOnWith 1 v (ball p R) := by
  have hdir (a : Euclidean n) : LipschitzOnWith ⟨‖a‖,norm_nonneg a⟩
      (fun x => ⟪v x,a⟫_ℝ) (ball p R) := by
    apply hX.continuous_local_gradient_lipschitz hn
      (sobolevColumnMap (hausdorff n X) hX.quadratic u a) _ p hR
      ⟨‖a‖,norm_nonneg a⟩ (hv.inner continuousOn_const)
      (sobolevColumnMap_representative (hausdorff n X) hX.quadratic u _ v hu a)
    exact (localGamma_column_orthonormal (hausdorff n X) hX.quadratic u _ hgram a).mono
      fun _ hx => hx.le
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let z := v x-v y
  have hz : ‖z‖^2≤‖z‖*dist x y := by
    have hh := (hdir z).dist_le_mul x hx y hy
    rw [Real.dist_eq,← inner_sub_left] at hh
    change |⟪z,z⟫_ℝ|≤‖z‖*dist x y at hh
    simpa only [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg ‖z‖)] using hh
  change ‖z‖≤(1:ℝ)*dist x y
  nlinarith [norm_nonneg z,dist_nonneg (x:=x) (y:=y)]

end RegularPointCoordinates

end

end OAI
