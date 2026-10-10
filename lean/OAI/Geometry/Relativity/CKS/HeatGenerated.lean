import OAI.Geometry.Relativity.CKS.SphereHeat
import OAI.Geometry.Relativity.CKS.InducedSphereCalculus

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

inductive HeatGenerated (p : ℕ → Poly) : (ℝ → E → ℝ) → Prop
  | basic (a : HeatJet) : HeatGenerated p (spatialHeat p a)
  | zero : HeatGenerated p (fun _ _ => 0)
  | add {F G} : HeatGenerated p F → HeatGenerated p G →
      HeatGenerated p (fun t x => F t x + G t x)
  | coeff (c : E → ℝ) {F} : ContDiffOn ℝ ∞ c U → HeatGenerated p F →
      HeatGenerated p (fun t x => c x * F t x)
  | congr {F G} : HeatGenerated p F → (∀ t x, x ∈ U → F t x = G t x) →
      HeatGenerated p G

variable {p : ℕ → Poly} (hp : PolynomialRapid p)
include hp

lemma HeatGenerated.joint_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain := by
  induction hF with
  | basic a => exact jointHeatSeries_smooth p hp a
  | zero => exact contDiffOn_const
  | add _ _ hF hG => exact hF.add hG
  | coeff c hc _ hF =>
    exact (hc.comp contDiffOn_snd (fun z hz => hz)).mul hF
  | congr _ he hF =>
    exact hF.congr (fun z hz => (he z.1 z.2 hz).symm)

lemma HeatGenerated.spatial_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U :=
  (hF.joint_smooth hp).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

lemma HeatGenerated.temporal_diff {F : ℝ → E → ℝ} (hF : HeatGenerated p F)
    (t : ℝ) {x : E} (hx : x ∈ U) : DifferentiableAt ℝ (fun s => F s x) t := by
  have h := (hF.joint_smooth hp).comp (contDiffOn_id.prodMk contDiffOn_const)
    (s := (Set.univ : Set ℝ)) (fun _ _ => hx)
  exact ((contDiffOn_univ.mp h).differentiable (by simp)).differentiableAt

omit hp in
lemma HeatGenerated.sum {J : Type*} (s : Finset J) {F : J → ℝ → E → ℝ}
    (h : ∀ j ∈ s, HeatGenerated p (F j)) :
    HeatGenerated p (fun t x => ∑ j ∈ s, F j t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HeatGenerated.zero (p := p))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (mem_insert_self j s)).add (ih (fun k hk => h k (mem_insert_of_mem hk)))

omit hp in
lemma angularCoefficient_smooth (i : Ix) :
    ContDiffOn ℝ ∞ (fun x : E => x i / ‖x‖ ^ 2) U := by
  have hn : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) U := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact (coordinate_smooth i).div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma pd_spatialHeat (a : HeatJet) (t : ℝ) {x : E} (hx : x ∈ U) (j : Ix) :
    pd j (spatialHeat p a t) x =
      ∑ i : Ix, (x i / ‖x‖ ^ 2) * spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [pd, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x)) (0, e j) = _
  simp only [Fintype.sum_option, add_apply,
    _root_.sum_apply, smul_apply, heatField,
    angularField, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero, zero_add,
    Fintype.sum_prod_type, EuclideanSpace.proj, PiLp.proj_apply, e_apply, heatNext]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply sum_congr rfl
  intro i hi
  exact mul_comm _ _

lemma HeatGenerated.partial {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (j : Ix) :
    HeatGenerated p (fun t x => pd j (F t) x) := by
  induction hF with
  | basic a =>
    apply HeatGenerated.congr (HeatGenerated.sum univ (fun i _ =>
      HeatGenerated.coeff _ (angularCoefficient_smooth i) (HeatGenerated.basic (a.1,(i,j)::a.2))))
    intro t x hx
    exact (pd_spatialHeat hp a t hx j).symm
  | zero => simpa only [pd_const] using (HeatGenerated.zero (p := p))
  | @add F G hF hG ihF ihG =>
    apply HeatGenerated.congr (ihF.add ihG)
    intro t x hx
    exact (pd_add (smooth_diff (hF.spatial_smooth hp t) hx)
      (smooth_diff (hG.spatial_smooth hp t) hx) j).symm
  | @coeff c F hc hF ih =>
    apply HeatGenerated.congr ((HeatGenerated.coeff _ (partial_smooth hc j) hF).add
      (HeatGenerated.coeff _ hc ih))
    intro t x hx
    exact (pd_mul (smooth_diff hc hx) (smooth_diff (hF.spatial_smooth hp t) hx) j).symm
  | @congr F G hF he ih =>
    apply HeatGenerated.congr ih
    intro t x hx
    have he' : F t =ᶠ[𝓝 x] G t := by
      filter_upwards [U_open.mem_nhds hx] with y hy
      exact he t y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (e j)) he'.fderiv_eq

def td (F : ℝ → E → ℝ) (t : ℝ) (x : E) : ℝ := deriv (fun s => F s x) t

lemma HeatGenerated.time {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    HeatGenerated p (td F) := by
  induction hF with
  | basic a =>
    apply HeatGenerated.congr (HeatGenerated.basic (a.1+1,a.2))
    intro t x hx
    exact (spatialHeat_time_derivative p hp a t hx).deriv.symm
  | zero =>
    change HeatGenerated p (fun t x => deriv (fun _ : ℝ => (0 : ℝ)) t)
    simpa only [deriv_const] using (HeatGenerated.zero (p := p))
  | @add F G hF hG ihF ihG =>
    apply HeatGenerated.congr (ihF.add ihG)
    intro t x hx
    exact (deriv_fun_add (hF.temporal_diff hp t hx) (hG.temporal_diff hp t hx)).symm
  | @coeff c F hc hF ih =>
    apply HeatGenerated.congr (HeatGenerated.coeff c hc ih)
    intro t x hx
    exact (deriv_const_mul (c x) (hF.temporal_diff hp t hx)).symm
  | @congr F G hF he ih =>
    apply HeatGenerated.congr ih
    intro t x hx
    unfold td
    congr 1
    funext s
    exact he s x hx

lemma HeatGenerated.decay {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      ‖F t x‖ ≤ C * Real.exp (-6 * t) := by
  induction hF with
  | basic a =>
    let C := ∑' n, CKSSpectralHeat.eigenvalue n ^ a.1 * ‖sphereEval (rotationWord a.2 (p n))‖
    refine ⟨C, tsum_nonneg (fun n => mul_nonneg (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le _) (norm_nonneg _)), ?_⟩
    intro t ht x hx
    let s : Sphere := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
    have he : spatialHeat p a t x = sphereHeatJet p a t s := (sphereHeatJet_eq p hp a t s).symm
    rw [he]
    exact ((sphereHeatJet p a t).norm_coe_le_norm s).trans
      (by simpa only [mul_comm, C] using sphereHeatJet_decay p hp a ht)
  | zero =>
    exact ⟨0, le_rfl, by intros; simp⟩
  | @add F G hF hG ihF ihG =>
    obtain ⟨C, hC, hbC⟩ := ihF
    obtain ⟨D, hD, hbD⟩ := ihG
    refine ⟨C+D, add_nonneg hC hD, fun t ht x hx => ?_⟩
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hbC t ht x hx) (hbD t ht x hx))
  | @coeff c F hc hF ih =>
    obtain ⟨C, hC, hb⟩ := ih
    let cr := smoothRestriction c hc
    refine ⟨‖cr‖ * C, mul_nonneg (norm_nonneg _) hC, fun t ht x hx => ?_⟩
    let s : Sphere := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
    have hc' : ‖c x‖ ≤ ‖cr‖ := cr.norm_coe_le_norm s
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hc' (hb t ht x hx) (norm_nonneg _) (norm_nonneg _)
  | @congr F G hF he ih =>
    obtain ⟨C, hC, hb⟩ := ih
    refine ⟨C, hC, fun t ht x hx => ?_⟩
    rw [← he t x (by intro h; simp [h] at hx)]
    exact hb t ht x hx

end
end CKSInducedSphere

end

end OAI
