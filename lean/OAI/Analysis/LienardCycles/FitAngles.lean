import OAI.Analysis.LienardCycles.HyperbolicCoordinate

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates PartialCalculus
noncomputable def θ (q : (ℝ × ℝ) × ℝ) : ℝ := angle (A q)
noncomputable def L (q : (ℝ × ℝ) × ℝ) : ℝ := angle (D q)
lemma E_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω E q := by
  apply ContDiffAt.div
  · exact contDiffAt_const.mul (A_analytic hr)
  · exact contDiffAt_snd.mul (contDiffAt_const.sub ((A_analytic hr).pow 2))
  · exact ne_of_gt (mul_pos hr (A_gap_pos hr))
lemma θ_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => θ ((z,k),s)) (J ((z,k),r)-E ((z,k),r)) r := by
  change HasDerivAt (fun s => angle (A ((z,k),s))) _ r
  have h := (angle_deriv (A_abs_lt (q := ((z,k),r)) hr)).comp (h := fun s => A ((z,k),s)) r (A_deriv (z := z) (k := k) hr)
  convert! h using 1
  dsimp only [E]
  field_simp [ne_of_gt (A_gap_pos (q := ((z,k),r)) hr),ne_of_gt hr]
lemma L_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => L ((z,k),s)) (E ((z,k),r)) r := by
  change HasDerivAt (fun s => angle (D ((z,k),s))) _ r
  have h := (angle_deriv (D_abs_lt (q := ((z,k),r)) hr)).comp (h := fun s => D ((z,k),s)) r (D_deriv' (z := z) (k := k) hr)
  convert! h using 1
  field_simp [ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)]
lemma L_tendsto_zero (z k : ℝ) :
    Tendsto (fun r => L ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simpa only [angle_zero,Function.comp_def,L] using ((angle_analytic (by norm_num : |(0:ℝ)|<1)).continuousAt.tendsto.comp (D_tendsto_zero z k))
lemma E_continuousOn (z k : ℝ) : ContinuousOn (fun s => E ((z,k),s)) (Ioi 0) :=
  fun x hs => ((E_analytic (q := ((z,k),x)) hs).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
lemma J_continuousOn (z k : ℝ) : ContinuousOn (fun s => J ((z,k),s)) (Ioi 0) :=
  fun _ hs => (J_deriv hs).continuousAt.continuousWithinAt
lemma integral_E {z k a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, E ((z,k),s))=L ((z,k),b)-L ((z,k),a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [uIcc_of_le hab] at hs
    exact L_deriv (ha.trans_le hs.1)
  · exact ((E_continuousOn z k).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
lemma integral_J {z k a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, J ((z,k),s)) = θ ((z,k),b)-θ ((z,k),a)+(∫ s in a..b, E ((z,k),s)) := by
  have hJ : IntervalIntegrable (fun s => J ((z,k),s)) volume a b := ((J_continuousOn z k).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
  have hE : IntervalIntegrable (fun s => E ((z,k),s)) volume a b := ((E_continuousOn z k).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => θ ((z,k),s)) (f' := fun s => J ((z,k),s)-E ((z,k),s))
    (a := a) (b := b) (fun s hs => θ_deriv (ha.trans_le ((uIcc_of_le hab) ▸ hs).1)) (hJ.sub hE)
  rw [intervalIntegral.integral_sub hJ hE] at he
  linarith
end QuinticLienard.ReferenceCharacteristic

namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic
lemma conditionalE_strictMono {r A₀ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hs : 0 < s) (hsr : s < r) : StrictMono (fun k => E ((label ((k,r),A₀),k),s)) := by
  apply strictMono_of_deriv_pos
  intro k
  let a' := Az ((label ((k,r),A₀),k),s)*(T ((label ((k,r),A₀),k),s)-T ((label ((k,r),A₀),k),r))
  have hd := conditionalA_deriv (k := k) hr hA hs
  have he : HasDerivAt (fun k => E ((label ((k,r),A₀),k),s))
      (K ((label ((k,r),A₀),k),s)*a') k := by
    convert! (hd.const_mul 2).div (((hd.pow 2).const_sub 1).const_mul s)
      (ne_of_gt (mul_pos hs (A_gap_pos (q := ((label ((k,r),A₀),k),s)) hs))) using 1
    dsimp only [E,K,a',Pi.pow_apply]
    field_simp [ne_of_gt hs,ne_of_gt (A_gap_pos (q := ((label ((k,r),A₀),k),s)) hs)]
    ring
  rw [he.deriv]
  exact mul_pos (K_pos hs) (mul_pos (Az_pos hs) (sub_pos.mpr (T_strictAnti _ _ hs hr hsr)))

lemma L_difference_nonneg {r A₀ k₁ k₂ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hk : k₁ ≤ k₂) (hs : 0 < s) (hsr : s ≤ r) :
    0 ≤ L ((label ((k₂,r),A₀),k₂),s)-L ((label ((k₁,r),A₀),k₁),s) := by
  apply monotone_zero_nonneg hs
    (by simpa using (L_tendsto_zero (label ((k₂,r),A₀)) k₂).sub (L_tendsto_zero (label ((k₁,r),A₀)) k₁))
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 s)
    (fun t ht => ((L_deriv ht.1).sub (L_deriv ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => ((L_deriv (interior_subset ht).1).sub (L_deriv (interior_subset ht).1)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [interior_Ioc] at ht
  rw [((L_deriv (z := label ((k₂,r),A₀)) (k := k₂) ht.1).sub (L_deriv ht.1)).deriv]
  exact sub_nonneg.mpr ((conditionalE_strictMono hr hA ht.1 (ht.2.trans_le hsr)).monotone hk)

lemma integral_E_difference_bound {r A₀ k₁ k₂ a b : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hk : k₁ ≤ k₂) (ha : 0 < a) (hab : a ≤ b) (hbr : b ≤ r) :
    0 ≤ (∫ s in a..b, E ((label ((k₂,r),A₀),k₂),s)-E ((label ((k₁,r),A₀),k₁),s)) ∧
    (∫ s in a..b, E ((label ((k₂,r),A₀),k₂),s)-E ((label ((k₁,r),A₀),k₁),s)) ≤
      L ((label ((k₂,r),A₀),k₂),r)-L ((label ((k₁,r),A₀),k₁),r) := by
  have hE (k : ℝ) : IntervalIntegrable (fun s => E ((label ((k,r),A₀),k),s)) volume a b := ((E_continuousOn (label ((k,r),A₀)) k).mono
    (fun t (ht : t ∈ Icc a b) => ha.trans_le ht.1)).intervalIntegrable_of_Icc hab
  have hmono : MonotoneOn (fun t => L ((label ((k₂,r),A₀),k₂),t)-L ((label ((k₁,r),A₀),k₁),t)) (Ioc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 r)
      (fun t ht => ((L_deriv ht.1).sub (L_deriv ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => ((L_deriv (interior_subset ht).1).sub (L_deriv (interior_subset ht).1)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [interior_Ioc] at ht
    rw [((L_deriv (z := label ((k₂,r),A₀)) (k := k₂) ht.1).sub (L_deriv ht.1)).deriv]
    exact sub_nonneg.mpr ((conditionalE_strictMono hr hA ht.1 ht.2).monotone hk)
  rw [intervalIntegral.integral_sub (hE k₂) (hE k₁),integral_E ha hab,integral_E ha hab]
  have h₁ := hmono ⟨ha,hab.trans hbr⟩ ⟨ha.trans_le hab,hbr⟩ hab
  have h₂ := hmono ⟨ha.trans_le hab,hbr⟩ ⟨hr,le_rfl⟩ hbr
  have h₃ := L_difference_nonneg hr hA hk ha (hab.trans hbr)
  constructor <;> linarith
end QuinticLienard.QuadraticFit

end OAI
