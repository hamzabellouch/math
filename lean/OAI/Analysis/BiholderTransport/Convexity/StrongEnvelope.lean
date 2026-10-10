import Mathlib
import OAI.Analysis.BiholderTransport.Contact.MatchedSupports
import OAI.Analysis.BiholderTransport.LinearAlgebra.OuterDisplacementJetBound

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S T : Set E} {w F : E → ℝ} {C : E → E → ℝ} {Y : E → E}
  {m K B : ℝ}

lemma strongly_convex_minimizer_unique {f : E → ℝ} {x y:E}
    (hm : 0 < m) (hf : StrongConvexOn S m f) (hx : x∈S) (hy : y∈S)
    (hmin : IsMinOn f S x) (heq : f x=f y) : x=y := by
  have H := StrongConvexOn.quadratic_growth_half hf hx hy hmin
  rw [heq] at H
  have hnonneg := sq_nonneg ‖y-x‖
  have hs : ‖y-x‖^2=0 := by nlinarith only [H,hm,hnonneg]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))).symm

lemma strong_envelope_minimizer_lipschitz (hm :  0 < m) (hK :  0 ≤ K)
    (hY : ∀ z∈T,Y z∈S)
    (hval : ∀ z∈T,F z=w (Y z)+C (Y z) z)
    (hmin : ∀ z∈T,∀ y∈S,F z≤w y+C y z)
    (hstrong : ∀ z∈T,StrongConvexOn S m (fun y => w y+C y z))
    (hcross : ∀ y∈S,∀ y'∈S,∀ z∈T,∀ z'∈T,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖) :
    LipschitzOnWith (Real.toNNReal (2*K/m)) Y T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz z' hz'
  have hy := hY z hz
  have hy' := hY z' hz'
  have HM : IsMinOn (fun y => w y+C y z) S (Y z) := by
    intro y hy
    change w (Y z)+C (Y z) z≤w y+C y z
    rw [←hval z hz]
    exact hmin z hz y hy
  have HM' : IsMinOn (fun y => w y+C y z') S (Y z') := by
    intro y hy
    change w (Y z')+C (Y z') z'≤w y+C y z'
    rw [←hval z' hz']
    exact hmin z' hz' y hy
  have HG := StrongConvexOn.quadratic_growth_half (hstrong z hz) hy hy' HM
  have HG' := StrongConvexOn.quadratic_growth_half (hstrong z' hz') hy' hy HM'
  have HC := (abs_le.mp (hcross (Y z) hy (Y z') hy' z hz z' hz')).1
  rw [norm_sub_rev (Y z) (Y z')] at HG'
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ (div_nonneg (by positivity) hm.le)]
  rw [norm_sub_rev (Y z) (Y z'),norm_sub_rev z z']
  by_cases hd : ‖Y z'-Y z‖=0
  · rw [hd]; positivity
  have hp : 0<‖Y z'-Y z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
  have H : m/2*‖Y z'-Y z‖^2≤K*‖Y z'-Y z‖*‖z'-z‖ := by linarith only [HG,HG',HC]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).mpr
  change ‖Y z'-Y z‖*m≤2*K*‖z'-z‖
  nlinarith only [H,hp,hm]

lemma strong_envelope_quadratic_remainder (hm :  0 < m)
    (hY : ∀ z∈T,Y z∈S)
    (hval : ∀ z∈T,F z=w (Y z)+C (Y z) z)
    (hmin : ∀ z∈T,∀ y∈S,F z≤w y+C y z)
    (hstrong : ∀ z∈T,StrongConvexOn S m (fun y => w y+C y z))
    (hcross : ∀ y∈S,∀ y'∈S,∀ z∈T,∀ z'∈T,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖)
    {l:E → E →L[ℝ] ℝ}
    (hrem : ∀ z∈T,∀ z'∈T,
      |C (Y z) z'-C (Y z) z-l z (z'-z)|≤B*‖z'-z‖^2) :
    ∀ z∈T,∀ z'∈T,
      |F z'-F z-l z (z'-z)|≤(B+K^2/m)*‖z'-z‖^2 := by
  intro z hz z' hz'
  have hy := hY z hz
  have hy' := hY z' hz'
  have HM : IsMinOn (fun y => w y+C y z) S (Y z) := by
    intro y hy
    change w (Y z)+C (Y z) z≤w y+C y z
    rw [←hval z hz]
    exact hmin z hz y hy
  have HG := StrongConvexOn.quadratic_growth_half (hstrong z hz) hy hy' HM
  have HC := (abs_le.mp (hcross (Y z) hy (Y z') hy' z hz z' hz')).1
  have HR := abs_le.mp (hrem z hz z' hz')
  have HU := hmin z' hz' (Y z) hy
  have hYz := hval z hz
  have hYz' := hval z' hz'
  have hsquare := sq_nonneg (m*‖Y z'-Y z‖-2*K*‖z'-z‖)
  have hdiv : (K^2/m)*m=K^2 := div_mul_cancel₀ _ hm.ne'
  have Hcomplete : -(K^2/m)*‖z'-z‖^2≤
      m/4*‖Y z'-Y z‖^2-K*‖Y z'-Y z‖*‖z'-z‖ := by
    nlinarith only [hsquare,hdiv,hm]
  apply abs_le.mpr
  constructor
  · nlinarith only [HG,HC,HR.1,hYz,hYz',Hcomplete]
  · have hn : 0 ≤ K^2/m*‖z'-z‖^2 := by positivity
    nlinarith only [HU,hYz,HR.2,hn]

lemma strong_envelope_C11 {a:E} {r:ℝ} (hr :  0 < r) (hm :  0 < m) (hK :  0 ≤ K) (hB :  0 ≤ B)
    (hY : ∀ z∈ball a r,Y z∈S)
    (hval : ∀ z∈ball a r,F z=w (Y z)+C (Y z) z)
    (hmin : ∀ z∈ball a r,∀ y∈S,F z≤w y+C y z)
    (hstrong : ∀ z∈ball a r,StrongConvexOn S m (fun y => w y+C y z))
    (hcross : ∀ y∈S,∀ y'∈S,∀ z∈ball a r,∀ z'∈ball a r,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖)
    {l:E → E →L[ℝ] ℝ}
    (hrem : ∀ z∈ball a r,∀ z'∈ball a r,
      |C (Y z) z'-C (Y z) z-l z (z'-z)|≤B*‖z'-z‖^2) :
    (∀ z∈ball a r,HasFDerivAt F (l z) z) ∧
      LipschitzOnWith (Real.toNNReal (6*(B+K^2/m))) (fderiv ℝ F) (ball a (r/4)) := by
  have H := strong_envelope_quadratic_remainder hm hY hval hmin hstrong hcross hrem
  have hconst : 0 ≤ B+K^2/m := add_nonneg hB (div_nonneg (pow_nonneg hK 2) hm.le)
  have hd : ∀ z∈ball a r,HasFDerivAt F (l z) z := by
    intro z hz
    exact hasFDerivAt_of_quadratic_remainder hconst
      (by filter_upwards [isOpen_ball.mem_nhds hz] with z' hz'; exact H z hz z' hz')
  refine ⟨hd,?_⟩
  rw [Real.toNNReal_of_nonneg (show 0≤6*(B+K^2/m) from by positivity)]
  exact derivative_lipschitz_of_quadratic_remainder hr hconst
    (fun z hz z' hz' => by rw [(hd z hz).fderiv]; exact H z hz z' hz')
end WeakMTWTransport

end

end OAI
