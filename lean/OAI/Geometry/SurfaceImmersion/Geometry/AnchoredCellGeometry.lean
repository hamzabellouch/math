import OAI.Geometry.Immersion.ClosedSurface.PolynomialPhases

namespace OAI

/-! Phase cells anchored at the compact weight support need no enclosing
convex chart on which the immersion remains nondegenerate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma firstJet_anchor_neighborhood (R c A Q : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hQ : 0 ≤ Q) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
    ∀ z : ℝ, 0 < z → z ≤ η → ∀ F : RField 4, ContDiff ℝ ∞ F →
      WeightedBound univ z 3 A F → ∀ x : Base,
      ‖firstJetPair F x‖ ≤ R → c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 →
      ∀ y : Base, ‖y-x‖ ≤ Q*z^6 →
      ‖firstJetPair F y‖ ≤ R+1 ∧
        c/2 ≤ NormalFrame.gramDet (firstJetPair F y).1 (firstJetPair F y).2 := by
  obtain ⟨ε,hε,hε1,hgram⟩ := uniform_gram_neighborhood R c hc
  let η := min 1 (ε/(A*Q+1))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  intro z hz hzη F hF hb x hx hxg y hy
  have hz1 : z ≤ 1 := hzη.trans (min_le_left _ _)
  have hze : z ≤ ε/(A*Q+1) := hzη.trans (min_le_right _ _)
  have hz4 : z^4 ≤ z := by
    calc
      z^4 ≤ z^1 := pow_le_pow_of_le_one hz.le hz1 (by omega)
      _ = z := pow_one z
  have hsmall : A*Q*z^4 ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < A*Q+1)).mp hze
    nlinarith [mul_le_mul_of_nonneg_left hz4 (mul_nonneg hA hQ)]
  have hv := (coordinate_jets_variation isOpen_univ (convex_univ : Convex ℝ (univ : Set Base))
    hF.contDiffOn hz hA hb (mem_univ x) (mem_univ y)).1
  have hclose : ‖firstJetPair F x-firstJetPair F y‖ ≤ ε := by
    calc
      _ ≤ (A/z^2)*‖x-y‖ := hv
      _ = (A/z^2)*‖y-x‖ := by rw [norm_sub_rev x y]
      _ ≤ (A/z^2)*(Q*z^6) := mul_le_mul_of_nonneg_left hy (div_nonneg hA (sq_nonneg z))
      _ = A*Q*z^4 := by field_simp [hz.ne']
      _ ≤ ε := hsmall
  exact hgram _ _ hx hxg hclose

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

theorem anchored_polynomial_cell_phases {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ stock : Finset PhaseBasis, ∃ ε C δ z₀ : ℝ,
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧
      (∀ P ∈ stock, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : RField 4, ContDiff ℝ ∞ F →
      WeightedBound univ z 3 A F → ∀ (H : Base → PhaseMean.Tensor) (x : Base),
      ‖firstJetPair F x‖ ≤ R → c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 →
      b ≤ ‖realSecondTensor F x‖ → H x ∈ T →
      (∀ y, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∃ P ∈ stock, ∀ (y : Base) (G : RField 4) (H' : PhaseMean.Tensor),
        ‖y-x‖ ≤ 6*z^6 →
        ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
        ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
        c/4 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
        b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ P.Q i H' ∧
          (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          ε*b/8 ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          Good (realSecondTensor G y) (P.ξ i) := by
  obtain ⟨η,hη,hη1,hanchor⟩ := firstJet_anchor_neighborhood R c A 7 hc hA (by norm_num)
  obtain ⟨stock,ε,C,δ,z₁,hε,hC,hδ,hz₁,hz₁1,hstock,hcell⟩ :=
    actual_polynomial_cell_phases hT hT0 hTd (R+1) (c/2) A b K 6
      (half_pos hc) hA hb hK (by norm_num)
  refine ⟨stock,ε,C,δ,min η z₁,hε,hC,hδ,lt_min hη hz₁,
    (min_le_left _ _).trans hη1,hstock,?_⟩
  intro z hz hz0 F hF hbF H x hx hxg hxB hxH hLip
  let U : Set Base := Metric.ball x (7*z^6)
  have hxU : x ∈ U := Metric.mem_ball_self (by positivity)
  have hmetric (y : Base) (hy : y ∈ U) : ‖firstJetPair F y‖ ≤ R+1 ∧
      c/2 ≤ NormalFrame.gramDet (firstJetPair F y).1 (firstJetPair F y).2 := by
    apply hanchor z hz (hz0.trans (min_le_left _ _)) F hF hbF x hx hxg y
    exact (show ‖y-x‖ < 7*z^6 from by simpa only [U,Metric.mem_ball,dist_eq_norm] using hy).le
  obtain ⟨P,hPs,hp⟩ := hcell z hz (hz0.trans (min_le_right _ _)) F U Metric.isOpen_ball
    (convex_ball _ _) hF.contDiffOn
    (hbF.restrict_open Metric.isOpen_ball) hmetric H x hxU hxH hxB (fun y _ => hLip y)
  refine ⟨P,hPs,?_⟩
  intro y G H' hy h1 h2 hHH
  have hyU : y ∈ U := by
    change dist y x < 7*z^6
    rw [dist_eq_norm]
    exact hy.trans_lt (by nlinarith [pow_pos hz 6])
  have hh := hp y G H' hyU hy h1 h2 hHH
  simpa only [div_div, show (2:ℝ)*2=4 by norm_num] using hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
