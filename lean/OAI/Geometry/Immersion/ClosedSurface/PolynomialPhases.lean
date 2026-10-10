import OAI.Geometry.Immersion.ClosedSurface.DirectionStability
import OAI.Geometry.Immersion.ClosedSurface.PhaseStock

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set

lemma finite_phase_basis_bounds (s : Finset PhaseBasis) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P ∈ s, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C := by
  classical
  let d (P : PhaseBasis) := ∑ i : Fin 3, (‖P.ξ i‖+‖P.Q i‖)
  have hd (P : PhaseBasis) : 0 ≤ d P := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨1+∑ P ∈ s, d P,by linarith [Finset.sum_nonneg (fun P (_ : P ∈ s) => hd P)],?_⟩
  intro P hP i
  have hi : ‖P.ξ i‖+‖P.Q i‖ ≤ d P :=
    Finset.single_le_sum (f := fun j => ‖P.ξ j‖+‖P.Q j‖) (fun j (_ : j ∈ Finset.univ) => by positivity) (Finset.mem_univ i)
  have hp : d P ≤ ∑ P ∈ s, d P := Finset.single_le_sum (fun P (_ : P ∈ s) => hd P) hP
  constructor <;> linarith [norm_nonneg (P.ξ i),norm_nonneg (P.Q i)]




theorem finite_phase_stock_neighborhoods {n : ℕ} {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) :
    ∃ (s : Finset PhaseBasis) (ε C δ : ℝ), 0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      (∀ P ∈ s, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C) ∧
      ∀ (B : Fin 3 → RVec n) (H : PhaseMean.Tensor), B ≠ 0 → H ∈ T →
      ∃ P ∈ s, ∀ (B' : Fin 3 → RVec n) (H' : PhaseMean.Tensor),
        ‖B'-B‖ ≤ δ*‖B‖ → ‖H'-H‖ ≤ δ →
        ∀ i, ε/2 ≤ P.Q i H' ∧
          (ε/4)*‖B'‖ ≤ ‖secondQuadratic B' (-(P.ξ i).2,(P.ξ i).1)‖ ∧ Good B' (P.ξ i) := by
  obtain ⟨s,ε,hε,hs⟩ := normalized_positive_phase_bases (n := n) hT hT0 hTd
  obtain ⟨C,hC,hbounds⟩ := finite_phase_basis_bounds s
  let δ := min 1 (min (ε/(8*C ^ 2+2)) (ε/(2*(C+1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ*(8*C ^ 2+2) ≤ ε := by
    exact (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hδQ : δ*(2*(C+1)) ≤ ε := by
    exact (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨s,ε,C,δ,hε,hC,hδ,hδ1,hbounds,fun B H hB hH => ?_⟩
  obtain ⟨P,hP,hpm⟩ := hs B H hB hH
  refine ⟨P,hP,fun B' H' hb hh i => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hQ : |P.Q i H'-P.Q i H| ≤ C*δ := by
    rw [← map_sub]
    exact ((P.Q i).le_opNorm _).trans (mul_le_mul (hbounds P hP i).2 hh (norm_nonneg _) (by linarith))
  have hq : ε/2 ≤ P.Q i H' := by
    have hlow := neg_abs_le (P.Q i H'-P.Q i H)
    have hbase := (hpm i).1
    have hcd : C*δ ≤ ε/2 := by nlinarith [hδ.le]
    linarith
  have hbc : 4*‖B-B'‖*‖P.ξ i‖^2 ≤ (ε*‖B‖)/2 := by
    rw [norm_sub_rev B B']
    calc
      _ ≤ 4*(δ*‖B‖)*C ^ 2 := by gcongr; exact (hbounds P hP i).1
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hδε hn.le]
  obtain ⟨hl,hgood⟩ := second_form_direction_persists B B' (P.ξ i)
    (mul_pos hε hn) (hpm i).2.le hbc
  have hBn : ‖B'‖ ≤ 2*‖B‖ := by
    have hh := norm_le_insert' B' B
    have hsmall : ‖B'-B‖ ≤ ‖B‖ := hb.trans (mul_le_of_le_one_left hn.le hδ1)
    linarith
  refine ⟨hq,?_,hgood⟩
  have hh := mul_le_mul_of_nonneg_left hBn (by positivity : 0 ≤ ε/4)
  linarith

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set






theorem actual_polynomial_cell_phases {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K Q : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) :
    ∃ (stock : Finset PhaseBasis) (ε C δ z₀ : ℝ),
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧
      (∀ P ∈ stock, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C) ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
      ∀ (F : RField 4) (U : Set Base), IsOpen U → Convex ℝ U → ContDiffOn ℝ ∞ F U →
        WeightedBound U z 3 A F →
        (∀ p ∈ U, ‖firstJetPair F p‖ ≤ R ∧
          c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2) →
      ∀ (H : Base → PhaseMean.Tensor) (x : Base), x ∈ U → H x ∈ T → b ≤ ‖realSecondTensor F x‖ →
        (∀ y ∈ U, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∃ P ∈ stock, ∀ (y : Base) (G : RField 4) (H' : PhaseMean.Tensor),
        y ∈ U → ‖y-x‖ ≤ Q*z^6 →
        ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
        ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
        c/2 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
        b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ P.Q i H' ∧
          (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          ε*b/8 ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          Good (realSecondTensor G y) (P.ξ i) := by
  obtain ⟨stock,ε,C,d,hε,hC,hd,hd1,hbounds,hstock⟩ :=
    finite_phase_stock_neighborhoods (n := 4) hT hT0 hTd
  obtain ⟨L,hL,hvariation⟩ := second_form_cell_variation R c A hc hA
  obtain ⟨η,D,hη,hD,hperturb⟩ := secondTensor_z4_stability R c A hc hA
  obtain ⟨ηg,hηg,_,hgram⟩ := uniform_gram_neighborhood R c hc
  let E := D+L*Q
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let z₀ := min 1 (min η (min ηg (min (d*b/(2*(E+1))) (d/(2*(K*Q+1))))))
  have hz₀ : 0 < z₀ := by dsimp [z₀]; positivity
  have hz₀1 : z₀ ≤ 1 := min_le_left _ _
  refine ⟨stock,ε,C,d/2,z₀,hε,hC,half_pos hd,hz₀,hz₀1,hbounds,?_⟩
  intro z hz hz0 F U hU hconv hF hFbound hmetric H x hx hHx hBx hH
  have hz1 := hz0.trans hz₀1
  have hzη : z ≤ η := hz0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzηg : z ≤ ηg := hz0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hze : z ≤ d*b/(2*(E+1)) := hz0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hzh : z ≤ d/(2*(K*Q+1)) := hz0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hz41 : z^4 ≤ z := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ 4))
  have hz61 : z^6 ≤ z := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ 6))
  have hz21 : z^2 ≤ z := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ 2))
  have hEz : E*z^2 ≤ d*b/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(E+1))).mp hze
    nlinarith [mul_le_mul_of_nonneg_left hz21 hE]
  have hHz : K*Q*z^6 ≤ d/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(K*Q+1))).mp hzh
    nlinarith [mul_le_mul_of_nonneg_left hz61 (mul_nonneg hK hQ)]
  have hBn : realSecondTensor F x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hb.trans_le hBx))
  obtain ⟨P,hP,hPb⟩ := hstock (realSecondTensor F x) (H x) hBn hHx
  refine ⟨P,hP,?_⟩
  intro y G H' hy hxy hFG1 hFG2 hH'
  have hnormjet := (coordinate_jets_variation hU hconv hF hz hA hFbound hy hy).2.1
  have hdiff : ‖realSecondTensor G y-realSecondTensor F x‖ ≤ E*z^2 := by
    have hp := hperturb z hz hz1 (hz41.trans hzη) F G y
      (hmetric y hy).1 (hmetric y hy).2 hFG1 hnormjet hFG2
    have hv := hvariation z hz hz1 F U hU hconv hF hFbound hmetric y hy x hx
    calc
      _ ≤ ‖realSecondTensor G y-realSecondTensor F y‖+
          ‖realSecondTensor F y-realSecondTensor F x‖ := by
            simpa only [dist_eq_norm] using dist_triangle (realSecondTensor G y) (realSecondTensor F y) (realSecondTensor F x)
      _ = ‖realSecondTensor F y-realSecondTensor G y‖+
          ‖realSecondTensor F y-realSecondTensor F x‖ := by rw [norm_sub_rev (realSecondTensor G y)]
      _ ≤ D*z^2+(L/z^4)*‖y-x‖ := add_le_add hp hv
      _ ≤ D*z^2+(L/z^4)*(Q*z^6) := by gcongr
      _ = E*z^2 := by dsimp [E]; field_simp [hz.ne']
  have hsmall : ‖realSecondTensor G y-realSecondTensor F x‖ ≤ d*‖realSecondTensor F x‖ := by
    apply hdiff.trans (hEz.trans _)
    nlinarith [mul_le_mul_of_nonneg_left hBx hd.le]
  have hnearH : ‖H'-H x‖ ≤ d := by
    calc
      _ ≤ ‖H'-H y‖+‖H y-H x‖ := by
        simpa only [dist_eq_norm] using dist_triangle H' (H y) (H x)
      _ ≤ d/2+K*‖y-x‖ := add_le_add hH' (hH y hy)
      _ ≤ d/2+K*(Q*z^6) := by gcongr
      _ ≤ d := by nlinarith [hHz]
  have hhalf : b/2 ≤ ‖realSecondTensor G y‖ := by
    have hn := norm_le_insert' (realSecondTensor F x) (realSecondTensor G y)
    rw [norm_sub_rev (realSecondTensor F x)] at hn
    have he : d*b/2 ≤ b/2 := by nlinarith
    linarith [hdiff.trans (hEz.trans he)]
  refine ⟨(hgram _ _ (hmetric y hy).1 (hmetric y hy).2
    (hFG1.trans (hz41.trans hzηg))).2,hhalf,?_⟩
  intro i
  obtain ⟨hq,hl,hgood⟩ := hPb _ H' hsmall hnearH i
  refine ⟨hq,hl,?_,hgood⟩
  have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ ε/4)
  linarith

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
