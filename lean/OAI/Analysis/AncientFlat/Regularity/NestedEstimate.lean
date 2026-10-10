import OAI.Analysis.AncientFlat.Geometry.WindowEstimate
import OAI.Analysis.AncientFlat.Evolution.TopSeminorm

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicInterpolation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
lemma exists_window_scale {α δ K : ℝ} (hα : 0<α) (hδ : 0<δ) (hK : 0≤K) :
    ∃ η : ℝ, 0<η ∧ η≤1/4 ∧ K*(4*η)^α≤δ := by
  let D := K*(4:ℝ)^α+1
  have hD : 0<D := by dsimp [D]; positivity
  obtain ⟨η,hη,hη1,hgap,hsmall⟩ := exists_interpolation_scale (1-α) (δ/D) 1
    (by linarith) (div_pos hδ hD) (by norm_num)
  rw [show 1-(1-α)=α by ring] at hsmall
  refine ⟨η,hη,by linarith,?_⟩
  have hn : 0≤η^α := Real.rpow_nonneg hη.le _
  have hsm : η^α≤δ/D := by linarith
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hη.le]
  calc
    _=(K*(4:ℝ)^α)*η^α := by ring
    _≤D*η^α := by dsimp [D]; nlinarith
    _≤D*(δ/D) := mul_le_mul_of_nonneg_left hsm hD.le
    _=δ := by field_simp

theorem nested_fourth_estimate (α κ K θ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hθ : 0<θ) :
    ∃ C : ℝ, 0<C ∧ ∀ (r R : ℝ), 1≤r → r<R → R≤3/2 →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder R) a K → HolderBound α (cylinder R) b K →
      (∀ p∈cylinder R, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder R, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α (cylinder R) u ut M) →
      HolderBound α (cylinder R) (fun p => f p.2 p.1) F → (∀ p∈cylinder R, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder R, ∀ z∈cylinder R,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤H*pdist p z^α) →
      (∀ p∈cylinder R, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      ∀ p∈cylinder r, ∀ z∈cylinder r,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤
          (θ*H+(C/(R-r)^5)*(F+U))*pdist p z^α := by
  obtain ⟨δ,C0,hδ,hC0,Hwin⟩ := window_fourth_estimate (V := V) α κ K (θ/2) hα hα1 hκ hK (by linarith)
  obtain ⟨η,hη,hη4,hsmall⟩ := exists_window_scale hα hδ hK
  refine ⟨2*C0/η^5,by positivity,?_⟩
  intro r R hr hrR hR a b ha hb hella u ut f F U H hF hU hH hs hd hj hf hu hh he
  let q := η*(R-r)
  have hg : 0<R-r := sub_pos.mpr hrR
  have hg1 : R-r≤1 := by linarith
  have hq : 0<q := mul_pos hη hg
  have hqη : q≤η := by dsimp [q]; nlinarith
  have hq1 : q≤1 := by linarith
  have hgap : 4*q≤R-r := by dsimp [q]; nlinarith
  have hqsmall : K*(4*q)^α≤δ :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith : 4*q≤4*η) hα.le) hK).trans hsmall
  have hr0 : 0≤r := by linarith
  have hsub : (cylinder r : Set (V × ℝ))⊆cylinder R := cylinder_mono hr0 hrR.le
  let B := θ/2*H+C0/(q^4*q^α)*(F+U)
  have hB : 0≤B := by dsimp [B]; positivity
  have Hw (p0 : V × ℝ) (hp0 : p0∈cylinder r) :=
    Hwin q hq hq1 hqsmall p0 (cylinder R) (hsub hp0) (small_window_maps hr0 hq hgap p0 hp0)
      a b ha hb hella u ut f F U H hF hU hH hs hd hj hf hu hh he
  have hn (p : V × ℝ) (hp : p∈cylinder r) : ‖iteratedFDeriv ℝ 4 (u p.2) p.1‖≤B*q^α := by
    have hz : ((0:V),(0:ℝ))∈cylinder 1 := by norm_num [cylinder]
    simpa only [window_zero] using (Hw p hp).1 (0,0) hz
  have Hsemi : ∀ p∈cylinder r, ∀ z∈cylinder r,
      ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤(2*B)*pdist p z^α := by
    intro p hp z hz
    by_cases hnear : pdist p z<q
    · obtain ⟨hctr,hip,hiz⟩ := close_pair_window hq p z hp hz hnear
      have hc := (Hw (p.1,max p.2 z.2) hctr).2 (windowInv (p.1,max p.2 z.2) q p) hip
        (windowInv (p.1,max p.2 z.2) q z) hiz
      simp only [window_windowInv _ hq.ne'] at hc
      exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : B ≤ 2*B)
        (Real.rpow_nonneg (pdist_nonneg p z) _))
    · have hdq : q≤pdist p z := le_of_not_gt hnear
      calc
        _≤‖iteratedFDeriv ℝ 4 (u p.2) p.1‖+‖iteratedFDeriv ℝ 4 (u z.2) z.1‖ := norm_sub_le _ _
        _≤B*q^α+B*q^α := add_le_add (hn p hp) (hn z hz)
        _=(2*B)*q^α := by ring
        _≤(2*B)*pdist p z^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.le hdq hα.le) (by positivity)
  have hqden : q^5≤q^4*q^α := by
    have := mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hq.le hq1 hα1.le) (pow_nonneg hq.le 4)
    simpa only [←pow_succ] using this
  have hc : 2*(C0/(q^4*q^α))≤(2*C0/η^5)/(R-r)^5 := by
    have hdiv : C0/(q^4*q^α)≤C0/q^5 := div_le_div_of_nonneg_left hC0.le (pow_pos hq _) hqden
    calc
      _≤2*(C0/q^5) := by gcongr
      _=_ := by dsimp [q]; rw [mul_pow]; field_simp
  have HB : 2*B≤θ*H+((2*C0/η^5)/(R-r)^5)*(F+U) := by
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hc (add_nonneg hF hU)]
  intro p hp z hz
  exact (Hsemi p hp z hz).trans (mul_le_mul_of_nonneg_right HB (Real.rpow_nonneg (pdist_nonneg p z) _))
end ParabolicLocalization

end

end OAI
