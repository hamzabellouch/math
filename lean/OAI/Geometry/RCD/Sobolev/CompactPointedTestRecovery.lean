import OAI.Geometry.RCD.Sobolev.PointedTestRecovery
import OAI.Geometry.RCD.Sobolev.NestedBallCutoff

namespace OAI

/-! # Compactly supported recovery of Euclidean test functions -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

omit [ProperSpace X] in
private theorem bounded_product_lipschitz {f g : X → ℝ} {L M A B : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (hA : ∀ x, |f x|≤A) (hB : ∀ x, |g x|≤B) :
    LipschitzWith (B*L+A*M) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y=(f x-f y)*g x+f y*(g x-g y) := by ring
  rw [he]
  calc
    _ ≤ |(f x-f y)*g x|+|f y*(g x-g y)| := abs_add_le _ _
    _ = |f x-f y| * |g x|+|f y| * |g x-g y| := by rw [abs_mul,abs_mul]
    _ ≤ ((L:ℝ)*dist x y)*B+A*((M:ℝ)*dist x y) := by
      gcongr
      · simpa only [Real.dist_eq] using hf.dist_le_mul x y
      · exact hB x
      · exact hA y
      · simpa only [Real.dist_eq] using hg.dist_le_mul x y
    _ = (B*L+A*M:ℝ≥0)*dist x y := by push_cast; ring

theorem compact_pointed_test_recovery_support {n : ℕ} {p : X} {r S ρ a b ε B : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hρa : ρ<a) (hab : a<b) (hbS : b<S)
    (hε : 0≤ε) (hsmall : 2*ε<a-ρ) (hB : 0≤B)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {ψ : Euclidean n → ℝ} {M : ℝ≥0} (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0) :
    ∃ (w : X → ℝ) (L : ℝ≥0), LipschitzWith L w ∧ HasCompactSupport w ∧
      tsupport w ⊆ closedBall p (b*r) ∧ (∀ x, |w x|≤B+M*ε) ∧
      r*(L:ℝ)≤M+(B+M*ε)/(b-a) ∧
      ∀ x, dist x p≤S*r → |w x-ψ (v x)|≤M*ε := by
  have hS : 0≤S := by linarith
  obtain ⟨F,hF,hFb,hFe⟩ := pointed_lipschitz_test_recovery hr hS hε hB hv hψ hψb
  let χ := nestedBallCutoff p (a*r) (b*r)
  have harbr : a*r<b*r := mul_lt_mul_of_pos_right hab hr
  have hχ := nestedBallCutoff_lipschitz p harbr
  have hχb (x : X) : |χ x|≤(1:ℝ≥0) := by
    rw [abs_of_nonneg (nestedBallCutoff_bounds p (a*r) (b*r) x).1]
    exact (nestedBallCutoff_bounds p (a*r) (b*r) x).2
  let A : ℝ≥0 := ⟨B+M*ε,add_nonneg hB (mul_nonneg M.coe_nonneg hε)⟩
  have hprod := bounded_product_lipschitz (A := 1) (B := A) hχ hF hχb hFb
  refine ⟨fun x => χ x*F x,_,hprod,?_,?_,?_,?_,?_⟩
  · exact (nestedBallCutoff_hasCompactSupport p harbr).mul_right
  · exact tsupport_mul_subset_left.trans (nestedBallCutoff_tsupport p harbr)
  · intro x
    rw [abs_mul]
    exact (mul_le_mul (hχb x) (hFb x) (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  · change r*((B+(M:ℝ)*ε)*(b*r-a*r)⁻¹+1*((M:ℝ)/r))≤M+(B+M*ε)/(b-a)
    have hgap : b*r-a*r=(b-a)*r := by ring
    rw [hgap]
    apply le_of_eq
    field_simp [hr.ne',(sub_pos.mpr hab).ne']
    ring
  · intro x hx
    change |χ x*F x-ψ (v x)|≤M*ε
    by_cases hz : ψ (v x)=0
    · have he := hFe x hx
      rw [hz,sub_zero] at he ⊢
      rw [abs_mul]
      exact (mul_le_mul (hχb x) he (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
    · have hn : ‖v x‖<ρ := lt_of_not_ge (fun h => hz (hψ0 _ h))
      have hd := (abs_le.mp (hv.2.1 x p hx
        (by simpa only [dist_self] using mul_nonneg hS hr.le))).1
      have ht := dist_triangle (v x) 0 (v p)
      have hc := hv.1
      rw [dist_comm 0 (v p)] at ht
      simp only [dist_zero_right] at ht hc
      have hxa : dist p x≤a*r := by
        rw [dist_comm]
        apply (div_le_iff₀ hr).mp
        linarith
      rw [show χ x=1 from nestedBallCutoff_eq_one p harbr hxa,one_mul]
      exact hFe x hx


/-- Compactly supported smooth tests on an open ball admit harmonic recovery. -/
theorem compact_pointed_test_recovery {n : ℕ} {p : X} {r S ρ a b ε B : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hρa : ρ<a) (hab : a<b) (hbS : b<S)
    (hε : 0≤ε) (hsmall : 2*ε<a-ρ) (hB : 0≤B)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {ψ : Euclidean n → ℝ} {M : ℝ≥0} (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0) :
    ∃ (w : X → ℝ) (L : ℝ≥0), LipschitzWith L w ∧ HasCompactSupport w ∧
      tsupport w ⊆ ball p (S*r) ∧ (∀ x, |w x|≤B+M*ε) ∧
      r*(L:ℝ)≤M+(B+M*ε)/(b-a) ∧
      ∀ x, dist x p≤S*r → |w x-ψ (v x)|≤M*ε := by
  obtain ⟨w,L,hw,hc,hs,hb,hL,he⟩ := compact_pointed_test_recovery_support
    hr hρ hρa hab hbS hε hsmall hB hv hψ hψb hψ0
  exact ⟨w,L,hw,hc,hs.trans (closedBall_subset_ball
    (mul_lt_mul_of_pos_right hbS hr)),hb,hL,he⟩

end RegularPointCoordinates

end

end OAI
