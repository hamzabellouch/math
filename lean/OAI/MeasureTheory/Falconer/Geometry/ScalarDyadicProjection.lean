import OAI.MeasureTheory.Falconer.Estimates.ScalarScaleAlignment
import OAI.MeasureTheory.Falconer.Geometry.ScalarUnitProjection

namespace OAI

/-! The scalar projection theorem at every sufficiently fine dyadic scale. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_dyadic_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, 0 ≤ x ∧ x < 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  obtain ⟨B,M0,η,hB,hM0,hη,hprojection⟩ := scalar_unit_projection hκ hκ1
  let C : ℝ := (2:ℝ)^B
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  let F : ℝ := (2*(2^B:ℕ)+3:ℕ)
  have hF : 0 < F := by positivity
  have hD : 0 < C^(2*κ) := by positivity
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hη hF hD
  refine ⟨η/4,max (B*M0) N1,by positivity,lt_of_lt_of_le hN1 (le_max_right _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXunit hsep hsize hadd hpoint E hE hEbound hEball
  let M := N/B+1
  have hdepth : N < B*M := (scalar_block_ceiling_bounds N B hB).1
  have hNM : N ≤ B*M := hdepth.le
  have hNMreal : (N:ℝ) ≤ (B:ℝ)*(M:ℝ) := by exact_mod_cast hNM
  have hM : M0 ≤ M := by
    by_contra hn
    have hh := Nat.mul_le_mul_left B (show M ≤ M0 by omega)
    have hn0 : B*M0 ≤ N := (le_max_left _ _).trans hN
    omega
  let δ := (1/2:ℝ)^N
  let δf := (1/2:ℝ)^(B*M)
  let W := Real.exp ((η/4)*(N:ℝ)*Real.log 2)
  let Wf := Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hδf : 0 < δf := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨hff,hcf⟩ := scalar_block_scale_comparison N B hB
  change δf ≤ δ at hff
  change δ ≤ C*δf at hcf
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hExp : Real.exp (η*(N:ℝ)*Real.log 2) ≤ Wf := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hNMreal (show 0 ≤ η*Real.log 2 by positivity)
    nlinarith
  obtain ⟨hcover,hball⟩ := hloss N ((le_max_right _ _).trans hN)
  have hcover' : F*W ≤ Wf := hcover.trans hExp
  have hball' : C^(2*κ)*W ≤ Wf := hball.trans hExp
  have hCpow : C^κ ≤ C^(2*κ) := Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  have hpointFactor : C^κ*W ≤ Wf :=
    (mul_le_mul_of_nonneg_right hCpow hW.le).trans hball'
  have hfineCover (Y : Finset ℝ) : ((scalarCells δf Y).card:ℝ) ≤ F*(scalarCells δ Y).card := by
    dsimp only [F]
    exact_mod_cast scalar_cells_resolution hδf hδ (2^B) (by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hcf) Y
  have hsizef : Real.log (X.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hNMreal
      (mul_nonneg (sub_nonneg.mpr hκ1) (Real.log_pos (by norm_num : (1:ℝ) < 2)).le)
    nlinarith
  have haddf : ((scalarCells δf (X+X)).card:ℝ) ≤ Wf*(X.card:ℝ) := by
    have hh := hfineCover (X+X)
    have hm := mul_le_mul_of_nonneg_left hadd hF.le
    have hf := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
    nlinarith
  have hpointf : ∀ u r : ℝ, δf ≤ r → r ≤ 1 → scalarBallMass X u r ≤ Wf*r^κ*(X.card:ℝ) := by
    intro u r hr hr1
    have hh := scalar_refined_ball_bound hδf hδ1 hC hcf hW.le hκ.le X hpoint u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hpointFactor
      (mul_nonneg (Real.rpow_nonneg (hδf.le.trans hr) κ) (Nat.cast_nonneg X.card))
    nlinarith
  have hcoefff : ∀ u r : ℝ, δf ≤ r → r ≤ 1 → scalarBallMass E u r ≤ Wf*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr hr1
    have hh := scalar_refined_ball_bound hδf hδ1 hC hcf hW.le (by linarith : 0 ≤ 2*κ) E hEball u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hball'
      (mul_nonneg (Real.rpow_nonneg (hδf.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    nlinarith
  obtain ⟨a,ha,hgain⟩ := hprojection M hM X hX hXunit
    (fun x hx y hy hxy => hff.trans (hsep x hx y hy hxy)) hsizef haddf hpointf E hE hEbound hcoefff
  by_contra hn
  push Not at hn
  have hh := hfineCover (X+X.image (fun x => a*x))
  have hp := mul_le_mul_of_nonneg_left (hn a ha) hF.le
  have hm := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
  nlinarith

end Falconer.Regularization

end OAI
