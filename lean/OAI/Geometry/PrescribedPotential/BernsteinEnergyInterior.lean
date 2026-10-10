import Mathlib
import OAI.Geometry.PrescribedPotential.BernsteinHigherRescue
import OAI.Geometry.PrescribedPotential.BernsteinLocalC2
import OAI.Geometry.PrescribedPotential.RealCutoffBounds

namespace OAI

/-! Bernstein Energy Interior. -/

section

 
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma quartic_energy_interior {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχval : ∀ x ∈ K, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχint : ∀ x ∈ K, χ x ≠ 0 → x ∈ interior K)
    {A R B : ℝ} (hA : 1 ≤ A) (hR : 1 ≤ R) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S T : E → ℝ, ContDiffOn ℝ ∞ S U → ContDiffOn ℝ ∞ T U →
      ∀ v : E → ι → E, (∀ x ∈ K, ∀ i, ‖v x i‖ ≤ B) →
      (∀ x ∈ K, 0 ≤ S x ∧ S x ≤ R ∧ 0 ≤ T x) →
      (∀ x ∈ K, ∃ D : ℝ, 0 ≤ D ∧ T x ≤ A*D ∧ D ≤ A*T x ∧
        D-R ≤ frameLaplace (v x) S x ∧
        -R*(1+T x*Real.sqrt (T x)) ≤ frameLaplace (v x) T x ∧
        ‖frameGradient (v x) S x‖^2 ≤ 4*S x*D) →
      ∀ z ∈ K, χ z=1 → T z ≤ C := by
  classical
  obtain ⟨C0,hC0,hcut⟩ := cutoff_uniform_frames (ι := ι) hK χ hχ hB
  let C1 := 1+C0+R+A*R+4*A^3*R
  have hA0 : 0 ≤ A := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hC1 : 1 ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have hc0 : C0 ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have hr1 : R ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have har : A*R ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have hgradC : 4*A^3*R ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  let C := (8*C1+1+A*R)*(2*quarticConstant C1 (8*C1+1+A*R)+2)^2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro S T hS hT v hv hvalues hineq z hz hz1
  apply quartic_cutoff_uniform hK hU hKU (contDiffOn_const.mul hS) hT (hχ.pow 2).contDiffOn
    hC1 (mul_nonneg hA0 hR0) (S := fun y => A*S y) (η := fun y => (χ y)^2) ?_ ?_ v ?_ z hz (by rw [hz1]; norm_num)
  · intro x hx
    obtain ⟨hs,hsR,ht⟩ := hvalues x hx
    obtain ⟨hχ0,hχ1⟩ := hχval x hx
    exact ⟨mul_nonneg hA0 hs,mul_le_mul_of_nonneg_left hsR hA0,ht,sq_nonneg _,by nlinarith⟩
  · intro x hx hn
    exact hχint x hx (fun he => hn (by rw [he]; ring))
  · intro x hx _
    obtain ⟨D,hD,htD,hDt,hLS,hLT,hGS⟩ := hineq x hx
    obtain ⟨hs,hsR,ht⟩ := hvalues x hx
    obtain ⟨hLχ,hGχ⟩ := hcut x hx (v x) (hv x hx)
    refine ⟨?_,?_,(neg_le_neg hc0).trans hLχ,hGχ.trans (mul_le_mul_of_nonneg_right hc0 (sq_nonneg _)),?_⟩
    · rw [frameLaplace_const_mul hU hS (hKU hx)]
      have hh := mul_le_mul_of_nonneg_left hLS hA0
      nlinarith only [hh,htD,har]
    · have hh := mul_le_mul_of_nonneg_right hr1 (show 0 ≤ 1+T x*Real.sqrt (T x) by positivity)
      nlinarith only [hh,hLT]
    · rw [frameGradient_const_mul ((hS.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp)),norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      calc
        _ ≤ A^2*(4*S x*D) := mul_le_mul_of_nonneg_left hGS (sq_nonneg A)
        _ ≤ A^2*(4*R*(A*T x)) := mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hsR (by norm_num)) hDt hD (by positivity)) (sq_nonneg A)
        _ = (4*A^3*R)*T x := by ring
        _ ≤ C1*T x := mul_le_mul_of_nonneg_right hgradC ht

lemma linear_energy_interior {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχval : ∀ x ∈ K, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχint : ∀ x ∈ K, χ x ≠ 0 → x ∈ interior K)
    {A R B : ℝ} (hA : 1 ≤ A) (hR : 1 ≤ R) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S T : E → ℝ, ContDiffOn ℝ ∞ S U → ContDiffOn ℝ ∞ T U →
      ∀ v : E → ι → E, (∀ x ∈ K, ∀ i, ‖v x i‖ ≤ B) →
      (∀ x ∈ K, 0 ≤ S x ∧ S x ≤ R ∧ 0 ≤ T x) →
      (∀ x ∈ K, ∃ D Q : ℝ, 0 ≤ D ∧ 0 ≤ Q ∧ T x ≤ A*D ∧
        D-R ≤ frameLaplace (v x) S x ∧
        Q-R*(1+T x) ≤ frameLaplace (v x) T x ∧
        ‖frameGradient (v x) T x‖^2 ≤ 4*T x*Q) →
      ∀ z ∈ K, χ z=1 → T z ≤ C := by
  classical
  obtain ⟨C0,hC0,hcut⟩ := cutoff_uniform_frames (ι := ι) hK χ hχ hB
  let C1 := 1+C0+R+A*R
  have hA0 : 0 ≤ A := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hC1 : 0 ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have hc0 : C0 ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have hr1 : R ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  have har : A*R ≤ C1 := by dsimp [C1]; nlinarith [mul_nonneg hA0 hR0, show 0 ≤ 4*A^3*R by positivity]
  let C := 2*C1*(1+(12*C1+1)/1)+((12*C1+1)/1)*(A*R)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro S T hS hT v hv hvalues hineq
  choose D Q hD hQ htD hLS hLT hGT using hineq
  let Q' : E → ℝ := fun x => if hx : x ∈ K then Q x hx else 0
  intro z hz hz1
  apply linear_cutoff_uniform hK hU hKU (contDiffOn_const.mul hS) hT (hχ.pow 2).contDiffOn
    hC1 (mul_nonneg hA0 hR0) (show (0:ℝ)<1 by norm_num)
    (S := fun y => A*S y) (η := fun y => (χ y)^2) ?_ ?_ v Q' ?_ z hz (by rw [hz1]; norm_num)
  · intro x hx
    obtain ⟨hs,hsR,ht⟩ := hvalues x hx
    obtain ⟨hχ0,hχ1⟩ := hχval x hx
    exact ⟨mul_nonneg hA0 hs,mul_le_mul_of_nonneg_left hsR hA0,ht,sq_nonneg _,by nlinarith⟩
  · intro x hx hn
    exact hχint x hx (fun he => hn (by rw [he]; ring))
  · intro x hx _
    have hqx : Q' x=Q x hx := dite_eq_left hx
    rw [hqx]
    obtain ⟨hLχ,hGχ⟩ := hcut x hx (v x) (hv x hx)
    refine ⟨hQ x hx,?_,?_,(neg_le_neg hc0).trans hLχ,hGχ.trans (mul_le_mul_of_nonneg_right hc0 (sq_nonneg _)),hGT x hx⟩
    · rw [frameLaplace_const_mul hU hS (hKU hx)]
      have hh := mul_le_mul_of_nonneg_left (hLS x hx) hA0
      have ht := htD x hx
      nlinarith only [hh,ht,har]
    · have hh := mul_le_mul_of_nonneg_right hr1 (show 0 ≤ 1+T x by linarith [(hvalues x hx).2.2])
      linarith only [hLT x hx,hh]
end HigherJet

end
end

end OAI
