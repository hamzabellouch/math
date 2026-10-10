import OAI.NumberTheory.DirichletL.Descent.SecondActualMass

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_second_original_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*(1+ε)) := by
  obtain ⟨C,hC,hb⟩ := actual_second_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hm := hb p hp source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  let c := ell+R/2-j+t+g-theta+11*eta/2
  calc
    _ = Z^c * (Z^(-c)*(∑ γ∈actualSecondTriples p u v source,tripleDivisorWeight K γ)) := by
      rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _ ≤ Z^c*(C*Z^(c*ε)) := mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hZ _).le
    _ = _ := by
      rw [mul_left_comm,←Real.rpow_add hZ]
      congr 2
      dsimp only [c]
      ring

end
end SevenEighths.InverseMoment

end OAI
