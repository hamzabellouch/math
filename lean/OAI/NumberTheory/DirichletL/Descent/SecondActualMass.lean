import OAI.NumberTheory.DirichletL.Descent.SecondTripleBounds

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzero_ideal_norm_one (I : Ideal Eis) (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_normalized_mass_source_bounds (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      0 < B → 0 < T → 0 < R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro Γ B T R hB hT hR hz hn
  rcases Γ.eq_empty_or_nonempty with he|⟨γ,hγ⟩
  · subst Γ
    simp only [Finset.sum_empty,mul_zero]
    positivity
  · obtain ⟨hq,ht,hr⟩ := hz γ hγ
    obtain ⟨hqb,htb,hrb⟩ := hn γ hγ
    exact hb Γ B T R ((nonzero_ideal_norm_one _ hq).trans hqb)
      ((nonzero_ideal_norm_one _ ht).trans htb) ((nonzero_ideal_norm_one _ hr).trans hrb) hz hn

theorem actual_second_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
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
      Z^(-(ell+R/2-j+t+g-theta+11*eta/2)) *
        (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*ε) := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass_source_bounds K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hz : ∀ γ ∈ actualSecondTriples p u v source,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0 := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    exact (actualSecondChild_nonzero p hp u v x (ht x hx)).2
  have hn : ∀ γ ∈ actualSecondTriples p u v source,
      (Ideal.absNorm γ.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ Z^(t+eta) ∧
      (Ideal.absNorm γ.residual : ℝ) ≤ Z^(g-theta+2*eta) := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    refine ⟨actual_second_q0_power_bound p hp x u v Z ell R j eta hZ
      (h1 x hx) (h2 x hx) (ha x hx) (hJ x hx),hT x hx,?_⟩
    have hr := second_residual_norm_power_bound p hp _ _ (hE x hx) Z g theta eta hZ (hG x hx) (hD x hx)
    change (Ideal.absNorm (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) : ℝ) ≤ _
    simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hr
  have hm := hb (actualSecondTriples p u v source)
    (Z^(ell+R/2-j+5*eta/2)) (Z^(t+eta)) (Z^(g-theta+2*eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hz hn
  have he : Z^(ell+R/2-j+5*eta/2)*Z^(t+eta)*Z^(g-theta+2*eta) =
      Z^(ell+R/2-j+t+g-theta+11*eta/2) := by
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
    congr 1
    ring
  rw [he,←Real.rpow_mul hZ.le,←Real.rpow_neg hZ.le] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI
