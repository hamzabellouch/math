import OAI.NumberTheory.DirichletL.Descent.FirstSourceSize

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem choose_actual_first_tail_order (Mmax Fmax eta tau saving : ℝ)
    (hMm : 0≤Mmax) (hFm : 0≤Fmax) (heta : 0≤eta) (htau : 0<tau) :
    ∃ order : ℕ,∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (b : CubeCoordinates ι) (C D : Finset ι),Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      ∀ (Z M r ell V G₁ G₂ P : ℝ),1≤Z → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤r →
      r+3*ell+V≤Fmax → 0≤G₁ → 0≤G₂ → 0≤P →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      primeProductNorm p C≤Z^(r+eta) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C)
      let active := cubeActiveSupport b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p D*primeProductNorm p active*U₁*U₂)
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*(P/((min 1 slow)^2*(1+Z^tau)^order))≤
        65536*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨order,he⟩ := choose_first_tail_order (Mmax+Fmax+3*eta) tau saving (by linarith) htau
  refine ⟨order,?_⟩
  intro ι _ p hp _ b C D hCB hD Z M r ell V G₁ G₂ P hZ hM hMmax hell hV hr hwhole hG₁ hG₂ hP h1 h2 hC
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨hk,hki,hd,ha,hu⟩ := first_source_scalar_caps p hp b C D hCB hD
    Z M Mmax Fmax r ell V eta hZ hM hMmax hFm hell hV heta hr hwhole h1 h2 hC
  have hapos (eps : ι→Bool) : 0<‖eisEmbedding (aLabel p b.support eps)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  exact he Z (Z^M) (primeProductNorm p D)
    (primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
    (Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C))
    (Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C))
    G₁ G₂ P hZ (Real.rpow_pos_of_pos hz _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    hG₁ hG₂ hP hk hki hd ha (hu _) (hu _)

end
end SevenEighths.InverseMoment

end OAI
