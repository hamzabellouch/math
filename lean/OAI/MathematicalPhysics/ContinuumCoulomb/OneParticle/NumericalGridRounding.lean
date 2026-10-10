import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EnumeratedGridNuclei
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GroundRoundingInterval
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGaussList
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalFieldDifferences

namespace OAI

/-! Transfer of the full ground-energy interval to the actual rational
Euler/Gauss nodes, with the physical inverse-scale coordinates. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open CappedKernelProgram (Triple position)

def physicalRationalNuclei {m : ℕ} (hm : 0 < m) (q : Fin m → Triple)
    (hq : Function.Injective q) {scale : ℝ} (hs : 0 < scale) : Coulomb.Nuclei m where
  nonempty := hm
  position a := scale⁻¹ • position (q a)
  distinct := by
    intro a b hab
    apply hq
    apply RationalFieldDifferences.position_injective
    have he := congrArg (fun x : Position => scale • x) hab
    simpa only [smul_inv_smul₀ hs.ne'] using he
  charge _ := 1
  charge_ge_one _ := le_rfl

theorem physicalRationalNuclei_totalCharge {m : ℕ} (hm : 0 < m) (q : Fin m → Triple)
    (hq : Function.Injective q) {scale : ℝ} (hs : 0 < scale) :
    Coulomb.totalCharge (physicalRationalNuclei hm q hq hs)=m := by
  simp [Coulomb.totalCharge,physicalRationalNuclei]

namespace CenteredGaussLabels

theorem numerical_ground_interval (r : Radii) (rho U C K P : ℕ) {N : ℕ} (hN : 0 < N)
    (fieldScale S : ℚ) (sites : List (ℚ×ℚ)) (G : Position → Position)
    (hG : Function.Injective G) {J : ℝ≥0} (hAnti : AntilipschitzWith J G)
    (herror : ∀ l : TransformedGauss.Label,
      ‖position (TransformedGauss.value rho U C K P N fieldScale S sites l.1 l.2)-
        G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤ ((P:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (N:ℝ)⁻¹/3)
    {scale : ℝ} (hs : 0 < scale) (n : ℕ) {center error roundError : ℝ}
    (hlo : ((center-error:ℝ):EReal) ≤
      formGroundEnergy (dilatedNuclei (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) scale hs.ne') n)
    (hhi : formGroundEnergy (dilatedNuclei (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) scale hs.ne') n ≤
      ((center+error:ℝ):EReal))
    (hsmall : 32*(scale⁻¹*((P:ℝ)+1)⁻¹)*(labels r).length ≤ 1)
    (hbudget : 32*(scale⁻¹*((P:ℝ)+1)⁻¹)*(labels r).length*
      (center+error+4*(n:ℝ)*((labels r).length:ℝ)^2) ≤ roundError) :
    let q := fun a : Fin (labels r).length => TransformedGauss.value rho U C K P N fieldScale S sites
      ((labels r).get a).1 ((labels r).get a).2
    ∃ hq : Function.Injective q,
      ((center-error-roundError:ℝ):EReal) ≤
        formGroundEnergy (physicalRationalNuclei (by rw [labels_length]; positivity) q hq hs) n ∧
      formGroundEnergy (physicalRationalNuclei (by rw [labels_length]; positivity) q hq hs) n ≤
        ((center+error+roundError:ℝ):EReal) := by
  dsimp only
  let q := fun a : Fin (labels r).length => TransformedGauss.value rho U C K P N fieldScale S sites
    ((labels r).get a).1 ((labels r).get a).2
  have hlabels : Function.Injective (fun a : Fin (labels r).length => (labels r).get a) := by
    intro a b hab
    apply (List.Nodup.getEquiv (labels r) (labels_nodup r)).injective
    exact Subtype.ext hab
  have hq : Function.Injective q := TransformedGauss.value_injective _ hlabels rho U C K P hN
    fieldScale S sites G hAnti (fun a => herror ((labels r).get a)) hprecision
  refine ⟨hq,?_⟩
  let exactNuc := dilatedNuclei (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) scale hs.ne'
  let approxNuc := physicalRationalNuclei (by rw [labels_length]; positivity) q hq hs
  have hcharge : exactNuc.charge=approxNuc.charge := rfl
  have htotal : Coulomb.totalCharge exactNuc=(labels r).length := by
    change Coulomb.totalCharge (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) = _
    exact nuclei_totalCharge r G hG (by positivity : 0 < (N:ℝ)⁻¹)
  have hmove (a : Fin (labels r).length) :
      ‖exactNuc.position a-approxNuc.position a‖ ≤ scale⁻¹*((P:ℝ)+1)⁻¹ := by
    change ‖scale⁻¹ • G (gaussLatticePoint (N:ℝ)⁻¹
      (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2))-
        scale⁻¹ • position (q a)‖ ≤ _
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (herror ((labels r).get a)) (inv_nonneg.mpr hs.le)
  apply formGroundEnergy_rounding_interval exactNuc approxNuc hlo hhi (by positivity)
    hcharge hmove
  · simpa only [htotal] using hsmall
  · simpa only [htotal] using hbudget

end CenteredGaussLabels
end ContinuumCoulomb

end

end OAI
