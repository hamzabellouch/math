import Mathlib
import OAI.Analysis.HardSphere.Fourier.CharacterDerivativeFactor
import OAI.Analysis.HardSphere.Operators.CompactFormCutoff

namespace OAI

section

noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ComplexOrder
namespace HardSphere

lemma finite_fourier_resolvent (N : ℕ) (L : Length) (ε : ℝ) (hε : 0<ε) :
    {k : Direction N→ℤ | ε≤(1+fourierEnergy N L k)⁻¹}.Finite := by
  have hL := L.property
  let b : ℝ := 2*Real.pi/L.val
  have hb : 0<b := by dsimp only [b]; positivity
  let C : ℝ := 1/(ε*b^2)
  have hC : 0<C := by dsimp only [C]; positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (Real.sqrt C)
  apply (Set.Finite.pi (fun p : Direction N ↦ Set.finite_Icc (-(M:ℤ)) M)).subset
  intro k hk p _
  change ε≤(1+fourierEnergy N L k)⁻¹ at hk
  have hE := fourierEnergy_nonneg N L k
  have he : ε*(1+fourierEnergy N L k)≤1 :=
    (le_div_iff₀ (by linarith : 0<1+fourierEnergy N L k)).mp (by simpa only [one_div] using hk)
  have hp : (2*Real.pi*k p/L.val)^2≤fourierEnergy N L k := by
    unfold fourierEnergy
    exact Finset.single_le_sum (fun q _ ↦ sq_nonneg (2*Real.pi*k q/L.val)) (Finset.mem_univ p)
  have hx : (k p:ℝ)^2≤C := by
    apply (le_div_iff₀ (by positivity : 0<ε*b^2)).mpr
    calc
      (k p:ℝ)^2*(ε*b^2) = ε*(2*Real.pi*k p/L.val)^2 := by dsimp only [b]; ring
      _ ≤ ε*fourierEnergy N L k := mul_le_mul_of_nonneg_left hp hε.le
      _ ≤ 1 := by nlinarith
  have ha : |(k p:ℝ)|≤Real.sqrt C := by
    nlinarith [Real.sq_sqrt hC.le,Real.sqrt_nonneg C,sq_abs (k p:ℝ),abs_nonneg (k p:ℝ)]
  have hh := abs_le.mp (ha.trans hM.le)
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

lemma free_scalarEmbedding_compact (N : ℕ) (L : Length) :
    IsCompactOperator (scalarEmbedding N L (-1)) := by
  apply CompactForm.compact_embedding (scalarEmbedding N L (-1)) (formResolvent N L (-1))
    rfl (formResolvent_isPositive N L (-1)) (formResolvent_norm_le_one N L (-1))
    (characterL2 N L) (fun k ↦ (1+fourierEnergy N L k)⁻¹)
    (characterL2_span_dense N L)
  · intro k
    change formResolvent N L (-1) (characterL2 N L k) =
      ((1+fourierEnergy N L k)⁻¹:ℝ) • characterL2 N L k
    rw [←IsScalarTower.algebraMap_smul ℂ ((1+fourierEnergy N L k)⁻¹:ℝ) (characterL2 N L k)]
    change formResolvent N L (-1) (characterL2 N L k) =
      (((1+fourierEnergy N L k)⁻¹:ℝ):ℂ) • characterL2 N L k
    simpa only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one] using
      character_resolvent N L (-1) (by norm_num) k
  · exact finite_fourier_resolvent N L

lemma scalarEmbedding_compact (N : ℕ) (L : Length) {a : ℝ} (ha : 0<a) :
    IsCompactOperator (scalarEmbedding N L a) := by
  let ι : hilbertDomain N L a →L[ℂ] hilbertDomain N L (-1) :=
    ((hilbertDomain N L a).subtypeL).codRestrict (hilbertDomain N L (-1))
      (fun u ↦ hilbertDomain_antitone N L (by linarith : -1≤a) u.property)
  have hh := (free_scalarEmbedding_compact N L).comp_clm ι
  exact hh

lemma formResolvent_compact (N : ℕ) (L : Length) {a : ℝ} (ha : 0<a) :
    IsCompactOperator (formResolvent N L a) :=
  (scalarEmbedding_compact N L ha).comp_clm (scalarEmbedding N L a).adjoint

end HardSphere
end
end

end OAI
