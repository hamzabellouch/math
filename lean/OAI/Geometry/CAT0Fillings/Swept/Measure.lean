import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Currents.PushMajorant
import OAI.Geometry.CAT0Fillings.Prism.Differential
import OAI.Geometry.CAT0Fillings.Swept.RadialChart

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

local instance {k : ℕ} : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := borel _
local instance {k : ℕ} : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩

lemma measurable_matrix_inverse {E : Type*} [MeasurableSpace E] {k : ℕ}
    (P : E → Matrix (Fin k) (Fin k) ℝ) (hm : Measurable P) :
    Measurable (fun z => (P z)⁻¹) := by
  have hd : Measurable (fun z => (P z).det) := continuous_id.matrix_det.measurable.comp hm
  have ha : Measurable (fun z => (P z).adjugate) := continuous_id.matrix_adjugate.measurable.comp hm
  simp only [Matrix.inv_def,Ring.inverse_eq_inv]
  convert hd.inv.smul ha using 1

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [nonemptyX : Nonempty X] {k : ℕ} (C : IntegerChart X k)

include nonemptyX

omit nonemptyX in
lemma aestronglyMeasurable_sweptWeight [Nonempty X]
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    AEStronglyMeasurable (C.sweptWeight p o g) (volume.restrict C.domain) := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  let P (z : Euc k) := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hPm : Measurable P := by
    have hh : Measurable (fun z i j => P z i j) :=
      measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
        measurable_polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis hpm i j
    have heq : _root_.borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi :=
      BorelSpace.measurable_eq.symm
    change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (_root_.borel _) P
    rw [heq]
    exact hh
  have hRd : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [differentialRow]
    fun_prop
  have hPi := measurable_matrix_inverse P hPm
  let J (z : Euc k) := C.scalar (dist o) z*C.scalar g z*
    Real.sqrt (1-differentialRow (fderiv ℝ R z) ⬝ᵥ
      (P z)⁻¹.mulVec (differentialRow (fderiv ℝ R z)))*Real.sqrt (P z).det
  have hJ : Measurable J := by
    have hprod : Measurable (fun z => differentialRow (fderiv ℝ R z) ⬝ᵥ
        (P z)⁻¹.mulVec (differentialRow (fderiv ℝ R z))) := by
      have hc : Continuous (fun q : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
          q.1 ⬝ᵥ q.2.mulVec q.1) := by fun_prop
      exact hc.measurable.comp (hRd.prodMk hPi)
    exact (((C.measurable_scalar (LipschitzWith.dist_right o)).mul (C.measurable_scalar hg)).mul
      ((measurable_const.sub hprod).sqrt)).mul
      ((continuous_id.matrix_det.measurable.comp hPm).sqrt)
  apply hJ.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR] with z hz
  simp only [J,sweptWeight,hz,P]

omit nonemptyX in
lemma ae_sweptWeight_nonneg [Nonempty X]
    (p : Euc k → Seminorm ℝ (Euc k)) (o : X) {g : X → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) : 0 ≤ᵐ[volume.restrict C.domain] C.sweptWeight p o g := by
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simp only [sweptWeight,C.scalar_eq hz]
  exact mul_nonneg (mul_nonneg (mul_nonneg dist_nonneg (hg0 _)) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

omit nonemptyX in
lemma ae_sweptWeight_bound [Nonempty X]
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (o : X) {g : X → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    {B : ℝ} (hB : ∀ x, dist o x*g x ≤ B) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.sweptWeight p o g z ≤ B*Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  filter_upwards [hp,ae_restrict_mem C.borel] with z hpz hz
  let G := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let α := differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z)
  have hG : G.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hq : 0 ≤ α ⬝ᵥ G⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  have hs : Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α) ≤ 1 := by
    apply (Real.sqrt_le_left zero_le_one).mpr
    linarith
  change C.scalar (dist o) z*C.scalar g z*Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α)*Real.sqrt G.det ≤ _
  rw [C.scalar_eq hz,C.scalar_eq hz]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact ((mul_le_mul_of_nonneg_left hs (mul_nonneg dist_nonneg (hg0 _))).trans_eq
    (mul_one _)).trans (hB _)

theorem integrable_sweptWeight
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict C.domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ x, 0 ≤ g x) {B : ℝ} (hB : ∀ x, dist o x*g x ≤ B) :
    Integrable (fun z => |(C.multiplicity z : ℝ)| * C.sweptWeight p o g z)
      (volume.restrict C.domain) := by
  apply (hρ.const_mul B).mono'
    (C.integrable.abs.aestronglyMeasurable.mul (C.aestronglyMeasurable_sweptWeight p hpm o hg))
  filter_upwards [C.ae_sweptWeight_nonneg p o hg0,C.ae_sweptWeight_bound p hp o hg0 hB] with z hn hb
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (by ring)
end IntegerChart
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma integrable_prism_tail {f : Euc k → ℝ}
    (hf : Integrable f (volume.restrict C.domain)) :
    Integrable (fun z => f (Prism.tail k z)) (volume.restrict C.prism.domain) := by
  have hi := hf.comp_snd (volume.restrict (Icc (0:ℝ) 1))
  rw [Measure.prod_restrict] at hi
  exact ((Prism.split_measurePreserving k).restrict_preimage
    (measurableSet_Icc.prod C.borel)).integrable_comp_emb
      (Prism.split k).toHomeomorph.measurableEmbedding |>.mpr hi

lemma integral_prism_tail {f : Euc k → ℝ}
    (hf : Integrable f (volume.restrict C.domain)) :
    (∫ z, f (Prism.tail k z) ∂volume.restrict C.prism.domain) =
      ∫ z, f z ∂volume.restrict C.domain := by
  rw [←C.prism_split_measurePreserving.integral_comp
    (Prism.split k).symm.toHomeomorph.measurableEmbedding]
  have heq (q : ℝ × Euc k) : Prism.tail k ((Prism.split k).symm q) = q.2 := by
    change (Prism.split k ((Prism.split k).symm q)).2 = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [heq]
  rw [integral_prod _ (hf.comp_snd _)]
  simp [integral_const,Measure.real,Real.volume_Icc]

variable [Nonempty X] [MeasurableSpace X] [BorelSpace X]

theorem swept_prism_mass_le
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg KF : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (F : ℝ × X → X) (hF : LipschitzWith KF F)
    (hFeq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y, F (t,y) = seg o y (1-t*g y))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hI : Integrable (fun z => |(C.multiplicity z : ℝ)| *C.sweptWeight p o g z)
      (volume.restrict C.domain))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0)) :
    mass (pushCurrent F C.prism.action) ≤
      ∫ z, |(C.multiplicity z : ℝ)| *C.sweptWeight p o g z ∂volume.restrict C.domain := by
  have hi : Integrable (fun z => |(C.prism.multiplicity z : ℝ)| *
      C.sweptWeight p o g (Prism.tail k z)) (volume.restrict C.prism.domain) :=
    C.integrable_prism_tail hI
  have hm := C.prism.push_mass_le_majorant hF hi
    (C.ae_prism_tail (C.ae_sweptWeight_nonneg p o hg0))
    (C.ae_swept_jacobian_bound seg hcomp o g hg hg0 hg1 F hF hFeq p hp)
  exact hm.trans_eq (C.integral_prism_tail hI)

end IntegerChart
end CAT0Fillings
end

end OAI
