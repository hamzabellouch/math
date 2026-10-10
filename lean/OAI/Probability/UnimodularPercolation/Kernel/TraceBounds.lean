import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.RussoRows

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RussoOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem russoSlope_symm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x y : V) :
    russoSlope G x y (p:ℝ) = russoSlope G y x (p:ℝ) := by
  have hh := hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ x y
  have he : realTwoPoint G x y = realTwoPoint G y x := funext (fun _ => twoPoint_symm G _ x y)
  rw [he] at hh
  exact hh.unique (hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ y x)

theorem russoSlope_aut [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    russoSlope G (a x) (a y) (p:ℝ) = russoSlope G x y (p:ℝ) := by
  have hh := hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ (a x) (a y)
  have he : realTwoPoint G (a x) (a y) = realTwoPoint G x y := funext (fun _ => twoPoint_aut G _ hab x y)
  rw [he] at hh
  exact hh.unique (hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ x y)

 

theorem exists_russoOperator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) :
    ∃ D : Hilbert V →L[ℂ] Hilbert V,
      ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ) := by
  obtain ⟨R,hR,hrow⟩ := russoMajorant_uniform_row_bound G hloc hqt p hp
  have hb (x : V) (s : Finset V) : ∑ y ∈ s, russoSlope G x y (p:ℝ) ≤ R := by
    calc
      _ ≤ ∑ y ∈ s, russoMajorant G p x y := Finset.sum_le_sum (fun y _ => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)
      _ ≤ ∑' y, russoMajorant G p x y := Summable.sum_le_tsum s (fun y _ => russoMajorant_nonneg G p x y)
        (summable_russoMajorant G hloc hqt p hp x)
      _ ≤ R := hrow x
  obtain ⟨D,_,hD⟩ := exists_operator_of_row_column_bound (fun x y => russoSlope G x y (p:ℝ)) R hR
    (fun x y => russoSlope_nonneg G x y p p.2.2) hb
    (fun y s => by simpa only [russoSlope_symm G hloc hqt p hp0 hp] using hb y s)
  exact ⟨D,hD⟩

theorem russoOperator_positiveReal (G : BondGraph V E) (p : unitInterval)
    (D : Hilbert V →L[ℂ] Hilbert V)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) : PositiveRealMatrix D := by
  intro x y
  rw [hD x y]
  exact ⟨rfl,russoSlope_nonneg G x y p p.2.2⟩

theorem russoOperator_invariant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (D : Hilbert V →L[ℂ] Hilbert V)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ))
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) : KernelInvariant Γ D := by
  intro a ha x y
  obtain ⟨b,hab⟩ := hΓ ha
  simp only [hD,russoSlope_aut G hloc hqt p hp0 hp hab]

end RussoOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PositiveTriangleSeries
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem PositiveRealMatrix.triple_hasSum
    {A B C : Hilbert V →L[ℂ] Hilbert V}
    (hA : PositiveRealMatrix A) (hB : PositiveRealMatrix B) (hC : PositiveRealMatrix C)
    (x y : V) :
    HasSum (fun ab : V×V => (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re *
      (matrixCoeff C ab.2 y).re) (matrixCoeff (A*B*C) x y).re := by
  have hi (a : V) : HasSum (fun b => (matrixCoeff A x a).re * (matrixCoeff B a b).re * (matrixCoeff C b y).re)
      ((matrixCoeff A x a).re * (matrixCoeff (B*C) a y).re) := by
    simpa only [mul_assoc] using (hB.mul_hasSum C a y).mul_left (matrixCoeff A x a).re
  have ho := hA.mul_hasSum (B*C) x y
  have hs : Summable (fun ab : V×V => (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re * (matrixCoeff C ab.2 y).re) := by
    apply (summable_prod_of_nonneg (f := fun ab : V×V => (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re * (matrixCoeff C ab.2 y).re)
      (fun ab => mul_nonneg (mul_nonneg (hA _ _).2 (hB _ _).2) (hC _ _).2)).mpr
    refine ⟨fun a => (hi a).summable,?_⟩
    simp only [(hi _).tsum_eq]
    exact ho.summable
  have he : (∑' ab : V×V, (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re * (matrixCoeff C ab.2 y).re) =
      (matrixCoeff (A*B*C) x y).re := by
    rw [hs.tsum_prod]
    simp only [(hi _).tsum_eq]
    rw [ho.tsum_eq,mul_assoc]
  exact he ▸ hs.hasSum

theorem HasKernel.matrixCoeff_re (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (matrixCoeff T x y).re = twoPoint G p x y := by
  change (T (lp.single 2 y (1:ℂ)) x).re = _
  rw [hT x y,Complex.ofReal_re]

theorem realTriangle_eq_matrixCoeff (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x : V) :
    realTriangle G x (p:ℝ) = (matrixCoeff (T^3) x x).re := by
  have ht := hT.positiveRealMatrix G p T
  have hs := ht.triple_hasSum ht ht x x
  rw [show T*T*T = T^3 by simp only [pow_succ,pow_zero,one_mul]] at hs
  simpa only [HasKernel.matrixCoeff_re G p T hT,realTriangle,realTriangleTerm,realTwoPoint_coe] using hs.tsum_eq

theorem rootTriangle_eq_trace (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) :
    rootTriangle G root weight (p:ℝ) = (rootTrace root weight (T^3)).re := by
  simp only [rootTriangle,realTriangle_eq_matrixCoeff G p T hT,rootTrace,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem triangleSlope_eq_matrixCoeff (G : BondGraph V E) (p : unitInterval)
    (T D : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) (x : V) :
    (∑' ab, realTriangleSlope G x ab (p:ℝ)) =
      (matrixCoeff (D*T*T + T*D*T + T*T*D) x x).re := by
  have ht := hT.positiveRealMatrix G p T
  have hd := russoOperator_positiveReal G p D hD
  have h₁ := (hd.triple_hasSum ht ht x x)
  have h₂ := (ht.triple_hasSum hd ht x x)
  have h₃ := (ht.triple_hasSum ht hd x x)
  have h := (h₁.add h₂).add h₃
  have ha (A B : Hilbert V →L[ℂ] Hilbert V) : matrixCoeff (A+B) x x = matrixCoeff A x x + matrixCoeff B x x := rfl
  simp only [ha,Complex.add_re]
  simpa only [hD,Complex.ofReal_re,HasKernel.matrixCoeff_re G p T hT,
    realTriangleSlope,realTwoPoint_coe] using h.tsum_eq

end PositiveTriangleSeries
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleTraceDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootTrace_triangleSlope_cyclic
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    {Γ : Set (V ≃ V)} (htr : RootTransport root weight Γ)
    (T D : Hilbert V →L[ℂ] Hilbert V) (hT : KernelInvariant Γ T) (hD : KernelInvariant Γ D) :
    rootTrace root weight (D*T*T+T*D*T+T*T*D) = 3*rootTrace root weight (T^2*D) := by
  have h₁ : rootTrace root weight (D*T*T) = rootTrace root weight (T^2*D) := by
    rw [mul_assoc,rootTrace_cyclic root weight htr D (T*T) hD (hT.mul hT),pow_two]
  have h₂ : rootTrace root weight (T*D*T) = rootTrace root weight (T^2*D) := by
    rw [mul_assoc,rootTrace_cyclic root weight htr T (D*T) hT (hD.mul hT),h₁]
  rw [rootTrace_add,rootTrace_add,h₁,h₂,←pow_two]
  ring

 

theorem hasDerivAt_rootTriangle_trace [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (T D : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) :
    HasDerivAt (rootTriangle G root weight) (3*(rootTrace root weight (T^2*D)).re) (p:ℝ) := by
  have hti : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hdi := russoOperator_invariant G hloc hqt p hp0 hp D hD Γ hΓ
  have hs := hasDerivAt_rootTriangle_subcritical G hloc hqt root weight p hp0 hp
  have he : (∑ i, weight i * ∑' ab, realTriangleSlope G (root i) ab (p:ℝ)) =
      3*(rootTrace root weight (T^2*D)).re := by
    simp only [triangleSlope_eq_matrixCoeff G p T D hT hD]
    have hr := congrArg Complex.re (rootTrace_triangleSlope_cyclic root weight htr T D hti hdi)
    simpa only [rootTrace,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] using hr
  exact he ▸ hs

end RootTriangleTraceDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section ContactKernelReroot
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem contactKernel_reroot [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y) =
      ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        J (root i) y * ENNReal.ofReal (fullLargeContact G (root i) y 0 ω) ∂law p := by
  have ht := clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin
    J hJ (fun ω x y => ENNReal.ofReal (fullLargeContact G x y 0 ω))
    (fun x y => (measurable_fullLargeContact G hloc x y 0).ennreal_ofReal)
    (fun ω x y a b hxa hyb => congrArg ENNReal.ofReal (fullLargeContact_cluster_constant G ω 0 x y a b hxa hyb))
    (fun a _ b hab ω x y => congrArg ENNReal.ofReal (fullLargeContact_aut G hab ω x y 0))
  simp_rw [fullLargeContact_distinct] at ht
  rw [←ht]
  unfold clusterPairFunctional
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hfin (root i)] with ω hω
  unfold clusterPairDensity
  congr 1
  apply tsum_congr
  intro y
  congr 1
  by_cases hd : Conn G ω (root i) y
  · simp only [hd,not_true_eq_false,ite_false]
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [clusterPairKernel_edge G hloc ω (root i) y hd hω]
    simp only [fullLargeContact,hd,not_false_eq_true,Nat.zero_le,and_self,ite_true,ENNReal.ofReal_natCast]
    exact mul_comm _ _

theorem contact_lintegral_eq_russoOperator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Hilbert V →L[ℂ] Hilbert V)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) (x y : V) :
    (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ENNReal.ofReal (1-(p:ℝ)) * ennMatrixCoeff D x y := by
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Eventually.of_forall (fullLargeContact_nonneg G x y 0))]
  simp only [ennMatrixCoeff,hD,Complex.ofReal_re,russoSlope,realContactExpectation_coe]
  rw [←ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]
  congr 1
  have hd : 1-(p:ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr ((show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2))
  exact (mul_div_cancel₀ _ hd).symm

end ContactKernelReroot
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section MixedRussoTrace
attribute [local instance] Classical.propDecidable Classical.decEq

theorem mixedFunctional_eq_russoTrace [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (J D : Hilbert V →L[ℂ] Hilbert V) (hJ : PositiveRealMatrix J) (hiJ : KernelInvariant Γ J)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff J) x y) =
      ENNReal.ofReal ((1-(p:ℝ))*(rootTrace root weight (J*D)).re) := by
  have hd := russoOperator_positiveReal G p D hD
  have hdi (x y : V) : ennMatrixCoeff D x y = ennMatrixCoeff D y x := by
    simp only [ennMatrixCoeff,hD,Complex.ofReal_re,russoSlope_symm G hloc hqt p hp0 hp x y]
  have hji : ∀ a ∈ Γ, ∀ x y, ennMatrixCoeff J (a x) (a y) = ennMatrixCoeff J x y := by
    intro a ha x y; unfold ennMatrixCoeff; rw [hiJ a ha]
  rw [contactKernel_reroot G hconn hloc root weight Γ hΓ htr hw p
    (subcritical_cluster_finite_ae G p hp) (ennMatrixCoeff J) hji]
  have he (x : V) : (∫⁻ ω, ∑' y, ennMatrixCoeff J x y * ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ENNReal.ofReal (1-(p:ℝ)) * ennMatrixCoeff (J*D) x x := by
    have hm (y : V) : Measurable (fun ω : Set E => ennMatrixCoeff J x y * ENNReal.ofReal (fullLargeContact G x y 0 ω)) :=
      (measurable_const : Measurable (fun _ : Set E => ennMatrixCoeff J x y)).mul
        (measurable_fullLargeContact G hloc x y 0).ennreal_ofReal
    rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
    simp_rw [lintegral_const_mul _ (measurable_fullLargeContact G hloc x _ 0).ennreal_ofReal,
      contact_lintegral_eq_russoOperator G hloc hqt p hp D hD]
    rw [ennMatrixCoeff_mul hJ hd,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro y
    rw [hdi x y]
    ac_rfl
  simp_rw [he]
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2),←enn_rootTrace root weight hw (J*D) (hJ.mul hd),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem mixedFunctional_toReal_eq_russoTrace [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (J D : Hilbert V →L[ℂ] Hilbert V) (hJ : PositiveRealMatrix J) (hiJ : KernelInvariant Γ J)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) :
    (clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff J) x y)).toReal =
      (1-(p:ℝ))*(rootTrace root weight (J*D)).re := by
  rw [mixedFunctional_eq_russoTrace G hconn hloc hqt root weight Γ hΓ htr hw p hp0 hp J D hJ hiJ hD]
  apply ENNReal.toReal_ofReal
  apply mul_nonneg (sub_nonneg.mpr p.2.2)
  have hd := hJ.mul (russoOperator_positiveReal G p D hD)
  simp only [rootTrace,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hd _ _).2)

end MixedRussoTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleRusso
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem rootTriangle_russo [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) :
    (1-(p:ℝ))*deriv (rootTriangle G root weight) (p:ℝ) =
      3*(clusterPairFunctional G p root weight (fun ω x y =>
        clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)).toReal := by
  obtain ⟨D,hD⟩ := exists_russoOperator G hloc hqt p hp0 hp
  have hi : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  rw [(hasDerivAt_rootTriangle_trace G hloc hqt root weight Γ hΓ htr p hp0 hp T D hT hD).deriv,
    mixedFunctional_toReal_eq_russoTrace G hconn hloc hqt root weight Γ hΓ htr hw p hp0 hp
      (T^2) D ((hT.positiveRealMatrix G p T).pow 2) (hi.pow 2) hD]
  ring

theorem realTriangle_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ realTriangle G x (p:ℝ) := by
  have hh := (summable_realTriangleTerm G hloc hqt p hp x).le_tsum (x,x)
    (fun ab _ => by
      simp only [realTriangleTerm,realTwoPoint_coe]
      exact mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _))
  simpa only [realTriangleTerm,realTwoPoint_coe,twoPoint_self,mul_one,realTriangle] using hh

theorem rootTriangle_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ rootTriangle G root weight (p:ℝ) := by
  calc
    1 = ∑ i, weight i * 1 := by simpa using hw1.symm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (realTriangle_one_le G hloc hqt p hp (root i)) (hw i))

end RootTriangleRusso
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section RealMixedTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem critical_mixed_trace_bound_real
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        (clusterPairFunctional G p root weight (fun ω x y =>
          clusterPairKernel G ω (indexedEdgeKernel G) x y *
          clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)).toReal ≤
        2*(A*L^(1-α)*rootTriangle G root weight (p:ℝ)) +
          (B*L^((1:ℝ)/2+ε-2*α))^((1:ℝ)/2) *
          (‖T‖^3*rootTriangle G root weight (p:ℝ))^((1:ℝ)/2) := by
  obtain ⟨A,B,hA,hB,hb⟩ := critical_mixed_trace_bound G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  refine ⟨A,B,hA,hB,?_⟩
  intro p hp hpq T hT L hL
  have ht : 0 ≤ rootTriangle G root weight (p:ℝ) := (rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 p hpq).trans' (by norm_num)
  have ha : 0 ≤ A*L^(1-α)*rootTriangle G root weight (p:ℝ) := mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _)) ht
  have hc : 0 ≤ B*L^((1:ℝ)/2+ε-2*α) := mul_nonneg hB.le (Real.rpow_nonneg (by linarith) _)
  have hn : 0 ≤ ‖T‖^3*rootTriangle G root weight (p:ℝ) := mul_nonneg (pow_nonneg (norm_nonneg _) _) ht
  have hb' := hb p hp hpq.le T hT L hL
  rw [←rootTriangle_eq_trace G p root weight T hT] at hb'
  have htop : 2*ENNReal.ofReal (A*L^(1-α)*rootTriangle G root weight (p:ℝ)) +
      (ENNReal.ofReal (B*L^((1:ℝ)/2+ε-2*α)))^((1:ℝ)/2) *
      (ENNReal.ofReal (‖T‖^3*rootTriangle G root weight (p:ℝ)))^((1:ℝ)/2) ≠ ⊤ := by finiteness
  have hh := ENNReal.toReal_mono htop hb'
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hh
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofNat,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hc,ENNReal.toReal_ofReal hn] using hh

end RealMixedTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceNumerics
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem HasKernel.norm_le_susceptibility_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, susceptibility G p x ≤ C) :
    ‖T‖ ≤ C := by
  have hr (x : V) (s : Finset V) : ∑ y ∈ s, twoPoint G p x y ≤ C :=
    ((summable_twoPoint_subcritical G hloc hqt p hp x).sum_le_tsum s
      (fun y _ => twoPoint_nonneg G p x y)).trans (hb x)
  obtain ⟨S,hS,hK⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC (twoPoint_nonneg G p)
    hr (fun y s => by simpa only [twoPoint_symm G p] using hr y s)
  rwa [hT.unique hK]

lemma sqrt_mixed_power (B L m a r : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hm : 0 ≤ m) (ha : 0 ≤ a) :
    (B*L^r)^((1:ℝ)/2) * (m^3*a)^((1:ℝ)/2) =
      Real.sqrt B * L^(r/2) * m^((3:ℝ)/2) * Real.sqrt a := by
  rw [Real.mul_rpow hB (Real.rpow_nonneg hL _), Real.mul_rpow (pow_nonneg hm _) ha,
    ←Real.rpow_mul hL,←Real.rpow_natCast m 3,←Real.rpow_mul hm,
    ←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
  rw [show r*(1/2:ℝ) = r/2 by ring]
  norm_num only [Nat.cast_ofNat]
  ring

lemma sqrt_derivative_estimate (p q A B L m a a' F : ℝ)
    (hp : p ≤ q) (hq : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 1 ≤ L) (hm : 0 ≤ m) (ha : 1 ≤ a)
    (α r : ℝ) (hid : (1-p)*a' = 3*F)
    (hF : F ≤ 2*(A*L^(1-α)*a) + (B*L^r)^((1:ℝ)/2)*(m^3*a)^((1:ℝ)/2)) :
    a'/(2*Real.sqrt a) ≤
      (3*(A+Real.sqrt B)/(1-q))*L^(1-α)*Real.sqrt a +
      (3*(A+Real.sqrt B)/(1-q))*L^(r/2)*m^((3:ℝ)/2) := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hp1 : 0 < 1-p := by linarith
  have hq1 : 0 < 1-q := by linarith
  have he := Real.sq_sqrt ha0.le
  have hL0 : 0 ≤ L := by linarith
  rw [sqrt_mixed_power B L m a r hB hL0 hm ha0.le] at hF
  have hu : 0 ≤ L^(1-α) := Real.rpow_nonneg hL0 _
  have hv : 0 ≤ L^(r/2)*m^((3:ℝ)/2) := mul_nonneg (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hm _)
  have hB0 := Real.sqrt_nonneg B
  have hcoef : 3*A/(1-p) ≤ 3*(A+Real.sqrt B)/(1-q) := by
    apply (div_le_div_iff₀ hp1 hq1).mpr
    nlinarith
  have hcoef2 : 3*Real.sqrt B/(2*(1-p)) ≤ 3*(A+Real.sqrt B)/(1-q) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hp1) hq1).mpr
    nlinarith
  have hbase : a'/(2*Real.sqrt a) ≤ 3*A/(1-p)*L^(1-α)*Real.sqrt a +
      (3*Real.sqrt B/(2*(1-p)))*(L^(r/2)*m^((3:ℝ)/2)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
    apply (mul_le_mul_iff_right₀ hp1).mp
    have hex : (3*A/(1-p)*L^(1-α)*Real.sqrt a +
        (3*Real.sqrt B/(2*(1-p)))*(L^(r/2)*m^((3:ℝ)/2))) * (2*Real.sqrt a) * (1-p) =
        3*(2*(A*L^(1-α)*a) + Real.sqrt B*L^(r/2)*m^((3:ℝ)/2)*Real.sqrt a) := by
      field_simp
      ring_nf
      rw [he]
      ring
    rw [hid,mul_comm (1-p) _,hex]
    linarith
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hu) hs.le)
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef2 hv))

end TraceNumerics
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TraceSquareRoot
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rootTriangleSqrt (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ := Real.sqrt (rootTriangle G root weight t)

theorem hasDerivAt_rootTriangleSqrt [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) :
    HasDerivAt (rootTriangleSqrt G root weight)
      (deriv (rootTriangle G root weight) (p:ℝ) / (2*rootTriangleSqrt G root weight (p:ℝ))) (p:ℝ) := by
  apply (hasDerivAt_rootTriangle_subcritical G hloc hqt root weight p hp0 hp).differentiableAt.hasDerivAt.sqrt
  have hh := rootTriangle_one_le G hloc hqt root weight hw hw1 p hp
  linarith

 
theorem critical_rootTriangleSqrt_derivative
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        deriv (rootTriangleSqrt G root weight) (p:ℝ) ≤
        C*L^(1-α)*rootTriangleSqrt G root weight (p:ℝ) +
          C*L^(((1:ℝ)/2+ε-2*α)/2)*‖T‖^((3:ℝ)/2) := by
  obtain ⟨A,B,hA,hB,hb⟩ := critical_mixed_trace_bound_real G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  refine ⟨3*(A+Real.sqrt B)/(1-(pc G:ℝ)),div_pos (mul_pos (by norm_num)
    (add_pos_of_pos_of_nonneg hA (Real.sqrt_nonneg B))) (sub_pos.mpr hp₁),?_⟩
  intro p hp hpq T hT L hL
  have hp0 : 0 < (p:ℝ) := lt_of_lt_of_le (half_pos hp₀) hp
  rw [(hasDerivAt_rootTriangleSqrt G hloc hqt root weight (fun i => (hw i).le) hw1 p hp0 hpq).deriv]
  exact sqrt_derivative_estimate p (pc G) A B L ‖T‖ (rootTriangle G root weight p)
    (deriv (rootTriangle G root weight) p) _ hpq.le hp₁ hA.le hB.le hL (norm_nonneg _)
    (rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 p hpq) α _
    (rootTriangle_russo G hconn hloc hqt root weight Γ hΓ htr (fun i => (hw i).le) p hp0 hpq T hT)
    (hb p hp hpq T hT L hL)

end TraceSquareRoot
end Percolation

 
namespace Percolation
section TraceExponents

lemma trace_exponent_choices (η : ℝ) (hη : 0 < η) :
    ∃ α ε ρ lambda : ℝ, 0 < α ∧ α < 1/2 ∧ 0 < ε ∧ 0 < ρ ∧ 0 < lambda ∧
      (1:ℝ)/2+ε-2*α < 0 ∧ lambda*(1-α) < 1 ∧
      lambda*(((1:ℝ)/2+ε-2*α)/2) + (3:ℝ)/2*(1+ρ) < 1+η/2 := by
  let ζ := min (1/2:ℝ) η
  let d := min (ζ/16) (η/32)
  have hz : 0 < ζ := lt_min (by norm_num) hη
  have hz1 : ζ ≤ 1/2 := min_le_left _ _
  have hze : ζ ≤ η := min_le_right _ _
  have hd : 0 < d := lt_min (div_pos hz (by norm_num)) (div_pos hη (by norm_num))
  have hdz : d ≤ ζ/16 := min_le_left _ _
  have hde : d ≤ η/32 := min_le_right _ _
  have hzd : 0 ≤ ζ*d := mul_nonneg hz.le hd.le
  refine ⟨1/2-d,d,d,2-ζ,?_,?_,hd,hd,?_,?_,?_,?_⟩ <;> nlinarith

lemma trace_scale_large_term (δ D lambda r ρ : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    (δ^(-lambda))^(r/2)*(D*δ^(-1-ρ))^((3:ℝ)/2) =
      D^((3:ℝ)/2)*δ^(-(lambda*(r/2)+(3:ℝ)/2*(1+ρ))) := by
  rw [Real.mul_rpow hD (Real.rpow_nonneg hδ.le _),←Real.rpow_mul hδ.le,←Real.rpow_mul hδ.le]
  rw [show δ^(-lambda*(r/2))*(D^((3:ℝ)/2)*δ^((-1-ρ)*((3:ℝ)/2))) =
    D^((3:ℝ)/2)*(δ^(-lambda*(r/2))*δ^((-1-ρ)*((3:ℝ)/2))) by ring,
    ←Real.rpow_add hδ]
  congr 2
  ring

lemma trace_scale_derivative (δ D C lambda r ρ α b b' m : ℝ)
    (hδ : 0 < δ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (hm : 0 ≤ m) (hmD : m ≤ D*δ^(-1-ρ))
    (hd : b' ≤ C*(δ^(-lambda))^(1-α)*b + C*(δ^(-lambda))^(r/2)*m^((3:ℝ)/2)) :
    b' ≤ (C*(1+D^((3:ℝ)/2)))*δ^(-(lambda*(1-α)))*b +
      (C*(1+D^((3:ℝ)/2)))*δ^(-(lambda*(r/2)+(3:ℝ)/2*(1+ρ))) := by
  have hs := Real.rpow_le_rpow hm hmD (by norm_num : (0:ℝ) ≤ 3/2)
  have he : (δ^(-lambda))^(1-α) = δ^(-(lambda*(1-α))) := by rw [←Real.rpow_mul hδ.le]; congr 1; ring
  have hc1 : C ≤ C*(1+D^((3:ℝ)/2)) := by nlinarith [Real.rpow_nonneg hD ((3:ℝ)/2)]
  have hc2 : C*D^((3:ℝ)/2) ≤ C*(1+D^((3:ℝ)/2)) := by nlinarith
  calc
    b' ≤ C*(δ^(-lambda))^(1-α)*b + C*(δ^(-lambda))^(r/2)*m^((3:ℝ)/2) := hd
    _ ≤ C*(δ^(-lambda))^(1-α)*b + C*(δ^(-lambda))^(r/2)*(D*δ^(-1-ρ))^((3:ℝ)/2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hδ.le _) _)))
    _ = C*δ^(-(lambda*(1-α)))*b + (C*D^((3:ℝ)/2))*δ^(-(lambda*(r/2)+(3:ℝ)/2*(1+ρ))) := by
      rw [he,mul_assoc C ((δ^(-lambda))^(r/2)),trace_scale_large_term δ D lambda r ρ hδ hD]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hδ.le _)) hb)
      (mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hδ.le _))

end TraceExponents
end Percolation

 
namespace Percolation
section IntegratingFactor

lemma hasDerivAt_gap_rpow (q r t : ℝ) (ht : t < q) :
    HasDerivAt (fun x : ℝ => (q-x)^r) (-r*(q-t)^(r-1)) t := by
  convert! ((hasDerivAt_const t q).sub (hasDerivAt_id t)).rpow_const
    (Or.inl (ne_of_gt (sub_pos.mpr ht))) using 1
  simp only [Pi.sub_apply, id_eq]
  ring

noncomputable def traceIntegratingFactor (q C A t : ℝ) : ℝ :=
  Real.exp (C/(1-A)*(q-t)^(1-A))

lemma hasDerivAt_traceIntegratingFactor (q C A t : ℝ) (hA : A < 1) (ht : t < q) :
    HasDerivAt (traceIntegratingFactor q C A)
      (-C*(q-t)^(-A)*traceIntegratingFactor q C A t) t := by
  have hd := ((hasDerivAt_gap_rpow q (1-A) t ht).const_mul (C/(1-A))).exp
  convert! hd using 1
  unfold traceIntegratingFactor
  rw [show 1-A-1 = -A by ring]
  field_simp [ne_of_gt (sub_pos.mpr hA)]

lemma traceIntegratingFactor_bounds (q C A t : ℝ) (hC : 0 ≤ C) (hA : A < 1)
    (ht : t < q) (hd : q-t ≤ 1) :
    1 ≤ traceIntegratingFactor q C A t ∧
      traceIntegratingFactor q C A t ≤ Real.exp (C/(1-A)) := by
  have hk : 0 ≤ C/(1-A) := div_nonneg hC (sub_pos.mpr hA).le
  have hr : 0 ≤ (q-t)^(1-A) := Real.rpow_nonneg (sub_pos.mpr ht).le _
  constructor
  · exact Real.one_le_exp (mul_nonneg hk hr)
  · apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right hk (Real.rpow_le_one (sub_pos.mpr ht).le hd (sub_pos.mpr hA).le)

lemma hasDerivAt_traceComparison (f : ℝ → ℝ) (q C A κ t : ℝ)
    (hA : A < 1) (hκ : 0 < κ) (ht : t < q) (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun x => traceIntegratingFactor q C A x*f x -
      (C*Real.exp (C/(1-A))/κ)*(q-x)^(-κ))
      (traceIntegratingFactor q C A t*(deriv f t-C*(q-t)^(-A)*f t) -
        C*Real.exp (C/(1-A))*(q-t)^(-κ-1)) t := by
  have hh := ((hasDerivAt_traceIntegratingFactor q C A t hA ht).mul hf.hasDerivAt).sub
    ((hasDerivAt_gap_rpow q (-κ) t ht).const_mul (C*Real.exp (C/(1-A))/κ))
  convert! hh using 1
  field_simp [ne_of_gt hκ]
  ring

 

theorem singular_ode_subpower (f : ℝ → ℝ) (q s C A B κ : ℝ)
    (hs : s < q) (hqs : q-s ≤ 1) (hC : 0 < C) (hA : A < 1)
    (hκ : 0 < κ) (hB : B ≤ 1+κ)
    (hf : ∀ t ∈ Set.Ico s q, DifferentiableAt ℝ f t)
    (hn : ∀ t ∈ Set.Ico s q, 0 ≤ f t)
    (hd : ∀ t ∈ Set.Ico s q,
      deriv f t ≤ C*(q-t)^(-A)*f t + C*(q-t)^(-B)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Set.Ico s q, f t ≤ K*(q-t)^(-κ) := by
  let M := Real.exp (C/(1-A))
  let Q := C*M/κ
  let g := fun t => traceIntegratingFactor q C A t*f t - Q*(q-t)^(-κ)
  have hM : 0 < M := Real.exp_pos _
  have hQ : 0 < Q := div_pos (mul_pos hC hM) hκ
  have hgs (t : ℝ) (ht : t ∈ Set.Ico s q) :
      HasDerivAt g (traceIntegratingFactor q C A t*(deriv f t-C*(q-t)^(-A)*f t) -
        C*M*(q-t)^(-κ-1)) t := hasDerivAt_traceComparison f q C A κ t hA hκ ht.2 (hf t ht)
  have hgn (t : ℝ) (ht : t ∈ Set.Ico s q) : deriv g t ≤ 0 := by
    have htq : 0 < q-t := sub_pos.mpr ht.2
    have ht1 : q-t ≤ 1 := by linarith [ht.1]
    obtain ⟨hw,hwM⟩ := traceIntegratingFactor_bounds q C A t hC.le hA ht.2 ht1
    have hpow : (q-t)^(-B) ≤ (q-t)^(-κ-1) :=
      Real.rpow_le_rpow_of_exponent_ge htq ht1 (by linarith)
    have hmul := mul_le_mul_of_nonneg_left (hd t ht) (show 0 ≤ traceIntegratingFactor q C A t by linarith)
    have h₂ := mul_le_mul_of_nonneg_right hwM (mul_nonneg hC.le (Real.rpow_nonneg htq.le (-B)))
    have h₃ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le hM.le)
    rw [(hgs t ht).deriv]
    dsimp only [M] at hM ⊢
    dsimp only [M] at h₃
    nlinarith
  have hgmono : AntitoneOn g (Set.Ico s q) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico s q)
    · intro t ht
      exact (hgs t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hgs t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      exact hgn t (interior_subset ht)
  have hsI : s ∈ Set.Ico s q := ⟨le_rfl,hs⟩
  refine ⟨M*f s+Q,add_pos_of_nonneg_of_pos (mul_nonneg hM.le (hn s hsI)) hQ,?_⟩
  intro t ht
  have htq : 0 < q-t := sub_pos.mpr ht.2
  have ht1 : q-t ≤ 1 := by linarith [ht.1]
  obtain ⟨hwt,_⟩ := traceIntegratingFactor_bounds q C A t hC.le hA ht.2 ht1
  obtain ⟨_,hws⟩ := traceIntegratingFactor_bounds q C A s hC.le hA hs hqs
  have hmono := hgmono hsI ht ht.1
  have hneg : 0 ≤ Q*(q-s)^(-κ) := mul_nonneg hQ.le (Real.rpow_nonneg (sub_pos.mpr hs).le _)
  have hft := mul_le_mul_of_nonneg_right hwt (hn t ht)
  have hfs := mul_le_mul_of_nonneg_right hws (hn s hsI)
  have hpow : 1 ≤ (q-t)^(-κ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos htq ht1 (neg_nonpos.mpr hκ.le)
  have hscale := mul_le_mul_of_nonneg_left hpow (mul_nonneg hM.le (hn s hsI))
  dsimp only [g] at hmono
  dsimp only [M] at hscale ⊢
  nlinarith

end IntegratingFactor
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SubpowerTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_rootTriangle_subpower
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      rootTriangle G root weight (p:ℝ) ≤ K*((pc G:ℝ)-(p:ℝ))^(-η) := by
  obtain ⟨α,ε,ρ,lambda,hα,hα1,hε,hρ,hlambda,hr,hA,hB⟩ := trace_exponent_choices η hη
  obtain ⟨C₀,hC₀,hder⟩ := critical_rootTriangleSqrt_derivative G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  obtain ⟨D,hD,hχ⟩ := almost_linear_susceptibility G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin ρ hρ
  let C := C₀*(1+D^((3:ℝ)/2))
  let A := lambda*(1-α)
  let B := lambda*(((1:ℝ)/2+ε-2*α)/2)+(3:ℝ)/2*(1+ρ)
  have hC : 0 < C := mul_pos hC₀ (by linarith [Real.rpow_nonneg hD.le ((3:ℝ)/2)])
  have hunit (t : ℝ) (ht : t ∈ Set.Ico ((pc G:ℝ)/2) (pc G:ℝ)) : t ∈ unitInterval :=
    ⟨(half_pos hp₀).le.trans ht.1,ht.2.le.trans (pc G).2.2⟩
  have hdf (t : ℝ) (ht : t ∈ Set.Ico ((pc G:ℝ)/2) (pc G:ℝ)) :
      DifferentiableAt ℝ (rootTriangleSqrt G root weight) t := by
    exact (hasDerivAt_rootTriangleSqrt G hloc hqt root weight (fun i => (hw i).le) hw1
      ⟨t,hunit t ht⟩ ((half_pos hp₀).trans_le ht.1) ht.2).differentiableAt
  have hod (t : ℝ) (ht : t ∈ Set.Ico ((pc G:ℝ)/2) (pc G:ℝ)) :
      deriv (rootTriangleSqrt G root weight) t ≤ C*((pc G:ℝ)-t)^(-A)*rootTriangleSqrt G root weight t +
        C*((pc G:ℝ)-t)^(-B) := by
    let p : unitInterval := ⟨t,hunit t ht⟩
    have hδ : 0 < (pc G:ℝ)-t := sub_pos.mpr ht.2
    have hδ1 : (pc G:ℝ)-t ≤ 1 := by linarith [(pc G).2.2,ht.1]
    obtain ⟨T,hT⟩ := operatorBounded_of_lt_pc G hloc hqt p ht.2
    have hm := hT.norm_le_susceptibility_bound G hloc hqt p ht.2 T (D*((pc G:ℝ)-t)^(-1-ρ))
      (mul_nonneg hD.le (Real.rpow_nonneg hδ.le _)) (hχ p ht.2)
    have hL : 1 ≤ (((pc G:ℝ)-t)^(-lambda)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hlambda.le)
    exact trace_scale_derivative ((pc G:ℝ)-t) D C₀ lambda ((1:ℝ)/2+ε-2*α) ρ α
      (rootTriangleSqrt G root weight t) (deriv (rootTriangleSqrt G root weight) t) ‖T‖
      hδ hD.le hC₀.le (Real.sqrt_nonneg _) (norm_nonneg _) hm
      (hder p ht.1 ht.2 T hT (((pc G:ℝ)-t)^(-lambda)) hL)
  obtain ⟨K,hK,hb⟩ := singular_ode_subpower (rootTriangleSqrt G root weight) (pc G) ((pc G:ℝ)/2)
    C A B (η/2) (by linarith) (by linarith [(pc G).2.2]) hC hA (half_pos hη) hB.le
    hdf (fun _ _ => Real.sqrt_nonneg _) hod
  refine ⟨K^2,sq_pos_of_pos hK,?_⟩
  intro p hp hpq
  have ha : 0 ≤ rootTriangle G root weight (p:ℝ) :=
    le_trans (by norm_num) (rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 p hpq)
  have hb' := pow_le_pow_left₀ (Real.sqrt_nonneg (rootTriangle G root weight (p:ℝ))) (hb p ⟨hp,hpq⟩) 2
  change (Real.sqrt (rootTriangle G root weight (p:ℝ)))^2 ≤ _ at hb'
  rw [Real.sq_sqrt ha,mul_pow] at hb'
  have he : (((pc G:ℝ)-(p:ℝ))^(-(η/2)))^2 = ((pc G:ℝ)-(p:ℝ))^(-η) := by
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul (sub_pos.mpr (show (p:ℝ)<(pc G:ℝ) from hpq)).le]
    congr 1
    norm_num
  rw [he] at hb'
  exact hb'

end SubpowerTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section QuantitativeSprinkling
attribute [local instance] Classical.propDecidable Classical.decEq

lemma riccati_step (a M n x : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (_hn : 0 ≤ n)
    (_hx : 0 ≤ x) (hb : x ≤ M/(1-a*n*M)) (hh : a*(n+1)*M < 1) :
    a*x < 1 ∧ x/(1-a*x) ≤ M/(1-a*(n+1)*M) := by
  have haM : 0 ≤ a*M := mul_nonneg ha hM
  have hp : 0 < 1-a*n*M := by nlinarith
  have hb' := (le_div_iff₀ hp).mp hb
  have hs : a*(M/(1-a*n*M)) < 1 := by
    rw [←mul_div_assoc,div_lt_one hp]
    nlinarith
  have hax : a*x < 1 := (mul_le_mul_of_nonneg_left hb ha).trans_lt hs
  refine ⟨hax,?_⟩
  apply (div_le_div_iff₀ (sub_pos.mpr hax) (sub_pos.mpr hh)).mpr
  nlinarith

 

theorem sprinkling_iterated_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (m D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : HasKernel G (orParameter q m) A) (n : ℕ)
    (hn : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+n)) B ∧
      ‖B‖ ≤ ‖A‖/(1-(q:ℝ)*(2*D)*(n:ℝ)*‖A‖) := by
  induction n with
  | zero => exact ⟨A,by simpa using hA,by simp⟩
  | succ n ih =>
    have ha : 0 ≤ (q:ℝ)*(2*D) := mul_nonneg q.2.1 (by positivity)
    have hnext : (q:ℝ)*(2*D)*((n:ℝ)+1)*‖A‖ < 1 := by simpa using hn
    have hprev : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1 := by
      nlinarith [mul_nonneg ha (norm_nonneg A)]
    obtain ⟨B,hB,hBn⟩ := ih hprev
    obtain ⟨hs,hbound⟩ := riccati_step ((q:ℝ)*(2*D)) ‖A‖ n ‖B‖ ha (norm_nonneg _) (Nat.cast_nonneg _) (norm_nonneg _) hBn hnext
    obtain ⟨C,hC,hCn⟩ := sprinkling_bound G hloc q (m+n) D hD B hB hs
    exact ⟨C,by simpa [Nat.add_assoc] using hC,by simpa using hCn.trans hbound⟩

lemma closed_power_bound (q : unitInterval) (n : ℕ) :
    (1-(q:ℝ))^n * (1+(n:ℝ)*(q:ℝ)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1-(q:ℝ))^n := pow_nonneg (sub_nonneg.mpr q.2.2) _
    have hn : 0 ≤ (n:ℝ)*(q:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hp hn,mul_nonneg hp (sq_nonneg (q:ℝ))]

lemma orParameter_gap_bound (p q : unitInterval) (m n : ℕ) (hm : orParameter q m = p) :
    (1+(n:ℝ)*(q:ℝ))*(1-(orParameter q (m+n):ℝ)) ≤ 1-(p:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (closed_power_bound q n) (sub_nonneg.mpr p.2.2)
  have he : 1-(p:ℝ) = (1-(q:ℝ))^m := by rw [←hm]; simp [orParameter]
  rw [he] at hh ⊢
  change (1+(n:ℝ)*(q:ℝ))*(1-(1-(1-(q:ℝ))^(m+n))) ≤ _
  rw [sub_sub_cancel,pow_add]
  nlinarith

end QuantitativeSprinkling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section QuantitativeOpenness
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem operatorBounded_of_quantitative_gap [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (p r : unitInterval)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hsmall : ((r:ℝ)-(p:ℝ))*(4*D)*‖A‖ < 1-(r:ℝ)) : OperatorBounded G r := by
  let a := ((r:ℝ)-(p:ℝ))/(1-(r:ℝ))
  have hden : 0 < 1-(r:ℝ) := sub_pos.mpr hr
  have ha : 0 < a := div_pos (sub_pos.mpr hpr) hden
  obtain ⟨m,q,hq,hqp⟩ := exists_orParameter_small p (hpr.trans hr) (min a 1)
    (lt_min ha zero_lt_one) (min_le_right _ _)
  have hq0 : (0:ℝ) < q := by
    by_contra hn
    have hqe : q = 0 := Subtype.ext ((le_of_not_gt hn).antisymm q.2.1)
    have hpe : p = 0 := by rw [←hqp,hqe]; apply Subtype.ext; simp [orParameter]
    exact (ne_of_gt hp) hpe
  let n := ⌈a/(q:ℝ)⌉₊
  have hna : a ≤ (n:ℝ)*(q:ℝ) := (div_le_iff₀ hq0).mp (Nat.le_ceil _)
  have han : (n:ℝ)*(q:ℝ) < a+(q:ℝ) := by
    have hn := Nat.ceil_lt_add_one (div_nonneg ha.le hq0.le)
    have hh := mul_lt_mul_of_pos_right hn hq0
    dsimp only [n] at *
    field_simp at hh
    nlinarith
  have hn2 : (n:ℝ)*(q:ℝ) < 2*a := by linarith [hq.trans (min_le_left _ _)]
  have hbase : (2*a)*(2*D)*‖A‖ < 1 := by
    rw [show (2*a)*(2*D)*‖A‖ = (((r:ℝ)-(p:ℝ))*(4*D)*‖A‖)/(1-(r:ℝ)) by dsimp [a]; ring]
    exact (div_lt_one hden).mpr hsmall
  have hnsmall : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1 := by
    have hs := mul_le_mul_of_nonneg_right hn2.le (show 0 ≤ (2*(D:ℝ))*‖A‖ by positivity)
    nlinarith
  obtain ⟨B,hB,_⟩ := sprinkling_iterated_bound G hloc q m D hD A (hqp ▸ hA) n hnsmall
  apply operatorBounded_of_le G (q := orParameter q (m+n)) ?_ ⟨B,hB⟩
  have hgap := orParameter_gap_bound p q m n hqp
  have hae : a*(1-(r:ℝ)) = (r:ℝ)-(p:ℝ) := div_mul_cancel₀ _ (ne_of_gt hden)
  have hs := mul_le_mul_of_nonneg_right hna hden.le
  change (r:ℝ) ≤ (orParameter q (m+n):ℝ)
  nlinarith [mul_nonneg (Nat.cast_nonneg n) q.2.1]

 

theorem norm_gap_lower_of_endpoint_unbounded [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (p r : unitInterval)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hu : ¬OperatorBounded G r) :
    1-(r:ℝ) ≤ ((r:ℝ)-(p:ℝ))*(4*D)*‖A‖ := by
  by_contra h
  exact hu (operatorBounded_of_quantitative_gap G hloc D hD p r hp hpr hr A hA (lt_of_not_ge h))

end QuantitativeOpenness
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def maxSusceptibility (G : BondGraph V E) (p : unitInterval) : ℝ :=
  sSup (Set.range (susceptibility G p))

theorem susceptibility_bddAbove [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : BddAbove (Set.range (susceptibility G p)) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  refine ⟨C,?_⟩
  rintro _ ⟨x,rfl⟩
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).tsum_le_of_sum_le (hC x)

theorem susceptibility_le_max [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    susceptibility G p x ≤ maxSusceptibility G p :=
  le_csSup (susceptibility_bddAbove G hloc hqt p hp) (Set.mem_range_self x)

theorem maxSusceptibility_le [Nonempty V] (G : BondGraph V E) (p : unitInterval)
    (C : ℝ) (hC : ∀ x, susceptibility G p x ≤ C) : maxSusceptibility G p ≤ C := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x,rfl⟩
  exact hC x

theorem maxSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ maxSusceptibility G p := by
  let x : V := Classical.choice inferInstance
  exact (susceptibility_one_le G hloc hqt p hp x).trans (susceptibility_le_max G hloc hqt p hp x)

theorem HasKernel.norm_le_maxSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : ‖T‖ ≤ maxSusceptibility G p :=
  hT.norm_le_susceptibility_bound G hloc hqt p hp T _
    (le_trans zero_le_one (maxSusceptibility_one_le G hloc hqt p hp))
    (susceptibility_le_max G hloc hqt p hp)

theorem HasKernel.norm_one_le [Countable E] [Nonempty V]
    (G : BondGraph V E) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : 1 ≤ ‖T‖ := by
  let x : V := Classical.choice inferInstance
  have hd : twoPoint G p x x = 1 := twoPoint_self G p x
  have hh := (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (T (lp.single 2 x (1:ℂ))) x).trans (T.le_opNorm (lp.single 2 x (1:ℂ)))
  simpa [hT x x,hd,lp.norm_single] using hh

end NormRatio
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SourceNormRatio
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_norm_inverse_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hp₁ : (pc G:ℝ) < 1) (hu : ¬OperatorBounded G (pc G)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : unitInterval), 0 < p → p < pc G →
      ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T →
        c/((pc G:ℝ)-(p:ℝ)) ≤ ‖T‖ := by
  obtain ⟨D,hDp,hD⟩ := exists_degree_bound G hqt
  have hDpos : 0 < (4*(D:ℝ)) := by positivity
  refine ⟨(1-(pc G:ℝ))/(4*D),div_pos (sub_pos.mpr hp₁) hDpos,?_⟩
  intro p hp hpq T hT
  have hh := norm_gap_lower_of_endpoint_unbounded G hloc D hD p (pc G) hp hpq hp₁ T hT hu
  apply (div_le_iff₀ (sub_pos.mpr (show (p:ℝ)<(pc G:ℝ) from hpq))).mpr
  apply (div_le_iff₀ hDpos).mpr
  nlinarith

 

theorem critical_normRatio_subpower
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (hu : ¬OperatorBounded G (pc G)) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T →
      1 ≤ maxSusceptibility G p/‖T‖ ∧
      maxSusceptibility G p/‖T‖ ≤ K*((pc G:ℝ)-(p:ℝ))^(-η) := by
  obtain ⟨c,hc,hm⟩ := critical_norm_inverse_lower G hloc hqt hp₁ hu
  obtain ⟨D,hD,hχ⟩ := almost_linear_susceptibility G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin η hη
  refine ⟨D/c,div_pos hD hc,?_⟩
  intro p hp hpq T hT
  have hδ : 0 < (pc G:ℝ)-(p:ℝ) := sub_pos.mpr hpq
  have hnorm : 0 < ‖T‖ := zero_lt_one.trans_le (hT.norm_one_le G p T)
  have hM := hm p ((half_pos hp₀).trans_le hp) hpq T hT
  have hχb := maxSusceptibility_le G p _ (hχ p hpq)
  have he : ((pc G:ℝ)-(p:ℝ))^(-1-η)*((pc G:ℝ)-(p:ℝ)) = ((pc G:ℝ)-(p:ℝ))^(-η) := by
    calc
      _ = ((pc G:ℝ)-(p:ℝ))^(-1-η)*((pc G:ℝ)-(p:ℝ))^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hδ]; congr 1; ring
  refine ⟨(one_le_div hnorm).mpr (hT.norm_le_maxSusceptibility G hloc hqt p hpq T),?_⟩
  calc
    maxSusceptibility G p/‖T‖ ≤ (D*((pc G:ℝ)-(p:ℝ))^(-1-η))/(c/((pc G:ℝ)-(p:ℝ))) :=
      div_le_div₀ (mul_nonneg hD.le (Real.rpow_nonneg hδ.le _)) hχb (div_pos hc hδ) hM
    _ = (D/c)*((pc G:ℝ)-(p:ℝ))^(-η) := by rw [←he]; field_simp

end SourceNormRatio
end Percolation

 
namespace Percolation
universe u
section ChronologicalErasure
open List
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq

 

inductive HoldingWalk (H : SimpleGraph V) : ℕ → V → V → Type u
  | nil (x : V) : HoldingWalk H 0 x x
  | hold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : HoldingWalk H (k+1) x y
  | step {k : ℕ} {x z y : V} (h : H.Adj x z) (w : HoldingWalk H k z y) :
      HoldingWalk H (k+1) x y

namespace HoldingWalk
variable {H : SimpleGraph V} {k : ℕ} {x y : V}

def withoutHolds : {k : ℕ} → {x y : V} → HoldingWalk H k x y → H.Walk x y
  | _,_,_,.nil _ => .nil
  | _,_,_,.hold w => w.withoutHolds
  | _,_,_,.step h w => .cons h w.withoutHolds

def vertices : {k : ℕ} → {x y : V} → HoldingWalk H k x y → List V
  | _,x,_,.nil _ => [x]
  | _,x,_,.hold w => x :: w.vertices
  | _,x,_,.step _ w => x :: w.vertices

noncomputable def mass (P : V → V → ℝ) : {k : ℕ} → {x y : V} → HoldingWalk H k x y → ℝ
  | _,_,_,.nil _ => 1
  | _,x,_,.hold w => P x x * w.mass P
  | _,x,_,.step (z := z) _ w => P x z * w.mass P

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ a b, 0 ≤ P a b) (w : HoldingWalk H k x y) :
    0 ≤ w.mass P := by
  induction w with
  | nil => exact zero_le_one
  | hold w ih => exact mul_nonneg (hP _ _) ih
  | step h w ih => exact mul_nonneg (hP _ _) ih

theorem length_vertices (w : HoldingWalk H k x y) : w.vertices.length = k+1 := by
  induction w with
  | nil => rfl
  | hold w ih => simpa only [vertices,List.length_cons] using congrArg (fun n => n+1) ih
  | step h w ih => simpa only [vertices,List.length_cons] using congrArg (fun n => n+1) ih

theorem withoutHolds_length (w : HoldingWalk H k x y) : w.withoutHolds.length ≤ k := by
  induction w with
  | nil => simp [withoutHolds]
  | hold w ih => exact ih.trans (Nat.le_succ _)
  | step h w ih => simpa only [withoutHolds,SimpleGraph.Walk.length_cons] using Nat.succ_le_succ ih

theorem withoutHolds_support (w : HoldingWalk H k x y) : w.withoutHolds.support <+ w.vertices := by
  induction w with
  | nil => exact List.Sublist.refl _
  | hold w ih => exact ih.cons _
  | step h w ih => exact ih.cons_cons _

 

noncomputable def erase (w : HoldingWalk H k x y) : H.Walk x y :=
  w.withoutHolds.reverse.bypass.reverse

theorem erase_isPath (w : HoldingWalk H k x y) : w.erase.IsPath :=
  w.withoutHolds.reverse.bypass_isPath.reverse

theorem erase_length (w : HoldingWalk H k x y) : w.erase.length ≤ k := by
  have hh := w.withoutHolds.reverse.length_bypass_le_length
  simpa only [erase,SimpleGraph.Walk.length_reverse] using hh.trans (by simpa using w.withoutHolds_length)

theorem erase_support (w : HoldingWalk H k x y) : w.erase.support <+ w.vertices := by
  have hh := w.withoutHolds.reverse.support_bypass_sublist_support.reverse
  simp only [SimpleGraph.Walk.support_reverse,List.reverse_reverse] at hh
  simpa only [erase,SimpleGraph.Walk.support_reverse] using hh.trans w.withoutHolds_support

theorem erase_edges (w : HoldingWalk H k x y) : w.erase.edges <+ w.withoutHolds.edges := by
  have hh := w.withoutHolds.reverse.edges_bypass_sublist_edges.reverse
  simpa only [erase,SimpleGraph.Walk.edges_reverse,List.reverse_reverse] using hh

end HoldingWalk
end ChronologicalErasure
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorMonotonicity
attribute [local instance] Classical.propDecidable Classical.decEq

 

def corridorCounted (G : BondGraph V E) (retained blockers : Set E)
    (D : Set V) (ω : Set E) (x y : V) : Prop :=
  Conn G (ω ∩ internalEdges G D) x y ∧
    (∀ e ∈ retained, e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y) ∧
    Disjoint blockers (ω ∩ internalEdges G D)

lemma pivotal_restrict_of_conn (G : BondGraph V E) {S T : Set E} (hST : S ⊆ T)
    {x y : V} (hc : Conn G S x y) (e : E) (hp : ¬Conn G (T \ {e}) x y) :
    e ∈ S ∧ ¬Conn G (S \ {e}) x y := by
  constructor
  · by_contra he
    apply hp
    apply conn_mono G ?_ hc
    intro d hd
    exact ⟨hST hd,fun hde => he ((Set.mem_singleton_iff.mp hde) ▸ hd)⟩
  · intro h
    exact hp (conn_mono G (Set.sdiff_subset_sdiff_left hST) h)

 

theorem corridorCounted_restrict (G : BondGraph V E) (retained blockers : Set E)
    {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω') (x y : V)
    (hc : Conn G (ω ∩ internalEdges G D) x y)
    (ht : corridorCounted G retained blockers D' ω' x y) :
    corridorCounted G retained blockers D ω x y := by
  have hs : ω ∩ internalEdges G D ⊆ ω' ∩ internalEdges G D' :=
    Set.inter_subset_inter hω (internalEdges_mono G hD)
  refine ⟨hc,fun e he => pivotal_restrict_of_conn G hs hc e (ht.2.1 e he).2,?_⟩
  exact ht.2.2.mono_right hs

lemma corridorCounted_symm (G : BondGraph V E) (retained blockers : Set E)
    (D : Set V) (ω : Set E) (x y : V) :
    corridorCounted G retained blockers D ω x y ↔ corridorCounted G retained blockers D ω y x := by
  constructor <;> rintro ⟨hc,hp,hb⟩
  · exact ⟨conn_symm G _ hc,fun e he => ⟨(hp e he).1,fun hc => (hp e he).2 (conn_symm G _ hc)⟩,hb⟩
  · exact ⟨conn_symm G _ hc,fun e he => ⟨(hp e he).1,fun hc => (hp e he).2 (conn_symm G _ hc)⟩,hb⟩

 

theorem measurableSet_corridorCounted [Countable E] (G : BondGraph V E)
    (retained blockers : Set E) (D : Set V) (x y : V) :
    MeasurableSet {ω | corridorCounted G retained blockers D ω x y} := by
  have hmem (e : E) : MeasurableSet {ω : Set E | e ∈ ω ∩ internalEdges G D} := by
    by_cases he : e ∈ internalEdges G D
    · simpa only [Set.mem_inter_iff,he,and_true] using measurableSet_mem e
    · simp only [Set.mem_inter_iff,he,and_false,Set.ofPred_false]; exact MeasurableSet.empty
  have hp (e : E) : MeasurableSet {ω : Set E | e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y} := by
    apply (hmem e).inter
    have heq (ω : Set E) : (ω ∩ internalEdges G D) \ {e} = ω ∩ (internalEdges G D \ {e}) := by
      ext d; simp only [Set.mem_inter_iff,Set.mem_sdiff]; tauto
    simp_rw [heq]
    exact (measurableSet_restrictedConn G _ x y).compl
  have hb : MeasurableSet {ω : Set E | Disjoint blockers (ω ∩ internalEdges G D)} := by
    simp only [Set.disjoint_left,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun (_ : e ∈ blockers) => (hmem e).compl))
  have hkeep : MeasurableSet {ω : Set E | ∀ e ∈ retained, e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun (_ : e ∈ retained) => hp e))
  exact (measurableSet_restrictedConn G _ x y).inter (hkeep.inter hb)

end CorridorMonotonicity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralCorridors
attribute [local instance] Classical.propDecidable Classical.decEq

instance HoldingWalk.countable [Countable V] (H : SimpleGraph V) (k : ℕ) (x y : V) :
    Countable (HoldingWalk H k x y) := by
  induction k generalizing x y with
  | zero =>
    apply Function.Injective.countable (f := fun _ : HoldingWalk H 0 x y => ())
    intro a b _
    cases a
    cases b
    rfl
  | succ k ih =>
    let (a b : V) : Countable (HoldingWalk H k a b) := ih a b
    let f : HoldingWalk H (k+1) x y →
        HoldingWalk H k x y ⊕ (Σ z : {z // H.Adj x z}, HoldingWalk H k z.val y)
      | .hold w => .inl w
      | .step (z := z) h w => .inr ⟨⟨z,h⟩,w⟩
    apply Function.Injective.countable (f := f)
    intro a b hab
    cases a with
    | hold a =>
      cases b with
      | hold b => exact congrArg HoldingWalk.hold (Sum.inl.inj hab)
      | step h b => cases hab
    | @step _ _ z _ h a =>
      cases b with
      | hold b => cases hab
      | @step _ _ z' _ h' b =>
        have he := Sum.inr.inj hab
        have hz := congrArg (fun t => t.1.val) he
        change z = z' at hz
        subst z'
        have hab' : a = b := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
        subst b
        rfl

 
abbrev RawCorridor (G : BondGraph V E) (k : ℕ) :=
  Σ x y : V, HoldingWalk (openSimpleGraph G Set.univ) k x y

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def base (w : RawCorridor G k) : V := w.1
def endpoint (w : RawCorridor G k) : V := w.2.1
noncomputable def path (w : RawCorridor G k) :
    (openSimpleGraph G Set.univ).Walk w.base w.endpoint := w.2.2.erase
noncomputable def interior (w : RawCorridor G k) : Finset V :=
  w.path.support.toFinset \ {w.base,w.endpoint}
def retained (w : RawCorridor G k) : Set E := {e | G e ∈ w.path.edges}
noncomputable def blockers (w : RawCorridor G k) : Set E :=
  {e | ∃ z ∈ w.interior, z ∈ G e} \ w.retained
noncomputable def probability (P : V → V → ℝ) (w : RawCorridor G k) : ℝ := w.2.2.mass P
noncomputable def weight (P : V → V → ℝ) (p : ℝ) (w : RawCorridor G k) : ℝ :=
  w.probability P * (p^w.path.length)⁻¹ * ((1-p)^w.blockers.ncard)⁻¹

theorem path_isPath (w : RawCorridor G k) : w.path.IsPath := w.2.2.erase_isPath

theorem path_length (w : RawCorridor G k) : w.path.length ≤ k := w.2.2.erase_length

theorem retained_finite (hG : Function.Injective G) (w : RawCorridor G k) : w.retained.Finite :=
  (List.finite_toSet w.path.edges).preimage hG.injOn

theorem blockers_finite (hloc : LocallyFinite G) (w : RawCorridor G k) : w.blockers.Finite := by
  apply Set.Finite.subset (s := (incidentSupport G hloc w.interior : Set E)) (Finset.finite_toSet _)
  intro e he
  exact (mem_incidentSupport G hloc w.interior e).mpr he.1

theorem retained_disjoint_blockers (w : RawCorridor G k) : Disjoint w.retained w.blockers := by
  exact Set.disjoint_left.mpr (fun e he hb => hb.2 he)

theorem weight_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (w : RawCorridor G k) : 0 ≤ w.weight P p := by
  exact mul_nonneg (mul_nonneg (w.2.2.mass_nonneg P hP) (inv_nonneg.mpr (pow_nonneg p.2.1 _)))
    (inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr p.2.2) _))

end RawCorridor
end LiteralCorridors
end Percolation

end OAI
