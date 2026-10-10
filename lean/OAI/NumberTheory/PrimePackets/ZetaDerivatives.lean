import Mathlib
import OAI.NumberTheory.PrimePackets.HaarUniqueness

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
namespace PrimeDegreePackets

 

theorem residue_upper_reciprocal_of_deriv (K : Type*) [Field K] [NumberField K]
    {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (H : ∀ h ∈ Ioc (0:ℝ) (4/L), |deriv (logRegularizedDedekindZeta K) h| ≤ C*L) :
    (∀ h ∈ Ioc (0:ℝ) (4/L), regularizedDedekindZeta K h ≤
      Real.exp (4*C)*NumberField.dedekindZeta_residue K) ∧
    (NumberField.dedekindZeta_residue K)⁻¹ ≤ Real.exp (4*C)*L := by
  have hk := NumberField.dedekindZeta_residue_pos K
  have HR (h : ℝ) (hh : h ∈ Ioc (0:ℝ) (4/L)) :
      regularizedDedekindZeta K h ≤ Real.exp (4*C)*NumberField.dedekindZeta_residue K := by
    have HH := (residue_comparison_of_deriv_bound K (by positivity : 0 < 4/L) H hh.1 hh.2).2
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ hk.le
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_left ((le_div_iff₀ hL).mp hh.2) hC.le
    nlinarith only [hprod]
  refine ⟨HR,?_⟩
  have hh : 1/L ∈ Ioc (0:ℝ) (4/L) :=
    ⟨one_div_pos.mpr hL,div_le_div_of_nonneg_right (by norm_num) hL.le⟩
  have HS := HR (1/L) hh
  have HZ := dedekindZeta_real_one_le K (s := 1+1/L) (by linarith [hh.1])
  have Hreg : 1/L ≤ regularizedDedekindZeta K (1/L) := by
    unfold regularizedDedekindZeta
    have H := mul_le_mul_of_nonneg_left HZ hh.1.le
    simpa only [Complex.ofReal_add,Complex.ofReal_one,mul_one] using H
  have HP := mul_le_mul_of_nonneg_right (Hreg.trans HS) hL.le
  rw [div_mul_cancel₀ 1 hL.ne'] at HP
  rw [← one_div, div_le_iff₀ hk]
  nlinarith only [HP]

 

theorem uniform_zeta_scale_of_large_discr_deriv
    (n : ℕ) {C D₀ : ℝ} (hC : 0 < C)
    (H : ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      Module.finrank ℚ K = n → D₀ ≤ |(NumberField.discr K : ℝ)| →
      ∀ h ∈ Ioc (0:ℝ) (4/Real.log |(NumberField.discr K : ℝ)|),
        |deriv (logRegularizedDedekindZeta K) h| ≤ C*Real.log |(NumberField.discr K : ℝ)|) :
    ∃ A E : ℝ, 0 < A ∧ 0 < E ∧ ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
        (K →+* ℝ) → Module.finrank ℚ K = n →
        |(NumberField.discr K : ℝ)| ≤ Q^2 →
        (∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
          realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            A*NumberField.dedekindZeta_residue K) ∧
        (NumberField.dedekindZeta_residue K)⁻¹ ≤ E*(1+Real.log Q) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max D₀ (Real.exp 4))
  obtain ⟨B,hB,δ,hδ,Hδ⟩ := bounded_discr_residue_comparison N
  let F : ℝ := Real.exp (4*C)
  refine ⟨max 2 F,2*max B F,lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    mul_pos (by norm_num) (lt_of_lt_of_le hB (le_max_left _ _)),?_⟩
  have hlog : Tendsto (fun Q : ℝ => Real.log (Q^(3/4:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [eventually_ge_atTop (2:ℝ),hlog.eventually_gt_atTop (1/δ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hQ hQδ hQpow
  intro K _ _ _ σ hn hdisc
  let L : ℝ := Real.log |(NumberField.discr K : ℝ)|
  have hQp : 0 < Q := by linarith
  have hqlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hDpos : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hLQ : L ≤ 2*Real.log Q := by
    have H := Real.log_le_log hDpos hdisc
    simpa only [L, Real.log_pow, Nat.cast_ofNat] using H
  have hmax : 0 < max B F := lt_of_lt_of_le hB (le_max_left _ _)
  by_cases hsmall : |(NumberField.discr K : ℝ)| ≤ N
  · have hsmall' : |NumberField.discr K| ≤ N := by exact_mod_cast hsmall
    have HB := Hδ K σ hsmall'
    constructor
    · intro b hb
      have hb2 := hQpow.trans hb
      have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
      have hlt : 1/Real.log b < δ := by
        apply (one_div_lt hlogb hδ).mpr
        exact hQδ.trans_le (Real.log_le_log (by linarith) hb)
      have HR := (HB.2 (1/Real.log b) (one_div_pos.mpr hlogb) hlt).2
      calc
        realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            2*NumberField.dedekindZeta_residue K := by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using HR
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
          (NumberField.dedekindZeta_residue_pos K).le
    · apply HB.1.trans
      have hBmax : B ≤ max B F := le_max_left _ _
      nlinarith
  · have hlarge : (N:ℝ) < |(NumberField.discr K : ℝ)| := lt_of_not_ge hsmall
    have hD₀ : D₀ ≤ |(NumberField.discr K : ℝ)| :=
      ((le_max_left _ _).trans_lt hN).le.trans hlarge.le
    have he : Real.exp 4 < |(NumberField.discr K : ℝ)| :=
      (lt_of_le_of_lt (le_max_right _ _) hN).trans hlarge
    have hL4 : 4 < L := by
      have Hlog := Real.log_lt_log (Real.exp_pos 4) he
      simpa only [Real.log_exp] using Hlog
    have hLp : 0 < L := by linarith
    obtain ⟨Hupper,Hrecip⟩ := residue_upper_reciprocal_of_deriv K hLp hC (H K hn hD₀)
    constructor
    · intro b hb
      have hb2 := hQpow.trans hb
      have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
      have hloglow : (3/4:ℝ)*Real.log Q ≤ Real.log b := by
        have HE := Real.log_le_log (Real.rpow_pos_of_pos hQp _) hb
        simpa only [Real.log_rpow hQp] using HE
      have hbound : 1/Real.log b ≤ 4/L := by
        rw [div_le_div_iff₀ hlogb hLp]
        nlinarith only [hLQ,hloglow,hqlog]
      have HU := Hupper (1/Real.log b) ⟨one_div_pos.mpr hlogb,hbound⟩
      calc
        realDedekindZeta K (1+1/Real.log b) / Real.log b ≤ F*NumberField.dedekindZeta_residue K := by
          simpa only [F,regularizedDedekindZeta,realDedekindZeta,Complex.ofReal_add,
            Complex.ofReal_one,one_div,mul_comm,div_eq_mul_inv,one_mul] using HU
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (NumberField.dedekindZeta_residue_pos K).le
    · apply Hrecip.trans
      have hF : 0 < F := Real.exp_pos _
      have hFmax : F ≤ max B F := le_max_right _ _
      calc
        F*L ≤ F*(2*Real.log Q) := mul_le_mul_of_nonneg_left hLQ hF.le
        _ ≤ (max B F)*(2*Real.log Q) := mul_le_mul_of_nonneg_right hFmax (by positivity)
        _ ≤ _ := by nlinarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma realDedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : DifferentiableAt ℝ (realDedekindZeta K) s := by
  have H := (dedekindZeta_differentiableAt K (s := s) (by simpa using hs)).hasDerivAt.real_of_complex
  exact H.differentiableAt

 

lemma realDedekindZeta_deriv_nonpos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : deriv (realDedekindZeta K) s ≤ 0 := by
  have H : AntitoneOn (realDedekindZeta K) (Ioi 1) := by
    intro x hx y _ hxy
    exact dedekindZeta_real_antitone K hx hxy
  have HH := H.derivWithin_nonpos (x := s)
  rwa [derivWithin_of_isOpen isOpen_Ioi hs] at HH

lemma realDedekindZeta_pos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 0 < realDedekindZeta K s :=
  lt_of_lt_of_le zero_lt_one (dedekindZeta_real_one_le K hs)

lemma logRegularizedDedekindZeta_deriv (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) :
    deriv (logRegularizedDedekindZeta K) h = 1/h +
      deriv (realDedekindZeta K) (1+h) / realDedekindZeta K (1+h) := by
  have hs : 1 < 1+h := by linarith
  have hz := realDedekindZeta_pos K hs
  have hd := (realDedekindZeta_differentiableAt K hs).hasDerivAt.comp h
    ((hasDerivAt_id h).const_add 1)
  have hm := ((hasDerivAt_id h).mul hd).log (mul_pos hh hz).ne'
  have heq : logRegularizedDedekindZeta K =
      fun h => Real.log (h*realDedekindZeta K (1+h)) := by
    funext h
    simp only [logRegularizedDedekindZeta,regularizedDedekindZeta,realDedekindZeta,
      Complex.ofReal_add,Complex.ofReal_one]
  simp only [Function.comp_def,Pi.mul_apply,id_eq,one_mul,mul_one] at hm
  rw [heq,hm.deriv]
  field_simp

 

def archimedeanZetaTerm (n : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ)/2 * ((Complex.digamma ((s:ℂ)/2)).re - Real.log Real.pi)

lemma complex_digamma_continuousAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt Complex.digamma s := by
  let D : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen D := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hall : ∀ z ∈ D, ∀ m : ℕ, z ≠ -(m:ℂ) := by
    intro z hz m hm
    have hh : 0 < z.re := hz
    rw [hm] at hh
    simp only [Complex.neg_re,Complex.natCast_re] at hh
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hh
  have hd : DifferentiableOn ℂ Complex.Gamma D := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hall z hz)).differentiableWithinAt
  have ha := hd.analyticOnNhd ho s hs
  exact ha.deriv.continuousAt.div ha.continuousAt (Complex.Gamma_ne_zero (hall s hs))

lemma archimedeanZetaTerm_continuousOn (n : ℕ) :
    ContinuousOn (archimedeanZetaTerm n) (Icc 1 2) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  unfold archimedeanZetaTerm
  apply ContinuousAt.const_mul
  apply ContinuousAt.sub _ continuousAt_const
  apply Complex.continuous_re.continuousAt.comp
  have hc0 : ContinuousAt (fun t : ℝ => (t:ℂ)/2) s :=
    Complex.continuous_ofReal.continuousAt.div_const 2
  have hp : 0 < ((s:ℂ)/2).re := by
    have hs1 := hs.1
    simp only [Complex.div_ofNat_re,Complex.ofReal_re]
    positivity
  exact ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)/2)
    (complex_digamma_continuousAt_of_re_pos hp) hc0

lemma archimedeanZetaTerm_bounded (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm n s| ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc.bddAbove_image
    (archimedeanZetaTerm_continuousOn n).abs)
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro s hs
  exact (hB (Set.mem_image_of_mem _ hs)).trans (le_max_left _ _)

 

theorem logRegularized_deriv_bound_of_zero_sum
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (n : ℕ) {L c B : ℝ} (hL : 4 ≤ L) (hc : 0 < c) (hB : 0 < B)
    (X Y : ι → ℝ) (hX : ∀ i, 0 ≤ X i)
    (hgap : ∀ i, c^2 ≤ (X i)^2+(Y i)^2)
    (hsum : Summable (fun i => realPoleKernel (X i) (Y i) 1))
    (harch : ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm n s| ≤ B)
    (hidentity : ∀ h ∈ Ioc (0:ℝ) (4/L),
      L*(∑' i, realPoleKernel (X i) (Y i) (L*h)) =
        1/(1+h) + 1/h + L/2 +
          deriv (realDedekindZeta K) (1+h) / realDedekindZeta K (1+h) +
          archimedeanZetaTerm n (1+h)) :
    ∀ h ∈ Ioc (0:ℝ) (4/L),
      |deriv (logRegularizedDedekindZeta K) h| ≤
        (4*(1+3/c)^2*(3+B)+B+2)*L := by
  have hLp : 0 < L := by linarith
  have hupper : 4/L ≤ 1 := (div_le_one hLp).mpr hL
  have hinv : 0 < 1/L := one_div_pos.mpr hLp
  have hinv4 : 1/L ≤ 4/L := div_le_div_of_nonneg_right (by norm_num) hLp.le
  have hLs : L*(1/L) = 1 := by field_simp
  have H0 := hidentity (1/L) ⟨hinv,hinv4⟩
  rw [hLs,one_div_one_div] at H0
  have hG0 := abs_le.mp (harch (1+1/L) ⟨by linarith,by linarith⟩)
  have hR0 : deriv (realDedekindZeta K) (1+1/L) /
      realDedekindZeta K (1+1/L) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (realDedekindZeta_deriv_nonpos K (by linarith))
      (realDedekindZeta_pos K (by linarith)).le
  have hrec0 : 1/(1+1/L) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1+1/L)).mpr
    linarith
  have hBL : B ≤ B*L := by nlinarith
  have hbase : L*(∑' i, realPoleKernel (X i) (Y i) 1) ≤ (3+B)*L := by
    nlinarith only [H0,hG0.2,hR0,hrec0,hBL,hL]
  intro h hh
  have hhp : 0 < h := hh.1
  have hU : 0 < L*h := mul_pos hLp hh.1
  have hU4 : L*h ≤ 4 := by
    have H := (le_div_iff₀ hLp).mp hh.2
    nlinarith only [H]
  have Hcomp := tsum_realPoleKernel_comparison X Y hc hX hU hU4 hgap hsum
  let A : ℝ := 4*(1+3/c)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS0 : 0 ≤ L*(∑' i, realPoleKernel (X i) (Y i) (L*h)) :=
    mul_nonneg hLp.le Hcomp.2.1
  have hS : L*(∑' i, realPoleKernel (X i) (Y i) (L*h)) ≤ A*(3+B)*L := by
    calc
      _ ≤ L*(A*(∑' i, realPoleKernel (X i) (Y i) 1)) :=
        mul_le_mul_of_nonneg_left Hcomp.2.2 hLp.le
      _ = A*(L*(∑' i, realPoleKernel (X i) (Y i) 1)) := by ring
      _ ≤ A*((3+B)*L) := mul_le_mul_of_nonneg_left hbase hA
      _ = _ := by ring
  have hh1 : h ≤ 1 := hh.2.trans hupper
  have hG := abs_le.mp (harch (1+h) ⟨by linarith,by linarith⟩)
  have hrec : 0 ≤ 1/(1+h) ∧ 1/(1+h) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one (by linarith)).mpr (by linarith)
  have Hd := logRegularizedDedekindZeta_deriv K hh.1
  have HI := hidentity h hh
  have hAL : 0 ≤ A*(3+B)*L := by positivity
  change |deriv (logRegularizedDedekindZeta K) h| ≤ (A*(3+B)+B+2)*L
  apply abs_le.mpr
  constructor <;> nlinarith only [Hd,HI,hS0,hS,hG.1,hG.2,hrec.1,hrec.2,hL,hBL,hAL]

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem haar_barycenter {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (κ : Kernel Y (X n)) [IsMarkovKernel κ]
    (m : Measure (X n)) (hm : IsHaarProbability m)
    (hinv : ∀ᵐ y ∂μ, ∀ g : G n, Measure.map (fun x => rightAction x g) (κ y) = κ y) :
    κ ∘ₘ μ = m := by
  have heq : ∀ᵐ y ∂μ, κ y = (Kernel.const Y m) y := by
    filter_upwards [hinv] with y hy
    exact isHaarProbability_unique ⟨inferInstance,hy⟩ hm
  rw [Measure.comp_congr heq,Measure.const_comp,measure_univ,one_smul]

 

theorem measure_eq_haar_of_condExpKernel_invariance {n : ℕ}
    (ν : Measure (X n)) [IsProbabilityMeasure ν]
    (m : Measure (X n)) (hm : IsHaarProbability m)
    (s : MeasurableSpace (X n)) (hs : s ≤ xMeasurableSpace n) :
    let : MeasurableSpace (X n) := xMeasurableSpace n
    condExpKernel ν s ∘ₘ ν.trim hs = ν →
    (∀ᵐ y ∂ν.trim hs, ∀ g : G n,
      Measure.map (fun x => rightAction x g) (condExpKernel ν s y) = condExpKernel ν s y) →
    ν = m := by
  dsimp only
  let : MeasurableSpace (X n) := xMeasurableSpace n
  intro hdec hinv
  have hp : @IsProbabilityMeasure (X n) s (ν.trim hs) := by
    constructor
    rw [trim_measurableSet_eq hs (@MeasurableSet.univ _ s)]
    exact measure_univ
  exact hdec.symm.trans (@haar_barycenter (X n) s n (ν.trim hs) hp
    (condExpKernel ν s) inferInstance m hm hinv)

end PrimeDegreePackets

open MeasureTheory Filter Set Matrix
open scoped Topology Classical
namespace PrimeDegreePackets

lemma mem_thickLattices_iff {n : ℕ} (x : X n) (ε : ℝ) :
    x ∈ thickLattices n ε ↔ ∀ v ∈ pointLattice x, v ≠ 0 → ε ≤ ‖v‖ := by
  constructor
  · intro hx
    induction x using Quotient.inductionOn with
    | h g =>
      intro v hv hv0
      obtain ⟨z,hz⟩ := (integerRowEquiv g).surjective ⟨v,hv⟩
      have hz' : integerRowMap g.1 z = v := congrArg Subtype.val hz
      have hz0 : z ≠ 0 := by
        intro h
        apply hv0
        rw [←hz',h,_root_.map_zero]
      simpa only [←hz',integerRowMap_apply] using hx g rfl z hz0
  · intro hx g hg z hz
    have hzne : integerRowMap g.1 z ≠ 0 := by
      intro h
      exact hz (integerRowMap_injective g (h.trans (map_zero _).symm))
    have hmem : integerRowMap g.1 z ∈ pointLattice x := by
      rw [←hg,pointLattice_mk,←integerRowMap_range]
      exact ⟨z,rfl⟩
    simpa only [integerRowMap_apply] using hx _ hmem hzne

 

lemma exists_mem_thickLattices {n : ℕ} (x : X n) :
    ∃ ε : ℝ, 0 < ε ∧ x ∈ thickLattices n ε := by
  induction x using Quotient.inductionOn with
  | h g =>
    have he : rowLattice g.1 = Submodule.span ℤ (Set.range (rowBasis g)) := by
      congr 2
      ext i j
      exact (rowBasis_apply g i j).symm
    have hd : DiscreteTopology (rowLattice g.1) := by rw [he]; infer_instance
    obtain ⟨ε,hε,H⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (s := (rowLattice g.1 : Set (Fin n → ℝ))) DiscreteTopology.isDiscrete
      (Submodule.zero_mem _)
    refine ⟨ε,hε,(mem_thickLattices_iff _ _).mpr ?_⟩
    intro v hv hv0
    by_contra h
    have hball : v ∈ Metric.ball 0 ε := by simpa only [Metric.mem_ball,_root_.dist_zero_right] using lt_of_not_ge h
    have hm : v ∈ ({0} : Set (Fin n → ℝ)) := H ▸ ⟨hball,hv⟩
    exact hv0 (Set.mem_singleton_iff.mp hm)

lemma exists_mem_countable_thickLattices {n : ℕ} (x : X n) :
    ∃ k : ℕ, x ∈ thickLattices n ((k+1:ℝ)⁻¹) := by
  obtain ⟨ε,hε,hx⟩ := exists_mem_thickLattices x
  obtain ⟨k,hk⟩ := exists_nat_gt (ε⁻¹)
  refine ⟨k,(mem_thickLattices_iff _ _).mpr ?_⟩
  intro v hv hv0
  apply le_trans _ ((mem_thickLattices_iff _ _).mp hx v hv hv0)
  apply (inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ)<k+1)).mpr
  have H := (inv_lt_iff_one_lt_mul₀ hε).mp hk
  nlinarith

 
def coordinateContractionWeights (d : ℕ) (j : Fin (d+1)) (i : Fin (d+1)) : ℝ :=
  (if i=j then ((d+1:ℕ):ℝ) else 0)-1

lemma coordinateContractionWeights_sum (d : ℕ) (j : Fin (d+1)) :
    ∑ i, coordinateContractionWeights d j i = 0 := by
  simp [coordinateContractionWeights,Finset.sum_sub_distrib]

lemma coordinateContraction_vector (d : ℕ) (j : Fin (d+1))
    (v : Fin (d+1) → ℝ) (hv : v j = 0) (t : ℝ) :
    diagonalLinear (d+1) (fun i => Real.exp (coordinateContractionWeights d j i*t)) v =
      Real.exp (-t) • v := by
  ext i
  by_cases hi : i=j
  · subst i; simp [diagonalLinear,hv]
  · simp [diagonalLinear,coordinateContractionWeights,hi]

 

lemma no_coordinate_zero_of_recurrence (d : ℕ) (j : Fin (d+1)) (x : X (d+1))
    (hrec : ∀ k : ℕ, x ∈ thickLattices (d+1) ((k+1:ℝ)⁻¹) →
      ∃ᶠ l : ℕ in atTop,
        rightAction x ((diagonalOneParameter (coordinateContractionWeights d j)
          (coordinateContractionWeights_sum d j) 1)^l) ∈
            thickLattices (d+1) ((k+1:ℝ)⁻¹)) :
    ∀ v ∈ pointLattice x, v ≠ 0 → v j ≠ 0 := by
  intro v hv hv0 hvj
  obtain ⟨k,hk⟩ := exists_mem_countable_thickLattices x
  have hthin : Tendsto (fun l : ℕ => Real.exp (-(l:ℝ))*‖v‖) atTop (𝓝 0) := by
    have he : Tendsto (fun l : ℕ => Real.exp (-(l:ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    simpa only [zero_mul] using he.mul_const ‖v‖
  have hsmall := hthin.eventually_lt_const (by positivity : (0:ℝ)<(k+1:ℝ)⁻¹)
  obtain ⟨l,hl,hlt⟩ := ((hrec k hk).and_eventually hsmall).exists
  rw [←diagonalOneParameter_nat] at hl
  let w : Fin (d+1) → ℝ := Real.exp (-(l:ℝ)) • v
  have hw0 : w ≠ 0 := smul_ne_zero (Real.exp_ne_zero _) hv0
  have hw : w ∈ pointLattice (rightAction x
      (diagonalOneParameter (coordinateContractionWeights d j)
        (coordinateContractionWeights_sum d j) l)) := by
    rw [pointLattice_rightAction_diagonal _ _ _ rfl]
    exact ⟨v,hv,coordinateContraction_vector d j v hvj l⟩
  have H := (mem_thickLattices_iff _ _).mp hl w hw hw0
  have hn : ‖w‖ = Real.exp (-(l:ℝ))*‖v‖ := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [hn] at H
  exact (not_lt_of_ge H) hlt

 

theorem ae_no_coordinate_zero (d : ℕ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0 := by
  have H (j : Fin (d+1)) : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → v j ≠ 0 := by
    let ell := coordinateContractionWeights d j
    let a := diagonalOneParameter ell (coordinateContractionWeights_sum d j) 1
    have hp : MeasurePreserving (fun x : X (d+1) => rightAction x a) μ μ := by
      refine ⟨(continuous_rightAction a).measurable,?_⟩
      rw [show a = diagonalFlow (fun i : Fin d => ell i.castSucc*1) from
        diagonalOneParameter_eq_diagonalFlow ell (coordinateContractionWeights_sum d j) 1]
      exact hA _
    have hr (k : ℕ) := hp.conservative.ae_mem_imp_frequently_image_mem
      (thickLattices_isClosed (d+1) ((k+1:ℝ)⁻¹)).measurableSet.nullMeasurableSet
    filter_upwards [ae_all_iff.mpr hr] with x hx
    apply no_coordinate_zero_of_recurrence d j x
    intro k hk
    simpa only [rightAction_iterate,a,ell] using hx k hk
  filter_upwards [ae_all_iff.mpr H] with x hx
  intro v hv hv0 j
  exact hx j v hv hv0

end PrimeDegreePackets
end
end

end OAI
