import Mathlib
import OAI.Analysis.HardSphere.Operators.FreeTransition
import OAI.Analysis.HardSphere.Geometry.CoordinateLine
import OAI.Analysis.HardSphere.Geometry.HeatScalar

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open scoped ComplexConjugate

lemma configurationCharacter_smooth (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    configurationCharacter N L k ∈ smoothAlgebra N L := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ ∏ p : Direction N, fourier (k p) (X p.1 p.2 : AddCircle L.val))
  apply contDiff_prod
  intro p _
  simp_rw [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((((contDiff_const.mul contDiff_const).mul contDiff_const).mul contDiff_const).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ p.1 p.2)) |>.div_const _)

lemma configurationCharacter_single_argument (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (p : Direction N) (z : AddCircle L.val) :
    configurationCharacter N L k (Pi.single p.1 (Pi.single p.2 z))=fourier (k p) z := by
  unfold configurationCharacter
  simp only [ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single p]
  · simp
  · intro q _ hq
    have hh : q.1≠p.1 ∨ q.2≠p.2 := by
      by_contra hh
      push Not at hh
      exact hq (Prod.ext hh.1 hh.2)
    rcases hh with h | h
    · simp [Pi.single_eq_of_ne h]
    · by_cases h' : q.1=p.1 <;> simp [h',Pi.single_eq_of_ne h]
  · simp

lemma configurationCharacter_coordinateLine (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X : Configuration N L) (p : Direction N) (z : AddCircle L.val) :
    configurationCharacter N L k (coordinateLine X p z)=
      configurationCharacter N L k X * fourier (k p) z := by
  rw [coordinateLine,configurationCharacter_add_argument,configurationCharacter_single_argument]

def characterDerivativeFactor (L : Length) (n : ℤ) : ℂ :=
  ((2 : ℕ) : ℂ)*Real.pi*Complex.I*n/L.val

lemma configurationCharacter_partial (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (p : Direction N) (X : Configuration N L) :
    coordDerivative N L (configurationCharacter N L k) p X =
      characterDerivativeFactor L (k p)*configurationCharacter N L k X := by
  have h := hasDerivAt_coordinateLine
    ((show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : LiftedConfiguration N ↦ configurationCharacter N L k (project N L Z)) from configurationCharacter_smooth N L k).differentiable (by simp)) X p 0
  have g := (hasDerivAt_fourier L.val (k p) 0).const_mul (configurationCharacter N L k X)
  simp_rw [configurationCharacter_coordinateLine] at h
  have heq := h.unique g
  simpa [coordinateLine,characterDerivativeFactor,mul_comm] using heq

lemma character_smoothPartial (N : ℕ) (L : Length) (k : Direction N → ℤ) (p : Direction N) :
    smoothPartial ⟨configurationCharacter N L k,configurationCharacter_smooth N L k⟩ p =
      characterDerivativeFactor L (k p) • configurationCharacter N L k := by
  ext X
  exact configurationCharacter_partial N L k p X

lemma character_weak_derivative {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u∈dirichletDomain N L a) (k : Direction N → ℤ) (p : Direction N) :
    inner ℂ (characterL2 N L k) (u.2 p) =
      -conj (characterDerivativeFactor L (k p)) * inner ℂ (characterL2 N L k) u.1 := by
  have h := weak_derivative hu ⟨configurationCharacter N L k,configurationCharacter_smooth N L k⟩ p
  rw [character_smoothPartial,map_smul,inner_smul_left] at h
  change inner ℂ (characterL2 N L k) (u.2 p) +
    conj (characterDerivativeFactor L (k p)) * inner ℂ (characterL2 N L k) u.1 = 0 at h
  linear_combination h

lemma allowed_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0) : allowed N L a=Set.univ := by
  ext X
  simp only [Set.mem_univ,iff_true]
  intro i j _
  exact ha.trans_le (Real.sqrt_nonneg _)

def characterTest (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) (k : Direction N → ℤ) :
    SmoothTest N L a where
  toFun := configurationCharacter N L k
  smooth := configurationCharacter_smooth N L k
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by rw [allowed_of_neg N L ha]; exact Set.subset_univ _
  memLp := (configurationCharacter N L k).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  partial_memLp p := by
    have heq : coordDerivative N L (configurationCharacter N L k) p =
        fun X ↦ characterDerivativeFactor L (k p)*configurationCharacter N L k X :=
      funext (configurationCharacter_partial N L k p)
    rw [heq]
    exact ((configurationCharacter N L k).continuous.const_mul _).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma characterTest_jet (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) (k : Direction N → ℤ) :
    (characterTest N L a ha k).jet=
      (characterL2 N L k,fun p ↦ characterDerivativeFactor L (k p) • characterL2 N L k) := by
  apply Prod.ext
  · apply Lp.ext
    exact (characterTest N L a ha k).memLp.coeFn_toLp.trans (characterL2_ae N L k).symm
  · funext p
    apply Lp.ext
    filter_upwards [(characterTest N L a ha k).partial_memLp p |>.coeFn_toLp,
      Lp.coeFn_smul (characterDerivativeFactor L (k p)) (characterL2 N L k),characterL2_ae N L k] with X h₁ h₂ h₃
    change ((characterTest N L a ha k).partial_memLp p).toLp _ X = _
    rw [h₁,h₂]
    change coordDerivative N L (configurationCharacter N L k) p X =
      characterDerivativeFactor L (k p) * (characterL2 N L k) X
    rw [h₃]
    exact configurationCharacter_partial N L k p X

lemma character_factor_square (L : Length) (n : ℤ) :
    -(conj (characterDerivativeFactor L n))^2 = ((2*Real.pi*n/L.val)^2:ℝ) := by
  simp only [characterDerivativeFactor,Nat.cast_ofNat,map_div₀,map_mul,map_ofNat,Complex.conj_ofReal,
    Complex.conj_I,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,map_intCast,Complex.ofReal_intCast]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma character_form_pairing (N : ℕ) (L : Length) (a : ℝ) (ha : a<0)
    (k : Direction N → ℤ) {v : Jet N L} (hv : v∈dirichletDomain N L a) :
    Variational.gradientPairing (characterTest N L a ha k).jet v =
      (fourierEnergy N L k:ℂ) * inner ℂ (characterL2 N L k) v.1 := by
  rw [characterTest_jet]
  change (∑ p : Direction N, inner ℂ (characterDerivativeFactor L (k p) • characterL2 N L k) (v.2 p)) = _
  simp_rw [inner_smul_left,character_weak_derivative hv]
  have hterm (p : Direction N) :
      conj (characterDerivativeFactor L (k p)) *
        (-conj (characterDerivativeFactor L (k p)) * inner ℂ (characterL2 N L k) v.1) =
      (((2*Real.pi*k p/L.val)^2:ℝ):ℂ)*inner ℂ (characterL2 N L k) v.1 := by
    rw [← character_factor_square]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  simp only [fourierEnergy,Nat.cast_ofNat,Complex.ofReal_sum]

lemma character_resolvent (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) (k : Direction N → ℤ) :
    formResolvent N L a (characterL2 N L k) =
      ((1+(fourierEnergy N L k:ℂ))⁻¹) • characterL2 N L k := by
  let u := (characterTest N L a ha k).jet
  have hu : u∈dirichletDomain N L a := subset_closure ⟨characterTest N L a ha k,rfl⟩
  have huf : u.1=characterL2 N L k := congrArg Prod.fst (characterTest_jet N L a ha k)
  let ug : hilbertDomain N L a := ⟨(hilbertJetEquiv N L).symm u,by
    change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm u) ∈ dirichletSubmodule N L a
    simpa using hu⟩
  have hE := fourierEnergy_nonneg N L k
  have hne : 1+(fourierEnergy N L k:ℂ) ≠ 0 := by
    have hreal : (1:ℝ)+fourierEnergy N L k ≠ 0 := ne_of_gt (by linarith)
    exact_mod_cast hreal
  have heq : (scalarEmbedding N L a).adjoint (characterL2 N L k) =
      ((1+(fourierEnergy N L k:ℂ))⁻¹) • ug := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [inner_smul_left ug v ((1+(fourierEnergy N L k:ℂ))⁻¹)]
    have hv : hilbertJetEquiv N L (v : HilbertJet N L) ∈ dirichletDomain N L a := v.property
    have hg : inner ℂ ug v = (1+(fourierEnergy N L k:ℂ))*
        inner ℂ (characterL2 N L k) (scalarEmbedding N L a v) := by
      change inner ℂ (ug : HilbertJet N L) (v : HilbertJet N L) = _
      rw [hilbertJet_inner]
      have hgu : hilbertJetEquiv N L (ug : HilbertJet N L) = u := by simp [ug]
      rw [hgu,huf]
      have hh := character_form_pairing N L a ha k hv
      change (∑ p : Direction N, inner ℂ (u.2 p)
        ((hilbertJetEquiv N L (v : HilbertJet N L)).2 p)) = _ at hh
      rw [hh]
      change inner ℂ (characterL2 N L k) (scalarEmbedding N L a v) +
        (fourierEnergy N L k:ℂ)*inner ℂ (characterL2 N L k) (scalarEmbedding N L a v) = _
      ring
    rw [hg]
    simp only [map_inv₀,map_add,map_one,Complex.conj_ofReal]
    rw [← mul_assoc,inv_mul_cancel₀ hne,one_mul]
  change scalarEmbedding N L a ((scalarEmbedding N L a).adjoint (characterL2 N L k)) = _
  rw [heq,map_smul]
  congr 1

lemma character_formHeat (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) {t : ℝ}
    (ht : 0<t) (k : Direction N → ℤ) :
    formHeat N L a t (characterL2 N L k) =
      (Real.exp (-t*fourierEnergy N L k):ℂ) • characterL2 N L k := by
  have hh : formResolvent N L a (characterL2 N L k) =
      ((1+fourierEnergy N L k)⁻¹:ℝ) • characterL2 N L k := by
    rw [← IsScalarTower.algebraMap_smul ℂ ((1+fourierEnergy N L k)⁻¹:ℝ) (characterL2 N L k)]
    change formResolvent N L a (characterL2 N L k) = (((1+fourierEnergy N L k)⁻¹:ℝ):ℂ) • _
    simpa only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one] using
      character_resolvent N L a ha k
  rw [formHeat,cfc_eigen_apply _ (formResolvent_isPositive N L a).isSelfAdjoint _
    (heatScalar_smooth t).continuous _ ((heatScalar_smooth t).differentiable (by norm_num)).differentiableAt _ hh,
    heatScalar_resolvent ht (fourierEnergy_nonneg N L k)]
  exact (IsScalarTower.algebraMap_smul ℂ _ _).symm

lemma freeTransition_eq_formHeat (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) {t : ℝ}
    (ht : 0<t) : freeTransition N L t = formHeat N L a t := by
  apply ContinuousLinearMap.ext_on (s := Set.range (characterL2 N L))
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (characterL2_span_dense N L)
  · rintro _ ⟨k,rfl⟩
    rw [freeTransition_character N L t ht.le,character_formHeat N L a ha ht]

end HardSphere

end

end OAI
