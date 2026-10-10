import OAI.MathematicalPhysics.Fock.Beam
import OAI.InformationTheory.PhotonNumber.Gibbs
import OAI.Analysis.TensorLp

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
theorem weight_down (j : Fin n) (k : NumberIndex n) (hk : 0 < k j) :
    numberWeight (down j k)=numberWeight k-1 := by
  have hh := weight_up j (down j k)
  rw [up_down j k hk] at hh
  linarith
end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
def W (ke : NumberIndex n × NumberIndex n) : ℝ := numberWeight ke.1+numberWeight ke.2-1

theorem W_one_le (ke : NumberIndex n × NumberIndex n) : 1 ≤ W ke := by
  dsimp [W]
  linarith [numberWeight_one_le ke.1, numberWeight_one_le ke.2]

def upL (j : Fin n) (ke : NumberIndex n × NumberIndex n) := (up j ke.1,ke.2)
def upR (j : Fin n) (ke : NumberIndex n × NumberIndex n) := (ke.1,up j ke.2)

theorem upL_inj (j : Fin n) : Function.Injective (upL j) := by
  intro x y h
  change (up j x.1,x.2)=(up j y.1,y.2) at h
  exact Prod.ext (up_injective j (Prod.mk.inj h).1) (Prod.mk.inj h).2
theorem upR_inj (j : Fin n) : Function.Injective (upR j) := by
  intro x y h
  change (x.1,up j x.2)=(y.1,up j y.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (up_injective j (Prod.mk.inj h).2)
@[simp] theorem W_upL (j : Fin n) (ke : NumberIndex n × NumberIndex n) : W (upL j ke)=W ke+1 := by
  simp only [W, upL, weight_up]
  ring
@[simp] theorem W_upR (j : Fin n) (ke : NumberIndex n × NumberIndex n) : W (upR j ke)=W ke+1 := by
  simp only [W, upR, weight_up]
  ring

theorem up_update (j : Fin n) (k : NumberIndex n) : up j k=Function.update k j (k j+1) := by
  funext i
  by_cases he : i=j
  · subst i; simp
  · simp [he]

theorem coordinate_le (j : Fin n) (k : NumberIndex n) : (k j:ℝ)+1 ≤ numberWeight k := by
  unfold numberWeight
  have hh : (k j:ℝ) ≤ ∑ i : Fin n, (k i:ℝ) := Finset.single_le_sum (fun (i : Fin n) (_hi : i ∈ Finset.univ) => Nat.cast_nonneg (k i)) (Finset.mem_univ j)
  linarith

theorem lowerL_bound (j : Fin n) (ke : NumberIndex n × NumberIndex n) :
    ‖((Real.sqrt ((ke.1 j:ℝ)+1)/(W ke+1):ℝ):ℂ)‖ ≤ 1 := by
  have hw : 0 < W ke+1 := by linarith [W_one_le ke]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hw.le)]
  apply (div_le_one (by linarith [W_one_le ke])).mpr
  have hs : Real.sqrt ((ke.1 j:ℝ)+1) ≤ (ke.1 j:ℝ)+1 := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [Nat.cast_nonneg (ke.1 j) (α:=ℝ)]))
  dsimp [W]
  linarith [coordinate_le j ke.1, numberWeight_one_le ke.2]

theorem lowerR_bound (j : Fin n) (ke : NumberIndex n × NumberIndex n) :
    ‖((Real.sqrt ((ke.2 j:ℝ)+1)/(W ke+1):ℝ):ℂ)‖ ≤ 1 := by
  have hw : 0 < W ke+1 := by linarith [W_one_le ke]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hw.le)]
  apply (div_le_one (by linarith [W_one_le ke])).mpr
  have hs : Real.sqrt ((ke.2 j:ℝ)+1) ≤ (ke.2 j:ℝ)+1 := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [Nat.cast_nonneg (ke.2 j) (α:=ℝ)]))
  dsimp [W]
  linarith [coordinate_le j ke.2, numberWeight_one_le ke.1]

def lowerL (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM (upL j) (upL_inj j)
    (fun ke => ((Real.sqrt ((ke.1 j:ℝ)+1)/(W ke+1):ℝ):ℂ)) 1 (by norm_num) (lowerL_bound j)
def lowerR (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM (upR j) (upR_inj j)
    (fun ke => ((Real.sqrt ((ke.2 j:ℝ)+1)/(W ke+1):ℝ):ℂ)) 1 (by norm_num) (lowerR_bound j)
@[simp] theorem lowerL_apply (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    lowerL j x ke=((Real.sqrt ((ke.1 j:ℝ)+1)/(W ke+1):ℝ):ℂ)*x (upL j ke) := rfl
@[simp] theorem lowerR_apply (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    lowerR j x ke=((Real.sqrt ((ke.2 j:ℝ)+1)/(W ke+1):ℝ):ℂ)*x (upR j ke) := rfl

theorem lowerL_single (j : Fin n) (a b : NumberIndex n) :
    lowerL j (lp.single 2 (a,b) 1)=
      ((Real.sqrt (a j)/W (a,b):ℝ):ℂ) • lp.single 2 (down j a,b) 1 := by
  by_cases ha : 0<a j
  · have he : (a,b)=upL j (down j a,b) := by simp [upL, up_down j a ha]
    conv_lhs => arg 2; arg 2; rw [he]
    rw [lowerL, WeightedShift.pullCLM_single]
    have hw : W (down j a,b)+1=W (a,b) := by simpa only [upL, up_down j a ha] using W_upL j (down j a,b) |>.symm
    have hc : ((down j a) j:ℝ)+1=a j := by
      rw [down, Function.update_self]
      exact_mod_cast (Nat.sub_add_cancel ha)
    simp only [hc, hw, mul_one]
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E:=fun _ : NumberIndex n × NumberIndex n => ℂ) 2 (down j a,b) ((Real.sqrt (a j)/W (a,b):ℝ):ℂ) (1:ℂ)
  · have hz : a j=0 := Nat.eq_zero_of_not_pos ha
    have hout (ke : NumberIndex n × NumberIndex n) : upL j ke ≠ (a,b) := by
      intro he
      have hh := congrArg (fun p : NumberIndex n × NumberIndex n => p.1 j) he
      simp [upL, hz] at hh
    rw [lowerL, WeightedShift.pullCLM_single_outside _ _ _ _ _ _ _ hout]
    simp [hz]

theorem lowerR_single (j : Fin n) (a b : NumberIndex n) :
    lowerR j (lp.single 2 (a,b) 1)=
      ((Real.sqrt (b j)/W (a,b):ℝ):ℂ) • lp.single 2 (a,down j b) 1 := by
  by_cases hb : 0<b j
  · have he : (a,b)=upR j (a,down j b) := by simp [upR, up_down j b hb]
    conv_lhs => arg 2; arg 2; rw [he]
    rw [lowerR, WeightedShift.pullCLM_single]
    have hw : W (a,down j b)+1=W (a,b) := by simpa only [upR, up_down j b hb] using W_upR j (a,down j b) |>.symm
    have hc : ((down j b) j:ℝ)+1=b j := by
      rw [down, Function.update_self]
      exact_mod_cast (Nat.sub_add_cancel hb)
    simp only [hc, hw, mul_one]
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E:=fun _ : NumberIndex n × NumberIndex n => ℂ) 2 (a,down j b) ((Real.sqrt (b j)/W (a,b):ℝ):ℂ) (1:ℂ)
  · have hz : b j=0 := Nat.eq_zero_of_not_pos hb
    have hout (ke : NumberIndex n × NumberIndex n) : upR j ke ≠ (a,b) := by
      intro he
      have hh := congrArg (fun p : NumberIndex n × NumberIndex n => p.2 j) he
      simp [upR, hz] at hh
    rw [lowerR, WeightedShift.pullCLM_single_outside _ _ _ _ _ _ _ hout]
    simp [hz]

theorem coefficient_W (η : ℝ) (k e a b : NumberIndex n) (hc : beamCoefficient η k e a b ≠ 0) :
    W (k,e)=W (a,b) := by
  have hj (j : Fin n) : k j+e j=a j+b j := by
    have hp := (Finset.prod_ne_zero_iff.mp hc) j (Finset.mem_univ j)
    by_contra hh
    apply hp
    simp only [oneModeBeamCoefficient, ite_eq_right hh]
  have hs : (∑ j, (k j:ℝ))+(∑ j, (e j:ℝ))=(∑ j, (a j:ℝ))+(∑ j, (b j:ℝ)) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact_mod_cast hj j
  dsimp [W, numberWeight]
  linarith

theorem inverse_W_coefficient (η : ℝ) (j : Fin n) (k e a b : NumberIndex n) :
    (W (k,e)+1)⁻¹*beamCoefficient η (up j k) e a b=
      (W (a,b))⁻¹*beamCoefficient η (up j k) e a b := by
  by_cases hc : beamCoefficient η (up j k) e a b=0
  · simp [hc]
  · have hh : W (k,e)+1=W (a,b) := by
      rw [← W_upL j (k,e)]
      exact coefficient_W η _ _ _ _ hc
    rw [hh]

theorem retained_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    lowerL j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • lowerL j+(Real.sqrt (1-η):ℂ) • lowerR j) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ENNReal) ≠ ⊤)
  intro ab
  apply ContinuousLinearMap.ext_ring
  change lowerL j (beamUnitary η hη (lp.single 2 ab 1))=
    beamUnitary η hη (((Real.sqrt η:ℂ) • lowerL j+(Real.sqrt (1-η):ℂ) • lowerR j) (lp.single 2 ab 1))
  obtain ⟨a,b⟩ := ab
  simp only [add_apply, smul_apply, lowerL_single, lowerR_single, map_add, map_smul]
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [lowerL_apply, upL, beam_coordinate, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hh := beam_retained_lower η j k e a b
  rw [← up_update] at hh
  change _=(Real.sqrt η:ℂ)*(((Real.sqrt (a j)/W (a,b):ℝ):ℂ)*(beamCoefficient η k e (down j a) b:ℂ))+
    (Real.sqrt (1-η):ℂ)*(((Real.sqrt (b j)/W (a,b):ℝ):ℂ)*(beamCoefficient η k e a (down j b):ℂ))
  have hw := inverse_W_coefficient η j k e a b
  norm_cast
  dsimp [down] at *
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  linear_combination (Real.sqrt ((k j:ℝ)+1))*hw+(W (a,b))⁻¹*hh
end BeamLadder

namespace EntropyPhotonNumber
 theorem beam_discarded_lower {n : ℕ} (η : ℝ) (j : Fin n) (k e a b : NumberIndex n) :
    Real.sqrt ((e j:ℝ)+1)*beamCoefficient η k (Function.update e j (e j+1)) a b =
      -(Real.sqrt (1-η)*Real.sqrt (a j))*beamCoefficient η k e (Function.update a j (a j-1)) b+
      Real.sqrt η*Real.sqrt (b j)*beamCoefficient η k e a (Function.update b j (b j-1)) := by
  exact beam_product_lower j (fun _ e k a b => oneModeBeamCoefficient η k e a b) e k a b
    _ _ _ (oneMode_discarded_lower η (k j) (e j) (a j) (b j))
end EntropyPhotonNumber

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

theorem inverse_W_coefficient_right (η : ℝ) (j : Fin n) (k e a b : NumberIndex n) :
    (W (k,e)+1)⁻¹*beamCoefficient η k (up j e) a b=
      (W (a,b))⁻¹*beamCoefficient η k (up j e) a b := by
  by_cases hc : beamCoefficient η k (up j e) a b=0
  · simp [hc]
  · have hh : W (k,e)+1=W (a,b) := by
      rw [← W_upR j (k,e)]
      exact coefficient_W η _ _ _ _ hc
    rw [hh]

theorem discarded_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    lowerR j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • lowerL j+(Real.sqrt η:ℂ) • lowerR j) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ENNReal) ≠ ⊤)
  intro ab
  apply ContinuousLinearMap.ext_ring
  change lowerR j (beamUnitary η hη (lp.single 2 ab 1))=
    beamUnitary η hη ((-(Real.sqrt (1-η):ℂ) • lowerL j+(Real.sqrt η:ℂ) • lowerR j) (lp.single 2 ab 1))
  obtain ⟨a,b⟩ := ab
  simp only [add_apply, smul_apply, lowerL_single, lowerR_single, map_add, map_smul]
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [lowerR_apply, upR, beam_coordinate, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hh := beam_discarded_lower η j k e a b
  rw [← up_update] at hh
  change _= -(Real.sqrt (1-η):ℂ)*(((Real.sqrt (a j)/W (a,b):ℝ):ℂ)*(beamCoefficient η k e (down j a) b:ℂ))+
    (Real.sqrt η:ℂ)*(((Real.sqrt (b j)/W (a,b):ℝ):ℂ)*(beamCoefficient η k e a (down j b):ℂ))
  have hw := inverse_W_coefficient_right η j k e a b
  norm_cast
  dsimp [down] at *
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  linear_combination (Real.sqrt ((e j:ℝ)+1))*hw+(W (a,b))⁻¹*hh
end

section
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

def radial (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C) (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C) :
    JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM id Function.injective_id (fun ke => (f (W ke):ℂ)) C hC
    (fun ke => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf ke)

@[simp] theorem radial_apply (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C)
    (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    radial f C hC hf x ke=(f (W ke):ℂ)*x ke := rfl

theorem radial_single (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C)
    (ke : NumberIndex n × NumberIndex n) :
    radial f C hC hf (lp.single 2 ke 1)=(f (W ke):ℂ) • lp.single 2 ke 1 := by
  apply lp.ext
  funext ab
  by_cases he : ab=ke
  · subst ab
    simp only [radial_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  · simp only [radial_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_single, Pi.single_apply, ite_eq_right he, mul_zero]

theorem radial_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C) :
    radial f C hC hf ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L radial f C hC hf := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ENNReal)≠⊤)
  intro ab
  apply ContinuousLinearMap.ext_ring
  change radial f C hC hf (beamUnitary η hη (lp.single 2 ab 1))=
    beamUnitary η hη (radial f C hC hf (lp.single 2 ab 1))
  rw [radial_single, map_smul]
  obtain ⟨a,b⟩ := ab
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [radial_apply, beam_coordinate, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hc : beamCoefficient η k e a b=0
  · simp only [hc, Complex.ofReal_zero, mul_zero]
  · rw [coefficient_W η k e a b hc]

theorem adjoint_covariance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (A B : E →L[ℂ] E)
    (h : A ∘L U.toContinuousLinearEquiv.toContinuousLinearMap=
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L B) :
    A.adjoint ∘L U.toContinuousLinearEquiv.toContinuousLinearMap=
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L B.adjoint := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (A.adjoint (U y))=inner ℂ x (U (B.adjoint y))
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hh : A x=U (B (U.symm x)) := by
    have hh := congrArg (fun T : E →L[ℂ] E => T (U.symm x)) h
    change A (U (U.symm x))=U (B (U.symm x)) at hh
    simpa only [U.apply_symm_apply] using hh
  rw [hh, U.inner_map_map]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact (U.inner_map_map (U.symm x) (B.adjoint y)).symm.trans (by rw [U.apply_symm_apply])

theorem retained_adjoint_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    (lowerL j).adjoint ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • (lowerL j).adjoint+(Real.sqrt (1-η):ℂ) • (lowerR j).adjoint) := by
  simpa only [map_add, map_smulₛₗ, Complex.conj_ofReal] using
    adjoint_covariance (beamUnitary η hη) (lowerL j) _ (retained_covariance η hη j)

theorem discarded_adjoint_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    (lowerR j).adjoint ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • (lowerL j).adjoint+(Real.sqrt η:ℂ) • (lowerR j).adjoint) := by
  simpa only [map_add, map_smulₛₗ, map_neg, Complex.conj_ofReal] using
    adjoint_covariance (beamUnitary η hη) (lowerR j) _ (discarded_covariance η hη j)
end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

def increase (w : ℝ) : ℝ := if 1<w then w/(w-1) else 0

theorem W_nat (ke : NumberIndex n × NumberIndex n) :
    W ke = ((∑j, ke.1 j)+(∑j, ke.2 j):ℕ)+1 := by
  simp only [W, numberWeight, Nat.cast_add, Nat.cast_sum]
  ring

theorem increase_bound (ke : NumberIndex n × NumberIndex n) : |increase (W ke)|≤2 := by
  unfold increase
  split_ifs with hh
  · have hh₂ : 2≤W ke := by
      rw [W_nat] at hh ⊢
      have hn : 1≤(∑j, ke.1 j)+(∑j, ke.2 j) := by exact_mod_cast (by linarith : (0:ℝ)<(((∑j, ke.1 j)+(∑j, ke.2 j):ℕ):ℝ))
      exact_mod_cast Nat.succ_le_succ hn
    rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
    apply (div_le_iff₀ (by linarith : 0<W ke-1)).mpr
    linarith
  · norm_num

def raiseL (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  radial increase 2 (by norm_num) increase_bound ∘L (lowerL j).adjoint

def raiseR (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  radial increase 2 (by norm_num) increase_bound ∘L (lowerR j).adjoint

theorem retained_creation_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    raiseL j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • raiseL j+(Real.sqrt (1-η):ℂ) • raiseR j) := by
  unfold raiseL raiseR
  rw [ContinuousLinearMap.comp_assoc, retained_adjoint_covariance,
    ← ContinuousLinearMap.comp_assoc, radial_covariance, ContinuousLinearMap.comp_assoc]
  congr 1
  ext x ke
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul]

theorem discarded_creation_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    raiseR j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • raiseL j+(Real.sqrt η:ℂ) • raiseR j) := by
  unfold raiseL raiseR
  rw [ContinuousLinearMap.comp_assoc, discarded_adjoint_covariance,
    ← ContinuousLinearMap.comp_assoc, radial_covariance, ContinuousLinearMap.comp_assoc]
  congr 1
  ext x ke
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul]

theorem raiseL_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseL j x (upL j ke)=((Real.sqrt ((ke.1 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upL j ke)):ℂ)*((lowerL j).adjoint x (upL j ke))=_
  rw [lowerL, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upL, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, map_div₀, map_add, map_one, Complex.conj_ofReal]
  have hw1 : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith : W ke+1≠0)
  field_simp

theorem raiseR_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseR j x (upR j ke)=((Real.sqrt ((ke.2 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upR j ke)):ℂ)*((lowerR j).adjoint x (upR j ke))=_
  rw [lowerR, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upR, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, map_div₀, map_add, map_one, Complex.conj_ofReal]
  have hw1 : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith : W ke+1≠0)
  field_simp

theorem raiseL_zero (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n)
    (hk : ke.1 j=0) : raiseL j x ke=0 := by
  change _*((lowerL j).adjoint x ke)=0
  rw [lowerL, WeightedShift.adjoint_apply_outside]
  · exact mul_zero _
  · intro ab he
    have hh := congrArg (fun q => q.1 j) he
    simp only [upL, up_same, hk] at hh
    omega

theorem raiseR_zero (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n)
    (hk : ke.2 j=0) : raiseR j x ke=0 := by
  change _*((lowerR j).adjoint x ke)=0
  rw [lowerR, WeightedShift.adjoint_apply_outside]
  · exact mul_zero _
  · intro ab he
    have hh := congrArg (fun q => q.2 j) he
    simp only [upR, up_same, hk] at hh
    omega
end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem inverse_bound (ke : NumberIndex n × NumberIndex n) : |(W ke)⁻¹|≤1 := by
  rw [abs_of_nonneg (inv_nonneg.mpr (by linarith [W_one_le ke]))]
  exact inv_le_one_of_one_le₀ (W_one_le ke)

def inverse : JointFock n →L[ℂ] JointFock n :=
  radial (fun t => t⁻¹) 1 (by norm_num) inverse_bound

@[simp] theorem inverse_apply (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    inverse x ke=((W ke)⁻¹:ℂ)*x ke := by
  change (((W ke)⁻¹:ℝ):ℂ)*x ke=_
  rw [Complex.ofReal_inv]

theorem inverse_selfAdjoint : IsSelfAdjoint (inverse (n:=n)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜:=ℂ) (inverse x) y)
  convert! lp.hasSum_inner (𝕜:=ℂ) x (inverse y) using 1
  ext ke
  simp only [inverse_apply, RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem inverse_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    inverse ∘L (beamUnitary (n:=n) η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L inverse :=
  radial_covariance η hη (fun t => t⁻¹) 1 (by norm_num) inverse_bound

theorem slice_raiseR_up (j : Fin n) (x : JointFock n) (e : NumberIndex n) :
    slice (raiseR j x) (up j e)=(Real.sqrt ((e j:ℝ)+1):ℂ) • slice (inverse x) e := by
  apply lp.ext
  funext k
  change raiseR j x (upR j (k,e))=_
  rw [raiseR_up]
  simp only [slice_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, inverse_apply,
    div_eq_mul_inv]
  push_cast
  ring

theorem slice_raiseR_zero (j : Fin n) (x : JointFock n) (e : NumberIndex n)
    (he : e j=0) : slice (raiseR j x) e=0 := by
  apply lp.ext
  funext k
  exact raiseR_zero j x (k,e) he

theorem discarded_commutator_operator (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    inverse ∘L liftLeft Z ∘L raiseR j =
      (lowerR j).adjoint ∘L liftLeft Z ∘L inverse := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases he : 0<e j
  · obtain ⟨f,hf⟩ : ∃ f, e=up j f := ⟨down j e,(up_down j e he).symm⟩
    subst e
    change inverse (liftLeft Z (raiseR j x)) (k,up j f)=
      (lowerR j).adjoint (liftLeft Z (inverse x)) (upR j (k,f))
    rw [inverse_apply, liftLeft_apply]
    rw [slice_raiseR_up, map_smul]
    rw [lowerR, WeightedShift.adjoint_apply_image]
    simp only [show W (k,up j f)=W (k,f)+1 from W_upR j (k,f),
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, liftLeft_apply, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_div, map_div₀, map_add, map_one, Complex.conj_ofReal]
    ring
  · have hz : e j=0 := Nat.eq_zero_of_not_pos he
    change _*Z (slice (raiseR j x) e) k=(lowerR j).adjoint (liftLeft Z (inverse x)) (k,e)
    rw [slice_raiseR_zero j x e hz, map_zero]
    rw [lowerR, WeightedShift.adjoint_apply_outside]
    · exact mul_zero _
    · intro ab hh
      have h := congrArg (fun q => q.2 j) hh
      simp only [upR, up_same, hz] at h
      omega

theorem discarded_commutator (j : Fin n) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ (inverse x) (liftLeft Z (raiseR j y))=
      inner ℂ (lowerR j x) (liftLeft Z (inverse y)) := by
  have hi : inner ℂ (inverse x) (liftLeft Z (raiseR j y))=
      inner ℂ x (inverse (liftLeft Z (raiseR j y))) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverse_selfAdjoint (n:=n))) x _
  rw [hi]
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T y)
    (discarded_commutator_operator j Z)
  change inverse (liftLeft Z (raiseR j y))=(lowerR j).adjoint (liftLeft Z (inverse y)) at hh
  rw [hh, ContinuousLinearMap.adjoint_inner_right]

def conjugate (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) :
    JointFock n →L[ℂ] JointFock n :=
  (beamUnitary η hη).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    liftLeft Z ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap

theorem conjugate_inner (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ x (conjugate η hη Z y)=inner ℂ (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)) := by
  change inner ℂ x ((beamUnitary η hη).symm (liftLeft Z (beamUnitary η hη y)))=_
  rw [← (beamUnitary η hη).inner_map_map, (beamUnitary η hη).apply_symm_apply]

theorem covariance_lower_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    lowerL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (lowerL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (lowerR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (retained_covariance η hη j)
  change lowerL j (beamUnitary η hη x)=beamUnitary η hη ((Real.sqrt η:ℂ) • lowerL j x+(Real.sqrt (1-η):ℂ) • lowerR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_raise_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    raiseL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (raiseL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (raiseR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (retained_creation_covariance η hη j)
  change raiseL j (beamUnitary η hη x)=beamUnitary η hη ((Real.sqrt η:ℂ) • raiseL j x+(Real.sqrt (1-η):ℂ) • raiseR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_inverse_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x : JointFock n) :
    inverse (beamUnitary η hη x)=beamUnitary η hη (inverse x) :=
  congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (inverse_covariance η hη)

theorem covariance_discarded_lower_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    lowerR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (lowerL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (lowerR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (discarded_covariance η hη j)
  change lowerR j (beamUnitary η hη x)=beamUnitary η hη (-(Real.sqrt (1-η):ℂ) • lowerL j x+(Real.sqrt η:ℂ) • lowerR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_discarded_raise_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    raiseR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (raiseL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (raiseR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (discarded_creation_covariance η hη j)
  change raiseR j (beamUnitary η hη x)=beamUnitary η hη (-(Real.sqrt (1-η):ℂ) • raiseL j x+(Real.sqrt η:ℂ) • raiseR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem two_port_algebra (c s r a b A B C D : ℂ) (hs : c^2+s^2=1)
    (hr : r=c^2*a+s^2*b) (hd : -s*A+c*B= -s*C+c*D) :
    (r+1)*(c*A+s*B)-r*(c*C+s*D)=
      c*((a+1)*A-a*C)+s*((b+1)*B-b*D) := by
  rw [hr]
  linear_combination (c*a*(A-C)+s*b*(B-D))*hs+c*s*(a-b)*hd

def weakL (r : ℝ) (j : Fin n) (x y : JointFock n)
    (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  (r+1:ℂ)*inner ℂ (lowerL j x) (T (inverse y))-
    (r:ℂ)*inner ℂ (inverse x) (T (raiseL j y))

def weakR (r : ℝ) (j : Fin n) (x y : JointFock n)
    (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  (r+1:ℂ)*inner ℂ (lowerR j x) (T (inverse y))-
    (r:ℂ)*inner ℂ (inverse x) (T (raiseR j y))

theorem physical_weak_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (a b : ℝ) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    weakL (η*a+(1-η)*b) j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)=
      (Real.sqrt η:ℂ)*weakL a j x y (conjugate η hη Z)+
        (Real.sqrt (1-η):ℂ)*weakR b j x y (conjugate η hη Z) := by
  have hd := discarded_commutator j Z (beamUnitary η hη x) (beamUnitary η hη y)
  rw [covariance_inverse_apply, covariance_inverse_apply, covariance_discarded_lower_apply,
    covariance_discarded_raise_apply] at hd
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, map_neg, Complex.conj_ofReal, ← conjugate_inner] at hd
  unfold weakL weakR
  rw [covariance_lower_apply, covariance_raise_apply, covariance_inverse_apply, covariance_inverse_apply]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, ← conjugate_inner]
  apply two_port_algebra
  · have hc : (Real.sqrt η:ℂ)^2=(η:ℂ) := by exact_mod_cast Real.sq_sqrt hη.1
    have hs : (Real.sqrt (1-η):ℂ)^2=(1-η:ℂ) := by exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hη.2)
    rw [hc, hs]
    ring
  · norm_cast
    rw [Real.sq_sqrt hη.1, Real.sq_sqrt (sub_nonneg.mpr hη.2)]
  · exact hd.symm
end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

def tensorPreimage (x y : Fock n) : JointFock n :=
  tensor (inverseWeight 2 x) (inverseWeight 3 y)+
    tensor (inverseWeight 3 x) (inverseWeight 2 y)-
    tensor (inverseWeight 3 x) (inverseWeight 3 y)

theorem tensorPreimage_apply (x y : Fock n) (k e : NumberIndex n) :
    tensorPreimage x y (k,e)=(W (k,e):ℂ)*inverseWeight 3 x k*inverseWeight 3 y e := by
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [tensorPreimage, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply,
    tensor_apply, inverseWeight_apply, W]
  push_cast
  field_simp

theorem tensorPreimage_inverse (x y : Fock n) :
    inverse (tensorPreimage x y)=tensor (inverseWeight 3 x) (inverseWeight 3 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rw [inverse_apply, tensorPreimage_apply, tensor_apply]
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  field_simp

theorem tensorPreimage_lowerL (j : Fin n) (x y : Fock n) :
    lowerL j (tensorPreimage x y)=tensor (sandwich 0 3 (by omega) j x) (inverseWeight 3 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [lowerL_apply, upL, tensorPreimage_apply, tensor_apply, sandwich_apply, coefficient,
    pow_zero, one_mul, inverseWeight_apply]
  have hh := W_upL j (k,e)
  change W (up j k,e)=W (k,e)+1 at hh
  rw [hh]
  have hw : (W (k,e):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)+1≠0)
  push_cast
  field_simp

theorem tensorPreimage_lowerR (j : Fin n) (x y : Fock n) :
    lowerR j (tensorPreimage x y)=tensor (inverseWeight 3 x) (sandwich 0 3 (by omega) j y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [lowerR_apply, upR, tensorPreimage_apply, tensor_apply, sandwich_apply, coefficient,
    pow_zero, one_mul, inverseWeight_apply]
  have hh := W_upR j (k,e)
  change W (k,up j e)=W (k,e)+1 at hh
  rw [hh]
  have hw : (W (k,e):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)+1≠0)
  push_cast
  field_simp

theorem tensorPreimage_raiseL (j : Fin n) (x y : Fock n) :
    raiseL j (tensorPreimage x y)=tensor (creationSandwich 0 3 (by omega) j x) (inverseWeight 3 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rcases index_cases j k with hk | ⟨a,rfl⟩
  · rw [raiseL_zero j _ (k,e) hk, tensor_apply, creationSandwich_zero _ _ _ _ _ k hk, zero_mul]
  · change raiseL j (tensorPreimage x y) (upL j (a,e))=_
    rw [raiseL_up, tensorPreimage_apply, tensor_apply, creationSandwich_up]
    have hw : (W (a,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)≠0)
    simp only [creationCoefficient, pow_zero, one_mul, inverseWeight_apply]
    push_cast
    field_simp

theorem tensorPreimage_raiseR (j : Fin n) (x y : Fock n) :
    raiseR j (tensorPreimage x y)=tensor (inverseWeight 3 x) (creationSandwich 0 3 (by omega) j y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rcases index_cases j e with he | ⟨b,rfl⟩
  · rw [raiseR_zero j _ (k,e) he, tensor_apply, creationSandwich_zero _ _ _ _ _ e he, mul_zero]
  · change raiseR j (tensorPreimage x y) (upR j (k,b))=_
    rw [raiseR_up, tensorPreimage_apply, tensor_apply, creationSandwich_up]
    have hw : (W (k,b):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,b)] : W (k,b)≠0)
    simp only [creationCoefficient, pow_zero, one_mul, inverseWeight_apply]
    push_cast
    field_simp

theorem square_add_summable {I E : Type*} [NormedAddCommGroup E] {x y : I → E}
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖x i+y i‖^2) := by
  have hmx : Memℓp x 2 := by
    simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two] using hx
  have hmy : Memℓp y 2 := by
    simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two] using hy
  simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two, Pi.add_apply] using hmx.add hmy

theorem tensorPreimage_summable {I J : Type*} (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensorPreimage (x ij.1) (y ij.2)‖^2) := by
  have ht (a b : ℕ) : Summable (fun ij : I × J => ‖tensor (inverseWeight a (x ij.1)) (inverseWeight b (y ij.2))‖^2) := by
    simpa only [tensor_norm_sq] using
      (CrossEnsemble.applied_summable hx (inverseWeight a)).mul_of_nonneg
        (CrossEnsemble.applied_summable hy (inverseWeight b)) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hn : Summable (fun ij : I × J => ‖-tensor (inverseWeight 3 (x ij.1)) (inverseWeight 3 (y ij.2))‖^2) := by
    simpa only [norm_neg] using ht 3 3
  simpa only [tensorPreimage, sub_eq_add_neg] using square_add_summable (square_add_summable (ht 2 3) (ht 3 2)) hn
end BeamLadder

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def wave (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2)) (x : E) :
    lp (fun _ : I => H) 2 :=
  ⟨fun i => V i x, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs x)⟩

@[simp] theorem wave_apply (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2))
    (x : E) (i : I) : wave V hs x i = V i x := rfl

 theorem wave_square (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2)) (x : E) :
    ‖wave V hs x‖^2 = ∑' i, ‖V i x‖^2 := by
  symm
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, wave_apply] using
    (lp.hasSum_norm (p := 2) (by norm_num) (wave V hs x)).tsum_eq

def linearMap (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2)) :
    E →ₗ[ℂ] lp (fun _ : I => H) 2 where
  toFun := wave V hs
  map_add' := fun x y => by apply lp.ext; funext i; exact map_add (V i) x y
  map_smul' := fun c x => by apply lp.ext; funext i; exact map_smul (V i) c x

 theorem wave_bound (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖V i x‖^2) ≤ C^2*‖x‖^2) (x : E) :
    ‖wave V hs x‖ ≤ C*‖x‖ := by
  have hh := hb x
  rw [← wave_square V hs x] at hh
  nlinarith [norm_nonneg (wave V hs x), mul_nonneg hC (norm_nonneg x)]

def lift (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖V i x‖^2) ≤ C^2*‖x‖^2) :
    E →L[ℂ] lp (fun _ : I => H) 2 :=
  (linearMap V hs).mkContinuous C (wave_bound V hs hC hb)

 theorem sum_bound {V : I → E →L[ℂ] H} (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) (x : E) :
    Summable (fun i => ‖Z (V i x)‖^2) ∧ (∑' i, ‖Z (V i x)‖^2) ≤ ‖Z‖^2*‖x‖^2 := by
  have hb (i : I) : ‖Z (V i x)‖^2 ≤ ‖Z‖^2*‖V i x‖^2 := by
    nlinarith [Z.le_opNorm (V i x), norm_nonneg (Z (V i x)), mul_nonneg (norm_nonneg Z) (norm_nonneg (V i x))]
  have hs := (hV x).summable.mul_left (‖Z‖^2)
  have ht := hs.of_nonneg_of_le (fun _ => sq_nonneg _) hb
  exact ⟨ht, (ht.tsum_le_tsum hb hs).trans_eq (by rw [tsum_mul_left, (hV x).tsum_eq])⟩

variable [CompleteSpace E] [CompleteSpace H]

def analysis (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    E →L[ℂ] lp (fun _ : I => H) 2 :=
  lift V (fun x => (hV x).summable) 1 (by norm_num) (by intro x; simp [(hV x).tsum_eq])

def acted (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : E →L[ℂ] lp (fun _ : I => H) 2 :=
  lift (fun i => Z ∘L V i) (fun x => (sum_bound hV Z x).1) ‖Z‖ (norm_nonneg Z)
    (fun x => (sum_bound hV Z x).2)

def dual (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : E →L[ℂ] E := (analysis V hV).adjoint ∘L acted V hV Z

 theorem dual_entry (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) (x y : E) :
    HasSum (fun i => inner ℂ (V i x) (Z (V i y))) (inner ℂ x (dual V hV Z y)) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (analysis V hV x) (acted V hV Z y)
  rw [← ContinuousLinearMap.adjoint_inner_right] at hh
  exact hh

omit [CompleteSpace E] [CompleteSpace H] in
 theorem analysis_norm (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    ‖analysis V hV‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact wave_bound V (fun y => (hV y).summable) (by norm_num : (0:ℝ) ≤ 1) (by intro y; simp [(hV y).tsum_eq]) x

omit [CompleteSpace E] [CompleteSpace H] in
 theorem acted_norm (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : ‖acted V hV Z‖ ≤ ‖Z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Z)
  intro x
  exact wave_bound (fun i => Z ∘L V i) (fun y => (sum_bound hV Z y).1) (norm_nonneg Z) (fun y => (sum_bound hV Z y).2) x

 theorem dual_norm (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : ‖dual V hV Z‖ ≤ ‖Z‖ := by
  calc
    _ ≤ ‖(analysis V hV).adjoint‖*‖acted V hV Z‖ := opNorm_comp_le _ _
    _ = ‖analysis V hV‖*‖acted V hV Z‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1*‖Z‖ := mul_le_mul (analysis_norm V hV) (acted_norm V hV Z) (by positivity) (by norm_num)
    _ = _ := one_mul _

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

 theorem dual_add (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z T : H →L[ℂ] H) : dual V hV (Z+T) = dual V hV Z+dual V hV T := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (dual_entry V hV (Z+T) x y).unique (by
    simpa only [add_apply, inner_add_right] using
      (dual_entry V hV Z x y).add (dual_entry V hV T x y))

 theorem dual_smul (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (c : ℂ) (Z : H →L[ℂ] H) : dual V hV (c • Z) = c • dual V hV Z := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (dual_entry V hV (c • Z) x y).unique (by
    simpa only [smul_apply, inner_smul_right] using (dual_entry V hV Z x y).mul_left c)

 theorem dual_adjoint (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : dual V hV Z.adjoint = (dual V hV Z).adjoint := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hh := (dual_entry V hV Z y x).mapL Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun i => starRingEnd ℂ (inner ℂ (V i y) (Z (V i x))))
    (starRingEnd ℂ (inner ℂ y (dual V hV Z x))) at hh
  exact (dual_entry V hV Z.adjoint x y).unique (by
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm] using hh)

 theorem dual_selfAdjoint (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    {Z : H →L[ℂ] H} (hZ : IsSelfAdjoint Z) : IsSelfAdjoint (dual V hV Z) := by
  change (dual V hV Z).adjoint = _
  rw [← dual_adjoint, show Z.adjoint = Z from hZ]

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

 theorem rightFamily_norm (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1) (x : H A) :
    HasSum (fun j => ‖tensorRight (y j) x‖^2) (‖x‖^2) := by
  simpa only [tensorRight_apply, tensor_norm_sq, mul_one] using hy.mul_left (‖x‖^2)
 theorem leftFamily_norm (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1) (y : H B) :
    HasSum (fun i => ‖tensorLeft (x i) y‖^2) (‖y‖^2) := by
  simpa only [tensorLeft_apply, tensor_norm_sq, one_mul] using hx.mul_right (‖y‖^2)

def conditionalLeft (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) : H A →L[ℂ] H A :=
  KrausBounded.dual (fun j => tensorRight (y j)) (rightFamily_norm y hy) Z

def conditionalRight (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) : H B →L[ℂ] H B :=
  KrausBounded.dual (fun i => tensorLeft (x i)) (leftFamily_norm x hx) Z

 theorem conditionalLeft_entry (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H A) :
    HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (conditionalLeft y hy Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem conditionalRight_entry (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H B) :
    HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (conditionalRight x hx Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem tensorFamily_summable (x : I → H A) (y : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) := by
  simpa only [tensor_norm_sq] using hx.mul_of_nonneg hy (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

theorem pairing_conditionalLeft (u v : I → H A) (y : J → H B)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (hy : HasSum (fun j => ‖y j‖^2) 1) (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (u ij.1) (y ij.2))
      (fun ij : I × J => tensor (v ij.1) (y ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalLeft y hy Z) := by
  have hh := (CrossEnsemble.pairing_summable (tensorFamily_summable u y hu hy.summable)
    (tensorFamily_summable v y hv hy.summable) Z).hasSum.prod_fiberwise
      (fun i => conditionalLeft_entry y hy Z (v i) (u i))
  exact hh.tsum_eq.symm

theorem pairing_conditionalRight (x : I → H A) (u v : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1)
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (x ij.1) (u ij.2))
      (fun ij : I × J => tensor (x ij.1) (v ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalRight x hx Z) := by
  have hs := CrossEnsemble.pairing_summable (tensorFamily_summable x u hx.summable hu)
    (tensorFamily_summable x v hx.summable hv) Z
  have hh := hs.prod_symm.hasSum.prod_fiberwise
      (fun j => conditionalRight_entry x hx Z (v j) (u j))
  have he := (Equiv.prodComm J I).tsum_eq
    (fun ij : I × J => inner ℂ (tensor (x ij.1) (v ij.2)) (Z (tensor (x ij.1) (u ij.2))))
  change (∑' ji : J × I, inner ℂ (tensor (x ji.swap.1) (v ji.swap.2))
    (Z (tensor (x ji.swap.1) (u ji.swap.2))))=_ at he
  rw [he] at hh
  exact hh.tsum_eq.symm
end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

def singleWeak (r : ℝ) (j : Fin n) (x : I → Fock n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  (r+1:ℂ)*CrossEnsemble.pairing (fun i => inverseWeight 3 (x i))
    (fun i => sandwich 0 3 (by omega) j (x i)) Z-
  (r:ℂ)*CrossEnsemble.pairing (fun i => creationSandwich 0 3 (by omega) j (x i))
    (fun i => inverseWeight 3 (x i)) Z

theorem weakL_summable (r : ℝ) (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (T : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => weakL r j (x i) (y i) T) :=
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy inverse)
    (CrossEnsemble.applied_summable hx (lowerL j)) T).mul_left _).sub
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy (raiseL j))
    (CrossEnsemble.applied_summable hx inverse) T).mul_left _)

theorem weakR_summable (r : ℝ) (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (T : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => weakR r j (x i) (y i) T) :=
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy inverse)
    (CrossEnsemble.applied_summable hx (lowerR j)) T).mul_left _).sub
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy (raiseR j))
    (CrossEnsemble.applied_summable hx inverse) T).mul_left _)

theorem weakL_product (r : ℝ) (j : Fin n) (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2))
    (hy : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : JointFock n →L[ℂ] JointFock n) :
    (∑' ij : I × J, weakL r j (tensorPreimage (x ij.1) (y ij.2))
      (tensorPreimage (x ij.1) (y ij.2)) Z)=
        singleWeak r j x (conditionalLeft (fun j => inverseWeight 3 (y j)) hy Z) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakL, tensorPreimage_lowerL, tensorPreimage_inverse, tensorPreimage_raiseL]
  rw [Summable.tsum_sub (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hi hy.summable)
    (tensorFamily_summable _ _ hl hy.summable) Z).mul_left _))
    (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hr hy.summable)
    (tensorFamily_summable _ _ hi hy.summable) Z).mul_left _)), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ Z-(r:ℂ)*CrossEnsemble.pairing _ _ Z=_
  rw [pairing_conditionalLeft _ _ _ hi hl hy, pairing_conditionalLeft _ _ _ hr hi hy]
  rfl

theorem weakR_product (r : ℝ) (j : Fin n) (x : I → Fock n) (y : J → Fock n)
    (hx : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hy : Summable (fun j => ‖y j‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    (∑' ij : I × J, weakR r j (tensorPreimage (x ij.1) (y ij.2))
      (tensorPreimage (x ij.1) (y ij.2)) Z)=
        singleWeak r j y (conditionalRight (fun i => inverseWeight 3 (x i)) hx Z) := by
  have hi := CrossEnsemble.applied_summable hy (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hy (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hy (creationSandwich 0 3 (by omega) j)
  simp only [weakR, tensorPreimage_lowerR, tensorPreimage_inverse, tensorPreimage_raiseR]
  rw [Summable.tsum_sub (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hx.summable hi)
    (tensorFamily_summable _ _ hx.summable hl) Z).mul_left _))
    (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hx.summable hr)
    (tensorFamily_summable _ _ hx.summable hi) Z).mul_left _)), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ Z-(r:ℂ)*CrossEnsemble.pairing _ _ Z=_
  rw [pairing_conditionalRight _ _ _ hx hi hl, pairing_conditionalRight _ _ _ hx hr hi]
  rfl

theorem product_weak_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (a b : ℝ) (j : Fin n)
    (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' ij : I × J, weakL (η*a+(1-η)*b) j
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2)))
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))) (liftLeft Z))=
    (Real.sqrt η:ℂ)*singleWeak a j x (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn (conjugate η hη Z))+
    (Real.sqrt (1-η):ℂ)*singleWeak b j y (conditionalRight (fun i => inverseWeight 3 (x i)) hxn (conjugate η hη Z)) := by
  have hs := tensorPreimage_summable x y hx hy
  simp only [physical_weak_covariance]
  rw [Summable.tsum_add ((weakL_summable a j _ _ hs hs _).mul_left _)
    ((weakR_summable b j _ _ hs hs _).mul_left _), tsum_mul_left, tsum_mul_left,
    weakL_product a j x y hx hyn, weakR_product b j x y hxn hy]
end BeamLadder

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace EntropyPhotonNumber
variable {n : ℕ}
theorem entry_ext {T R : Fock n →L[ℂ] Fock n}
    (h : ∀ k l, entry T k l = entry R k l) : T = R := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro l
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext k
  have h₁ : lp.single (E := fun _ : NumberIndex n => ℂ) 2 l c = c • numberKet l := by
    simp [numberKet, ← lp.single_smul]
  change T (lp.single 2 l c) k = R (lp.single 2 l c) k
  rw [h₁, map_smul, map_smul]
  have he := h k l
  simpa [entry, numberKet, lp.inner_single_left] using congrArg (fun z : ℂ => c*z) he
end EntropyPhotonNumber

namespace TensorLp
variable {A B I : Type*}
theorem slice_family_summable (x : I → H (A × B)) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ie : I × B => ‖slice (x ie.1) ie.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun i => (hasSum_slice_norm_sq (x i)).summable, ?_⟩
  simpa only [(hasSum_slice_norm_sq _).tsum_eq] using hx

theorem pairing_liftLeft (x y : I → H (A × B))
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : H A →L[ℂ] H A) :
    CrossEnsemble.pairing x y (liftLeft Z)=
      CrossEnsemble.pairing (fun ie : I × B => slice (x ie.1) ie.2)
        (fun ie : I × B => slice (y ie.1) ie.2) Z := by
  have hh := (CrossEnsemble.pairing_summable (slice_family_summable x hx)
    (slice_family_summable y hy) Z).hasSum.prod_fiberwise
      (fun i => by simpa only [slice_liftLeft] using hasSum_slice_inner (y i) (liftLeft Z (x i)))
  exact hh.tsum_eq
end TensorLp

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

theorem coordinate_hasSum (x y : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (a b : NumberIndex n) : HasSum (fun i => x i a*conj (y i b)) (entry (operator x y) a b) := by
  simpa only [entry, numberKet, lp.inner_single_left, lp.inner_single_right,
    RCLike.inner_apply, map_one, one_mul, mul_one] using entry_hasSum hx hy (numberKet a) (numberKet b)

theorem shifted_right_operator_eq (x y : I → Fock n) (u v : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (f : NumberIndex n → NumberIndex n) (c : NumberIndex n → ℂ)
    (hyx : ∀ i k, y i k=c k*x i (f k)) (hvu : ∀ j k, v j k=c k*u j (f k))
    (he : operator x x=operator u u) : operator x y=operator u v := by
  apply entry_ext
  intro a b
  have h₁ := (coordinate_hasSum x x hx hx a (f b)).mul_right (conj (c b))
  have h₂ := (coordinate_hasSum u u hu hu a (f b)).mul_right (conj (c b))
  have he₁ : entry (operator x y) a b=entry (operator x x) a (f b)*conj (c b) := by
    apply (coordinate_hasSum x y hx hy a b).unique
    convert! h₁ using 1
    ext i
    rw [hyx, map_mul]
    ring
  have he₂ : entry (operator u v) a b=entry (operator u u) a (f b)*conj (c b) := by
    apply (coordinate_hasSum u v hu hv a b).unique
    convert! h₂ using 1
    ext j
    rw [hvu, map_mul]
    ring
  rw [he₁, he₂, he]

theorem shifted_left_operator_eq (x y : I → Fock n) (u v : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (f : NumberIndex n → NumberIndex n) (c : NumberIndex n → ℂ)
    (hyx : ∀ i k, y i k=c k*x i (f k)) (hvu : ∀ j k, v j k=c k*u j (f k))
    (he : operator x x=operator u u) : operator y x=operator v u := by
  apply entry_ext
  intro a b
  have h₁ := (coordinate_hasSum x x hx hx (f a) b).mul_left (c a)
  have h₂ := (coordinate_hasSum u u hu hu (f a) b).mul_left (c a)
  have he₁ : entry (operator y x) a b=c a*entry (operator x x) (f a) b := by
    apply (coordinate_hasSum y x hy hx a b).unique
    convert! h₁ using 1
    ext i
    rw [hyx]
    ring
  have he₂ : entry (operator v u) a b=c a*entry (operator u u) (f a) b := by
    apply (coordinate_hasSum v u hv hu a b).unique
    convert! h₂ using 1
    ext j
    rw [hvu]
    ring
  rw [he₁, he₂, he]
end CrossEnsemble

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem lowerL_inverse_apply (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    lowerL j x (k,e)=(Real.sqrt ((k j:ℝ)+1):ℂ)*inverse x (up j k,e) := by
  simp only [lowerL_apply, inverse_apply,
    show W (up j k,e)=W (k,e)+1 from W_upL j (k,e)]
  push_cast
  rw [div_eq_mul_inv, mul_assoc]
  rfl

theorem raiseL_inverse_apply (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    raiseL j x (k,e)=(Real.sqrt (k j:ℝ):ℂ)*inverse x (down j k,e) := by
  rcases index_cases j k with hk | ⟨a,rfl⟩
  · simp only [raiseL_zero j x (k,e) hk, hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
  · change raiseL j x (upL j (a,e))=_
    rw [raiseL_up, up_same, down_up, inverse_apply]
    push_cast
    ring

theorem single_lower_inverse_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich 0 3 (by omega) j x k=(Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  simp only [sandwich_apply, coefficient, pow_zero, one_mul, inverseWeight_apply]
  push_cast
  ring

theorem single_raise_inverse_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich 0 3 (by omega) j x k=(Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨a,rfl⟩
  · simp only [creationSandwich_zero _ _ _ _ _ k hk, hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
  · rw [creationSandwich_up, up_same, down_up, inverseWeight_apply]
    simp only [creationCoefficient, pow_zero, one_mul]
    push_cast
    ring

theorem output_weak (r : ℝ) (j : Fin n) (x : I → JointFock n) (z : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (he : CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)
        (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)=
      CrossEnsemble.operator (fun j => inverseWeight 3 (z j)) (fun j => inverseWeight 3 (z j)))
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' i, weakL r j (x i) (x i) (liftLeft Z))=singleWeak r j z Z := by
  have hi := CrossEnsemble.applied_summable hx inverse
  have hl := CrossEnsemble.applied_summable hx (lowerL j)
  have hr := CrossEnsemble.applied_summable hx (raiseL j)
  have hzi := CrossEnsemble.applied_summable hz (inverseWeight 3)
  have hzl := CrossEnsemble.applied_summable hz (sandwich 0 3 (by omega) j)
  have hzr := CrossEnsemble.applied_summable hz (creationSandwich 0 3 (by omega) j)
  have his := slice_family_summable _ hi
  have hls := slice_family_summable _ hl
  have hrs := slice_family_summable _ hr
  have heL := CrossEnsemble.shifted_right_operator_eq _ _ _ _ his hls hzi hzl
    (up j) (fun k => (Real.sqrt ((k j:ℝ)+1):ℂ))
    (fun ie k => lowerL_inverse_apply j (x ie.1) k ie.2)
    (fun i k => single_lower_inverse_apply j (z i) k) he
  have heR := CrossEnsemble.shifted_left_operator_eq _ _ _ _ his hrs hzi hzr
    (down j) (fun k => (Real.sqrt (k j:ℝ):ℂ))
    (fun ie k => raiseL_inverse_apply j (x ie.1) k ie.2)
    (fun i k => single_raise_inverse_apply j (z i) k) he
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hpL := CrossEnsemble.pairing_eq_of_operator_eq bas his hls hzi hzl heL Z
  have hpR := CrossEnsemble.pairing_eq_of_operator_eq bas hrs his hzr hzi heR Z
  simp only [weakL]
  rw [Summable.tsum_sub ((CrossEnsemble.pairing_summable hi hl (liftLeft Z)).mul_left _)
    ((CrossEnsemble.pairing_summable hr hi (liftLeft Z)).mul_left _), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ (liftLeft Z)-(r:ℂ)*CrossEnsemble.pairing _ _ (liftLeft Z)=_
  rw [pairing_liftLeft _ _ hi hl, pairing_liftLeft _ _ hr hi, hpL, hpR]
  rfl
end BeamLadder

namespace TensorLp
variable {A B I : Type*}

theorem hasSum_slice_family {v : I → H (A × B)} {t : ℝ}
    (hv : HasSum (fun i => ‖v i‖^2) t) :
    HasSum (fun bi : B × I => ‖slice (v bi.2) bi.1‖^2) t := by
  have hp (i : I) : (∑' b, ‖slice (v i) b‖^2) = ‖v i‖^2 := (hasSum_slice_norm_sq (v i)).tsum_eq
  have hd : Summable (fun ib : I × B => ‖slice (v ib.1) ib.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (hasSum_slice_norm_sq (v i)).summable, ?_⟩
    simpa only [hp] using hv.summable
  have ht : (∑' ib : I × B, ‖slice (v ib.1) ib.2‖^2) = t := by
    rw [hd.tsum_prod]
    simpa only [hp] using hv.tsum_eq
  have hsum : HasSum (fun ib : I × B => ‖slice (v ib.1) ib.2‖^2) t := ht ▸ hd.hasSum
  exact (Equiv.prodComm B I).hasSum_iff.mpr hsum

def partialTrace (v : I → H (A × B)) : H A →L[ℂ] H A :=
  TraceEnsemble.operator (fun bi : B × I => slice (v bi.2) bi.1)

theorem partialTrace_positive {v : I → H (A × B)}
    (hv : Summable (fun i => ‖v i‖^2)) : (partialTrace v).IsPositive :=
  TraceEnsemble.positive (hasSum_slice_family hv.hasSum).summable

theorem partialTrace_trace {v : I → H (A × B)} {t : ℝ}
    (hv : HasSum (fun i => ‖v i‖^2) t) (b : HilbertBasis A ℂ (H A)) :
    HasSum (fun a => (inner ℂ (b a) (partialTrace v (b a))).re) t :=
  TraceEnsemble.trace (hasSum_slice_family hv) b

theorem partialTrace_entry [DecidableEq A] [DecidableEq B]
    {v : I → H (A × B)} (hv : Summable (fun i => ‖v i‖^2)) (a c : A) :
    HasSum (fun b => inner ℂ (lp.single 2 (a,b) 1)
      (TraceEnsemble.operator v (lp.single 2 (c,b) 1)))
      (inner ℂ (lp.single 2 a 1) (partialTrace v (lp.single 2 c 1))) := by
  have hs := TraceEnsemble.hasSum_entry (hasSum_slice_family hv.hasSum).summable
    (lp.single 2 a 1) (lp.single 2 c 1)
  have hrow (b : B) : HasSum
      (fun i => inner ℂ (lp.single 2 a 1) (slice (v i) b) *
        inner ℂ (slice (v i) b) (lp.single 2 c 1))
      (inner ℂ (lp.single 2 (a,b) 1) (TraceEnsemble.operator v (lp.single 2 (c,b) 1))) := by
    convert! TraceEnsemble.hasSum_entry hv (lp.single 2 (a,b) 1) (lp.single 2 (c,b) 1) using 1
    ext i
    simp [lp.inner_single_left, lp.inner_single_right, slice_apply]
  exact hs.prod_fiberwise hrow

end TensorLp

namespace TraceEnsemble
open TensorLp
variable {A B I J : Type*}

theorem hasSum_tensor_norm {v : I → H A} {w : J → H B} {a b : ℝ}
    (hv : HasSum (fun i => ‖v i‖^2) a) (hw : HasSum (fun j => ‖w j‖^2) b) :
    HasSum (fun ij : I × J => ‖tensor (v ij.1) (w ij.2)‖^2) (a*b) := by
  simpa only [tensor_norm_sq] using hv.mul hw
    (hv.summable.mul_of_nonneg hw.summable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _))

theorem tensor_entry [DecidableEq A] [DecidableEq B]
    {v : I → H A} {w : J → H B}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (a c : A) (b d : B) :
    inner ℂ (lp.single 2 (a,b) 1)
      (operator (fun ij : I × J => tensor (v ij.1) (w ij.2)) (lp.single 2 (c,d) 1)) =
      inner ℂ (lp.single 2 a 1) (operator v (lp.single 2 c 1)) *
      inner ℂ (lp.single 2 b 1) (operator w (lp.single 2 d 1)) := by
  apply (hasSum_entry (hasSum_tensor_norm hv.hasSum hw.hasSum).summable _ _).unique
  convert! (hasSum_entry hv (lp.single 2 a 1) (lp.single 2 c 1)).mul
    (hasSum_entry hw (lp.single 2 b 1) (lp.single 2 d 1))
    (summable_mul_of_summable_norm
      (f := fun i => inner ℂ (lp.single 2 a 1) (v i)*inner ℂ (v i) (lp.single 2 c 1))
      (g := fun j => inner ℂ (lp.single 2 b 1) (w j)*inner ℂ (w j) (lp.single 2 d 1))
      (summable_entry_norm hv (lp.single 2 a 1) (lp.single 2 c 1))
      (summable_entry_norm hw (lp.single 2 b 1) (lp.single 2 d 1))) using 1
  ext ij
  simp only [lp.inner_single_left, lp.inner_single_right, tensor_apply, RCLike.inner_apply, map_mul, map_one]
  ring

theorem unitary_entry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {v : I → E} (hv : Summable (fun i => ‖v i‖^2))
    (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    inner ℂ x (operator (fun i => U (v i)) y) =
      inner ℂ (U.symm x) (operator v (U.symm y)) := by
  have hu : Summable (fun i => ‖U (v i)‖^2) := by simpa only [U.norm_map] using hv
  apply (hasSum_entry hu x y).unique
  convert! hasSum_entry hv (U.symm x) (U.symm y) using 1
  ext i
  have h₁ : inner ℂ x (U (v i)) = inner ℂ (U.symm x) (v i) := by
    simpa only [U.apply_symm_apply] using U.inner_map_map (U.symm x) (v i)
  have h₂ : inner ℂ (U (v i)) y = inner ℂ (v i) (U.symm y) := by
    simpa only [U.apply_symm_apply] using U.inner_map_map (v i) (U.symm y)
  rw [h₁,h₂]

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
theorem beam_ensemble_entry {n : ℕ} {I J : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v = ρ.op) (hew : TraceEnsemble.operator w = σ.op)
    (k l e : NumberIndex n) :
    inner ℂ (lp.single 2 (k,e) 1)
      (TraceEnsemble.operator (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))
        (lp.single 2 (l,e) 1)) = outputBlock η ρ σ k l e := by
  rw [TraceEnsemble.unitary_entry (TraceEnsemble.hasSum_tensor_norm hv hw).summable]
  rw [beam_symm_number, beam_symm_number]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold outputBlock
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [TraceEnsemble.tensor_entry hv.summable hw.summable, hev, hew]
  simp only [entry, numberKet]
  ring

end EntropyPhotonNumber

end

end OAI
