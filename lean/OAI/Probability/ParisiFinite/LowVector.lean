import Mathlib
import OAI.Probability.ParisiFinite.OrdinaryInverseSpecial

namespace OAI

/-! Low Vector. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def lowVector (d : E) : SpinSpace E :=
  SpinOperators.act Y (WZ ((2:ℝ) • d) (vacuum E))

@[simp] theorem norm_lowVector (d : E) : ‖lowVector d‖=1 := by
  rw [lowVector,SpinOperators.norm_act Y_unitary,norm_WZ,norm_vacuum]

theorem ordinary_insertion_eq (γ : ℝ) (v e : E) :
    (ordinaryMap γ (Real.pi/4) v e).symm
      (SpinOperators.act Z (ordinaryMap γ (Real.pi/4) v e (vacuum E)))=
      lowVector (γ • (v-e)) := by
  simp only [ordinaryMap,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_trans,
    costEquiv_apply,costEquiv_symm_apply,SpinOperators.actEquiv_apply,
    SpinOperators.actEquiv_symm_apply]
  rw [one_layer_insertion,show 2*(Real.pi/4)=Real.pi/2 by ring]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Complex.ofReal_zero,Complex.ofReal_one,
    zero_smul,one_smul,zero_add,lowVector,two_smul]

theorem inner_lowVector_initial (d : E) :
    ⟪lowVector d,SpinOperators.act Z (vacuum E)⟫_ℂ=
      I*(Real.exp (-2*‖d‖^2):ℂ) := by
  rw [← inner_conj_symm,lowVector,inner_rootZ_vac_rootY_WZ]
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  congr 2
  have hn : ‖(2:ℝ) • d‖^2=4*‖d‖^2 := by
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    ring
  rw [hn]
  ring_nf

theorem tendsto_norm_ordinaryDisplacement (n : ℕ) (b : ℝ) :
    Tendsto (fun t => ‖ordinaryDisplacement n b t‖) atTop (𝓝 (2*|b|)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
    (tendsto_ordinaryDisplacement_error n b)
  have h := abs_norm_sub_norm_le (ordinaryDisplacement n b t)
    ((2*b:ℝ) • highDirection n (gamma b t))
  have hn : ‖(2*b:ℝ) • highDirection n (gamma b t)‖=2*|b| := by
    rw [← Complex.coe_smul,norm_smul,highDirection_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_mul]
    norm_num
  simpa only [hn,Real.norm_eq_abs] using h

 
def initializedInsertion (n : ℕ) (b t : ℝ) : Mode (n+2) :=
  (ordinary (initializationWord (gamma b t) (delta t) (Real.pi/4)) (n+2)).insertion

@[simp] theorem initializedInsertion_coe (n : ℕ) (b t : ℝ) :
    (initializedInsertion n b t : Level (n+2))=
      (ordinary (initializationWord (gamma b t) (delta t) (Real.pi/4)) (n+2)).op.symm
        (SpinOperators.act Z
          ((ordinary (initializationWord (gamma b t) (delta t) (Real.pi/4)) (n+2)).op
            (vac (n+2)))) := rfl

@[simp] theorem norm_initializedInsertion (n : ℕ) (b t : ℝ) :
    ‖initializedInsertion n b t‖=1 := EvenUnitary.norm_insertion _

theorem initializedInsertion_error (n : ℕ) (b : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ‖(initializedInsertion n b t:Level (n+2))-lowVector (ordinaryDisplacement n b t)‖≤
      2*(amplitude t^2+amplitude t) := by
  have h := initial_insertion_error (E := Mode (n+1)) (gamma b t) (Real.pi/4) ht
    (actualV n b t) (initialDirection (n+1)) (SpinOperators.act Z)
    (fun x => (SpinOperators.norm_act Z_unitary x).le)
  rw [ordinary_insertion_eq,initialMap_eq_ordinary] at h
  rw [initializedInsertion_coe]
  exact h

theorem tendsto_initializedInsertion_error (n : ℕ) (b : ℝ) :
    Tendsto (fun t => ‖(initializedInsertion n b t:Level (n+2))-
      lowVector (ordinaryDisplacement n b t)‖) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_
    (by simpa only [zero_pow (by norm_num : (2:ℕ)≠0),add_zero,mul_zero] using
      ((tendsto_amplitude.pow 2).add tendsto_amplitude).const_mul 2)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  exact initializedInsertion_error n b ht

theorem tendsto_lowVector_initial (n : ℕ) (b : ℝ) :
    Tendsto (fun t => ⟪lowVector (ordinaryDisplacement n b t),
      (initialDirection (n+2):Level (n+2))⟫_ℂ) atTop
        (𝓝 (I*(Real.exp (-8*b^2):ℂ))) := by
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    (((tendsto_norm_ordinaryDisplacement n b).pow 2).const_mul (-2))
  have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp he).const_mul I
  have hpow : -2*(2*|b|)^2= -8*b^2 := by rw [mul_pow,sq_abs]; ring
  rw [hpow] at hh
  have hinit : (initialDirection (n+2):Level (n+2))=
      SpinOperators.act Z (vacuum (Mode (n+1))) := rfl
  simpa only [hinit,inner_lowVector_initial,Function.comp_def] using hh

 

theorem tendsto_initialized_initial (n : ℕ) (b : ℝ) :
    Tendsto (fun t => ⟪(initializedInsertion n b t:Level (n+2)),
      (initialDirection (n+2):Level (n+2))⟫_ℂ) atTop
        (𝓝 (I*(Real.exp (-8*b^2):ℂ))) := by
  have he : Tendsto (fun t =>
      ⟪(initializedInsertion n b t:Level (n+2)),(initialDirection (n+2):Level (n+2))⟫_ℂ-
      ⟪lowVector (ordinaryDisplacement n b t),(initialDirection (n+2):Level (n+2))⟫_ℂ)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
      (tendsto_initializedInsertion_error n b)
    rw [← inner_sub_left]
    have h := norm_inner_le_norm (𝕜 := ℂ)
      ((initializedInsertion n b t:Level (n+2))-lowVector (ordinaryDisplacement n b t))
      (initialDirection (n+2):Level (n+2))
    have hn : ‖(initialDirection (n+2):Level (n+2))‖=1 := initialDirection_norm (n+2)
    simpa only [hn,mul_one] using h
  simpa only [sub_add_cancel,zero_add] using he.add (tendsto_lowVector_initial n b)

theorem tendsto_initial_visibility (n : ℕ) (b z : ℝ) :
    Tendsto (fun t => -2*(⟪(initializedInsertion n b t:Level (n+2)),
      (-2*b*z:ℝ) • (initialDirection (n+2):Level (n+2))⟫_ℂ).im) atTop
      (𝓝 (4*b*z*Real.exp (-8*b^2))) := by
  have hc := (tendsto_initialized_initial n b).const_mul ((-2*b*z:ℝ):ℂ)
  have hi := Complex.continuous_im.continuousAt.tendsto.comp hc
  have h := hi.const_mul (-2)
  simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,zero_add,
    Complex.I_re,Complex.I_im,one_mul,mul_zero,add_zero,Function.comp_def] at h
  convert! h using 1
  · funext t
    rw [← Complex.coe_smul,inner_smul_right]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  · congr 1
    ring

theorem initial_visibility_nonzero (n : ℕ) {b : ℝ} (hb : 0 < b) {z : ℝ} (hz : z≠0) :
    ∀ᶠ t : ℝ in atTop, -2*(⟪(initializedInsertion n b t:Level (n+2)),
      (-2*b*z:ℝ) • (initialDirection (n+2):Level (n+2))⟫_ℂ).im≠0 := by
  apply (tendsto_initial_visibility n b z).eventually_ne
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb.ne') hz) (Real.exp_ne_zero _)

end SeedInitialization

namespace SeedInitialization
open CoherentFock RootSpin PointedTree Complex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def preVacuum (E : Type*) [Zero E] : PreSpin E := fun _ => spinCoefficient • basis 0

@[simp] theorem spinCoe_preVacuum : spinCoe (preVacuum E)=vacuum E := by
  ext i
  simp only [spinCoe_apply,preVacuum,UniformSpace.Completion.coe_smul,coe_basis,
    vacuum_apply,spinCoefficient]

omit [InnerProductSpace ℂ E] in
@[simp] theorem spinMass_preVacuum : spinMass (preVacuum E)=2*‖spinCoefficient‖ := by
  simp only [spinMass,preVacuum,mass_smul,mass_basis,mul_one,Fin.sum_univ_two]
  ring

omit [InnerProductSpace ℂ E] in
theorem radius_preVacuum : SpinRadiusLE (preVacuum E) 0 :=
  fun _ => (RadiusLE.basis (0:E) 0 (by simp)).smul _

def preLow (d : E) : PreSpin E := preRoot Y (preWZ ((2:ℝ) • d) (preVacuum E))

@[simp] theorem spinCoe_preLow (d : E) : spinCoe (preLow d)=lowVector d := by
  simp only [preLow,spinCoe_preRoot,spinCoe_preWZ,spinCoe_preVacuum,lowVector]

theorem mass_preLow (d : E) : spinMass (preLow d) ≤ matrixMass Y*(2*‖spinCoefficient‖) := by
  have hM : 0 ≤ matrixMass Y := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => norm_nonneg (Y i j)
  exact (spinMass_preRoot _ _).trans (mul_le_mul_of_nonneg_left
    ((spinMass_preWZ _ _).trans_eq spinMass_preVacuum) hM)

theorem radius_preLow (d : E) : SpinRadiusLE (preLow d) (2*‖d‖) := by
  have h := ((radius_preVacuum (E := E)).preWZ ((2:ℝ) • d)).preRoot Y
  simpa only [preLow,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),add_zero] using h

theorem bounded_preLow (n : ℕ) (b : ℝ) :
    ∀ᶠ t : ℝ in atTop,
      SpinRadiusLE (preLow (ordinaryDisplacement n b t)) (2*(2*|b|+1)) ∧
      spinMass (preLow (ordinaryDisplacement n b t)) ≤ matrixMass Y*(2*‖spinCoefficient‖) := by
  filter_upwards [ordinaryDisplacement_bounded n b] with t ht
  refine ⟨fun i => (radius_preLow _ i).mono ?_,mass_preLow _⟩
  exact mul_le_mul_of_nonneg_left ht (by norm_num)

theorem tendsto_inner_low_high (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪lowVector (ordinaryDisplacement n b t),
      (highDirection (n+1) (gamma b t):Level (n+2))⟫_ℂ) atTop (𝓝 0) := by
  simpa only [spinCoe_preLow] using tendsto_inner_high_uniform (n+1) b hb
    (fun t => preLow (ordinaryDisplacement n b t)) (2*(2*|b|+1))
    (matrixMass Y*(2*‖spinCoefficient‖)) (by positivity) (bounded_preLow n b)

theorem tendsto_inner_low_address (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪lowVector (ordinaryDisplacement n b t),actualAddress n b t⟫_ℂ)
      atTop (𝓝 0) := by
  simpa only [spinCoe_preLow] using tendsto_inner_address_uniform n b hb
    (fun t => preLow (ordinaryDisplacement n b t)) (2*(2*|b|+1))
    (matrixMass Y*(2*‖spinCoefficient‖)) (by positivity) (bounded_preLow n b)

variable {α : Type*} {l : Filter α}

theorem tendsto_inner_error_unit (x y z : α → E)
    (hxy : Tendsto (fun a => ‖x a-y a‖) l (𝓝 0)) (hz : ∀ a, ‖z a‖=1) :
    Tendsto (fun a => ⟪x a,z a⟫_ℂ-⟪y a,z a⟫_ℂ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) hxy
  rw [← inner_sub_left]
  simpa only [hz a,mul_one] using norm_inner_le_norm (𝕜 := ℂ) (x a-y a) (z a)

 
theorem tendsto_initialized_high (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪(initializedInsertion n b t:Level (n+2)),
      (highDirection (n+1) (gamma b t):Level (n+2))⟫_ℂ) atTop (𝓝 0) := by
  have he := tendsto_inner_error_unit
    (fun t => (initializedInsertion n b t:Level (n+2)))
    (fun t => lowVector (ordinaryDisplacement n b t))
    (fun t => (highDirection (n+1) (gamma b t):Level (n+2)))
    (tendsto_initializedInsertion_error n b) (fun _ => highDirection_norm (n+1) _)
  simpa only [sub_add_cancel,zero_add] using he.add (tendsto_inner_low_high n b hb)

theorem tendsto_initialized_address (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪(initializedInsertion n b t:Level (n+2)),actualAddress n b t⟫_ℂ)
      atTop (𝓝 0) := by
  have he := tendsto_inner_error_unit
    (fun t => (initializedInsertion n b t:Level (n+2)))
    (fun t => lowVector (ordinaryDisplacement n b t)) (actualAddress n b)
    (tendsto_initializedInsertion_error n b) (norm_actualAddress n b)
  simpa only [sub_add_cancel,zero_add] using he.add (tendsto_inner_low_address n b hb)

end SeedInitialization

namespace SeedInitialization
open CoherentFock RootSpin PointedTree Complex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_lowVector_creation (d v : E) :
    ⟪lowVector d,plusEmbedding (creationVacuum v)⟫_ℂ=
      (-2*Real.exp (-2*‖d‖^2):ℂ)*⟪d,v⟫_ℂ := by
  rw [lowVector,inner_rootY_WZ_creation]
  have hi : ⟪(2:ℝ) • d,v⟫_ℂ=(2:ℂ)*⟪d,v⟫_ℂ := by
    rw [← Complex.coe_smul,inner_smul_left,Complex.ofReal_ofNat,Complex.conj_ofNat]
  have hn : ‖(2:ℝ) • d‖^2=4*‖d‖^2 := by
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    ring
  rw [hi,hn,show -(4*‖d‖^2)/2= -2*‖d‖^2 by ring]
  ring

theorem tendsto_displacement_initialized (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪ordinaryDisplacement (n+1) b t,initializedInsertion n b t⟫_ℂ)
      atTop (𝓝 0) := by
  have he := tendsto_inner_error_unit
    (fun t => ordinaryDisplacement (n+1) b t)
    (fun t => (2*b:ℝ) • highDirection (n+1) (gamma b t))
    (initializedInsertion n b) (tendsto_ordinaryDisplacement_error (n+1) b)
    (norm_initializedInsertion n b)
  have hh := Complex.continuous_conj.continuousAt.tendsto.comp (tendsto_initialized_high n b hb)
  have hh' : Tendsto (fun t => ⟪(2*b:ℝ) • highDirection (n+1) (gamma b t),
      initializedInsertion n b t⟫_ℂ) atTop (𝓝 0) := by
    have h := hh.const_mul ((2*b:ℝ):ℂ)
    simpa only [Function.comp_def,inner_conj_symm,map_zero,mul_zero,
      ← Complex.coe_smul,inner_smul_left,Complex.conj_ofReal,Submodule.coe_inner] using h
  simpa only [sub_add_cancel,zero_add] using he.add hh'

theorem tendsto_low_rootShift (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪lowVector (ordinaryDisplacement (n+1) b t),
      (rootShift (n+2) (initializedInsertion n b t):Level (n+3))⟫_ℂ)
      atTop (𝓝 0) := by
  have hr := Real.continuous_exp.continuousAt.tendsto.comp
    (((tendsto_norm_ordinaryDisplacement (n+1) b).pow 2).const_mul (-2))
  have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).const_mul (-2)
  have he (t : ℝ) :
      ⟪lowVector (ordinaryDisplacement (n+1) b t),
        (rootShift (n+2) (initializedInsertion n b t):Level (n+3))⟫_ℂ=
      (-2*Real.exp (-2*‖ordinaryDisplacement (n+1) b t‖^2):ℂ)*
        ⟪ordinaryDisplacement (n+1) b t,initializedInsertion n b t⟫_ℂ :=
    inner_lowVector_creation (ordinaryDisplacement (n+1) b t) (initializedInsertion n b t)
  simp_rw [he]
  simpa only [mul_zero,Function.comp_def] using
    hc.mul (tendsto_displacement_initialized n b hb)

theorem tendsto_initialized_rootShift (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪(initializedInsertion (n+1) b t:Level (n+3)),
      (rootShift (n+2) (initializedInsertion n b t):Level (n+3))⟫_ℂ)
      atTop (𝓝 0) := by
  have he := tendsto_inner_error_unit
    (fun t => (initializedInsertion (n+1) b t:Level (n+3)))
    (fun t => lowVector (ordinaryDisplacement (n+1) b t))
    (fun t => (rootShift (n+2) (initializedInsertion n b t):Level (n+3)))
    (tendsto_initializedInsertion_error (n+1) b)
    (fun t => (rootShift (n+2)).norm_map (initializedInsertion n b t) |>.trans
      (norm_initializedInsertion n b t))
  simpa only [sub_add_cancel,zero_add] using he.add (tendsto_low_rootShift n b hb)

theorem tendsto_initialized_treeEnergy (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => treeEnergy (n+2) (initializedInsertion n b t)) atTop (𝓝 0) := by
  have hempty (t : ℝ) : centeredMap (empty (n+2)) (initializedInsertion n b t)=
      initializedInsertion (n+1) b t :=
    ordinary_insertion_empty _ (n+2) (by simp [initializationWord]; omega)
  have hi := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_initialized_rootShift n b hb)
  simpa only [treeEnergy,hempty,Submodule.coe_inner,Function.comp_def,Complex.zero_re] using hi

 

theorem tendsto_initialization_ordinaryValue (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ordinaryValue (initializationWord (gamma b t) (delta t) (Real.pi/4)))
      atTop (𝓝 0) := by
  have he (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
      treeEnergy (n+2) (initializedInsertion n b t)=
      ordinaryValue (initializationWord (gamma b t) (delta t) (Real.pi/4)) :=
    ordinary_energy_stable _ (n+2) (by simp [initializationWord]; omega)
  simpa only [he 2 (by omega)] using tendsto_initialized_treeEnergy 2 (by omega) b hb

end SeedInitialization

namespace ForwardControl
open Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem scaled_residual_bound (r t ε η : ℝ) (hr : 0 < r) (v v' s w : H)
    (hv : ‖v'-v+(2:ℂ) • s‖ ≤ r*ε)
    (hs : ‖r⁻¹ • s-w‖ ≤ η) :
    ‖(t/r) • (v'-v)-(-2*t) • w‖ ≤ |t| *(ε+2*η) := by
  have he : (t/r) • (v'-v)-(-2*t) • w =
      t • (r⁻¹ • (v'-v+(2:ℂ) • s)-(2:ℝ) • (r⁻¹ • s-w)) := by
    simp only [two_smul,smul_add,smul_sub,smul_smul,div_eq_mul_inv]
    module
  rw [he,norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
  have h1 : ‖r⁻¹ • (v'-v+(2:ℂ) • s)‖ ≤ ε := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ r⁻¹*(r*ε) := mul_le_mul_of_nonneg_left hv (le_of_lt (inv_pos.mpr hr))
      _ = ε := by field_simp
  have h2 : ‖(2:ℝ) • (r⁻¹ • s-w)‖ ≤ 2*η := by
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    gcongr
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

 

theorem actual_scaled_flip_bound (U V : H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x, ‖Z x‖ ≤ ‖x‖) (hanti : ∀x, Z (F x)=-F (Z x))
    (Ω o s w : H) (hx : U Ω=o+s) (r t ε η : ℝ) (hr : 0 < r)
    (h1 : ‖V o-o‖ ≤ r*ε) (h2 : ‖V s-F s‖ ≤ r*ε)
    (h3 : ‖V (Z o)-Z o‖ ≤ r*ε) (h4 : ‖V (Z s)-F (Z s)‖ ≤ r*ε)
    (ht : ‖r⁻¹ • U.symm (Z s)-w‖ ≤ η) :
    ‖(t/r) • (U.symm (V.symm (Z (V (U Ω))))-U.symm (Z (U Ω)))-
      (-2*t) • w‖ ≤ |t| *(4*ε+2*η) := by
  apply scaled_residual_bound r t (4*ε) η hr _ _ _ _ _ ht
  have hf := actual_flip_change U V Z F hZ hanti Ω o s hx
  linarith

end ForwardControl

namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem WZ_difference_le (d e : E) (x : SpinSpace E) :
    ‖WZ d x-WZ e x‖ ≤ ‖WZ (d-e) x-x‖+‖d-e‖*‖e‖*‖x‖ := by
  have he : phase e (d-e) • (WZ d x-WZ e x)=
      WZ e (WZ (d-e) x-x)+(1-phase e (d-e)) • WZ e x := by
    have h := congrArg (fun T : SpinSpace E →L[ℂ] SpinSpace E => T x) (WZ_mul e (d-e))
    simp only [ContinuousLinearMap.comp_apply,smul_apply,show e+(d-e)=d by abel] at h
    rw [map_sub,h]
    module
  calc
    _ = ‖phase e (d-e) • (WZ d x-WZ e x)‖ := by rw [norm_smul,norm_phase,one_mul]
    _ ≤ ‖WZ e (WZ (d-e) x-x)‖+‖(1-phase e (d-e)) • WZ e x‖ := by
      rw [he]; exact norm_add_le _ _
    _ = ‖WZ (d-e) x-x‖+‖phase e (d-e)-1‖*‖x‖ := by
      rw [norm_smul,norm_WZ,norm_WZ,norm_sub_rev (1:ℂ)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (phase_sub_one_le e (d-e)) (norm_nonneg x)]

omit [InnerProductSpace ℂ E] in
theorem tailBound_le_second (x : PreSpace E) : tailBound x ≤ secondTailBound x := by
  classical
  simp only [tailBound,secondTailBound,Finsupp.sum]
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  nlinarith [sq_nonneg ‖d‖]

theorem WZ_spinCoe_sub_le (h : E) (x : PreSpin E) :
    ‖WZ h (spinCoe x)-spinCoe x‖ ≤ ‖h‖*spinBound x := by
  calc
    _ ≤ ∑ i, ‖(WZ h (spinCoe x)-spinCoe x) i‖ := norm_spin_le_sum _
    _ ≤ ∑ i, ‖h‖*secondTailBound (x i) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [PiLp.sub_apply,WZ_apply,spinCoe_apply]
      have hb (h : E) := (W_coe_sub_le h (x i)).trans
        (mul_le_mul_of_nonneg_left (tailBound_le_second (x i)) (norm_nonneg h))
      split_ifs
      · exact hb h
      · simpa only [norm_neg] using hb (-h)
    _ = _ := by simp only [spinBound,Finset.mul_sum]

 

theorem WZ_spinCoe_difference (d e : E) (x : PreSpin E) {A B C : ℝ}
    (hx : SpinRadiusLE x B) (hB : 0 ≤ B) (hA : spinMass x ≤ A) (he : ‖e‖ ≤ C) :
    ‖WZ d (spinCoe x)-WZ e (spinCoe x)‖ ≤ ‖d-e‖*(A*(1+2*B+12*B^2)+C*A) := by
  have hM : ‖spinCoe x‖ ≤ A := (norm_spinCoe_le_mass x).trans hA
  have hN : 0 ≤ A := (spinMass_nonneg x).trans hA
  have hC : 0 ≤ C := (norm_nonneg e).trans he
  calc
    _ ≤ ‖WZ (d-e) (spinCoe x)-spinCoe x‖+‖d-e‖*‖e‖*‖spinCoe x‖ := WZ_difference_le _ _ _
    _ ≤ ‖d-e‖*spinBound x+‖d-e‖*C*A := by
      gcongr
      exact WZ_spinCoe_sub_le _ _
    _ ≤ ‖d-e‖*(A*(1+2*B+12*B^2))+‖d-e‖*C*A := by
      gcongr
      exact (spinBound_le_mass x hB hx).trans (by gcongr)
    _ = _ := by ring

end CoherentFock

namespace ForwardControl
open Complex
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

theorem actual_scaled_flip_tendsto (U V : α → H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x, ‖Z x‖ ≤ ‖x‖) (hanti : ∀x, Z (F x)=-F (Z x))
    (Ω : H) (o s w : α → H) (hx : ∀ a, U a Ω=o a+s a) (r ε η : α → ℝ) (t : ℝ)
    (hr : ∀ᶠ a in l, 0 < r a)
    (he : Tendsto ε l (𝓝 0)) (hh : Tendsto η l (𝓝 0))
    (h1 : ∀ᶠ a in l, ‖V a (o a)-o a‖ ≤ r a*ε a)
    (h2 : ∀ᶠ a in l, ‖V a (s a)-F (s a)‖ ≤ r a*ε a)
    (h3 : ∀ᶠ a in l, ‖V a (Z (o a))-Z (o a)‖ ≤ r a*ε a)
    (h4 : ∀ᶠ a in l, ‖V a (Z (s a))-F (Z (s a))‖ ≤ r a*ε a)
    (ht : ∀ᶠ a in l, ‖(r a)⁻¹ • (U a).symm (Z (s a))-w a‖ ≤ η a) :
    Tendsto (fun a => ‖(t/r a) • ((U a).symm ((V a).symm (Z (V a (U a Ω))))-
      (U a).symm (Z (U a Ω)))-(-2*t) • w a‖) l (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [mul_zero,add_zero] using ((he.const_mul 4).add (hh.const_mul 2)).const_mul |t|)
  filter_upwards [hr,h1,h2,h3,h4,ht] with a ha h1 h2 h3 h4 ht
  exact actual_scaled_flip_bound (U a) (V a) Z F hZ hanti Ω (o a) (s a) (w a)
    (hx a) (r a) t (ε a) (η a) ha h1 h2 h3 h4 ht

end ForwardControl

namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem echo_ordinary_error (t r : ℝ) (v v' : E) (V₁ V₂ : SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E)
    (x : SpinSpace E) :
    ‖(phase ((t/r) • v') (-(t/r) • v))⁻¹ •
      V₂ (WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x)))-WZ ((t/r) • (v'-v)) x‖ ≤
      ‖V₁ (WZ (-(t/r) • v) x)-WZ (-(t/r) • v) x‖+
      ‖V₂ (WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x)))-
        WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x))‖ := by
  rw [← corrected_echo t r v v' x,← smul_sub,norm_smul,norm_inv,norm_phase,inv_one,one_mul]
  have he : V₂ (WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x)))-
      WZ ((t/r) • v') (WZ (-(t/r) • v) x) =
      (V₂ (WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x)))-
        WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x)))+
      (WZ ((t/r) • v') (V₁ (WZ (-(t/r) • v) x))-
        WZ ((t/r) • v') (WZ (-(t/r) • v) x)) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by rw [WZ_error]; exact le_of_eq (add_comm _ _))

 

theorem tendsto_moving_corrected_echo {α : Type*} {l : Filter α}
    (t : ℝ) (r : α → ℝ) (v v' w : α → E) (x : α → PreSpin E) (A B : ℝ)
    (hB : 0 ≤ B) (hx : ∀ᶠ a in l, SpinRadiusLE (x a) B ∧ spinMass (x a)≤A)
    (hw : ∀ a, ‖w a‖=1)
    (hg : Tendsto (fun a => ‖(t/r a) • (v' a-v a)-(-2*t) • w a‖) l (𝓝 0)) :
    Tendsto (fun a => ‖(phase ((t/r a) • v' a) (-(t/r a) • v a))⁻¹ •
      WZ ((t/r a) • v' a) (WZ (-(t/r a) • v a) (spinCoe (x a)))-
      WZ ((-2*t) • w a) (spinCoe (x a))‖) l (𝓝 0) := by
  simp_rw [corrected_echo]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [zero_mul] using hg.mul_const (A*(1+2*B+12*B^2)+|(-2*t)| *A))
  filter_upwards [hx] with a ha
  exact WZ_spinCoe_difference _ _ _ ha.1 hB ha.2
    (by rw [norm_smul,hw,mul_one,Real.norm_eq_abs])

end CoherentFock

namespace CoherentFock
open PointedTree Complex
variable {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ α : Type*} [Fintype ι] [Fintype κ] {l : Filter α}

 

def spinPacket (a : ι → Fin 2 → ℂ) (d : ι → E) : SpinSpace E :=
  ∑ i, spinPair (a i 0 • coherent (d i)) (a i 1 • coherent (d i))

theorem inner_spinPacket (a : ι → Fin 2 → ℂ) (b : κ → Fin 2 → ℂ)
    (d : ι → E) (e : κ → E) :
    ⟪spinPacket a d,spinPacket b e⟫_ℂ=
      ∑ i, ∑ j, (conj (a i 0)*b j 0+conj (a i 1)*b j 1)*kernel (d i) (e j) := by
  simp only [spinPacket,sum_inner,inner_sum,inner_spinPair,inner_smul_left,inner_smul_right,
    inner_coherent]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

 

theorem inner_spinPacket_creation (a : ι → Fin 2 → ℂ) (d : ι → E) (h : E) :
    ⟪spinPacket a d,plusEmbedding (creationVacuum h)⟫_ℂ=
      ∑ i, (-I)*(conj (a i 0)+conj (a i 1))*spinCoefficient*
        (Real.exp (-‖d i‖^2/2):ℂ)*⟪d i,h⟫_ℂ := by
  simp only [spinPacket,sum_inner,plusEmbedding_pair,inner_spinPair,creationVacuum,
    inner_smul_left,inner_smul_right,inner_coherent_oneParticle]
  apply Finset.sum_congr rfl
  intro i hi
  ring

 
theorem tendsto_norm_sq_of_inner (d : α → E) (d₀ : F)
    (h : Tendsto (fun t => ⟪d t,d t⟫_ℂ) l (𝓝 ⟪d₀,d₀⟫_ℂ)) :
    Tendsto (fun t => ‖d t‖^2) l (𝓝 (‖d₀‖^2)) := by
  have hn (x : E) : (⟪x,x⟫_ℂ).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have hn₀ : (⟪d₀,d₀⟫_ℂ).re=‖d₀‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) d₀
  simpa only [Function.comp_def,hn,hn₀] using
    Complex.continuous_re.continuousAt.tendsto.comp h

theorem tendsto_kernel_of_gram (d e : α → E) (d₀ e₀ : F)
    (hd : Tendsto (fun t => ⟪d t,d t⟫_ℂ) l (𝓝 ⟪d₀,d₀⟫_ℂ))
    (he : Tendsto (fun t => ⟪e t,e t⟫_ℂ) l (𝓝 ⟪e₀,e₀⟫_ℂ))
    (hde : Tendsto (fun t => ⟪d t,e t⟫_ℂ) l (𝓝 ⟪d₀,e₀⟫_ℂ)) :
    Tendsto (fun t => kernel (d t) (e t)) l (𝓝 (kernel d₀ e₀)) := by
  have hd' := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_norm_sq_of_inner d d₀ hd).neg.div_const 2)
  have he' := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_norm_sq_of_inner e e₀ he).neg.div_const 2)
  exact Complex.continuous_exp.continuousAt.tendsto.comp ((hd'.add hde).add he')

 

theorem tendsto_inner_spinPacket (a : α → ι → Fin 2 → ℂ) (b : α → κ → Fin 2 → ℂ)
    (d : α → ι → E) (e : α → κ → E) (a₀ : ι → Fin 2 → ℂ) (b₀ : κ → Fin 2 → ℂ)
    (d₀ : ι → F) (e₀ : κ → F)
    (ha : ∀ i q, Tendsto (fun t => a t i q) l (𝓝 (a₀ i q)))
    (hb : ∀ j q, Tendsto (fun t => b t j q) l (𝓝 (b₀ j q)))
    (hd : ∀ i, Tendsto (fun t => ⟪d t i,d t i⟫_ℂ) l (𝓝 ⟪d₀ i,d₀ i⟫_ℂ))
    (he : ∀ j, Tendsto (fun t => ⟪e t j,e t j⟫_ℂ) l (𝓝 ⟪e₀ j,e₀ j⟫_ℂ))
    (hde : ∀ i j, Tendsto (fun t => ⟪d t i,e t j⟫_ℂ) l (𝓝 ⟪d₀ i,e₀ j⟫_ℂ)) :
    Tendsto (fun t => ⟪spinPacket (a t) (d t),spinPacket (b t) (e t)⟫_ℂ)
      l (𝓝 ⟪spinPacket a₀ d₀,spinPacket b₀ e₀⟫_ℂ) := by
  simp_rw [inner_spinPacket]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  have hc0 := ((Complex.continuous_conj.continuousAt.tendsto.comp (ha i 0)).mul (hb j 0))
  have hc1 := ((Complex.continuous_conj.continuousAt.tendsto.comp (ha i 1)).mul (hb j 1))
  exact (hc0.add hc1).mul (tendsto_kernel_of_gram _ _ _ _ (hd i) (he j) (hde i j))

 

theorem tendsto_inner_spinPacket_creation (a : α → ι → Fin 2 → ℂ) (d : α → ι → E)
    (h : α → E) (a₀ : ι → Fin 2 → ℂ) (d₀ : ι → F) (h₀ : F)
    (ha : ∀ i q, Tendsto (fun t => a t i q) l (𝓝 (a₀ i q)))
    (hd : ∀ i, Tendsto (fun t => ⟪d t i,d t i⟫_ℂ) l (𝓝 ⟪d₀ i,d₀ i⟫_ℂ))
    (hdh : ∀ i, Tendsto (fun t => ⟪d t i,h t⟫_ℂ) l (𝓝 ⟪d₀ i,h₀⟫_ℂ)) :
    Tendsto (fun t => ⟪spinPacket (a t) (d t),plusEmbedding (creationVacuum (h t))⟫_ℂ)
      l (𝓝 ⟪spinPacket a₀ d₀,plusEmbedding (creationVacuum h₀)⟫_ℂ) := by
  simp_rw [inner_spinPacket_creation]
  apply tendsto_finsetSum
  intro i hi
  have hc := ((Complex.continuous_conj.continuousAt.tendsto.comp (ha i 0)).add
    (Complex.continuous_conj.continuousAt.tendsto.comp (ha i 1))).const_mul (-I)
  have hnorm := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_norm_sq_of_inner _ _ (hd i)).neg.div_const 2)
  exact (((hc.mul_const spinCoefficient).mul
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hnorm)).mul (hdh i))

end CoherentFock

namespace CoherentFock
variable {E X : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

 

theorem analyticAt_norm_sq_of_inner (d : X → E)
    (h : AnalyticAt ℝ (fun t => ⟪d t,d t⟫_ℂ) x) :
    AnalyticAt ℝ (fun t => ‖d t‖^2) x := by
  have hr : AnalyticAt ℝ (fun t => (⟪d t,d t⟫_ℂ).re) x :=
    (Complex.reCLM.analyticAt _).comp h
  convert hr using 1
  ext t
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (d t)).symm

theorem analyticAt_kernel_of_gram (d e : X → E)
    (hd : AnalyticAt ℝ (fun t => ⟪d t,d t⟫_ℂ) x)
    (he : AnalyticAt ℝ (fun t => ⟪e t,e t⟫_ℂ) x)
    (hde : AnalyticAt ℝ (fun t => ⟪d t,e t⟫_ℂ) x) :
    AnalyticAt ℝ (fun t => kernel (d t) (e t)) x := by
  have hd' : AnalyticAt ℝ (fun t => ((-‖d t‖^2/2:ℝ):ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_norm_sq_of_inner d hd).neg.div_const
  have he' : AnalyticAt ℝ (fun t => ((-‖e t‖^2/2:ℝ):ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_norm_sq_of_inner e he).neg.div_const
  exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp ((hd'.add hde).add he')

theorem analyticAt_phase_of_gram (d e : X → E)
    (hde : AnalyticAt ℝ (fun t => ⟪d t,e t⟫_ℂ) x) :
    AnalyticAt ℝ (fun t => phase (d t) (e t)) x := by
  have him : AnalyticAt ℝ (fun t => (⟪d t,e t⟫_ℂ).im) x :=
    (Complex.imCLM.analyticAt _).comp hde
  have hc : AnalyticAt ℝ (fun t => ((⟪d t,e t⟫_ℂ).im:ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp him
  simpa only [phase,Complex.ofReal_neg,Function.comp_def,Pi.neg_apply,Pi.mul_apply] using
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp (hc.neg.mul (show AnalyticAt ℝ (fun _ : X => (Complex.I : ℂ)) x from analyticAt_const))

 

theorem analyticAt_inner_spinPacket {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : X → ι → Fin 2 → ℂ) (b : X → κ → Fin 2 → ℂ)
    (d : X → ι → E) (e : X → κ → E)
    (ha : ∀i q, AnalyticAt ℝ (fun t => a t i q) x)
    (hb : ∀j q, AnalyticAt ℝ (fun t => b t j q) x)
    (hd : ∀i, AnalyticAt ℝ (fun t => ⟪d t i,d t i⟫_ℂ) x)
    (he : ∀j, AnalyticAt ℝ (fun t => ⟪e t j,e t j⟫_ℂ) x)
    (hde : ∀i j, AnalyticAt ℝ (fun t => ⟪d t i,e t j⟫_ℂ) x) :
    AnalyticAt ℝ (fun t => ⟪spinPacket (a t) (d t),spinPacket (b t) (e t)⟫_ℂ) x := by
  simp_rw [inner_spinPacket]
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  have h0 : AnalyticAt ℝ (fun t => conj (a t i 0)) x :=
    (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (ha i 0)
  have h1 : AnalyticAt ℝ (fun t => conj (a t i 1)) x :=
    (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (ha i 1)
  exact ((h0.mul (hb j 0)).add (h1.mul (hb j 1))).mul
    (analyticAt_kernel_of_gram _ _ (hd i) (he j) (hde i j))

end CoherentFock

namespace CoherentFock
open PointedTree Complex
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

@[simp] theorem spinPacket_apply (a : ι → Fin 2 → ℂ) (d : ι → E) (q : Fin 2) :
    spinPacket a d q=∑i, a i q • coherent (d i) := by
  fin_cases q <;> simp [spinPacket]

theorem spinPacket_smul (z : ℂ) (a : ι → Fin 2 → ℂ) (d : ι → E) :
    z • spinPacket a d=spinPacket (fun i q => z*a i q) d := by
  ext q
  simp [Finset.smul_sum,mul_smul]

theorem spinPacket_sum (a : ι → Fin 2 → ℂ) (b : κ → Fin 2 → ℂ)
    (d : ι → E) (e : κ → E) :
    spinPacket a d+spinPacket b e=spinPacket (Sum.elim a b) (Sum.elim d e) := by
  ext q
  simp [Fintype.sum_sum_type]

theorem act_spinPacket (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a : ι → Fin 2 → ℂ) (d : ι → E) :
    SpinOperators.act A (spinPacket a d)=spinPacket (fun i q => ∑j, A q j*a i j) d := by
  ext q
  simp only [SpinOperators.act_apply,spinPacket_apply,Finset.sum_smul,Finset.smul_sum,mul_smul]
  exact Finset.sum_comm

theorem WZ_spinPacket (h : E) (a : ι → Fin 2 → ℂ) (d : ι → E) :
    WZ h (spinPacket a d)=spinPacket
      (fun p : ι×Fin 2 => fun q => if q=p.2 then
        phase (if p.2=0 then h else -h) (d p.1)*a p.1 q else 0)
      (fun p : ι×Fin 2 => (if p.2=0 then h else -h)+d p.1) := by
  ext q
  fin_cases q <;>
    simp [WZ_apply,spinPacket_apply,Fintype.sum_prod_type,
      map_sum,map_smul,W_coherent,smul_smul,mul_comm]

end CoherentFock

end

end OAI
