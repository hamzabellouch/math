import Mathlib
import OAI.Probability.ParisiFinite.InsertionFromForward

namespace OAI

/-! Ordinary Inverse Special. -/

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

theorem ordinary_inverse_special (γ : ℝ) (v e : E) (x : SpinSpace E) :
    (ordinaryMap γ (Real.pi/4) v e).symm
      (SpinOperators.act Z (specialMap γ (Real.pi/4) v e x))=
      (-I*phase (-(γ • (v-e))) ((-γ) • (v+e))) •
        SpinOperators.act Z (WZ ((-2*γ) • v) x) := by
  change WZ (-(γ • (v-e))) ((SpinOperators.actEquiv (R (Real.pi/4)) (R_unitary _)).symm
    (SpinOperators.act Z (specialMap γ (Real.pi/4) v e x)))=_
  rw [SpinOperators.actEquiv_symm_apply,specialMap_apply]
  change WZ (-(γ • (v-e)))
    (((SpinOperators.act (R (Real.pi/4)).conjTranspose).comp (SpinOperators.act Z)).comp
      ((SpinOperators.act (R (Real.pi/4))).comp (SpinOperators.act X))
      (WZ ((-γ) • (v+e)) x))=_
  rw [← SpinOperators.act_mul,← SpinOperators.act_mul,← SpinOperators.act_mul,
    ← mul_assoc,R_quarter_conjugate_Z,Y_mul_X]
  change WZ (-(γ • (v-e))) ((SpinOperators.rep ((-I) • Z))
    (WZ ((-γ) • (v+e)) x))=_
  rw [map_smul]
  simp only [SpinOperators.rep_apply,smul_apply,map_smul]
  change (-I) • (WZ (-(γ • (v-e)))).comp (SpinOperators.act Z)
    (WZ ((-γ) • (v+e)) x)=_
  rw [WZ_rootZ]
  change (-I) • SpinOperators.act Z
    ((WZ (-(γ • (v-e)))).comp (WZ ((-γ) • (v+e))) x)=_
  rw [WZ_mul]
  simp only [smul_apply,map_smul,smul_smul]
  have hd : -(γ • (v-e))+(-γ) • (v+e)=(-2*γ) • v := by module
  rw [hd]

def leading (γ : ℝ) (v : E) : SpinSpace E :=
  SpinOperators.act Z (WZ ((-2*γ) • v) (vacuum E))

@[simp] theorem norm_leading (γ : ℝ) (v : E) : ‖leading γ v‖=1 := by
  rw [leading,SpinOperators.norm_act Z_unitary,norm_WZ,norm_vacuum]

def leadingCoefficient (γ δ : ℝ) (v e : E) : ℂ :=
  star (ordinaryCoefficient γ δ v e)*specialPhase γ v e*
    (-I*phase (-(γ • (v-e))) ((-γ) • (v+e)))

@[simp] theorem norm_leadingCoefficient (γ δ : ℝ) (v e : E) :
    ‖leadingCoefficient γ δ v e‖=|Real.cos δ| := by
  simp only [leadingCoefficient,norm_mul,norm_specialPhase,norm_neg,Complex.norm_I,
    norm_phase,norm_star,ordinaryCoefficient,Complex.norm_real,
    Real.norm_eq_abs,mul_one]

theorem address_remainder_bound (γ δ : ℝ) (v e : E) :
    ‖address γ δ v e-leadingCoefficient γ δ v e • leading γ v‖≤|Real.sin δ| := by
  have h := UnitarySplit.inverse (initialMap γ δ (Real.pi/4) v e)
    (ordinaryMap γ (Real.pi/4) v e) (specialMap γ (Real.pi/4) v e)
    (ordinaryCoefficient γ δ v e) (specialCoefficient γ δ v e)
    (exact_split γ δ (Real.pi/4) v e)
    (SpinOperators.act Z (specialPhase γ v e • specialMap γ (Real.pi/4) v e (vacuum E)))
  change address γ δ v e=_ at h
  have hf : star (ordinaryCoefficient γ δ v e) •
      (ordinaryMap γ (Real.pi/4) v e).symm
        (SpinOperators.act Z (specialPhase γ v e • specialMap γ (Real.pi/4) v e (vacuum E)))=
      leadingCoefficient γ δ v e • leading γ v := by
    simp only [map_smul,ordinary_inverse_special,smul_smul,← mul_assoc,leadingCoefficient,leading]
  rw [h,hf,add_sub_cancel_left,norm_smul,norm_star,LinearIsometryEquiv.norm_map,
    SpinOperators.norm_act Z_unitary,norm_smul,norm_specialPhase,LinearIsometryEquiv.norm_map,
    norm_vacuum,mul_one,mul_one]
  simp only [specialCoefficient,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,
    norm_phase,one_mul,mul_one,Real.norm_eq_abs,le_refl]

end SeedInitialization

namespace PointedTree
open CoherentFock RootSpin Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rootZ_WZ_vac_pair (d : H) : SpinOperators.act Z (WZ d (vacuum H))=
    spinPair (spinCoefficient • coherent d) (-(spinCoefficient • coherent (-d))) := by
  ext i
  fin_cases i <;> simp [Z,spinPair,WZ_apply,vacuum_apply,spinCoefficient]

theorem inner_rootY_WZ_rootZ_WZ (d f : H) :
    ⟪SpinOperators.act Y (WZ d (vacuum H)),SpinOperators.act Z (WZ f (vacuum H))⟫_ℂ=
      I*kernel (-d) f := by
  rw [rootY_WZ_vac_pair,rootZ_WZ_vac_pair,inner_spinPair]
  simp only [inner_smul_left,inner_smul_right,inner_neg_right,
    inner_coherent,spinCoefficient_conj,map_mul,map_neg,Complex.conj_I]
  have hk : kernel d (-f)=kernel (-d) f := by
    have hn : ‖-d-f‖=‖d+f‖ := by rw [show -d-f=-(d+f) by module,norm_neg]
    simp [kernel_eq,inner_neg_left,inner_neg_right,hn]
  rw [hk]
  linear_combination 2*I*kernel (-d) f*spinCoefficient_sq

theorem norm_inner_high_leading (γ : ℝ) (v e : H) :
    ‖⟪SpinOperators.act Y (WZ ((-2*γ:ℝ) • e) (vacuum H)),
      SeedInitialization.leading γ v⟫_ℂ‖=
        Real.exp (-‖(2*γ:ℝ) • (e+v)‖^2/2) := by
  rw [SeedInitialization.leading,inner_rootY_WZ_rootZ_WZ,norm_mul,
    norm_I,one_mul,norm_kernel]
  congr 3
  have h : -((-2*γ:ℝ) • e)-(-2*γ:ℝ) • v=(2*γ:ℝ) • (e+v) := by module
  rw [h]

end PointedTree

namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_inner_address_bound (γ δ : ℝ) (v e : E) (x : SpinSpace E) :
    ‖⟪x,address γ δ v e⟫_ℂ‖≤‖x‖*|Real.sin δ|+
      |Real.cos δ| *‖⟪x,leading γ v⟫_ℂ‖ := by
  have he : address γ δ v e=(address γ δ v e-leadingCoefficient γ δ v e • leading γ v)+
      leadingCoefficient γ δ v e • leading γ v := (sub_add_cancel _ _).symm
  calc
    _ = ‖⟪x,address γ δ v e-leadingCoefficient γ δ v e • leading γ v⟫_ℂ+
      leadingCoefficient γ δ v e*⟪x,leading γ v⟫_ℂ‖ := by
      conv_lhs => rw [he,inner_add_right,inner_smul_right]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (address_remainder_bound γ δ v e) (norm_nonneg _)))
      (by rw [norm_mul,norm_leadingCoefficient]))

theorem gaussian_decay {α : Type*} {l : Filter α} {f : α → ℝ}
    (h : Tendsto f l atTop) :
    Tendsto (fun t => Real.exp (-(f t)^2/2)) l (𝓝 0) := by
  have hs := ((tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp h).const_mul_atTop
    (by positivity : (0:ℝ)<(2:ℝ)⁻¹)
  convert! Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs) using 1
  funext t
  congr 1
  dsimp only [Function.comp_def]
  ring

def actualV (n : ℕ) (b t : ℝ) : Mode (n+1) :=
  (ordinary [.mixer (delta t),.cost (gamma b t)] (n+1)).insertion

@[simp] theorem norm_actualV (n : ℕ) (b t : ℝ) : ‖actualV n b t‖=1 :=
  EvenUnitary.norm_insertion _

theorem actualV_eq (n : ℕ) (b t : ℝ) :
    actualV n b t=(Real.cos (2*delta t):ℂ) • initialDirection (n+1)+
      (Real.sin (2*delta t):ℂ) • highDirection n (gamma b t) :=
  ordinary_one_mode _ _ _

theorem norm_actualV_sub_initial_le (n : ℕ) (b t : ℝ) :
    ‖actualV n b t-initialDirection (n+1)‖≤
      |Real.cos (2*delta t)-1|+|Real.sin (2*delta t)| := by
  have he : actualV n b t-initialDirection (n+1)=
      ((Real.cos (2*delta t)-1:ℝ):ℂ) • initialDirection (n+1)+
        (Real.sin (2*delta t):ℂ) • highDirection n (gamma b t) := by
    rw [actualV_eq]
    push_cast
    module
  rw [he]
  have heN : ‖initialDirection (n+1)‖=1 := initialDirection_norm _
  have hlN : ‖highDirection n (gamma b t)‖=1 := highDirection_norm _ _
  simpa only [norm_smul,heN,hlN,mul_one,
    Complex.norm_real,Real.norm_eq_abs] using norm_add_le
      (((Real.cos (2*delta t)-1:ℝ):ℂ) • initialDirection (n+1))
      ((Real.sin (2*delta t):ℂ) • highDirection n (gamma b t))

theorem tendsto_actualV_sub_initial (n : ℕ) (b : ℝ) :
    Tendsto (fun t => ‖actualV n b t-initialDirection (n+1)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (norm_actualV_sub_initial_le n b)
  simpa only [sub_self,abs_zero,add_zero] using
    (tendsto_cos_two_delta.sub_const 1).abs.add tendsto_sin_two_delta.abs

theorem tendsto_center_gap (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ‖(2*gamma b t:ℝ) • (initialDirection (n+1)+actualV n b t)‖)
      atTop atTop := by
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖actualV n b t-initialDirection (n+1)‖<1 :=
    (tendsto_actualV_sub_initial n b).eventually (gt_mem_nhds zero_lt_one)
  refine tendsto_atTop_mono' atTop ?_ ((tendsto_gamma b hb).const_mul_atTop (by norm_num : (0:ℝ)<2))
  filter_upwards [hsmall,eventually_ge_atTop (0:ℝ)] with t ht ht0
  have hg : 0 ≤ 2*gamma b t := by unfold gamma; positivity
  have hn : 1 ≤ ‖initialDirection (n+1)+actualV n b t‖ := by
    have h := norm_add_le (initialDirection (n+1)+actualV n b t)
      (initialDirection (n+1)-actualV n b t)
    have he : (initialDirection (n+1)+actualV n b t)+
        (initialDirection (n+1)-actualV n b t)=(2:ℂ) • initialDirection (n+1) := by module
    rw [he,norm_smul,initialDirection_norm,mul_one,norm_sub_rev] at h
    rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at h
    linarith
  rw [← Complex.coe_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hg]
  nlinarith

def actualAddress (n : ℕ) (b t : ℝ) : Level (n+2) :=
  address (gamma b t) (delta t) (actualV n b t) (initialDirection (n+1))

@[simp] theorem norm_actualAddress (n : ℕ) (b t : ℝ) : ‖actualAddress n b t‖=1 :=
  norm_address _ _ _ _

theorem tendsto_high_address_inner (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => ⟪(highDirection (n+1) (gamma b t):Level (n+2)),
      actualAddress n b t⟫_ℂ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs : Tendsto (fun t => |Real.sin (delta t)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sin_zero,abs_zero] using
      (Real.continuous_sin.continuousAt.tendsto.comp tendsto_delta).abs
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun t => show ‖⟪(highDirection (n+1) (gamma b t):Level (n+2)),actualAddress n b t⟫_ℂ‖≤
      |Real.sin (delta t)|+Real.exp (-‖(2*gamma b t:ℝ) •
        (initialDirection (n+1)+actualV n b t)‖^2/2) from ?_)
    (by simpa only [add_zero] using hs.add (gaussian_decay (tendsto_center_gap n b hb)))
  have h := norm_inner_address_bound (gamma b t) (delta t) (actualV n b t)
    (initialDirection (n+1)) (highDirection (n+1) (gamma b t):Level (n+2))
  have hn : ‖(highDirection (n+1) (gamma b t):Level (n+2))‖=1 := highDirection_norm _ _
  rw [hn,one_mul] at h
  have hi : ‖⟪(highDirection (n+1) (gamma b t):Level (n+2)),
      leading (gamma b t) (actualV n b t)⟫_ℂ‖=
      Real.exp (-‖(2*gamma b t:ℝ) • (initialDirection (n+1)+actualV n b t)‖^2/2) := by
    rw [highDirection_coe]
    exact norm_inner_high_leading _ _ _
  rw [hi] at h
  exact h.trans (add_le_add_right (mul_le_of_le_one_left (Real.exp_pos _).le
    (Real.abs_cos_le_one _)) _)

end SeedInitialization

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} {l : Filter α} {d : α → E}

theorem tendsto_inner_coherent_escape (hd : Tendsto (fun a => ‖d a‖) l atTop) (x : E) :
    Tendsto (fun a => ⟪coherent x,coherent (d a)⟫_ℂ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [inner_coherent,norm_kernel]
  have hn : Tendsto (fun a => ‖x-d a‖) l atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [(tendsto_atTop.mp hd) (b+‖x‖)] with a ha
    have h := norm_sub_norm_le (d a) x
    rw [norm_sub_rev] at h
    linarith
  have hs := ((tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp hn).const_mul_atTop
    (by positivity : (0:ℝ)<(2:ℝ)⁻¹)
  convert! Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs) using 1
  funext a
  congr 1
  dsimp only [Function.comp_def]
  ring

theorem tendsto_inner_pre_coherent_escape (hd : Tendsto (fun a => ‖d a‖) l atTop)
    (x : PreSpace E) :
    Tendsto (fun a => ⟪(x:Space E),coherent (d a)⟫_ℂ) l (𝓝 0) := by
  classical
  simp_rw [coe_eq_sum,Finsupp.sum,sum_inner,inner_smul_left]
  convert! (tendsto_finsetSum (toFinsupp x).support fun e he =>
    tendsto_const_nhds.mul (tendsto_inner_coherent_escape hd e)) using 1
  simp

 

theorem tendsto_inner_coherent_escape_all (hd : Tendsto (fun a => ‖d a‖) l atTop)
    (x : Space E) :
    Tendsto (fun a => ⟪x,coherent (d a)⟫_ℂ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x',hx⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := PreSpace E)) x (ε/2) (half_pos hε)
  rw [dist_eq_norm] at hx
  have ht := (tendsto_inner_pre_coherent_escape hd x').norm
  have he : ∀ᶠ a in l, ‖⟪(x':Space E),coherent (d a)⟫_ℂ‖<ε/2 := by
    simpa using ht.eventually_lt_const (by simpa using half_pos hε)
  filter_upwards [he] with a ha
  rw [dist_zero_right,Real.norm_of_nonneg (norm_nonneg _)]
  have hi : ⟪x,coherent (d a)⟫_ℂ=
      ⟪x-(x':Space E),coherent (d a)⟫_ℂ+⟪(x':Space E),coherent (d a)⟫_ℂ := by
    simp only [inner_sub_left,sub_add_cancel]
  rw [hi]
  calc
    _ ≤ ‖⟪x-(x':Space E),coherent (d a)⟫_ℂ‖+‖⟪(x':Space E),coherent (d a)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖x-(x':Space E)‖+‖⟪(x':Space E),coherent (d a)⟫_ℂ‖ := by
      gcongr
      simpa only [norm_coherent,mul_one] using norm_inner_le_norm (x-(x':Space E)) (coherent (d a))
    _ < ε := by linarith

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {α : Type*} {l : Filter α} {d : α → H}

theorem inner_spinPair_right (x : SpinOperators.Double (Space H)) (y z : Space H) :
    ⟪x,spinPair y z⟫_ℂ=⟪x 0,y⟫_ℂ+⟪x 1,z⟫_ℂ := by
  rw [PiLp.inner_apply,Fin.sum_univ_two]
  rfl

theorem tendsto_inner_rootZ_WZ_escape (hd : Tendsto (fun a => ‖d a‖) l atTop)
    (x : SpinSpace H) :
    Tendsto (fun a => ⟪x,SpinOperators.act Z (WZ (d a) (vacuum H))⟫_ℂ) l (𝓝 0) := by
  have hp := tendsto_inner_coherent_escape_all hd (x 0)
  have hm := tendsto_inner_coherent_escape_all (d := fun a => -d a)
    (by simpa only [norm_neg] using hd) (x 1)
  simp_rw [rootZ_WZ_vac_pair,inner_spinPair_right,inner_neg_right,inner_smul_right]
  simpa only [mul_zero,neg_zero,add_zero] using
    (hp.const_mul (spinCoefficient:ℂ)).add (hm.const_mul (spinCoefficient:ℂ)).neg

theorem tendsto_inner_rootY_WZ_escape (hd : Tendsto (fun a => ‖d a‖) l atTop)
    (x : SpinSpace H) :
    Tendsto (fun a => ⟪x,SpinOperators.act Y (WZ (d a) (vacuum H))⟫_ℂ) l (𝓝 0) := by
  have hm := tendsto_inner_coherent_escape_all (d := fun a => -d a)
    (by simpa only [norm_neg] using hd) (x 0)
  have hp := tendsto_inner_coherent_escape_all hd (x 1)
  simp_rw [rootY_WZ_vac_pair,inner_spinPair_right,inner_smul_right]
  simpa only [mul_zero,add_zero,neg_mul] using
    (hm.const_mul (-(I*spinCoefficient))).add (hp.const_mul (I*spinCoefficient))

end PointedTree

namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree

theorem tendsto_norm_scaled_unit {α : Type*} {l : Filter α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → ℝ) (v : α → E) (hf : Tendsto f l atTop) (hv : ∀a, ‖v a‖=1) :
    Tendsto (fun a => ‖(-2*f a:ℝ) • v a‖) l atTop := by
  apply Tendsto.congr' (f₁ := fun a => 2*f a)
  · filter_upwards [hf.eventually (eventually_ge_atTop 0)] with a ha
    rw [norm_smul,hv,mul_one,Real.norm_eq_abs,show -2*f a= -(2*f a) by ring,
      abs_neg,abs_of_nonneg (mul_nonneg (by norm_num) ha)]
  · exact hf.const_mul_atTop (by norm_num : (0:ℝ)<2)

theorem tendsto_inner_high (n : ℕ) (b : ℝ) (hb : 0 < b) (x : Level (n+1)) :
    Tendsto (fun t => ⟪x,(highDirection n (gamma b t):Level (n+1))⟫_ℂ) atTop (𝓝 0) := by
  simp_rw [highDirection_coe]
  exact tendsto_inner_rootY_WZ_escape
    (tendsto_norm_scaled_unit (gamma b) (fun _ => initialDirection n) (tendsto_gamma b hb)
      (fun _ => initialDirection_norm n)) x

theorem tendsto_inner_actualLeading (n : ℕ) (b : ℝ) (hb : 0 < b) (x : Level (n+2)) :
    Tendsto (fun t => ⟪x,leading (gamma b t) (actualV n b t)⟫_ℂ) atTop (𝓝 0) := by
  exact tendsto_inner_rootZ_WZ_escape
    (tendsto_norm_scaled_unit (gamma b) (actualV n b) (tendsto_gamma b hb)
      (norm_actualV n b)) x

theorem tendsto_inner_actualAddress (n : ℕ) (b : ℝ) (hb : 0 < b) (x : Level (n+2)) :
    Tendsto (fun t => ⟪x,actualAddress n b t⟫_ℂ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs : Tendsto (fun t => |Real.sin (delta t)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sin_zero,abs_zero] using
      (Real.continuous_sin.continuousAt.tendsto.comp tendsto_delta).abs
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun t => show ‖⟪x,actualAddress n b t⟫_ℂ‖≤‖x‖*|Real.sin (delta t)|+
      ‖⟪x,leading (gamma b t) (actualV n b t)⟫_ℂ‖ from ?_)
    (by simpa only [mul_zero,norm_zero,add_zero] using
      (hs.const_mul ‖x‖).add (tendsto_inner_actualLeading n b hb x).norm)
  exact (norm_inner_address_bound _ _ _ _ x).trans (add_le_add_right
    (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)) _)

end SeedInitialization

namespace CoherentFock
open PointedTree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} {l : Filter α}

theorem norm_coe_le_mass (x : PreSpace E) : ‖(↑x:Space E)‖≤ mass x := by
  classical
  rw [coe_eq_sum]
  calc
    _ ≤ ∑ a ∈ (toFinsupp x).support, ‖(toFinsupp x) a • coherent a‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul,norm_coherent,mul_one,mass,Finsupp.sum]

theorem norm_spinCoe_le_mass (x : PreSpin E) : ‖spinCoe x‖≤ spinMass x := by
  apply (norm_spin_le_sum _).trans
  exact Finset.sum_le_sum fun i _ => norm_coe_le_mass (x i)

 

theorem tendsto_inner_coe_coherent_uniform (d : α → E) (x : α → PreSpace E)
    (hd : Tendsto (fun a => ‖d a‖) l atTop) (B A : ℝ) (hB : 0 ≤ B)
    (hx : ∀ᶠ a in l, RadiusLE (x a) B ∧ mass (x a)≤A) :
    Tendsto (fun a => ⟪(↑(x a):Space E),coherent (d a)⟫_ℂ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs : Tendsto (fun a => ‖d a‖-2*B) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-(2*B)) hd
  have he := (SeedInitialization.gaussian_decay hs).const_mul A
  simp only [mul_zero] at he
  apply squeeze_zero' (Filter.Eventually.of_forall fun a => norm_nonneg _) ?_ he
  filter_upwards [hx,hd.eventually (eventually_ge_atTop (2*B))] with a hxa hda
  have hb := translated_pre_bound (0:E) (d a) (x a) (basis (0:E)) B (‖d a‖-2*B)
    hxa.1 (RadiusLE.basis _ _ (by simpa only [norm_zero] using hB))
    (by linarith) (by simp only [zero_sub,norm_neg]; linarith)
  simp only [coe_basis,W_zero,ContinuousLinearMap.id_apply,W_vacuum,mass_basis,mul_one] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hxa.2 (Real.exp_nonneg _))

theorem tendsto_inner_spinCoe_rootZ_uniform (d : α → E) (x : α → PreSpin E)
    (hd : Tendsto (fun a => ‖d a‖) l atTop) (B A : ℝ) (hB : 0 ≤ B)
    (hx : ∀ᶠ a in l, SpinRadiusLE (x a) B ∧ spinMass (x a)≤A) :
    Tendsto (fun a => ⟪spinCoe (x a),SpinOperators.act RootSpin.Z (WZ (d a) (vacuum E))⟫_ℂ)
      l (𝓝 0) := by
  have h₀ : ∀ᶠ a in l, RadiusLE (x a 0) B ∧ mass (x a 0)≤A := by
    filter_upwards [hx] with a ha
    exact ⟨ha.1 0,(mass_le_spinMass _ _).trans ha.2⟩
  have h₁ : ∀ᶠ a in l, RadiusLE (x a 1) B ∧ mass (x a 1)≤A := by
    filter_upwards [hx] with a ha
    exact ⟨ha.1 1,(mass_le_spinMass _ _).trans ha.2⟩
  have hp := tendsto_inner_coe_coherent_uniform d (fun a => x a 0) hd B A hB h₀
  have hm := tendsto_inner_coe_coherent_uniform (fun a => -d a) (fun a => x a 1)
    (by simpa only [norm_neg] using hd) B A hB h₁
  simp_rw [rootZ_WZ_vac_pair,inner_spinPair_right,inner_neg_right,inner_smul_right,spinCoe_apply]
  simpa only [mul_zero,neg_zero,add_zero] using
    (hp.const_mul (spinCoefficient:ℂ)).add (hm.const_mul (spinCoefficient:ℂ)).neg

theorem tendsto_inner_spinCoe_rootY_uniform (d : α → E) (x : α → PreSpin E)
    (hd : Tendsto (fun a => ‖d a‖) l atTop) (B A : ℝ) (hB : 0 ≤ B)
    (hx : ∀ᶠ a in l, SpinRadiusLE (x a) B ∧ spinMass (x a)≤A) :
    Tendsto (fun a => ⟪spinCoe (x a),SpinOperators.act RootSpin.Y (WZ (d a) (vacuum E))⟫_ℂ)
      l (𝓝 0) := by
  have h₀ : ∀ᶠ a in l, RadiusLE (x a 0) B ∧ mass (x a 0)≤A := by
    filter_upwards [hx] with a ha
    exact ⟨ha.1 0,(mass_le_spinMass _ _).trans ha.2⟩
  have h₁ : ∀ᶠ a in l, RadiusLE (x a 1) B ∧ mass (x a 1)≤A := by
    filter_upwards [hx] with a ha
    exact ⟨ha.1 1,(mass_le_spinMass _ _).trans ha.2⟩
  have hm := tendsto_inner_coe_coherent_uniform (fun a => -d a) (fun a => x a 0)
    (by simpa only [norm_neg] using hd) B A hB h₀
  have hp := tendsto_inner_coe_coherent_uniform d (fun a => x a 1) hd B A hB h₁
  simp_rw [rootY_WZ_vac_pair,inner_spinPair_right,inner_smul_right,spinCoe_apply]
  simpa only [mul_zero,add_zero,neg_mul] using
    (hm.const_mul (-(Complex.I*spinCoefficient))).add (hp.const_mul (Complex.I*spinCoefficient))

end CoherentFock

namespace SeedInitialization
open CoherentFock PointedTree RootSpin Complex

theorem norm_inner_spinCoe_address_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (γ δ : ℝ) (v e : E) (x : PreSpin E) :
    ‖⟪spinCoe x,address γ δ v e⟫_ℂ‖ ≤ spinMass x*|Real.sin δ|+
      ‖⟪spinCoe x,leading γ v⟫_ℂ‖ := by
  exact (norm_inner_address_bound γ δ v e (spinCoe x)).trans
    (add_le_add (mul_le_mul_of_nonneg_right (norm_spinCoe_le_mass x) (abs_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)))

theorem norm_inner_spinCoe_address_bound_of_mass {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (γ δ : ℝ) (v e : E) (x : PreSpin E) (A : ℝ)
    (hA : spinMass x ≤ A) :
    ‖⟪spinCoe x,address γ δ v e⟫_ℂ‖ ≤ A*|Real.sin δ|+
      ‖⟪spinCoe x,leading γ v⟫_ℂ‖ :=
  (norm_inner_spinCoe_address_bound γ δ v e x).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) _)

theorem tendsto_inner_high_uniform (n : ℕ) (b : ℝ) (hb : 0 < b)
    (x : ℝ → PreSpin (Mode n)) (B A : ℝ) (hB : 0 ≤ B)
    (hx : ∀ᶠ t : ℝ in atTop, SpinRadiusLE (x t) B ∧ spinMass (x t)≤A) :
    Tendsto (fun t => ⟪spinCoe (x t),(highDirection n (gamma b t):Level (n+1))⟫_ℂ)
      atTop (𝓝 0) := by
  simp_rw [highDirection_coe]
  exact tendsto_inner_spinCoe_rootY_uniform _ x
    (tendsto_norm_scaled_unit (gamma b) (fun _ => initialDirection n) (tendsto_gamma b hb)
      (fun _ => initialDirection_norm n)) B A hB hx

theorem tendsto_inner_address_uniform (n : ℕ) (b : ℝ) (hb : 0 < b)
    (x : ℝ → PreSpin (Mode (n+1))) (B A : ℝ) (hB : 0 ≤ B)
    (hx : ∀ᶠ t : ℝ in atTop, SpinRadiusLE (x t) B ∧ spinMass (x t)≤A) :
    Tendsto (fun t => ⟪spinCoe (x t),actualAddress n b t⟫_ℂ) atTop (𝓝 0) := by
  have hl : Tendsto (fun t => ⟪spinCoe (x t),leading (gamma b t) (actualV n b t)⟫_ℂ)
      atTop (𝓝 0) :=
    tendsto_inner_spinCoe_rootZ_uniform _ x
      (tendsto_norm_scaled_unit (gamma b) (actualV n b) (tendsto_gamma b hb)
        (norm_actualV n b)) B A hB hx
  have hs : Tendsto (fun t => |Real.sin (delta t)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sin_zero,abs_zero] using
      (Real.continuous_sin.continuousAt.tendsto.comp tendsto_delta).abs
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_
    (by simpa only [mul_zero,norm_zero,add_zero] using (hs.const_mul A).add hl.norm)
  filter_upwards [hx] with t ht
  have hm : ‖(spinCoe (x t):Level (n+2))‖ ≤ A := (norm_spinCoe_le_mass (x t)).trans ht.2
  have h := norm_inner_address_bound (gamma b t) (delta t) (actualV n b t)
    (initialDirection (n+1)) (spinCoe (x t):Level (n+2))
  have h1 := mul_le_mul_of_nonneg_right hm (abs_nonneg (Real.sin (delta t)))
  have h2 := mul_le_of_le_one_left
    (norm_nonneg ⟪(spinCoe (x t):Level (n+2)),leading (gamma b t) (actualV n b t)⟫_ℂ)
    (Real.abs_cos_le_one (delta t))
  change ‖⟪(spinCoe (x t):Level (n+2)),address (gamma b t) (delta t) (actualV n b t)
    (initialDirection (n+1))⟫_ℂ‖ ≤ _
  exact h.trans (add_le_add h1 h2)

end SeedInitialization

namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem cos_delta_error {t : ℝ} (ht : 1 ≤ t) :
    |Real.cos (delta t)-1|≤(amplitude t)^2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
  have hc : 0 ≤ Real.cos (delta t) := by rw [cos_delta]; positivity
  have h := Real.sin_sq_add_cos_sq (delta t)
  rw [sin_delta ht] at h
  have hc1 := Real.cos_le_one (delta t)
  nlinarith

theorem ordinaryCoefficient_error (γ δ : ℝ) (v e : E) :
    ‖ordinaryCoefficient γ δ v e-phase (γ • v) ((-γ) • e)‖=|Real.cos δ-1| := by
  rw [ordinaryCoefficient,← sub_one_mul,norm_mul,norm_phase,mul_one]
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

theorem ordinary_component_error (γ β : ℝ) {t : ℝ} (ht : 1 ≤ t)
    (v e : E) (x : SpinSpace E) :
    ‖ordinaryCoefficient γ (delta t) v e • ordinaryMap γ β v e x-
      phase (γ • v) ((-γ) • e) • ordinaryMap γ β v e x‖≤(amplitude t)^2*‖x‖ := by
  rw [← sub_smul,norm_smul,ordinaryCoefficient_error,LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_right (cos_delta_error ht) (norm_nonneg _)

theorem initial_forward_error (γ β : ℝ) {t : ℝ} (ht : 1 ≤ t)
    (v e : E) (x : SpinSpace E) :
    ‖initialMap γ (delta t) β v e x-
      phase (γ • v) ((-γ) • e) • ordinaryMap γ β v e x‖≤
      ((amplitude t)^2+amplitude t)*‖x‖ := by
  rw [exact_split,add_sub_right_comm]
  calc
    _ ≤ ‖ordinaryCoefficient γ (delta t) v e • ordinaryMap γ β v e x-
      phase (γ • v) ((-γ) • e) • ordinaryMap γ β v e x‖+
        ‖specialCoefficient γ (delta t) v e • specialMap γ β v e x‖ := norm_add_le _ _
    _ ≤ (amplitude t)^2*‖x‖+amplitude t*‖x‖ := by
      apply add_le_add (ordinary_component_error γ β ht v e x)
      rw [norm_special_component,sin_delta ht,abs_of_pos (amplitude_pos ht)]
    _ = _ := (add_mul _ _ _).symm

theorem initial_insertion_error (γ β : ℝ) {t : ℝ} (ht : 1 ≤ t)
    (v e : E) (P : SpinSpace E →L[ℂ] SpinSpace E) (hP : ∀x, ‖P x‖≤‖x‖) :
    ‖(initialMap γ (delta t) β v e).symm (P (initialMap γ (delta t) β v e (vacuum E)))-
      (ordinaryMap γ β v e).symm (P (ordinaryMap γ β v e (vacuum E)))‖≤
      2*((amplitude t)^2+amplitude t) := by
  have h := ForwardControl.insertion_from_forward (initialMap γ (delta t) β v e)
    (ordinaryMap γ β v e) P hP (vacuum E) (phase (γ • v) ((-γ) • e))
  have h₁ := initial_forward_error γ β ht v e (vacuum E)
  have h₂ := initial_forward_error γ β ht v e
    ((ordinaryMap γ β v e).symm (P (ordinaryMap γ β v e (vacuum E))))
  rw [norm_vacuum,mul_one] at h₁
  have hn : ‖(ordinaryMap γ β v e).symm (P (ordinaryMap γ β v e (vacuum E)))‖≤1 := by
    rw [LinearIsometryEquiv.norm_map]
    simpa only [LinearIsometryEquiv.norm_map,norm_vacuum] using hP
      (ordinaryMap γ β v e (vacuum E))
  have hh := mul_le_mul_of_nonneg_left hn
    (add_nonneg (sq_nonneg (amplitude t)) (amplitude_pos ht).le)
  nlinarith

def ordinaryDisplacement (n : ℕ) (b t : ℝ) : Mode (n+1) :=
  gamma b t • (actualV n b t-initialDirection (n+1))

theorem ordinaryDisplacement_error_eq (n : ℕ) (b t : ℝ) :
    ordinaryDisplacement n b t-(2*b:ℝ) • highDirection n (gamma b t)=
      ((gamma b t*(Real.cos (2*delta t)-1):ℝ):ℂ) • initialDirection (n+1)+
        ((gamma b t*Real.sin (2*delta t)-2*b:ℝ):ℂ) • highDirection n (gamma b t) := by
  unfold ordinaryDisplacement
  rw [actualV_eq,← Complex.coe_smul,← Complex.coe_smul]
  push_cast
  module

theorem norm_ordinaryDisplacement_error (n : ℕ) (b t : ℝ) :
    ‖ordinaryDisplacement n b t-(2*b:ℝ) • highDirection n (gamma b t)‖≤
      |gamma b t*(Real.cos (2*delta t)-1)|+|gamma b t*Real.sin (2*delta t)-2*b| := by
  rw [ordinaryDisplacement_error_eq]
  have heN : ‖initialDirection (n+1)‖=1 := initialDirection_norm _
  have hlN : ‖highDirection n (gamma b t)‖=1 := highDirection_norm _ _
  simpa only [norm_smul,heN,hlN,mul_one,Complex.norm_real,Real.norm_eq_abs] using norm_add_le
    (((gamma b t*(Real.cos (2*delta t)-1):ℝ):ℂ) • initialDirection (n+1))
    (((gamma b t*Real.sin (2*delta t)-2*b:ℝ):ℂ) • highDirection n (gamma b t))

theorem tendsto_ordinaryDisplacement_error (n : ℕ) (b : ℝ) :
    Tendsto (fun t => ‖ordinaryDisplacement n b t-(2*b:ℝ) • highDirection n (gamma b t)‖)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (norm_ordinaryDisplacement_error n b)
  simpa only [abs_zero,sub_self,add_zero] using (tendsto_gamma_cos_error b).abs.add
    ((tendsto_gamma_sin b).sub_const (2*b)).abs

theorem ordinaryDisplacement_bounded (n : ℕ) (b : ℝ) :
    ∀ᶠ t : ℝ in atTop, ‖ordinaryDisplacement n b t‖≤2*|b|+1 := by
  filter_upwards [(tendsto_ordinaryDisplacement_error n b).eventually
    (gt_mem_nhds zero_lt_one)] with t ht
  have h := norm_le_norm_sub_add (ordinaryDisplacement n b t)
    ((2*b:ℝ) • highDirection n (gamma b t))
  have hn : ‖(2*b:ℝ) • highDirection n (gamma b t)‖=2*|b| := by
    rw [← Complex.coe_smul,norm_smul,highDirection_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_mul]
    norm_num
  rw [hn] at h
  linarith

end SeedInitialization

namespace PointedTree
open CoherentFock RootSpin

theorem symmetry_rootX (n : ℕ) (x : Level n) :
    (symmetry n).op (root n X x)=root n X ((symmetry n).op x) := by
  cases n with
  | zero => rfl
  | succ n =>
    change SpinOperators.act X
      (spinMap (gammaEmbedding (symmetry n).centered.toLinearIsometry) (SpinOperators.act X x))=_
    rw [spinMap_root]
    rfl

namespace EvenUnitary

def rootX (n : ℕ) : EvenUnitary n where
  op := rootEquiv n X X_unitary
  commutes x := by simpa only [rootEquiv_apply] using symmetry_rootX n x

end EvenUnitary
end PointedTree

namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree

theorem odd_real_smul {n : ℕ} {v : Mode n} (hv : (symmetry n).centered v=-v) (a : ℝ) :
    (symmetry n).centered (a • v)= -(a • v) := by
  rw [← Complex.coe_smul,map_smul,hv,smul_neg]

theorem odd_actualV (n : ℕ) (b t : ℝ) :
    (symmetry (n+1)).centered (actualV n b t)= -actualV n b t :=
  EvenUnitary.insertion_odd _

theorem odd_initialDirection (n : ℕ) :
    (symmetry n).centered (initialDirection n)= -initialDirection n :=
  EvenUnitary.insertion_odd _

def specialUnitary (n : ℕ) (b t : ℝ) : EvenUnitary (n+2) :=
  ((EvenUnitary.cost (n+1) ((-gamma b t) • (actualV n b t+initialDirection (n+1)))
    (odd_real_smul (by rw [map_add,odd_actualV,odd_initialDirection,neg_add]) _)).followedBy
    (EvenUnitary.rootX (n+2))).followedBy (EvenUnitary.mixer (n+2) (Real.pi/4))

theorem specialUnitary_apply (n : ℕ) (b t : ℝ) (x : Level (n+2)) :
    (specialUnitary n b t).op x=
      specialMap (gamma b t) (Real.pi/4) (actualV n b t) (initialDirection (n+1)) x := rfl

theorem initialMap_eq_ordinary (n : ℕ) (b t β : ℝ) :
    initialMap (gamma b t) (delta t) β (actualV n b t) (initialDirection (n+1))=
      (ordinary (initializationWord (gamma b t) (delta t) β) (n+2)).op := by
  apply LinearIsometryEquiv.ext
  intro x
  symm
  simpa only [initialMap_apply,actualV,Complex.coe_smul,← Complex.ofReal_neg] using
    initialization_op n (gamma b t) (delta t) β x

theorem actualAddress_odd (n : ℕ) (b t : ℝ) :
    (symmetry (n+2)).op (actualAddress n b t)= -actualAddress n b t := by
  let z : ℂ := specialPhase (gamma b t) (actualV n b t) (initialDirection (n+1))
  let S := specialUnitary n b t
  have hs : (symmetry (n+2)).op (z • S.op (vac (n+2)))=z • S.op (vac (n+2)) := by
    rw [map_smul,S.commutes,symmetry_vac]
  have hz := symmetry_rootZ (n+2) (z • S.op (vac (n+2)))
  rw [hs] at hz
  change (symmetry (n+2)).op (SpinOperators.act Z (z • S.op (vac (n+2))))=
    -SpinOperators.act Z (z • S.op (vac (n+2))) at hz
  have he : S.op (vac (n+2))=
      specialMap (gamma b t) (Real.pi/4) (actualV n b t) (initialDirection (n+1))
        (vacuum (Mode (n+1))) := rfl
  rw [he] at hz
  unfold actualAddress address
  rw [initialMap_eq_ordinary,EvenUnitary.symm_commutes,hz,map_neg]

 

def addressMode (n : ℕ) (b t : ℝ) : Mode (n+2) :=
  ⟨actualAddress n b t,odd_centered (symmetry (n+2)) _ (actualAddress_odd n b t)⟩

@[simp] theorem norm_addressMode (n : ℕ) (b t : ℝ) : ‖addressMode n b t‖=1 :=
  norm_actualAddress n b t

@[simp] theorem addressMode_odd (n : ℕ) (b t : ℝ) :
    (symmetry (n+2)).centered (addressMode n b t)= -addressMode n b t := by
  apply Subtype.ext
  exact actualAddress_odd n b t

end SeedInitialization

end

end OAI
