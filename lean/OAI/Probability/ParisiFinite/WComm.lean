import Mathlib
import OAI.Probability.ParisiFinite.ExpVector

namespace OAI

/-! W Comm. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
namespace CoherentFock
open Complex
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem W_comm (v d : E) :
    (W v).comp (W d) = Complex.exp (((-2*(⟪v,d⟫_ℂ).im:ℝ):ℂ)*I) •
      (W d).comp (W v) := by
  rw [W_mul,W_mul,add_comm d v,smul_smul]
  congr 1
  have hi := inner_im_symm (𝕜 := ℂ) d v
  change (⟪d,v⟫_ℂ).im = -(⟪v,d⟫_ℂ).im at hi
  simp only [phase,← Complex.exp_add,hi,neg_neg]
  congr 1
  push_cast
  ring

 
theorem W_centered_difference_le (v d : E) (x : Space E) :
    ‖W v (W d x)-W d x‖ ≤ ‖W v x-x‖+2*‖v‖*‖d‖*‖x‖ := by
  let c := Complex.exp (((-2*(⟪v,d⟫_ℂ).im:ℝ):ℂ)*I)
  have hc : ‖c‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hs : ‖c-1‖ ≤ 2*‖v‖*‖d‖ := by
    have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2*(⟪v,d⟫_ℂ).im)
    have hb := (Complex.abs_im_le_norm ⟪v,d⟫_ℂ).trans (norm_inner_le_norm v d)
    have he : |(-2:ℝ)*(⟪v,d⟫_ℂ).im|=2*|(⟪v,d⟫_ℂ).im| := by simp
    change ‖c-1‖ ≤ _
    have hh' : ‖c-1‖ ≤ 2*|(⟪v,d⟫_ℂ).im| := by
      simpa only [c,mul_comm I,Real.norm_eq_abs,he] using hh
    nlinarith
  have he : W v (W d x)-W d x = c • W d (W v x-x)+(c-1) • W d x := by
    have hw := congrArg (fun A : Space E →L[ℂ] Space E => A x) (W_comm v d)
    simp only [ContinuousLinearMap.comp_apply,smul_apply] at hw
    rw [hw,map_sub]
    change c • W d (W v x)-W d x = _
    module
  rw [he]
  calc
    _ ≤ ‖c • W d (W v x-x)‖+‖(c-1) • W d x‖ := norm_add_le _ _
    _ = ‖W v x-x‖+‖c-1‖*‖x‖ := by simp only [norm_smul,hc,one_mul,norm_W]
    _ ≤ _ := by gcongr

 
theorem W_fieldCoherent_sub_le (h v d : E) :
    ‖W h (fieldCoherent v d)-fieldCoherent v d‖ ≤
      2*‖h‖*‖v‖*(1+2*‖d‖+2*‖d‖^2) := by
  have h1 : ‖W h (W d (oneParticle v))-W d (oneParticle v)‖ ≤
      2*‖h‖*‖v‖+2*‖h‖*‖d‖*‖v‖ := by
    exact (W_centered_difference_le h d (oneParticle v)).trans (by
      rw [norm_oneParticle]
      exact add_le_add_left (W_oneParticle_sub_le h v) _)
  have h2 := W_coherent_sub_le h d
  have hb : ‖((2*(⟪v,d⟫_ℂ).im:ℝ):ℂ)‖ ≤ 2*‖v‖*‖d‖ := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul]
    have hh := (Complex.abs_im_le_norm ⟪v,d⟫_ℂ).trans (norm_inner_le_norm v d)
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    nlinarith
  have he : W h (fieldCoherent v d)-fieldCoherent v d =
      (-I) • (W h (W d (oneParticle v))-W d (oneParticle v))-
      ((2*(⟪v,d⟫_ℂ).im:ℝ):ℂ) • (W h (coherent d)-coherent d) := by
    simp only [fieldCoherent,map_sub,map_smul]
    module
  rw [he]
  calc
    _ ≤ ‖(-I) • (W h (W d (oneParticle v))-W d (oneParticle v))‖+
      ‖((2*(⟪v,d⟫_ℂ).im:ℝ):ℂ) • (W h (coherent d)-coherent d)‖ := norm_sub_le _ _
    _ = ‖W h (W d (oneParticle v))-W d (oneParticle v)‖+
      ‖((2*(⟪v,d⟫_ℂ).im:ℝ):ℂ)‖*‖W h (coherent d)-coherent d‖ := by
      simp only [norm_smul,norm_neg,Complex.norm_I,one_mul]
    _ ≤ (2*‖h‖*‖v‖+2*‖h‖*‖d‖*‖v‖)+(2*‖v‖*‖d‖)*(‖h‖*(1+2*‖d‖)) := by
      gcongr
    _ = _ := by ring

theorem W_preField_sub_le (h v : E) (x : PreSpace E) :
    ‖W h (preField v x)-preField v x‖ ≤ 2*‖h‖*‖v‖*secondTailBound x := by
  classical
  simp only [preField_eq_sum,Finsupp.sum,map_sum,map_smul,← Finset.sum_sub_distrib,← smul_sub]
  calc
    _ ≤ ∑ e ∈ (toFinsupp x).support,
      ‖(toFinsupp x) e • (W h (fieldCoherent v e)-fieldCoherent v e)‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ (toFinsupp x).support,
      ‖(toFinsupp x) e‖*(2*‖h‖*‖v‖*(1+2*‖e‖+12*‖e‖^2)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (W_fieldCoherent_sub_le h v e).trans (by gcongr; norm_num)
    _ = _ := by
      simp only [secondTailBound,Finsupp.sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
 
abbrev SpinSpace (E : Type*) [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  PiLp 2 (fun _ : Fin 2 => Space E)

 
def WZ (d : E) : SpinSpace E →L[ℂ] SpinSpace E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => Space E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (W (if i = 0 then d else -d)).comp (PiLp.proj 2 (fun _ : Fin 2 => Space E) i))

@[simp] theorem WZ_apply (d : E) (x : SpinSpace E) (i : Fin 2) :
    WZ d x i = W (if i = 0 then d else -d) (x i) := by rfl

@[simp] theorem norm_WZ (d : E) (x : SpinSpace E) : ‖WZ d x‖ = ‖x‖ := by
  have h : ‖WZ d x‖^2 = ‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp
  nlinarith [norm_nonneg (WZ d x),norm_nonneg x]

@[simp] theorem phase_neg_neg (d e : E) : phase (-d) (-e) = phase d e := by
  simp [phase]

@[simp] theorem WZ_zero : WZ (0 : E) = ContinuousLinearMap.id ℂ (SpinSpace E) := by
  ext x i
  simp [WZ_apply]

theorem WZ_mul (d e : E) : (WZ d).comp (WZ e) = phase d e • WZ (d+e) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    PiLp.smul_apply,WZ_apply]
  split_ifs with hi
  · exact congrArg (fun T : Space E →L[ℂ] Space E => T (x i)) (W_mul d e)
  · simpa only [neg_add,phase_neg_neg,ContinuousLinearMap.comp_apply,smul_apply] using
      congrArg (fun T : Space E →L[ℂ] Space E => T (x i)) (W_mul (-d) (-e))

 

theorem exact_echo (t r : ℝ) (v v' : E) :
    (WZ ((t/r) • v')).comp (WZ (-(t/r) • v)) =
      phase ((t/r) • v') (-(t/r) • v) • WZ ((t/r) • (v'-v)) := by
  rw [WZ_mul]
  have heq : (t/r) • v' + (-(t/r)) • v = (t/r) • (v'-v) := by
    rw [smul_sub,neg_smul,sub_eq_add_neg]
  rw [heq]

 
theorem exact_echo_unimodular (t r : ℝ) (v v' : E) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧
    (WZ ((t/r) • v')).comp (WZ (-(t/r) • v)) = ξ • WZ ((t/r) • (v'-v)) :=
  ⟨_,norm_phase _ _,exact_echo t r v v'⟩

theorem continuous_WZ (x : SpinSpace E) : Continuous (fun d : E => WZ d x) := by
  rw [← (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => Space E)).toHomeomorph.comp_continuous_iff]
  apply continuous_pi
  intro i
  change Continuous (fun d : E => W (if i = 0 then d else -d) (x i))
  split_ifs with hi
  · exact continuous_W (x i)
  · exact (continuous_W (x i)).comp continuous_neg

theorem tendsto_WZ {α : Type*} {l : Filter α} {ds : α → E} {xs : α → SpinSpace E}
    {d : E} {x : SpinSpace E} (hd : Tendsto ds l (𝓝 d)) (hx : Tendsto xs l (𝓝 x)) :
    Tendsto (fun a => WZ (ds a) (xs a)) l (𝓝 (WZ d x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he1 := Metric.tendsto_nhds.mp hx (ε/2) (by positivity)
  have he2 := Metric.tendsto_nhds.mp (((continuous_WZ x).tendsto d).comp hd)
    (ε/2) (by positivity)
  filter_upwards [he1,he2] with a ha hb
  have heq : dist (WZ (ds a) (xs a)) (WZ (ds a) x) = dist (xs a) x := by
    simp only [dist_eq_norm,← map_sub,norm_WZ]
  have ht := dist_triangle (WZ (ds a) (xs a)) (WZ (ds a) x) (WZ d x)
  rw [heq] at ht
  dsimp only [Function.comp_def] at hb
  linarith

 
@[simp] theorem WZ_error (d : E) (x y : SpinSpace E) :
    ‖WZ d x-WZ d y‖=‖x-y‖ := by rw [← map_sub,norm_WZ]

 

theorem corrected_echo (t r : ℝ) (v v' : E) (x : SpinSpace E) :
    (phase ((t/r) • v') (-(t/r) • v))⁻¹ •
      WZ ((t/r) • v') (WZ (-(t/r) • v) x) = WZ ((t/r) • (v'-v)) x := by
  have hp : phase ((t/r) • v') (-(t/r) • v) ≠ 0 := by
    intro hz
    have h := norm_phase ((t/r) • v') (-(t/r) • v)
    rw [hz,norm_zero] at h
    norm_num at h
  have h := congrArg (fun T : SpinSpace E →L[ℂ] SpinSpace E => T x) (exact_echo t r v v')
  simp only [ContinuousLinearMap.comp_apply,smul_apply] at h
  rw [h,smul_smul,inv_mul_cancel₀ hp,one_smul]

 

theorem tendsto_corrected_echo {α : Type*} {l : Filter α}
    (t : ℝ) (r : α → ℝ) (v v' : α → E) (xs : α → SpinSpace E)
    (w : E) (x : SpinSpace E)
    (hd : Tendsto (fun a => (r a)⁻¹ • (v' a-v a)) l (𝓝 ((-2:ℝ) • w)))
    (hx : Tendsto xs l (𝓝 x)) :
    Tendsto (fun a => (phase ((t/r a) • v' a) (-(t/r a) • v a))⁻¹ •
      WZ ((t/r a) • v' a) (WZ (-(t/r a) • v a) (xs a)))
      l (𝓝 (WZ ((-2*t) • w) x)) := by
  simp_rw [corrected_echo]
  have hd' : Tendsto (fun a => (t/r a) • (v' a-v a)) l (𝓝 ((-2*t) • w)) := by
    convert! (tendsto_const_nhds (x := t)).smul hd using 1
    · ext a
      rw [smul_smul,div_eq_mul_inv]
    · simp only [smul_smul,mul_comm t (-2)]
  exact tendsto_WZ hd' hx

end CoherentFock

namespace SpinOperators
open scoped Matrix.Norms.L2Operator
local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ _
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev Double (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  PiLp 2 (fun _ : Fin 2 => H)

def act (A : Matrix (Fin 2) (Fin 2) ℂ) : Double H →L[ℂ] Double H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ∑ j : Fin 2, A i j • PiLp.proj 2 (fun _ : Fin 2 => H) j)

@[simp] theorem act_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Double H) (i : Fin 2) :
    act A x i = ∑ j : Fin 2, A i j • x j := by
  simp [act,PiLp.proj_apply]

@[simp] theorem act_one : act (1 : Matrix (Fin 2) (Fin 2) ℂ) = ContinuousLinearMap.id ℂ (Double H) := by
  ext x i
  simp [act_apply,Matrix.one_apply]

 theorem act_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    act (A*B) = (act A : Double H →L[ℂ] Double H).comp (act B) := by
  ext x i
  simp only [act_apply,ContinuousLinearMap.comp_apply,Matrix.mul_apply,
    Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]

 theorem act_add (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    act (A+B) = (act A : Double H →L[ℂ] Double H)+act B := by
  ext x i
  simp [act_apply,add_smul,Finset.sum_add_distrib]

 theorem act_scalar (z : ℂ) :
    act (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z) =
      algebraMap ℂ (Double H →L[ℂ] Double H) z := by
  ext x i
  simp [act_apply,Matrix.algebraMap_eq_diagonal,Matrix.diagonal_apply,Pi.algebraMap_apply]

def rep : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] (Double H →L[ℂ] Double H) where
  toFun := act
  map_zero' := by ext x i; simp [act_apply]
  map_one' := act_one
  map_add' := act_add
  map_mul' := act_mul
  commutes' := act_scalar

@[simp] theorem rep_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    rep (H := H) A = act A := rfl

variable [CompleteSpace H]

theorem act_adjoint (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (act A : Double H →L[ℂ] Double H).adjoint = act A.conjTranspose := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,act_apply,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_conj]
  rw [Finset.sum_comm]

def starRep : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] (Double H →L[ℂ] Double H) where
  toAlgHom := rep
  map_star' A := by
    change act A.conjTranspose = star (act A : Double H →L[ℂ] Double H)
    rw [ContinuousLinearMap.star_eq_adjoint,act_adjoint]

omit [CompleteSpace H] in
 theorem continuous_rep : Continuous (rep (H := H)) :=
  (rep (H := H)).toLinearMap.continuous_of_finiteDimensional

local instance : NormedAlgebra ℚ (Double H →L[ℂ] Double H) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

 theorem act_exp (A : Matrix (Fin 2) (Fin 2) ℂ) :
    act (NormedSpace.exp A) = NormedSpace.exp (act A : Double H →L[ℂ] Double H) :=
  NormedSpace.map_exp (rep (H := H)) continuous_rep A

 theorem act_mem_unitary {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ unitary _) :
    (act A : Double H →L[ℂ] Double H) ∈ unitary _ := by
  exact Unitary.map_mem (starRep (H := H)) hA

 theorem norm_act {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ unitary _) (x : Double H) :
    ‖act A x‖=‖x‖ := ContinuousLinearMap.norm_map_of_mem_unitary (act_mem_unitary hA) x

end SpinOperators

open scoped BigOperators
namespace WeightedMass
variable {ι : Type*}
def mass (w : ι → ℝ) (x : ι →₀ ℂ) := x.sum (fun i a => ‖a‖*w i)

theorem nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ι →₀ ℂ) : 0 ≤ mass w x := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hw i))

theorem add_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x y : ι →₀ ℂ) :
    mass w (x+y) ≤ mass w x+mass w y := by
  classical
  let s := x.support ∪ y.support
  have hx : x.support ⊆ s := Finset.subset_union_left
  have hy : y.support ⊆ s := Finset.subset_union_right
  have hxy : (x+y).support ⊆ s := Finsupp.support_add
  unfold mass
  rw [Finsupp.sum_of_support_subset (x+y) hxy _ (fun i hi => by simp),
    Finsupp.sum_of_support_subset x hx _ (fun i hi => by simp),
    Finsupp.sum_of_support_subset y hy _ (fun i hi => by simp),← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Finsupp.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right (norm_add_le (x i) (y i)) (hw i)]

@[simp] theorem zero (w : ι → ℝ) : mass w 0=0 := by simp [mass]

theorem smul (w : ι → ℝ) (c : ℂ) (x : ι →₀ ℂ) :
    mass w (c • x) = ‖c‖*mass w x := by
  classical
  by_cases hc : c=0
  · simp [hc]
  unfold mass
  simp only [Finsupp.sum,Finset.mul_sum]
  rw [Finsupp.support_smul_eq hc]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finsupp.smul_apply,norm_smul]
  ring

theorem sum_le {κ : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s : Finset κ) (x : κ → ι →₀ ℂ) : mass w (∑ j ∈ s, x j) ≤ ∑ j ∈ s, mass w (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (add_le w hw _ _).trans (add_le_add_right ih _)

end WeightedMass

namespace CoherentFock
open Complex
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
theorem secondTailBound_nonneg (x : PreSpace E) : 0 ≤ secondTailBound x :=
  WeightedMass.nonneg _ (fun d => by positivity) (toFinsupp x)

omit [InnerProductSpace ℂ E] in
theorem secondTailBound_smul (c : ℂ) (x : PreSpace E) :
    secondTailBound (c • x)=‖c‖*secondTailBound x := by
  exact WeightedMass.smul _ c (toFinsupp x)

omit [InnerProductSpace ℂ E] in
theorem secondTailBound_add (x y : PreSpace E) :
    secondTailBound (x+y) ≤ secondTailBound x+secondTailBound y :=
  WeightedMass.add_le _ (fun d => by positivity) (toFinsupp x) (toFinsupp y)

omit [InnerProductSpace ℂ E] in
theorem secondTailBound_sum {κ : Type*} (s : Finset κ) (x : κ → PreSpace E) :
    secondTailBound (∑ j ∈ s, x j) ≤ ∑ j ∈ s, secondTailBound (x j) := by
  simpa only [secondTailBound,WeightedMass.mass,map_sum] using
    WeightedMass.sum_le _ (fun d : E => by positivity) s (fun j => toFinsupp (x j))

theorem norm_preField_le (v : E) (x : PreSpace E) :
    ‖preField v x‖ ≤ ‖v‖*secondTailBound x := by
  classical
  simp only [preField_eq_sum,Finsupp.sum]
  calc
    _ ≤ ∑ e ∈ (toFinsupp x).support, ‖(toFinsupp x) e‖*‖fieldCoherent v e‖ := by
      simpa only [norm_smul] using norm_sum_le (toFinsupp x).support
        (fun e => (toFinsupp x) e • fieldCoherent v e)
    _ ≤ ∑ e ∈ (toFinsupp x).support, ‖(toFinsupp x) e‖*(‖v‖*(1+2*‖e‖+12*‖e‖^2)) := by
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_fieldCoherent_le v e).trans (mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg ‖e‖]) (norm_nonneg v))
    _ = _ := by
      simp only [secondTailBound,Finsupp.sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring

theorem preField_add (v w : E) (x : PreSpace E) :
    preField (v+w) x=preField v x+preField w x := by
  classical
  simp only [preField_eq_sum,Finsupp.sum,fieldCoherent_add,smul_add,Finset.sum_add_distrib]

theorem preField_neg (v : E) (x : PreSpace E) : preField (-v) x= -preField v x := by
  simpa only [neg_one_smul] using preField_real_smul (-1) v x

theorem preField_sub (v w : E) (x : PreSpace E) :
    preField (v-w) x=preField v x-preField w x := by
  simp only [sub_eq_add_neg,preField_add,preField_neg]

abbrev PreSpin (E : Type*) := Fin 2 → PreSpace E

def spinCoe (x : PreSpin E) : SpinSpace E := WithLp.toLp 2 (fun i => (x i : Space E))
@[simp] theorem spinCoe_apply (x : PreSpin E) (i : Fin 2) : spinCoe x i=(↑(x i) : Space E) := rfl

def preRoot (A : Matrix (Fin 2) (Fin 2) ℂ) (x : PreSpin E) : PreSpin E :=
  fun i => ∑ j, A i j • x j

def spinBound (x : PreSpin E) : ℝ := ∑ i, secondTailBound (x i)

def matrixMass (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

omit [InnerProductSpace ℂ E] in
theorem spinBound_nonneg (x : PreSpin E) : 0 ≤ spinBound x :=
  Finset.sum_nonneg (fun i _ => secondTailBound_nonneg (x i))

omit [InnerProductSpace ℂ E] in
theorem secondTailBound_le_spinBound (x : PreSpin E) (i : Fin 2) :
    secondTailBound (x i) ≤ spinBound x :=
  Finset.single_le_sum (fun j _ => secondTailBound_nonneg (x j)) (Finset.mem_univ i)

omit [InnerProductSpace ℂ E] in
theorem spinBound_preRoot (A : Matrix (Fin 2) (Fin 2) ℂ) (x : PreSpin E) :
    spinBound (preRoot A x) ≤ matrixMass A * spinBound x := by
  classical
  unfold spinBound preRoot
  calc
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖*secondTailBound (x j) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [secondTailBound_smul] using secondTailBound_sum Finset.univ (fun j => A i j • x j)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖*spinBound x := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (secondTailBound_le_spinBound x j) (norm_nonneg _)
    _ = _ := by simp only [matrixMass,Finset.sum_mul,spinBound]

@[simp] theorem spinCoe_preRoot (A : Matrix (Fin 2) (Fin 2) ℂ) (x : PreSpin E) :
    spinCoe (preRoot A x)=SpinOperators.act A (spinCoe x) := by
  ext i
  simp only [spinCoe_apply,preRoot,SpinOperators.act_apply,Fin.sum_univ_two,UniformSpace.Completion.coe_add,
    UniformSpace.Completion.coe_smul]

theorem norm_spin_le_sum (x : SpinSpace E) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have he : ‖x‖^2 = ‖x 0‖^2+‖x 1‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
  rw [Fin.sum_univ_two]
  nlinarith [norm_nonneg x,norm_nonneg (x 0),norm_nonneg (x 1),
    mul_nonneg (norm_nonneg (x 0)) (norm_nonneg (x 1))]

def spinField (v : E) (x : PreSpin E) : SpinSpace E :=
  WithLp.toLp 2 (fun i => preField v (x i))
@[simp] theorem spinField_apply (v : E) (x : PreSpin E) (i : Fin 2) :
    spinField v x i=preField v (x i) := rfl

@[simp] theorem spinField_preRoot (A : Matrix (Fin 2) (Fin 2) ℂ) (v : E) (x : PreSpin E) :
    spinField v (preRoot A x)=SpinOperators.act A (spinField v x) := by
  ext i
  simp only [spinField_apply,preRoot,SpinOperators.act_apply,map_sum,map_smul]

theorem WZ_spinField_sub_le (h v : E) (x : PreSpin E) :
    ‖WZ h (spinField v x)-spinField v x‖ ≤ 2*‖h‖*‖v‖*spinBound x := by
  calc
    _ ≤ ∑ i, ‖(WZ h (spinField v x)-spinField v x) i‖ := norm_spin_le_sum _
    _ ≤ ∑ i, 2*‖h‖*‖v‖*secondTailBound (x i) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [PiLp.sub_apply,WZ_apply,spinField_apply]
      split_ifs
      · exact W_preField_sub_le h v (x i)
      · simpa only [norm_neg] using W_preField_sub_le (-h) v (x i)
    _ = _ := by simp only [spinBound,Finset.mul_sum]

end CoherentFock

namespace CoherentFock
open Complex
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

def preZ (x : PreSpin E) : PreSpin E := fun i => if i=0 then x i else -x i

def zField (v : E) (x : PreSpin E) : SpinSpace E := spinField v (preZ x)

@[simp] theorem zField_apply (v : E) (x : PreSpin E) (i : Fin 2) :
    zField v x i=if i=0 then preField v (x i) else -preField v (x i) := by
  simp only [zField,spinField_apply,preZ]
  split_ifs <;> simp

omit [InnerProductSpace ℂ E] in
theorem spinBound_preZ (x : PreSpin E) : spinBound (preZ x)=spinBound x := by
  unfold spinBound
  apply Finset.sum_congr rfl
  intro i hi
  simp only [preZ]
  split_ifs
  · rfl
  · simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using secondTailBound_smul (-1) (x i)

theorem norm_spinField_le (v : E) (x : PreSpin E) :
    ‖spinField v x‖ ≤ ‖v‖*spinBound x := by
  calc
    _ ≤ ∑ i, ‖spinField v x i‖ := norm_spin_le_sum _
    _ ≤ ∑ i, ‖v‖*secondTailBound (x i) :=
      Finset.sum_le_sum (fun i _ => norm_preField_le v (x i))
    _ = _ := by simp only [spinBound,Finset.mul_sum]

theorem norm_zField_le (v : E) (x : PreSpin E) :
    ‖zField v x‖ ≤ ‖v‖*spinBound x := by
  simpa only [zField,spinBound_preZ] using norm_spinField_le v (preZ x)

theorem zField_real_smul (r : ℝ) (v : E) (x : PreSpin E) :
    zField (r • v) x=r • zField v x := by
  ext i
  simp only [zField,spinField_apply,PiLp.smul_apply,preField_real_smul]

theorem zField_sub (v w : E) (x : PreSpin E) :
    zField (v-w) x=zField v x-zField w x := by
  ext i
  simp only [zField,spinField_apply,PiLp.sub_apply,preField_sub]

theorem WZ_taylor (v : E) (x : PreSpin E) :
    ‖WZ v (spinCoe x)-spinCoe x-I • zField v x‖ ≤ ‖v‖^2*spinBound x := by
  calc
    _ ≤ ∑ i, ‖(WZ v (spinCoe x)-spinCoe x-I • zField v x) i‖ := norm_spin_le_sum _
    _ ≤ ∑ i, ‖v‖^2*secondTailBound (x i) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [PiLp.sub_apply,PiLp.smul_apply,WZ_apply,spinCoe_apply,zField_apply]
      split_ifs
      · exact W_coe_taylor v (x i)
      · simpa only [preField_neg,norm_neg] using W_coe_taylor (-v) (x i)
    _ = _ := by simp only [spinBound,Finset.mul_sum]

def probe (A : Matrix (Fin 2) (Fin 2) ℂ) (v : E) : SpinSpace E →L[ℂ] SpinSpace E :=
  (SpinOperators.act A.conjTranspose).comp ((WZ v).comp (SpinOperators.act A))

def probeField (A : Matrix (Fin 2) (Fin 2) ℂ) (v : E) (x : PreSpin E) : SpinSpace E :=
  SpinOperators.act A.conjTranspose (zField v (preRoot A x))

@[simp] theorem probe_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (v : E) (x : SpinSpace E) :
    probe A v x=SpinOperators.act A.conjTranspose (WZ v (SpinOperators.act A x)) := rfl

theorem root_left_inverse (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (x : SpinSpace E) : SpinOperators.act A.conjTranspose (SpinOperators.act A x)=x := by
  have hh : A.conjTranspose*A=1 := (Unitary.mem_iff.mp hA).1
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => SpinOperators.act (H := Space E) B x) hh
  simpa only [SpinOperators.act_mul,ContinuousLinearMap.comp_apply,SpinOperators.act_one,
    ContinuousLinearMap.id_apply] using h

theorem root_adjoint_unitary (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) :
    A.conjTranspose ∈ unitary _ := by
  exact Unitary.star_mem hA

@[simp] theorem norm_probe (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (v : E) (x : SpinSpace E) : ‖probe A v x‖=‖x‖ := by
  rw [probe_apply,SpinOperators.norm_act (root_adjoint_unitary A hA),norm_WZ,SpinOperators.norm_act hA]

theorem probe_taylor (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (v : E) (x : PreSpin E) :
    ‖probe A v (spinCoe x)-spinCoe x-I • probeField A v x‖ ≤
      ‖v‖^2*matrixMass A*spinBound x := by
  have he : probe A v (spinCoe x)-spinCoe x-I • probeField A v x =
      SpinOperators.act A.conjTranspose
        (WZ v (spinCoe (preRoot A x))-spinCoe (preRoot A x)-I • zField v (preRoot A x)) := by
    simp only [map_sub,map_smul,spinCoe_preRoot,root_left_inverse A hA,probe_apply,probeField]
  rw [he,SpinOperators.norm_act (root_adjoint_unitary A hA)]
  exact (WZ_taylor v (preRoot A x)).trans (by
    have hh := mul_le_mul_of_nonneg_left (spinBound_preRoot A x) (sq_nonneg ‖v‖)
    simpa only [mul_assoc] using hh)

theorem probeField_eq_spinField (A : Matrix (Fin 2) (Fin 2) ℂ) (v : E) (x : PreSpin E) :
    probeField A v x=spinField v (preRoot A.conjTranspose (preZ (preRoot A x))) := by
  simp only [probeField,zField,spinField_preRoot]

theorem probeField_real_smul (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (v : E) (x : PreSpin E) :
    probeField A (r • v) x=r • probeField A v x := by
  simp only [probeField,zField_real_smul,ContinuousLinearMap.map_smul_of_tower]

theorem probeField_sub (A : Matrix (Fin 2) (Fin 2) ℂ) (v w : E) (x : PreSpin E) :
    probeField A (v-w) x=probeField A v x-probeField A w x := by
  simp only [probeField,zField_sub,map_sub]

theorem norm_probeField_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (v : E) (x : PreSpin E) : ‖probeField A v x‖ ≤ ‖v‖*matrixMass A*spinBound x := by
  rw [probeField,SpinOperators.norm_act (root_adjoint_unitary A hA)]
  exact (norm_zField_le v (preRoot A x)).trans (by
    have hh := mul_le_mul_of_nonneg_left (spinBound_preRoot A x) (norm_nonneg v)
    simpa only [mul_assoc] using hh)

theorem probe_cross (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (h v : E) (x : PreSpin E) :
    ‖probe A h (probeField B v x)-probeField B v x‖ ≤
      2*‖h‖*‖v‖*matrixMass A*matrixMass B.conjTranspose*matrixMass B*spinBound x := by
  have he : probe A h (probeField B v x)-probeField B v x =
      SpinOperators.act A.conjTranspose
      (WZ h (SpinOperators.act A (probeField B v x))-SpinOperators.act A (probeField B v x)) := by
    simp only [map_sub,root_left_inverse A hA,probe_apply]
  rw [he,SpinOperators.norm_act (root_adjoint_unitary A hA),probeField_eq_spinField,
    ← spinField_preRoot]
  have hM (C : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ matrixMass C :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have ht : spinBound (preRoot A (preRoot B.conjTranspose (preZ (preRoot B x)))) ≤
      matrixMass A*(matrixMass B.conjTranspose*(matrixMass B*spinBound x)) := by
    calc
      _ ≤ matrixMass A*spinBound (preRoot B.conjTranspose (preZ (preRoot B x))) := spinBound_preRoot _ _
      _ ≤ matrixMass A*(matrixMass B.conjTranspose*spinBound (preZ (preRoot B x))) := by
        exact mul_le_mul_of_nonneg_left (spinBound_preRoot B.conjTranspose _) (hM A)
      _ = matrixMass A*(matrixMass B.conjTranspose*spinBound (preRoot B x)) := by rw [spinBound_preZ]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spinBound_preRoot B x) (hM B.conjTranspose)) (hM A)
  exact (WZ_spinField_sub_le h v _).trans (by
    have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*‖h‖*‖v‖)
    simpa only [mul_assoc] using hh)

end CoherentFock

end

end OAI
