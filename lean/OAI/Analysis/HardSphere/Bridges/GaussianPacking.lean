import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeResidual

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking
abbrev Point := Fin 3 → ℝ
def square (x : Point) : ℝ := ∑j,x j^2
def kernel (b : ℝ) (x : Point) : ℝ := Real.exp (-b*square x)
def cube (q : Point) (δ : ℝ) : Set Point := Icc (fun j ↦ q j-δ) (fun j ↦ q j+δ)

lemma kernel_product (b : ℝ) (x : Point) : kernel b x=∏j,Real.exp (-b*x j^2) := by
  rw [kernel,square,Finset.mul_sum,Real.exp_sum]

lemma kernel_integrable {b : ℝ} (hb : 0<b) : Integrable (kernel b) volume := by
  rw [show kernel b = (fun x : Point ↦ ∏j,Real.exp (-b*x j^2)) from funext (kernel_product b)]
  exact Integrable.fintype_prod (fun _ ↦ integrable_exp_neg_mul_sq hb)

lemma kernel_integral (b : ℝ) : (∫x,kernel b x)=(Real.sqrt (Real.pi/b))^3 := by
  simp only [kernel_product]
  convert integral_fintype_prod_volume_eq_prod (fun (_ : Fin 3) (y : ℝ) ↦ Real.exp (-b*y^2)) using 1
  simp only [integral_gaussian,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cube_real_volume (q : Point) {δ : ℝ} (hδ : 0≤δ) : volume.real (cube q δ)=(2*δ)^3 := by
  rw [Measure.real,cube,Real.volume_Icc_pi_toReal (by intro j; dsimp; linarith)]
  simp only [show ∀j,(q j+δ)-(q j-δ)=2*δ by intro j; ring,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cube_coord {q y : Point} {δ : ℝ} (hy : y∈cube q δ) (j : Fin 3) :
    |y j-q j|≤δ := by
  rw [abs_le]
  constructor <;> have h1:=hy.1 j <;> have h2:=hy.2 j <;> dsimp at * <;> linarith

lemma square_triangle (x y : Point) : square (x+y)≤2*square x+2*square y := by
  simp only [square,Pi.add_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  nlinarith [sq_nonneg (x j-y j)]

lemma square_le_of_coord {x : Point} {δ : ℝ} (hδ : 0≤δ) (hx : ∀j,|x j|≤δ) :
    square x≤3*δ^2 := by
  unfold square
  calc
    _ ≤ ∑_j : Fin 3,δ^2 := Finset.sum_le_sum (fun j _ ↦ by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hx j))
    _ = _ := by simp [Finset.sum_const]

lemma cube_kernel_lower {b δ : ℝ} (hb : 0≤b) (hδ : 0≤δ) (x q : Point)
    {y : Point} (hy : y∈cube q δ) :
    kernel b (x-q) ≤ Real.exp (3*b*δ^2)*kernel (b/2) (x-y) := by
  have ht : square (x-y)≤2*square (x-q)+6*δ^2 := by
    have he : x-y=(x-q)+(q-y) := by ext j; simp
    rw [he]
    apply (square_triangle _ _).trans
    have hx : square (q-y)≤3*δ^2 := square_le_of_coord hδ (fun j ↦ by
      simpa only [Pi.sub_apply,abs_sub_comm] using cube_coord hy j)
    linarith
  rw [kernel,kernel,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left ht hb]

lemma cubes_disjoint {m : ℕ} (q : Fin m → Point) {ε δ : ℝ} (hε : 0<ε) (hδ : 0≤δ)
    (hδε : 4*δ≤ε) (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    Pairwise (fun i j ↦ Disjoint (cube (q i) δ) (cube (q j) δ)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro y hyi hyj
  have hxy : square (q i-q j)≤3*(2*δ)^2 := square_le_of_coord (by positivity) (fun k ↦ by
    have h1:=cube_coord hyi k
    have h2:=cube_coord hyj k
    rw [abs_le] at h1 h2 ⊢
    change -(2*δ)≤q i k-q j k ∧ q i k-q j k≤2*δ
    constructor <;> linarith)
  have he := hsep i j hij
  have hd : (4*δ)^2≤ε^2 := (sq_le_sq₀ (by positivity) hε.le).mpr hδε
  nlinarith [sq_pos_of_pos hε]

lemma kernel_translate_integrable {b : ℝ} (hb : 0 < b) (x : Point) :
    Integrable (fun y ↦ kernel b (x-y)) volume :=
  (integrable_comp_sub_left (kernel b) x).mpr (kernel_integrable hb)

lemma sum_kernel_le {m : ℕ} (q : Fin m → Point) (x : Point)
    {b ε δ : ℝ} (hb : 0 < b) (hε : 0 < ε) (hδ : 0 < δ)
    (hδε : 4*δ ≤ ε) (hsep : ∀i j, i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,kernel b (x-q i)) ≤
      Real.exp (3*b*δ^2)*(Real.sqrt (Real.pi/(b/2)))^3/(2*δ)^3 := by
  have hi := kernel_translate_integrable (by positivity : 0 < b/2) x
  have hp := cubes_disjoint q hε hδ.le hδε hsep
  have hc (i : Fin m) : (2*δ)^3*kernel b (x-q i) ≤
      Real.exp (3*b*δ^2)*∫y in cube (q i) δ,kernel (b/2) (x-y) := by
    have hn : (∫y in cube (q i) δ, kernel b (x-q i)) ≤
        ∫y in cube (q i) δ,Real.exp (3*b*δ^2)*kernel (b/2) (x-y) := by
      apply integral_mono_ae (integrableOn_const (μ:=volume) (s:=cube (q i) δ) (C:=kernel b (x-q i)) (IsCompact.measure_lt_top isCompact_Icc).ne)
        ((hi.const_mul _).integrableOn)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact cube_kernel_lower hb.le hδ.le x (q i) hy
    simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,
      cube_real_volume _ hδ.le,integral_const_mul] using hn
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ hc i)
  rw [←Finset.mul_sum,←Finset.mul_sum] at hs
  have heu : (∫y in ⋃i,cube (q i) δ,kernel (b/2) (x-y)) = ∑i,∫y in cube (q i) δ,kernel (b/2) (x-y) :=
    integral_iUnion_fintype (fun i ↦ (measurableSet_Icc : MeasurableSet (cube (q i) δ))) hp (fun _ ↦ hi.integrableOn)
  rw [←heu] at hs
  have hm : (∫y in ⋃i,cube (q i) δ,kernel (b/2) (x-y)) ≤
      (Real.sqrt (Real.pi/(b/2)))^3 := by
    apply (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun y ↦ (Real.exp_pos _).le)) hi).trans_eq
    exact (integral_sub_left_eq_self (kernel (b/2)) volume x).trans (kernel_integral _)
  have ht := hs.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
  exact (le_div_iff₀ (by positivity : 0 < (2*δ)^3)).mpr (by simpa only [mul_comm] using ht)

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking
abbrev Noise := Fin 3 → C(Time,ℝ)
def law : Measure Noise := Measure.pi (fun _ ↦ bridgeLaw)
instance : IsProbabilityMeasure law := by unfold law; infer_instance

def eval (s : Time) (β : Noise) : Point := fun j ↦ β j s
def remainder (s : Time) (β : Noise) : Noise := fun j ↦ bridgeRemainder s (β j)
lemma eval_measurable (s : Time) : Measurable (eval s) :=
  Measurable.of_eval fun coordinate ↦
    (continuous_eval_const s).measurable.comp (measurable_pi_apply coordinate)
lemma remainder_measurable (s : Time) : Measurable (remainder s) := by unfold remainder; fun_prop

def variance (s : Time) : ℝ≥0 := Real.toNNReal ((s:ℝ)-(s:ℝ)^2)
lemma scalar_eval (s : Time) : bridgeLaw.map (fun β : C(Time,ℝ) ↦ β s)=gaussianReal 0 (variance s) := by
  rw [bridgeLaw,Measure.map_map (continuous_eval_const s).measurable measurable_bridge]
  exact (bridge_eval_law s).map_eq
lemma scalar_remainder (s : Time) : bridgeLaw.map (bridgeRemainder s)=
    bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β) := by
  rw [bridgeLaw,Measure.map_map (bridgeRemainder s).continuous.measurable measurable_bridge]
  exact bridgeRemainder_law s
lemma scalar_joint (s : Time) : bridgeLaw.map (fun β : C(Time,ℝ) ↦ (β s,bridgeRemainder s β))=
    (gaussianReal 0 (variance s)).prod (bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β)) := by
  rw [bridgeLaw,Measure.map_map (by fun_prop) measurable_bridge]
  simp only [Function.comp_def]
  have hj := (bridgeRemainder_independent s).map_prod_eq_prod_map_map
    (((continuous_eval_const s).measurable.comp measurable_bridge).aemeasurable)
    (((bridgeRemainder s).continuous.measurable.comp measurable_bridge).aemeasurable)
  simp only [Function.comp_def] at hj
  rw [(bridge_eval_law s).map_eq,bridgeRemainder_law] at hj
  exact hj

lemma eval_law (s : Time) : law.map (eval s)=Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (variance s)) := by
  unfold law eval
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ β s) from (continuous_eval_const s).measurable).aemeasurable)]
  simp_rw [scalar_eval]
lemma remainder_law (s : Time) : law.map (remainder s)=
    law.map (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j) := by
  unfold law remainder
  rw [Measure.pi_map_pi (fun _ ↦ (bridgeRemainder s).continuous.measurable.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ Real.sqrt (1-(s:ℝ)) • β) from by fun_prop).aemeasurable)]
  simp_rw [scalar_remainder]

lemma joint_law (s : Time) : law.map (fun β ↦ (eval s β,remainder s β))=
    (Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (variance s))).prod (law.map (remainder s)) := by
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ C(Time,ℝ) (Fin 3)
    (fun _ ↦ gaussianReal 0 (variance s)) (fun _ ↦ bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β))
  have he : law.map (fun β : Noise ↦ fun j ↦ (β j s,bridgeRemainder s (β j)))=
      Measure.pi (fun _ : Fin 3 ↦ (gaussianReal 0 (variance s)).prod (bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β))) := by
    unfold law
    rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ (β s,bridgeRemainder s β)) from by fun_prop).aemeasurable)]
    simp_rw [scalar_joint]
  rw [remainder_law]
  have her : law.map (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j)=
      Measure.pi (fun _ : Fin 3 ↦ bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β)) := by
    unfold law
    rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ Real.sqrt (1-(s:ℝ)) • β) from by fun_prop).aemeasurable)]
  rw [her,←hp.map_eq,←he,Measure.map_map hp.measurable (by fun_prop)]
  rfl

lemma independent (s : Time) : IndepFun (eval s) (remainder s) law :=
  (indepFun_iff_map_prod_eq_prod_map_map (eval_measurable s).aemeasurable (remainder_measurable s).aemeasurable).mpr
    (by rw [eval_law]; exact joint_law s)

end HardSphere.Bridge

end
end

end

end OAI
