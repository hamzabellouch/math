import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Form

namespace OAI


noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms ExteriorForms
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [FiniteDimensional ℝ E] in
def covectorWedge (a b : E →L[ℝ] ℝ) : MetricForms.Form E 2 :=
  wedgeOne a (ofSubsingletonLIE (0 : Fin 1) b)
omit [FiniteDimensional ℝ E] in
lemma covectorWedge_apply (a b : E →L[ℝ] ℝ) (u v : E) :
    covectorWedge a b ![u,v] = a u * b v - a v * b u := by
  rw [covectorWedge,wedgeOne_apply_two]
  rfl

def realPart (g : Metric E) (b : Fin 4 → E) : MetricForms.Form E 2 :=
  covectorWedge (g.bilinear (b 0)) (g.bilinear (b 2)) -
    covectorWedge (g.bilinear (b 1)) (g.bilinear (b 3))
def imagPart (g : Metric E) (b : Fin 4 → E) : MetricForms.Form E 2 :=
  covectorWedge (g.bilinear (b 0)) (g.bilinear (b 3)) +
    covectorWedge (g.bilinear (b 1)) (g.bilinear (b 2))

omit [FiniteDimensional ℝ E] in
lemma realPart_apply (g : Metric E) (b : Fin 4 → E) (u v : E) :
    realPart g b ![u,v] =
      (g.bilinear (b 0) u * g.bilinear (b 2) v - g.bilinear (b 0) v * g.bilinear (b 2) u) -
      (g.bilinear (b 1) u * g.bilinear (b 3) v - g.bilinear (b 1) v * g.bilinear (b 3) u) := by
  simp only [realPart,ContinuousAlternatingMap.sub_apply,covectorWedge_apply]
omit [FiniteDimensional ℝ E] in
lemma imagPart_apply (g : Metric E) (b : Fin 4 → E) (u v : E) :
    imagPart g b ![u,v] =
      (g.bilinear (b 0) u * g.bilinear (b 3) v - g.bilinear (b 0) v * g.bilinear (b 3) u) +
      (g.bilinear (b 1) u * g.bilinear (b 2) v - g.bilinear (b 1) v * g.bilinear (b 2) u) := by
  simp only [imagPart,ContinuousAlternatingMap.add_apply,covectorWedge_apply]

lemma frame_ext (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    {a c : MetricForms.Form E 2} (h : ∀ i j, a ![b i,b j] = c ![b i,b j]) : a = c := by
  let B := (basisOfFrame g hdim b hb).toBasis.map (equiv g).toLinearEquiv
  have hB (i : Fin 4) : B i = b i := by
    simp only [B,Module.Basis.map_apply,OrthonormalBasis.coe_toBasis,basisOfFrame_apply]
    rfl
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => B)
  intro v
  change a (fun i => B (v i)) = c (fun i => B (v i))
  have hv : (fun i => B (v i)) = ![b (v 0),b (v 1)] := by
    ext i
    rw [hB]
    fin_cases i <;> rfl
  rw [hv]
  exact h _ _

omit [FiniteDimensional ℝ E] in
lemma eval_neg_left (a : MetricForms.Form E 2) (u v : E) : a ![-u,v] = -a ![u,v] := by
  simpa only [neg_one_smul,smul_eq_mul,neg_one_mul] using a.vecCons_smul ![v] (-1 : ℝ) u
omit [FiniteDimensional ℝ E] in
lemma eval_neg_right (a : MetricForms.Form E 2) (u v : E) : a ![u,-v] = -a ![u,v] := by
  rw [two_swap,eval_neg_left,two_swap,neg_neg]
omit [FiniteDimensional ℝ E] in
lemma eval_self (a : MetricForms.Form E 2) (u : E) : a ![u,u] = 0 :=
  a.map_eq_zero_of_eq ![u,u] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2) ≠ 1)

section Unitary
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)

include hdim hb h0 h1 h2 h3 in
lemma realPart_antiInvariant : (realPart g b).compContinuousLinearMap J = -realPart g b := by
  apply frame_ext g hdim b hb
  intro i j
  rw [MetricForms.comp_two,ContinuousAlternatingMap.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [h0,h1,h2,h3,eval_neg_left,eval_neg_right,realPart_apply,hb]
include hdim hb h0 h1 h2 h3 in
lemma imagPart_antiInvariant : (imagPart g b).compContinuousLinearMap J = -imagPart g b := by
  apply frame_ext g hdim b hb
  intro i j
  rw [MetricForms.comp_two,ContinuousAlternatingMap.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [h0,h1,h2,h3,eval_neg_left,eval_neg_right,imagPart_apply,hb]

include hdim hb h0 h1 h2 h3 in
lemma expansion (a : MetricForms.Form E 2) (ha : a.compContinuousLinearMap J = -a) :
    a = a ![b 0,b 2] • realPart g b + a ![b 0,b 3] • imagPart g b := by
  have h01 := congrArg (fun c : MetricForms.Form E 2 => c ![b 0,b 1]) ha
  have h23 := congrArg (fun c : MetricForms.Form E 2 => c ![b 2,b 3]) ha
  have h02 := congrArg (fun c : MetricForms.Form E 2 => c ![b 0,b 2]) ha
  have h03 := congrArg (fun c : MetricForms.Form E 2 => c ![b 0,b 3]) ha
  simp only [MetricForms.comp_two,h0,h1,h2,h3,eval_neg_right,
    ContinuousAlternatingMap.neg_apply] at h01 h23 h02 h03
  rw [two_swap] at h01 h23
  have hz01 : a ![b 0,b 1] = 0 := by linarith
  have hz23 : a ![b 2,b 3] = 0 := by linarith
  have he12 : a ![b 1,b 2] = a ![b 0,b 3] := by linarith
  apply frame_ext g hdim b hb
  intro i j
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,
    smul_eq_mul,realPart_apply,imagPart_apply,hb]
  fin_cases i <;> fin_cases j
  all_goals simp [eval_self, hz01, hz23, h02, he12]
  all_goals first | rw [two_swap a (b 0) (b 1), hz01] <;> simp
                  | rw [two_swap a (b 0) (b 2)]
                  | rw [two_swap a (b 0) (b 3)]
                  | rw [two_swap a (b 1) (b 2), he12]
                  | rw [two_swap a (b 1) (b 3), h02] <;> simp
                  | rw [two_swap a (b 2) (b 3), hz23]; simp

end Unitary

lemma realPart_smooth {g : D → Metric E} {b : Fin 4 → D → E} {U : Set D}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun x => realPart (g x) (fun i => b i x)) U := by
  apply FormSmooth.contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have hv : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1)] := by ext i; fin_cases i <;> rfl
  simp only [hv,realPart_apply]
  exact (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)) |>.sub
    ((((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)))
lemma imagPart_smooth {g : D → Metric E} {b : Fin 4 → D → E} {U : Set D}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun x => imagPart (g x) (fun i => b i x)) U := by
  apply FormSmooth.contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have hv : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1)] := by ext i; fin_cases i <;> rfl
  simp only [hv,imagPart_apply]
  exact (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)) |>.add
    ((((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)))
end TamingCompatibility.AntiInvariantFrame

end

end OAI
