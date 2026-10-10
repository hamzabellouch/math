import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrozenEnergy

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma alternating_swap (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) :
    a ![v,u] = -a ![u,v] := by
  have hv : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.map_swap ![u,v] (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_sum_left {ι : Type*} (a : E [⋀^Fin 2]→L[ℝ] ℝ)
    (s : Finset ι) (f : ι → E) (v : E) :
    a ![∑ i ∈ s, f i, v] = ∑ i ∈ s, a ![f i,v] := by
  have hu (w : E) : Function.update ![0,v] (0 : Fin 2) w = ![w,v] := by
    ext i
    fin_cases i <;> simp
  simpa only [hu,ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.toAlternatingMap.map_update_sum s 0 f ![0,v]

lemma alternating_smul_left (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![c • u,v] = c * a ![u,v] := by
  simpa only [smul_eq_mul] using a.vecCons_smul ![v] c u

lemma alternating_sum_right {ι : Type*} (a : E [⋀^Fin 2]→L[ℝ] ℝ)
    (s : Finset ι) (f : ι → E) (u : E) :
    a ![u, ∑ i ∈ s, f i] = ∑ i ∈ s, a ![u,f i] := by
  rw [alternating_swap,alternating_sum_left,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [alternating_swap,neg_neg]

lemma alternating_smul_right (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![u,c • v] = c * a ![u,v] := by
  rw [alternating_swap,alternating_smul_left,alternating_swap]
  ring

lemma alternating_self (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) : a ![u,u] = 0 :=
  a.map_eq_zero_of_eq ![u,u] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_frame_eval (a : E [⋀^Fin 2]→L[ℝ] ℝ) (b : Fin 4 → E) (v w : V) :
    a ![∑ i : Fin 4, v i • b i, ∑ i : Fin 4, w i • b i] =
      ⟪WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
        a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]], wedge v w⟫ := by
  rw [alternating_sum_left]
  simp_rw [alternating_sum_right,alternating_smul_left,alternating_smul_right]
  simp [Fin.sum_univ_succ,alternating_self,wedge,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  rw [alternating_swap a (b 0) (b 1),alternating_swap a (b 0) (b 2),
    alternating_swap a (b 0) (b 3),alternating_swap a (b 1) (b 2),
    alternating_swap a (b 1) (b 3),alternating_swap a (b 2) (b 3)]
  ring

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E) :
    UnitaryFrame.V :=
  (basisOfFrame g hdim b hb).repr (ofOriginal g u)

lemma directionCoordinates_apply (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E) (i : Fin 4) :
    directionCoordinates g hdim b hb u i = g.bilinear (b i) u := by
  rw [directionCoordinates,OrthonormalBasis.repr_apply_apply,basisOfFrame_apply]
  rfl

lemma sum_directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E) :
    ∑ i : Fin 4, directionCoordinates g hdim b hb u i • b i = u := by
  have h := congrArg (equiv g) ((basisOfFrame g hdim b hb).sum_repr (ofOriginal g u))
  have he (x : E) : equiv g (ofOriginal g x) = x := rfl
  simpa only [map_sum,map_smul,basisOfFrame_apply,he,directionCoordinates] using h

lemma norm_directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E)
    (hu : g.bilinear u u = 1) : ‖directionCoordinates g hdim b hb u‖ = 1 := by
  rw [directionCoordinates,LinearIsometryEquiv.norm_map]
  have h : ‖ofOriginal g u‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hu
  nlinarith [norm_nonneg (ofOriginal g u)]

omit [FiniteDimensional ℝ E] in
lemma complex_frame_sum (b : Fin 4 → E) (j : E →L[ℝ] E)
    (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2) (v : UnitaryFrame.V) :
    j (∑ i : Fin 4, v i • b i) = ∑ i : Fin 4, UnitaryFrame.J v i • b i := by
  simp [Fin.sum_univ_succ,UnitaryFrame.J,h0,h1,h2,h3]
  abel

lemma directionCoordinates_eval (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (j : E →L[ℝ] E) (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2)
    (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) :
    a ![u,j u] =
      ⟪WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
        a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]],
        UnitaryFrame.line (directionCoordinates g hdim b hb u)⟫ := by
  let v := directionCoordinates g hdim b hb u
  have hv : ∑ i : Fin 4, v i • b i = u := sum_directionCoordinates g hdim b hb u
  have hw : ∑ i : Fin 4, UnitaryFrame.J v i • b i = j u := by
    rw [← complex_frame_sum b j h0 h1 h2 h3,hv]
  calc
    _ = a ![∑ i : Fin 4, v i • b i, ∑ i : Fin 4, UnitaryFrame.J v i • b i] := by rw [hv,hw]
    _ = _ := UnitaryFrame.alternating_frame_eval a b v (UnitaryFrame.J v)

end TamingCompatibility.HodgeFrame

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma coordinates_eq_six (b : Fin 4 → E) (a : MetricForms.Form E 2) :
    coordinates b a = WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
      a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]] := by
  ext i
  fin_cases i <;> rfl

variable [FiniteDimensional ℝ E]
lemma coordinates_direction_eval (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (j : E →L[ℝ] E) (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2)
    (a : MetricForms.Form E 2) (u : E) :
    a ![u,j u] = ⟪coordinates b a,UnitaryFrame.line (directionCoordinates g hdim b hb u)⟫ := by
  rw [coordinates_eq_six]
  exact directionCoordinates_eval g hdim b hb j h0 h1 h2 h3 a u
end TamingCompatibility.HodgeFrame

end
end

end OAI
