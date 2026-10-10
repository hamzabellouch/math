import OAI.Analysis.FiniteFactor.Diffuse.SupportLimit
import OAI.Analysis.FiniteFactor.Diffuse.TracePowers

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (v:H) : (H→L[ℂ]H)→ₗ[ℂ]ℂ where
  toFun T := inner ℂ v (T v)
  map_add' T S := inner_add_right v (T v) (S v)
  map_smul' c T := inner_smul_right v (T v) c

theorem support_trace_eq (M:VonNeumannAlgebra H) (v:H)
    (hcyclic:∀a b:M.toStarSubalgebra,
      inner ℂ v (((a*b:M.toStarSubalgebra):H→L[ℂ]H) v)=
      inner ℂ v (((b*a:M.toStarSubalgebra):H→L[ℂ]H) v))
    (T:M.toStarSubalgebra) (hT:‖(T:H→L[ℂ]H)‖≤1) :
    inner ℂ v (rangeSupport (T:H→L[ℂ]H) v)=
      inner ℂ v (rangeSupport (star (T:H→L[ℂ]H)) v) := by
  let t:H→L[ℂ]H := T
  let f:M.toStarSubalgebra→ₗ[ℂ]ℂ :=
    (vectorFunctional v).comp M.toStarSubalgebra.toSubmodule.subtype
  have hf : ∀a b,f (a*b)=f (b*a) := hcyclic
  have he : ∀n, inner ℂ v (cesaro (1-t*star t) n v)=
      inner ℂ v (cesaro (1-star t*t) n v) := by
    intro n
    change vectorFunctional v (cesaro (1-t*star t) n)=
      vectorFunctional v (cesaro (1-star t*t) n)
    simp only [cesaro,map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact trace_defect_pow f hf T (star T) k
  have hts : ‖star t‖≤1 := by simpa [t,ContinuousLinearMap.star_eq_adjoint] using hT
  have hl := Filter.Tendsto.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=v)) (cesaro_star_mul_tendsto (star t) hts v)
  have hr := Filter.Tendsto.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=v)) (cesaro_star_mul_tendsto t hT v)
  have hlim : inner ℂ v ((star t).ker.starProjection v)=
      inner ℂ v (t.ker.starProjection v) := by
    apply tendsto_nhds_unique hl
    apply hr.congr'
    exact Filter.Eventually.of_forall (fun n=>by simpa only [star_star] using (he n).symm)
  change inner ℂ v (rangeSupport t v)=inner ℂ v (rangeSupport (star t) v)
  rw [rangeSupport_eq_one_sub_kernel,rangeSupport_eq_one_sub_kernel,star_star]
  change inner ℂ v (v-(star t).ker.starProjection v)=inner ℂ v (v-t.ker.starProjection v)
  rw [inner_sub_right,inner_sub_right,hlim]

end Nonhyperlinear.Diffuseness

end

end OAI
