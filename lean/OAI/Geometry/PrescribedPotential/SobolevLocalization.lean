import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevParametrix

namespace OAI

/-! Sobolev Localization. -/

section

 

noncomputable section
open Filter Topology MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Laplacian Real

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma schwartz_deriv_product (v : E) (g φ : 𝓢(E, ℂ)) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ (⇑(∂_{v} g : 𝓢(E, ℂ))) φ +
      SchwartzMap.smulLeftCLM ℂ g (∂_{v} φ) := by
  ext x
  have he : (SchwartzMap.smulLeftCLM ℂ g φ : E → ℂ) = fun y => g y * φ y := by
    ext y
    simp [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, he, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (∂_{v} g).hasTemperateGrowth, smul_eq_mul]
  rw [fderiv_fun_mul g.differentiableAt φ.differentiableAt]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

 
lemma weak_deriv_product (v : E) (g : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (smulLeftCLM ℂ g u) = smulLeftCLM ℂ (⇑(∂_{v} g : 𝓢(E, ℂ))) u +
      smulLeftCLM ℂ g (∂_{v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply, map_neg]
  rw [schwartz_deriv_product, map_add]
  abel

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma multiplier_add {g h : E → ℂ} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (u : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (g + h) u = fourierMultiplierCLM ℂ g u +
      fourierMultiplierCLM ℂ h u := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh]

lemma bessel_two_laplacian (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 u = u - (((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹ • Δ u := by
  have hpi : (((2 * Real.pi)^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi)^2 ≠ 0)
  have hlo := TemperedDistribution.laplacian_eq_fourierMultiplierCLM u
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_neg] at hlo
  change Δ u = -(((2 * Real.pi)^2 : ℝ) : ℂ) • _ at hlo
  rw [hlo, smul_smul, mul_neg, inv_mul_cancel₀ hpi, neg_one_smul,
    sub_neg_eq_add]
  unfold besselPotential
  have hs : (fun x : E => (((1 + ‖x‖^2)^((2:ℝ)/2) : ℝ) : ℂ)) =
      (fun _ : E => (1:ℂ)) + (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    ext x
    norm_num
  rw [hs, multiplier_add (by fun_prop) (by fun_prop)]
  simp

lemma memSobolev_sum {ι : Type*} (s : ℝ) (S : Finset ι) (u : ι → 𝓢'(E, ℂ))
    (hu : ∀ i ∈ S, MemSobolev s 2 (u i)) : MemSobolev s 2 (∑ i ∈ S, u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self ..)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

 
lemma memSobolev_of_laplacian {s : ℝ} {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) : MemSobolev (s + 2) 2 u := by
  rw [add_comm, ← memSobolev_besselPotential_iff]
  rw [bessel_two_laplacian]
  exact hu.sub (hΔ.smul _)

lemma memSobolev_of_second_basis {s : ℝ} {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u)
    (hD : ∀ j, MemSobolev s 2 (∂_{stdOrthonormalBasis ℝ E j}
      (∂_{stdOrthonormalBasis ℝ E j} u))) : MemSobolev (s + 2) 2 u := by
  apply memSobolev_of_laplacian hu
  rw [TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  exact memSobolev_sum _ _ _ (fun j _ => hD j)

lemma memSobolev_zero_mul_schwartz (g : 𝓢(E, ℂ)) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev 0 2 u) : MemSobolev 0 2 (smulLeftCLM ℂ g u) := by
  obtain ⟨v, hv⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  refine ⟨multiply g.toBoundedContinuousFunction v, ?_⟩
  rw [hv, multiply_distribution _ g.hasTemperateGrowth]
  rfl

 

theorem memSobolev_even_mul_schwartz (k : ℕ) (g : 𝓢(E, ℂ)) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev (2 * (k : ℝ)) 2 u) :
    MemSobolev (2 * (k : ℝ)) 2 (smulLeftCLM ℂ g u) := by
  induction k generalizing g u with
  | zero => simpa using memSobolev_zero_mul_schwartz g (by simpa using hu)
  | succ k ih =>
    have he : 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
    rw [he] at hu ⊢
    apply memSobolev_of_second_basis (ih g (hu.mono (by linarith)))
    intro j
    let v := stdOrthonormalBasis ℝ E j
    have hu' : MemSobolev (2 * (k : ℝ)) 2 (∂_{v} u) :=
      hu.lineDerivOp.mono (by linarith)
    have hu'' : MemSobolev (2 * (k : ℝ)) 2 (∂_{v} (∂_{v} u)) :=
      hu.lineDerivOp.lineDerivOp.mono (by linarith)
    change MemSobolev _ _ (∂_{v} (∂_{v} (smulLeftCLM ℂ g u)))
    rw [weak_deriv_product, lineDerivOp_add, weak_deriv_product, weak_deriv_product]
    exact ((ih _ (hu.mono (by linarith))).add (ih _ hu')).add
      ((ih _ hu').add (ih _ hu''))

 

def liftOperatorValue (s t : ℝ) (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (hT : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (T u)) (u : L2 E) : L2 E :=
  ((memSobolev_iff_realize t (T (realize s u))).mp
    (hT _ (realize_memSobolev s u))).choose

lemma realize_liftOperatorValue (s t : ℝ) (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (hT : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (T u)) (u : L2 E) :
    realize t (liftOperatorValue s t T hT u) = T (realize s u) :=
  ((memSobolev_iff_realize t _).mp (hT _ (realize_memSobolev s u))).choose_spec

def liftOperatorLinear (s t : ℝ)
    (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (hT : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (T u)) : L2 E →ₗ[ℂ] L2 E where
  toFun := liftOperatorValue s t T hT
  map_add' u v := by
    apply realize_injective t
    simp only [map_add, realize_liftOperatorValue]
  map_smul' c u := by
    apply realize_injective t
    simp only [map_smul, realize_liftOperatorValue, RingHom.id_apply]

lemma realize_liftOperatorLinear (s t : ℝ)
    (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (hT : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (T u)) (u : L2 E) :
    realize t (liftOperatorLinear s t T hT u) = T (realize s u) :=
  ((memSobolev_iff_realize t _).mp (hT _ (realize_memSobolev s u))).choose_spec

def liftOperator (s t : ℝ) (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (hT : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (T u)) : L2 E →L[ℂ] L2 E where
  toLinearMap := liftOperatorLinear s t T hT
  cont := by
    apply LinearMap.continuous_of_seq_closed_graph
    intro u x y hu hv
    apply realize_injective t
    have h₁ := ((realize t).continuous.tendsto y).comp hv
    have h₂ := (T.continuous.tendsto (realize s x)).comp
      (((realize s).continuous.tendsto x).comp hu)
    change Tendsto (fun n => realize t (liftOperatorLinear s t T hT (u n)))
      atTop (nhds (realize t y)) at h₁
    simp_rw [realize_liftOperatorLinear] at h₁
    exact (tendsto_nhds_unique h₁ h₂).trans (realize_liftOperatorLinear s t T hT x).symm

lemma realize_liftOperator (s t : ℝ)
    (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (hT : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (T u)) (u : L2 E) :
    realize t (liftOperator s t T hT u) = T (realize s u) :=
  realize_liftOperatorLinear s t T hT u

 
def cutoff (k : ℕ) (g : 𝓢(E, ℂ)) : L2 E →L[ℂ] L2 E :=
  liftOperator (2 * (k : ℝ)) (2 * (k : ℝ)) (smulLeftCLM ℂ g)
    (fun _ hu => memSobolev_even_mul_schwartz k g hu)

lemma realize_cutoff (k : ℕ) (g : 𝓢(E, ℂ)) (u : L2 E) :
    realize (2 * (k : ℝ)) (cutoff k g u) =
      smulLeftCLM ℂ g (realize (2 * (k : ℝ)) u) :=
  realize_liftOperator _ _ _ _ _

end SobolevChart

end
end

end OAI
