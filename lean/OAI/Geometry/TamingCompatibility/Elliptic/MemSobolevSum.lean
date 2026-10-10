import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Helmholtz

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap Laplacian ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolev_sum {ι : Type*} (s : Finset ι) {t : ℝ} (f : ι → 𝓢'(E,F))
    (h : ∀ i ∈ s, MemSobolev t 2 (f i)) : MemSobolev t 2 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma memSobolev_of_laplacian {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  apply (EuclideanGreen.memSobolev_helmholtz_iff s 2 u).mp
  exact hu.sub (hd.smul _)

lemma memSobolev_succ_of_derivatives {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hl : MemSobolev (s-1) 2 (Δ u) := by
    rw [TemperedDistribution.laplacian_eq_sum b]
    exact memSobolev_sum _ _ (fun i _ => (hd i).lineDerivOp)
  have hm := memSobolev_of_laplacian (hu.mono (show s-1 ≤ s by linarith)) hl
  convert hm using 1
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_derivative_product (g φ : 𝓢(E,ℂ)) (v : E) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ (∂_{v} g : 𝓢(E,ℂ)) φ +
      SchwartzMap.smulLeftCLM ℂ g (∂_{v} φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply]
  have hf : (SchwartzMap.smulLeftCLM ℂ g φ : E → ℂ) = (⇑g * ⇑φ) := by
    ext y
    simp [g.hasTemperateGrowth, smul_eq_mul]
  rw [hf, fderiv_mul g.differentiableAt φ.differentiableAt]
  simp [g.hasTemperateGrowth,
    (∂_{v} g : 𝓢(E,ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, mul_comm, add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma distribution_derivative_product (g : 𝓢(E,ℂ)) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} (smulLeftCLM F g u) =
      smulLeftCLM F (∂_{v} g : 𝓢(E,ℂ)) u + smulLeftCLM F g (∂_{v} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply_apply,
    add_apply, map_neg]
  rw [schwartz_derivative_product]
  simp only [map_add, neg_add_rev]
  abel

lemma memSobolev_zero_product (g : 𝓢(E,ℂ)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨f,hf⟩ := hu
  have he : u = (f : 𝓢'(E,F)) := by simpa using hf
  rw [he]
  let b := g.toBoundedContinuousFunction
  let w : Lp F 2 (volume : Measure E) := ((b.memLp_top (μ := volume)).toLp b) • f
  refine ⟨w, ?_⟩
  simp only [besselPotential_zero, ContinuousLinearMap.id_apply]
  exact (Lp.toTemperedDistribution_smul_eq (g.hasTemperateGrowth) (b.memLp_top (μ := volume)) f).symm

theorem memSobolev_nat_product (n : ℕ) (g : 𝓢(E,ℂ)) {u : 𝓢'(E,F)}
    (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing g u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_product g hu
  | succ n ih =>
    have hu' : MemSobolev n 2 u := hu.mono (by exact_mod_cast Nat.le_succ n)
    have hp := ih g hu'
    have hd (i : Fin (Module.finrank ℝ E)) :
        MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} (smulLeftCLM F g u)) := by
      rw [distribution_derivative_product]
      have hdu : MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} u) := by
        convert hu.lineDerivOp using 1
        simp
      exact (ih _ hu').add (ih g hdu)
    simpa using memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) hp hd

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
