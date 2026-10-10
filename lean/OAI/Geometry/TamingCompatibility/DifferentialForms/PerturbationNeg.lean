import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.SecondDerivative
import OAI.Geometry.TamingCompatibility.DifferentialForms.GreenNeg

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def perturbationNegOne (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    H E F 1 →L[ℂ] H E F (-1) :=
  ∑ i, ∑ j, (productNegOne (F := F) (a i j)).comp
    (secondDerivative (F := F) (-1) (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E j))

lemma toDistribution_perturbationNegOne
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F 1) :
    toDistribution E F (-1) (perturbationNegOne a u) =
      differentialPerturbation a (toDistribution E F 1 u) := by
  have hs (i j : basisIndex E) :
      toDistribution E F (-1) (secondDerivative (-1)
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) u) =
      ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j}
        (toDistribution E F 1 u)) := by
    have h := toDistribution_secondDerivative (-1)
      (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) u
    have he : (-1:ℝ)+2 = 1 := by norm_num
    simpa only [toDistribution, he] using h
  simp only [perturbationNegOne, differentialPerturbation, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, toDistribution_productNegOne, hs]

lemma perturbedHelmholtz_negOne_toDistribution
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F 1) :
    perturbedHelmholtz a (toDistribution E F 1 u) =
      toDistribution E F (-1) (u + perturbationNegOne a u) := by
  have hh : EuclideanGreen.helmholtz (toDistribution E F 1 u) =
      toDistribution E F (-1) u := by
    have h := helmholtz_toDistribution (-1) u
    have he : (-1:ℝ)+2=1 := by norm_num
    simpa only [toDistribution, he] using h
  rw [perturbedHelmholtz, hh, map_add, toDistribution_perturbationNegOne]

def weakPrincipalCoefficientSize
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) : ℝ :=
  ∑ i, ∑ j, coefficientSize 1 (a i j) *
    ‖secondDerivative (F := F) (-1) (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖

lemma weakPrincipalCoefficientSize_nonneg
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    0 ≤ weakPrincipalCoefficientSize (F := F) a :=
  Finset.sum_nonneg (fun _i _ => Finset.sum_nonneg (fun _j _ =>
    mul_nonneg (coefficientSize_nonneg _ _) (norm_nonneg _)))

lemma perturbationNegOne_norm_le {C : ℝ}
    (hp : ∀ g : 𝓢(E,ℂ), ‖productNegOne (F := F) g‖ ≤ C * coefficientSize 1 g)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    ‖perturbationNegOne (F := F) a‖ ≤ C * weakPrincipalCoefficientSize (F := F) a := by
  unfold perturbationNegOne weakPrincipalCoefficientSize
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right (hp (a i j))
        (norm_nonneg (secondDerivative (F := F) (-1)
          (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)))))

theorem perturbedHelmholtz_solve_negOne
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbationNegOne (F := F) a‖ < 1) {f : 𝓢'(E,F)}
    (hf : MemSobolev (-1) 2 f) :
    ∃! u : 𝓢'(E,F), MemSobolev 1 2 u ∧ perturbedHelmholtz a u = f := by
  have hf' : f ∈ Set.range (toDistribution E F (-1)) := by
    rw [range_toDistribution]
    exact hf
  obtain ⟨v, hv⟩ := hf'
  obtain ⟨w, hw, hu⟩ := Neumann.existsUnique (perturbationNegOne (F := F) a) ha v
  refine ⟨toDistribution E F 1 w, ⟨toDistribution_memSobolev _ _, ?_⟩, ?_⟩
  · rw [perturbedHelmholtz_negOne_toDistribution, hw, hv]
  · intro z hz
    have hz' : z ∈ Set.range (toDistribution E F 1) := by
      rw [range_toDistribution]
      exact hz.1
    obtain ⟨q, hq⟩ := hz'
    have he : q + perturbationNegOne a q = v := by
      apply toDistribution_injective (-1)
      rw [← perturbedHelmholtz_negOne_toDistribution, hq, hz.2, hv]
    rw [← hq, hu q he]

theorem weak_H1_regular
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u) (hf : MemSobolev 0 2 (perturbedHelmholtz a u)) :
    MemSobolev 2 2 u := by
  have hf' : MemSobolev (0:ℕ) 2 (perturbedHelmholtz a u) := by
    simpa only [Nat.cast_zero] using hf
  obtain ⟨v, hv, _⟩ := perturbedHelmholtz_solve 0 a hstrong hf'
  have hv2 : MemSobolev 2 2 v := by simpa only [Nat.cast_zero, zero_add] using hv.1
  obtain ⟨w, _, hw⟩ := perturbedHelmholtz_solve_negOne a hweak
    (hf.mono (show (-1:ℝ) ≤ 0 by norm_num))
  have hu_eq : u = w := hw u ⟨hu, rfl⟩
  have hv_eq : v = w := hw v ⟨hv2.mono (by norm_num), hv.2⟩
  rwa [hu_eq, ← hv_eq]

theorem weak_succ_regular (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbation (F := F) n a‖ < 1)
    (hstrong : ‖perturbation (F := F) (n+1) a‖ < 1) {u : 𝓢'(E,F)}
    (hu : MemSobolev ((n:ℝ)+2) 2 u)
    (hf : MemSobolev ((n:ℝ)+1) 2 (perturbedHelmholtz a u)) :
    MemSobolev ((n:ℝ)+3) 2 u := by
  have hf' : MemSobolev (n+1:ℕ) 2 (perturbedHelmholtz a u) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hf
  obtain ⟨v, hv, _⟩ := perturbedHelmholtz_solve (n+1) a hstrong hf'
  have hv3 : MemSobolev ((n:ℝ)+3) 2 v := by
    convert hv.1 using 1
    push_cast
    ring
  obtain ⟨w, _, hw⟩ := perturbedHelmholtz_solve n a hweak
    (hf.mono (show (n:ℝ) ≤ (n:ℝ)+1 by linarith))
  have hu_eq : u = w := hw u ⟨hu, rfl⟩
  have hv_eq : v = w := hw v ⟨hv3.mono (by linarith), hv.2⟩
  rwa [hu_eq, ← hv_eq]


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma coefficient_products_commute (g h : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F h u) =
      smulLeftCLM F h (smulLeftCLM F g u) := by
  rw [smulLeftCLM_smulLeftCLM_apply g.hasTemperateGrowth h.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply h.hasTemperateGrowth g.hasTemperateGrowth]
  rw [mul_comm (g : E → ℂ) (h : E → ℂ)]

def secondCommutator (g : 𝓢(E,ℂ)) (v w : E) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  smulLeftCLM F (∂_{v} (∂_{w} g) : 𝓢(E,ℂ)) u +
  smulLeftCLM F (∂_{w} g : 𝓢(E,ℂ)) (∂_{v} u) +
  smulLeftCLM F (∂_{v} g : 𝓢(E,ℂ)) (∂_{w} u)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma distribution_second_product (g : 𝓢(E,ℂ)) (v w : E) (u : 𝓢'(E,F)) :
    ∂_{v} (∂_{w} (smulLeftCLM F g u)) =
      smulLeftCLM F g (∂_{v} (∂_{w} u)) + secondCommutator g v w u := by
  rw [distribution_derivative_product, LineDeriv.lineDerivOp_add,
    distribution_derivative_product, distribution_derivative_product]
  unfold secondCommutator
  abel

lemma secondCommutator_memSobolev (n : ℕ) (g : 𝓢(E,ℂ)) (v w : E)
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (secondCommutator g v w u) := by
  have huv : MemSobolev n 2 (∂_{v} u) := by
    convert hu.lineDerivOp (m := v) using 1
    ring
  have huw : MemSobolev n 2 (∂_{w} u) := by
    convert hu.lineDerivOp (m := w) using 1
    ring
  exact ((memSobolev_nat_product n _ (hu.mono (by linarith))).add
    (memSobolev_nat_product n _ huv)).add (memSobolev_nat_product n _ huw)

def localizationError (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  -(((2*Real.pi)^2)⁻¹ : ℝ) • ∑ i, secondCommutator g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) u +
  ∑ i, ∑ j, smulLeftCLM F (a i j) (secondCommutator g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) u)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma helmholtz_cutoff (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    EuclideanGreen.helmholtz (smulLeftCLM F g u) =
      smulLeftCLM F g (EuclideanGreen.helmholtz u) -
      (((2*Real.pi)^2)⁻¹ : ℝ) • ∑ i : basisIndex E, secondCommutator g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) u := by
  simp only [EuclideanGreen.helmholtz,
    TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E),
    distribution_second_product, Finset.sum_add_distrib, smul_add,
    map_sub, ContinuousLinearMap.map_smul_of_tower, map_sum]
  abel

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma perturbedHelmholtz_cutoff
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    perturbedHelmholtz a (smulLeftCLM F g u) =
      smulLeftCLM F g (perturbedHelmholtz a u) + localizationError a g u := by
  simp only [perturbedHelmholtz, helmholtz_cutoff, differentialPerturbation,
    distribution_second_product, map_add, map_sum, Finset.sum_add_distrib,
    coefficient_products_commute (g := g), localizationError, neg_smul]
  abel

lemma localizationError_memSobolev (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (localizationError a g u) := by
  apply MemSobolev.add
  · exact (memSobolev_sum _ _ (fun _i _ => secondCommutator_memSobolev n g _ _ hu)).smul _
  · exact memSobolev_sum _ _ (fun i _ => memSobolev_sum _ _
      (fun j _ => memSobolev_nat_product n (a i j) (secondCommutator_memSobolev n g _ _ hu)))

theorem cutoff_H1_regular
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev 1 2 u)
    (hf : MemSobolev 0 2 (smulLeftCLM F g (perturbedHelmholtz a u))) :
    MemSobolev 2 2 (smulLeftCLM F g u) := by
  apply weak_H1_regular a hweak hstrong
  · have hu1 : MemSobolev (1:ℕ) 2 u := by simpa only [Nat.cast_one] using hu
    simpa only [Nat.cast_one] using memSobolev_nat_product (E := E) (F := F) 1 g hu1
  · rw [perturbedHelmholtz_cutoff]
    apply hf.add
    have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
    simpa only [Nat.cast_zero] using localizationError_memSobolev 0 a g hu'

def lowerOrder (b : basisIndex E → 𝓢(E,ℂ)) (c : 𝓢(E,ℂ))
    (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  smulLeftCLM F c u + ∑ i, smulLeftCLM F (b i) (∂_{stdOrthonormalBasis ℝ E i} u)

lemma lowerOrder_memSobolev (n : ℕ) (b : basisIndex E → 𝓢(E,ℂ)) (c : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (lowerOrder b c u) := by
  apply (memSobolev_nat_product n c (hu.mono (by linarith))).add
  apply memSobolev_sum
  intro i _
  apply memSobolev_nat_product
  convert hu.lineDerivOp (m := stdOrthonormalBasis ℝ E i) using 1
  ring

theorem full_operator_H1_regular
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : basisIndex E → 𝓢(E,ℂ)) (c : 𝓢(E,ℂ)) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u)
    (hf : MemSobolev 0 2 (perturbedHelmholtz a u + lowerOrder b c u)) :
    MemSobolev 2 2 u := by
  apply weak_H1_regular a hweak hstrong hu
  have hl : MemSobolev 0 2 (lowerOrder b c u) := by
    have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
    simpa only [Nat.cast_zero] using lowerOrder_memSobolev 0 b c hu'
  simpa only [add_sub_cancel_right] using hf.sub hl

end TamingCompatibility.HilbertSobolev

end

end OAI
