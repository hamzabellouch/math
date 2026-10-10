import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityUniformRemainder
import OAI.Probability.Perceptron.Cavity.CavitySphericalMoments
import OAI.Probability.Perceptron.Cavity.CavityShellPerturbation

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

def cavityJoinedPatterns (N L M : ℕ) (a : Fin M→Fin N→ℝ) (y : Fin M→Spin L) :
    Fin M→Fin (N+L)→ℝ := fun i=>Fin.addCases (a i) (fun j=>y i j)

lemma cavityJoinedPatterns_projection (N L M : ℕ) (a : Fin M→Fin N→ℝ)
    (y : Fin M→Spin L) (x : NormalizedSpin N) (z : Spin L) (i : Fin M) :
    (∑ j,cavityJoinedPatterns N L M a y i j*cavityNormalizedVec N L x z j)=
      cavityRho N L z*(∑ j,a i j*x.val j)+inner ℝ z (y i)/Real.sqrt (N+L:ℕ) := by
  rw [Fin.sum_univ_add]
  simp only [cavityJoinedPatterns,cavityNormalizedVec,gaussianBlockJoin,PiLp.toLp_apply,
    Fin.addCases_left,Fin.addCases_right,PiLp.smul_apply,smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [Finset.mul_sum,Finset.sum_div]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · apply Finset.sum_congr rfl
    intro j _hj
    ring

lemma cavityShellPatternEnergy_join (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) (s : CavityShellSpin n L) :
    cavityShellPatternEnergy n L M f (cavityJoinedPatterns (n+1) L M a y) s=
      ∑ i,f (Real.sqrt (1-‖s.2.val‖^2/((n+1:ℕ)+L))*(∑ j,a i j*s.1.val j)+
        inner ℝ s.2.val (y i)/Real.sqrt ((n+1:ℕ)+L)) := by
  unfold cavityShellPatternEnergy normalizedPatternEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  change (∑ j,cavityJoinedPatterns (n+1) L M a y i j*cavityNormalizedVec (n+1) L s.1 s.2.val j)=_
  rw [cavityJoinedPatterns_projection]
  simp only [cavityRho,Nat.cast_add]

def cavityShellTaylorModel (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (y : Fin M→Spin L) (s : CavityShellSpin n L) : ℝ :=
  normalizedPatternEnergy (n+1) M f.f a s.1+
    (cavityLinearField M L (fun i=>f.d1 (∑ j,a i j*s.1.val j))
      (Real.sqrt (n+1:ℕ))⁻¹ s.2.val y+
      ‖s.2.val‖^2/2*bulkC (n+1) M f a s.1+
      cavityQuadraticField M L (fun i=>f.d2 (∑ j,a i j*s.1.val j))
        (1/(2*(n+1:ℕ))) s.2.val y)

theorem cavity_true_shell_expansion (n L M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*(L+1)≤n+1)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M a y) s-
      cavityShellTaylorModel n L M f a y s|≤
      ∑ i,cavityRemainderMajorant (cavityRemainderCoefficients f h1 h2 h3 L (L+1)) (n+1:ℕ) ‖y i‖ := by
  have hnR : (2:ℝ)*((L:ℝ)+1)≤(n+1:ℕ) := by exact_mod_cast hn
  have hz : ‖s.2.val‖^2≤(L:ℝ)+1:=s.2.prop.2
  have hρ : ‖s.2.val‖^2<(n+1:ℕ)+L := by nlinarith [Nat.cast_nonneg (α:=ℝ) L]
  rw [cavityShellPatternEnergy_join]
  change |(∑ i,_) - (_+_)|≤_
  rw [←sub_sub]
  exact (cavity_pattern_sum_expansion n M L f h1 h2 h3 a s.1 s.2.val y hρ).trans
    (Finset.sum_le_sum fun i _hi=>cavityTaylorError_inner_le f h1 h2 h3 L (by positivity)
      (by positivity) hnR s.2.val (y i) hz)

lemma cavity_true_shell_error_tendsto (M : ℕ→ℕ) (L : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) {α : ℝ}
    (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>∫ y : Fin (M n)→Spin L,
      ∑ i,cavityRemainderMajorant (cavityRemainderCoefficients f h1 h2 h3 L (L+1)) (n+1:ℕ) ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin L))) atTop (𝓝 0) :=
  cavityRemainderMajorant_row_tendsto M L _ hM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianRows_basis (n : ℕ) (σ : ℝ) (y : Spin (n+1)) :
    gaussianRows (fun i : Fin (n+1)=>σ • EuclideanSpace.single i (1:ℝ)) y=σ •y := by
  ext i
  simp [gaussianRows_apply,real_inner_smul_left,EuclideanSpace.inner_single_left]

lemma gaussianRows_isotropic_law (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) :
    (stdGaussian E).map (gaussianRows v)=
      (stdGaussian (Spin (n+1))).map (fun y=>Real.sqrt b •y) := by
  have hg : Matrix.gram ℝ v=Matrix.gram ℝ (fun i : Fin (n+1)=>Real.sqrt b • EuclideanSpace.single i (1:ℝ)) := by
    ext i j
    simp only [Matrix.gram_apply,hv,inner_smul_left,inner_smul_right,conj_trivial]
    by_cases h : i=j
    · subst j
      simp [Real.sq_sqrt hb,←pow_two]
    · simp [EuclideanSpace.inner_single_left,h]
  rw [gaussianRows_map_stdGaussian,hg,←gaussianRows_map_stdGaussian]
  congr 1
  funext y
  exact gaussianRows_basis n (Real.sqrt b) y

lemma gaussianRows_spherical_average (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    (∫ g,sphericalExp n (gaussianRows v g) R ∂stdGaussian E)=Real.exp (R^2*b/2) := by
  rw [←integral_map (gaussianRows v).measurable.aemeasurable
    (sphericalExp_continuous n R).aestronglyMeasurable,gaussianRows_isotropic_law n v hb hv,
    integral_map (by fun_prop) (sphericalExp_continuous n R).aestronglyMeasurable]
  have h:=sphericalExp_gaussian_average n R (Real.sqrt b) 0
  have hz : sphericalExp n 0 R=1 := by simp [sphericalExp]
  simpa only [zero_add,Real.sq_sqrt hb,hz,mul_one] using h

lemma gaussianRows_spherical_memLp (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    MemLp (fun g=>sphericalExp n (gaussianRows v g) R) 2 (stdGaussian E) := by
  have hm := (sphericalExp_continuous n R).comp (gaussianRows v).continuous
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi : Integrable (fun g=>sphericalExp n (gaussianRows v g) (2*R)) (stdGaussian E) := by
    by_contra hn
    have h:=gaussianRows_spherical_average n v hb hv (2*R)
    rw [integral_undef hn] at h
    exact (Real.exp_pos _).ne' h.symm
  apply hi.mono' (hm.pow 2).aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sphericalExp_square_le n R _

lemma gaussianRows_spherical_second (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    (∫ g,sphericalExp n (gaussianRows v g) R^2 ∂stdGaussian E)≤Real.exp (2*R^2*b) := by
  have hs := (memLp_two_iff_integrable_sq
    ((gaussianRows_spherical_memLp n v hb hv R).aestronglyMeasurable)).mp
    (gaussianRows_spherical_memLp n v hb hv R)
  have hi := (gaussianRows_spherical_memLp n v hb hv (2*R)).integrable (by norm_num)
  apply (integral_mono hs hi (fun g=>sphericalExp_square_le n R _)).trans_eq
  rw [gaussianRows_spherical_average n v hb hv]
  congr 1
  ring
end SphericalPerceptronFreeEnergy
end

end OAI
