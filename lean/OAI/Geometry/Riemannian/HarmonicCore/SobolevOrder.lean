import OAI.Geometry.Riemannian.HarmonicCore.ClassicalDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

def CompactSobolev : ℕ → ValueL2 → Prop
  | 0, _ => True
  | n+1, f => ∃ R : ℝ, ∃ u : ZeroSobolev R, sobolevValue R u = f ∧
      ∀ a : E3, CompactSobolev n (componentL2 a (sobolevDerivative R u))

lemma sobolevDerivative_eq_of_value_eq (R S : ℝ) (u : ZeroSobolev R) (v : ZeroSobolev S)
    (h : sobolevValue R u = sobolevValue S v) :
    sobolevDerivative R u = sobolevDerivative S v := by
  have he : includeSobolev (le_max_left R S) u = includeSobolev (le_max_right R S) v :=
    sobolevValue_injective (max R S) h
  exact congrArg (sobolevDerivative (max R S)) he

lemma CompactSobolev.zero (n : ℕ) : CompactSobolev n 0 := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨0,0,by simp,fun a ↦ by simpa using ih⟩

lemma CompactSobolev.lower {n : ℕ} {f : ValueL2} (hf : CompactSobolev (n+1) f) : CompactSobolev n f := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    obtain ⟨R,u,hu,hd⟩ := hf
    exact ⟨R,u,hu,fun a ↦ ih (hd a)⟩

lemma CompactSobolev.gradient {n : ℕ} {f : ValueL2} (hf : CompactSobolev (n+1) f)
    (R : ℝ) (u : ZeroSobolev R) (hu : sobolevValue R u = f) (a : E3) :
    CompactSobolev n (componentL2 a (sobolevDerivative R u)) := by
  obtain ⟨S,v,hv,hd⟩ := hf
  rw [sobolevDerivative_eq_of_value_eq R S u v (hu.trans hv.symm)]
  exact hd a

lemma CompactSobolev.add {n : ℕ} {f g : ValueL2} (hf : CompactSobolev n f) (hg : CompactSobolev n g) :
    CompactSobolev n (f+g) := by
  induction n generalizing f g with
  | zero => trivial
  | succ n ih =>
    obtain ⟨R,u,hu,hd⟩ := hf
    obtain ⟨S,v,hv,he⟩ := hg
    refine ⟨max R S,includeSobolev (le_max_left R S) u+includeSobolev (le_max_right R S) v,?_,?_⟩
    · change sobolevValue R u+sobolevValue S v=f+g
      rw [hu,hv]
    · intro a
      change CompactSobolev n (componentL2 a (sobolevDerivative R u+sobolevDerivative S v))
      rw [map_add]
      exact ih (hd a) (he a)

lemma CompactSobolev.smul {n : ℕ} {f : ValueL2} (hf : CompactSobolev n f) (c : ℝ) :
    CompactSobolev n (c • f) := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    obtain ⟨R,u,hu,hd⟩ := hf
    refine ⟨R,c • u,by rw [map_smul,hu],fun a ↦ ?_⟩
    rw [map_smul,map_smul]
    exact ih (hd a)

lemma CompactSobolev.sum {ι : Type*} {n : ℕ} (s : Finset ι) (f : ι → ValueL2)
    (h : ∀ i ∈ s, CompactSobolev n (f i)) : CompactSobolev n (∑ i ∈ s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CompactSobolev.zero n
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

lemma smooth_direction_contDiff {χ : E3 → ℝ} (hχ : ContDiff ℝ ∞ χ) (a : E3) :
    ContDiff ℝ ∞ (fun x ↦ fderiv ℝ χ x a) :=
  (hχ.fderiv_right (by simp)).clm_apply contDiff_const

lemma cutoffSobolev_direction (R T : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R) (K D : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (u : ZeroSobolev T) (a : E3)
    (Ka : ℝ) (hKa : ∀ x, ‖fderiv ℝ χ x a‖ ≤ Ka) :
    componentL2 a (sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u)) =
      scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u))+
      scalarFieldCLM (fun x ↦ fderiv ℝ χ x a)
        (smooth_direction_contDiff hχ a).continuous Ka hKa (sobolevValue T u) := by
  apply Lp.ext
  filter_upwards [componentL2_coe a (sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u)),
    cutoffSobolev_derivative_coe R T χ hχ hsupp K D hK hD u,
    Lp.coeFn_add (scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)))
      (scalarFieldCLM (fun x ↦ fderiv ℝ χ x a) (smooth_direction_contDiff hχ a).continuous Ka hKa (sobolevValue T u)),
    scalarFieldCLM_coe χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)),
    scalarFieldCLM_coe (fun x ↦ fderiv ℝ χ x a) (smooth_direction_contDiff hχ a).continuous Ka hKa (sobolevValue T u),
    componentL2_coe a (sobolevDerivative T u)] with x h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,Pi.add_apply,h4,h5,h6,inner_add_right,inner_smul_right,inner_smul_right,inner_gradient_right]
  simp only [conj_trivial,smul_eq_mul]
  congr 1
  exact mul_comm _ _

theorem CompactSobolev.smooth_mul {n : ℕ} {f : ValueL2} (hf : CompactSobolev n f)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (K : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) :
    CompactSobolev n (scalarFieldCLM χ hχ.continuous K hK f) := by
  induction n generalizing f χ K with
  | zero => trivial
  | succ n ih =>
    obtain ⟨R,u,hu,hd⟩ := hf
    obtain ⟨S,_,hs⟩ := hc.isBounded.subset_ball_lt (0:ℝ) (0:E3)
    obtain ⟨D,hD⟩ := continuous_compact_bound (_root_.gradient χ) (gradient_continuous hχ) (gradient_compact hc)
    refine ⟨S,cutoffSobolev S R χ hχ hs K D hK hD u,?_,fun a ↦ ?_⟩
    · change scalarFieldCLM χ hχ.continuous K hK (sobolevValue R u)=_
      rw [hu]
    · let θ : E3 → ℝ := fun x ↦ fderiv ℝ χ x a
      have hθ : ContDiff ℝ ∞ θ := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
      have hcθ : HasCompactSupport θ := hc.fderiv_apply ℝ a
      obtain ⟨Ka,hKa⟩ := continuous_compact_bound θ hθ.continuous hcθ
      rw [cutoffSobolev_direction S R χ hχ hs K D hK hD u a Ka hKa]
      exact (ih (hd a) χ hχ hc K hK).add
        (ih (CompactSobolev.lower (show CompactSobolev (n+1) (sobolevValue R u) from ⟨R,u,rfl,hd⟩)) θ hθ hcθ Ka hKa)



lemma CompactSobolev.exists_common_graph {ι : Type*} [Fintype ι] (f : ι → ValueL2)
    (h : ∀ i, CompactSobolev 1 (f i)) :
    ∃ R : ℝ, ∃ u : ι → ZeroSobolev R, ∀ i, sobolevValue R (u i) = f i := by
  classical
  choose R u hu hd using h
  let S : ℝ := ∑ i,|R i|
  have hRS (i) : R i ≤ S := (le_abs_self _).trans
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (R j)) (Finset.mem_univ i))
  exact ⟨S,fun i ↦ includeSobolev (hRS i) (u i),hu⟩

lemma CompactSobolev.mono {m n : ℕ} {f : ValueL2} (hf : CompactSobolev n f) (hmn : m ≤ n) :
    CompactSobolev m f := by
  induction n with
  | zero => have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
            subst m
            exact hf
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl|hlt
    · exact hf
    · exact ih hf.lower (Nat.le_of_lt_succ hlt)

lemma CompactSobolev.coefficient {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    {n : ℕ} (V : DerivativeL2) (hV : ∀ i, CompactSobolev n (componentL2 (b i) V))
    (B : E3 → E3 →L[ℝ] E3) (hB : ContDiff ℝ ∞ B) (hc : HasCompactSupport B)
    (C : ℝ) (hC : ∀ x, ‖B x‖ ≤ C) (a : E3) :
    CompactSobolev n (componentL2 a (coefficientCLM B C hB.continuous.aestronglyMeasurable hC V)) := by
  classical
  let θ : ι → E3 → ℝ := fun i x ↦ ⟪a,B x (b i)⟫_ℝ
  have hθ (i) : ContDiff ℝ ∞ (θ i) := ContDiff.inner ℝ contDiff_const (hB.clm_apply contDiff_const)
  have hcθ (i) : HasCompactSupport (θ i) := hc.mono (matrix_component_support B a (b i))
  choose K hK using fun i ↦ continuous_compact_bound (θ i) (hθ i).continuous (hcθ i)
  have he : componentL2 a (coefficientCLM B C hB.continuous.aestronglyMeasurable hC V) =
      ∑ i,scalarFieldCLM (θ i) (hθ i).continuous (K i) (hK i) (componentL2 (b i) V) := by
    conv_lhs => rw [←vectorize_component_sum b V,map_sum,map_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ coefficient_component_vectorize B hB.continuous C hC a (b i)
      (θ i) (hθ i).continuous (K i) (hK i) (fun _ ↦ rfl) _)
  rw [he]
  exact CompactSobolev.sum Finset.univ _ (fun i _ ↦ (hV i).smooth_mul (θ i) (hθ i) (hcθ i) (K i) (hK i))

lemma componentL2_vectorize (a b : E3) (u : ValueL2) :
    componentL2 a (vectorizeL2 b u) = ⟪a,b⟫_ℝ • u := by
  apply Lp.ext
  filter_upwards [componentL2_coe a (vectorizeL2 b u),vectorizeL2_coe b u,
    Lp.coeFn_smul ⟪a,b⟫_ℝ u] with x h1 h2 h3
  rw [h1,h2,h3,Pi.smul_apply,inner_smul_right]
  simp only [smul_eq_mul,mul_comm]

lemma CompactSobolev.vector_sum {ι : Type*} [Fintype ι] {n : ℕ} (b : ι → E3)
    (f : ι → ValueL2) (hf : ∀ i, CompactSobolev n (f i)) (a : E3) :
    CompactSobolev n (componentL2 a (∑ i,vectorizeL2 (b i) (f i))) := by
  rw [map_sum]
  simp only [componentL2_vectorize]
  exact CompactSobolev.sum _ _ (fun i _ ↦ (hf i).smul _)

lemma scalarFieldCLM_mul (χ ψ : E3 → ℝ) (hχ : Continuous χ) (hψ : Continuous ψ)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖ψ x‖ ≤ D)
    (h : ∀ x, χ x*ψ x=χ x) (f : ValueL2) :
    scalarFieldCLM χ hχ K hK (scalarFieldCLM ψ hψ D hD f) = scalarFieldCLM χ hχ K hK f := by
  apply Lp.ext
  filter_upwards [scalarFieldCLM_coe χ hχ K hK (scalarFieldCLM ψ hψ D hD f),
    scalarFieldCLM_coe ψ hψ D hD f,scalarFieldCLM_coe χ hχ K hK f] with x h1 h2 h3
  rw [h1,h2,h3]
  simp only [smul_eq_mul,←mul_assoc,h]

lemma weak_forced_cutoff_restrict (R S T : ℝ) (hRS : R ≤ S)
    (A : E3 → E3 →L[ℝ] E3) (C : ℝ) (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hC : ∀ x, ‖A x‖ ≤ C) (u : ZeroSobolev T) (F : DerivativeL2)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = ⟪F,sobolevDerivative S v⟫_ℝ)
    (ψ : E3 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Metric.ball 0 S)
    (K D : ℝ) (hK : ∀ x, ‖ψ x‖ ≤ K) (hD : ∀ x, ‖gradient ψ x‖ ≤ D)
    (hψ1 : ∀ x ∈ Metric.closedBall (0:E3) R, ψ x = 1)
    (hdψ : ∀ x ∈ Metric.closedBall (0:E3) R, gradient ψ x = 0) :
    ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hC (sobolevDerivative S (cutoffSobolev S T ψ hψ hsupp K D hK hD u)),
        sobolevDerivative R v⟫_ℝ = ⟪F,sobolevDerivative R v⟫_ℝ := by
  intro v
  have he := hu (includeSobolev hRS v)
  change ⟪coefficientCLM A C hA hC (sobolevDerivative T u),sobolevDerivative R v⟫_ℝ = ⟪F,sobolevDerivative R v⟫_ℝ at he
  rw [←he,coefficient_inner_integral,coefficient_inner_integral]
  apply integral_congr_ae
  filter_upwards [cutoffSobolev_derivative_coe S T ψ hψ hsupp K D hK hD u,
    sobolevDerivative_supported R v] with x h3 h4
  rw [h3]
  by_cases hx : x ∈ Metric.closedBall (0:E3) R
  · rw [hψ1 x hx,hdψ x hx,one_smul,smul_zero,add_zero]
  · rw [h4 hx]
    simp

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
