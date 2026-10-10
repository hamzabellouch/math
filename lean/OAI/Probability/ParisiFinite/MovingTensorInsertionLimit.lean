import Mathlib
import OAI.Probability.ParisiFinite.SecondCoefficient

namespace OAI

/-! Moving Tensor Insertion Limit. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
namespace FiniteTensor
open scoped InnerProductSpace Topology
open Filter QuantumCLT ContinuousLinearMap

 

theorem moving_tensor_insertion_limit
    {κ : Type*} (ι : ℕ → Type*)
    [∀n, Fintype (ι n)] [∀n, DecidableEq (ι n)] [∀n, Nonempty (ι n)]
    (Ω : ∀n, EuclideanSpace ℂ (ι n)) (l : List κ)
    (X : ∀n, κ → EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (S : ∀n, EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hΩ : ∀n, ‖Ω n‖=1) (hX : ∀n i, i ∈ l → ‖X n i‖ ≤ L) (hS : ∀n, ‖S n‖ ≤ K)
    (hc : ∀n, ⟪Ω n,(l.map (X n)).sum (Ω n)⟫_ℂ=0)
    (hSc : ∀n, ⟪Ω n,S n (Ω n)⟫_ℂ=0) {z v : ℂ}
    (hz : Tendsto (fun n => ⟪Ω n,(second (l.map (X n))) (Ω n)⟫_ℂ) atTop (𝓝 z))
    (hv : Tendsto (fun n => ⟪Ω n,S n ((l.map (X n)).sum (Ω n))⟫_ℂ) atTop (𝓝 v)) :
    Tendsto (fun n =>
      ⟪power n (Ω n),normalizedInsertion n
        (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹)
        (S n*generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹) (power n (Ω n))⟫_ℂ)
      atTop (𝓝 (v*Complex.exp z)) := by
  have hp (n : ℕ) : ‖vacuumFunctional (Ω n)‖ ≤ 1 := by
    simpa [hΩ n] using vacuumFunctional_norm (Ω n)
  have hq (n : ℕ) : ‖markedFunctional (Ω n) (S n)‖ ≤ K := by
    exact (markedFunctional_norm (Ω n) (S n)).trans (by simpa [hΩ n] using hS n)
  have h1 (n : ℕ) : vacuumFunctional (Ω n) 1=1 := by
    change ⟪Ω n,Ω n⟫_ℂ=1
    rw [inner_self_eq_norm_sq_to_K,hΩ n]
    norm_num
  have hs1 (n : ℕ) : markedFunctional (Ω n) (S n) 1=0 := by
    simpa using hSc n
  have hh := moving_generators_inserted_limit
    (fun n => EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    l X (fun n => vacuumFunctional (Ω n)) (fun n => markedFunctional (Ω n) (S n))
    L 1 K hL (by norm_num) hK hX hp hq h1 hs1 hc hz hv
  simpa only [inner_normalizedInsertion,vacuumFunctional_apply,markedFunctional_apply,
    mul_apply_eq_comp] using hh

end FiniteTensor

namespace CoherentFock
open scoped InnerProductSpace
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
 
def exponential (d : E) : Space E :=
  Complex.exp (Complex.ofReal (‖d‖^2/2)) • coherent d

@[simp] theorem inner_exponential (d e : E) :
    ⟪exponential d,exponential e⟫_ℂ=Complex.exp ⟪d,e⟫_ℂ := by
  simp only [exponential,inner_smul_left,inner_smul_right,inner_coherent,kernel,
    ←Complex.exp_conj,Complex.conj_ofReal]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem W_exponential (d x : E) :
    W d (exponential x)=
      Complex.exp (-Complex.ofReal (‖d‖^2/2)-⟪d,x⟫_ℂ) • exponential (d+x) := by
  simp only [exponential,map_smul,W_coherent,smul_smul,phase,←Complex.exp_add]
  congr 2
  rw [norm_add_sq (𝕜 := ℂ)]
  apply Complex.ext <;> simp <;> ring

end CoherentFock

namespace QuantumCLT
open scoped InnerProductSpace Topology
open CoherentFock Filter
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem weylProduct_exponential (ds : List E) (x : E) :
    weylProduct ds (exponential x)=
      Complex.exp (secondCoefficient (fun d e : E => -⟪d,e⟫_ℂ) ds-⟪ds.sum,x⟫_ℂ) •
        exponential (ds.sum+x) := by
  induction ds with
  | nil => simp [weylProduct,secondCoefficient]
  | cons d ds ih =>
    simp only [weylProduct,ContinuousLinearMap.comp_apply,ih,map_smul,W_exponential,
      smul_smul,←Complex.exp_add,List.sum_cons,secondCoefficient_gram_cons,
      inner_add_left,inner_add_right]
    rw [inner_self_eq_norm_sq_to_K]
    have h : secondCoefficient (fun d e : E => -⟪d,e⟫_ℂ) ds-⟪ds.sum,x⟫_ℂ+
        (-Complex.ofReal (‖d‖^2/2)-(⟪d,ds.sum⟫_ℂ+⟪d,x⟫_ℂ))=
        (2:ℂ)⁻¹*(-Complex.ofReal (‖d‖^2))+secondCoefficient (fun d e : E => -⟪d,e⟫_ℂ) ds-
          ⟪d,ds.sum⟫_ℂ-(⟪d,x⟫_ℂ+⟪ds.sum,x⟫_ℂ) := by push_cast; ring
    rw [h,add_assoc]
    simp only [Complex.ofReal_pow]
    rfl

 

theorem weylProduct_exponential_pairing (ds : List E) (x z : E) :
    ⟪exponential z,weylProduct ds (exponential x)⟫_ℂ=
      Complex.exp (secondCoefficient (fun d e : E => -⟪d,e⟫_ℂ) ds+
        ⟪z,ds.sum⟫_ℂ+⟪z,x⟫_ℂ-⟪ds.sum,x⟫_ℂ) := by
  rw [weylProduct_exponential,inner_smul_right,inner_exponential,←Complex.exp_add,
    inner_add_right]
  congr 1
  ring

end QuantumCLT

namespace FiniteTensor
open scoped InnerProductSpace Topology
open QuantumCLT CoherentFock Filter ContinuousLinearMap
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem moving_tensor_weyl_limit
    {κ : Type*} (ι : ℕ → Type*)
    [∀n, Fintype (ι n)] [∀n, DecidableEq (ι n)] [∀n, Nonempty (ι n)]
    (Ω xn zn : ∀n, EuclideanSpace ℂ (ι n)) (l : List κ)
    (X : ∀n, κ → EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (d : κ → E) (x z : E) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hΩ : ∀n, ‖Ω n‖=1) (hX : ∀n i, i ∈ l → ‖X n i‖ ≤ L)
    (hx : ∀n, ‖xn n‖ ≤ R) (hz : ∀n, ‖zn n‖ ≤ R)
    (hxc : ∀n, ⟪Ω n,xn n⟫_ℂ=0) (hzc : ∀n, ⟪zn n,Ω n⟫_ℂ=0)
    (hc : ∀n, ⟪Ω n,(l.map (X n)).sum (Ω n)⟫_ℂ=0)
    (hqq : ∀i ∈ l, ∀j ∈ l,
      Tendsto (fun n => ⟪Ω n,X n i (X n j (Ω n))⟫_ℂ) atTop (𝓝 (-⟪d i,d j⟫_ℂ)))
    (hza : Tendsto (fun n => ⟪zn n,(l.map (X n)).sum (Ω n)⟫_ℂ)
      atTop (𝓝 ⟪z,(l.map d).sum⟫_ℂ))
    (hzx : Tendsto (fun n => ⟪zn n,xn n⟫_ℂ) atTop (𝓝 ⟪z,x⟫_ℂ))
    (hax : Tendsto (fun n => ⟪Ω n,(l.map (X n)).sum (xn n)⟫_ℂ)
      atTop (𝓝 (-⟪(l.map d).sum,x⟫_ℂ))) :
    Tendsto (fun n =>
      ⟪exponentialVector n (Ω n) (zn n),
        operatorPower n (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹)
          (exponentialVector n (Ω n) (xn n))⟫_ℂ)
      atTop (𝓝 ⟪exponential z,weylProduct (l.map d) (exponential x)⟫_ℂ) := by
  have hj (n : ℕ) : JetBound (orderedBound L l.length) (generators (l.map (X n)))
      (l.map (X n)).sum (second (l.map (X n))) := by
    let : CompleteSpace (EuclideanSpace ℂ (ι n)) :=
      PiLp.completeSpace 2 (fun _ : ι n => ℂ)
    let : CompleteSpace (EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n)) :=
      ContinuousLinearMap.instCompleteSpace
    simpa only [List.length_map] using generators_jetBound (l.map (X n)) hL (by
      intro Y hY
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hY
      exact hX n i hi)
  have hb : Tendsto (fun n => ⟪Ω n,(second (l.map (X n))) (Ω n)⟫_ℂ)
      atTop (𝓝 (secondCoefficient (fun i j => -⟪d i,d j⟫_ℂ) l)) := by
    change Tendsto (fun n => vacuumFunctional (Ω n) (second (l.map (X n)))) _ _
    simp_rw [second_matrixElement]
    apply secondCoefficient_tendsto
    intro i hi j hj
    simpa only [vacuumFunctional_apply,mul_apply_eq_comp] using hqq i hi j hj
  rw [weylProduct_exponential_pairing,secondCoefficient_map]
  have ht := ((hb.add hza).add hzx).add hax
  simpa only [sub_eq_add_neg] using moving_tensor_pairing_limit ι Ω xn zn
    (fun n => generators (l.map (X n))) (fun n => (l.map (X n)).sum)
    (fun n => second (l.map (X n))) R (orderedBound L l.length)
    hR (orderedBound_nonneg hL _) hΩ hx hz hj hxc hzc hc ht

end FiniteTensor

namespace CoherentFock
open scoped InnerProductSpace Topology
open Filter
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem tendsto_inner_of_coherent_tests {α : Type*} {l : Filter α}
    (v : α → Space E) (v₀ : Space E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ a in l, ‖v a‖ ≤ C)
    (ht : ∀e : E, Tendsto (fun a => ⟪coherent e,v a⟫_ℂ) l (𝓝 ⟪coherent e,v₀⟫_ℂ))
    (y : Space E) : Tendsto (fun a => ⟪y,v a⟫_ℂ) l (𝓝 ⟪y,v₀⟫_ℂ) := by
  classical
  have hpre (x : PreSpace E) :
      Tendsto (fun a => ⟪(↑x : Space E),v a⟫_ℂ) l (𝓝 ⟪(↑x : Space E),v₀⟫_ℂ) := by
    simp_rw [coe_eq_sum,Finsupp.sum,sum_inner,inner_smul_left]
    exact tendsto_finsetSum _ (fun e _ => tendsto_const_nhds.mul (ht e))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x,hx⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := PreSpace E)) y
    (ε / (2*(C+‖v₀‖+1))) (by positivity)
  rw [dist_eq_norm,lt_div_iff₀ (by positivity)] at hx
  have ha := Metric.tendsto_nhds.mp (hpre x) (ε/2) (half_pos hε)
  filter_upwards [ha,hb] with a ha hb
  rw [dist_eq_norm] at ha ⊢
  have heq : ⟪y,v a⟫_ℂ-⟪y,v₀⟫_ℂ =
      ⟪y-(↑x : Space E),v a⟫_ℂ + (⟪(↑x : Space E),v a⟫_ℂ-⟪(↑x : Space E),v₀⟫_ℂ) -
      ⟪y-(↑x : Space E),v₀⟫_ℂ := by simp only [inner_sub_left]; ring
  rw [heq]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (y-(↑x : Space E)) (v a)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (y-(↑x : Space E)) v₀
  have hsum := (norm_sub_le
    (⟪y-(↑x : Space E),v a⟫_ℂ + (⟪(↑x : Space E),v a⟫_ℂ-⟪(↑x : Space E),v₀⟫_ℂ))
    ⟪y-(↑x : Space E),v₀⟫_ℂ).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hb' := mul_le_mul_of_nonneg_left hb (norm_nonneg (y-(↑x : Space E)))
  nlinarith [norm_nonneg (y-(↑x : Space E))]

 

theorem tendsto_of_coherent_tests_and_norm {α : Type*} {l : Filter α}
    (v : α → Space E) (v₀ : Space E)
    (hn : Tendsto (fun a => ‖v a‖) l (𝓝 ‖v₀‖))
    (ht : ∀e : E, Tendsto (fun a => ⟪coherent e,v a⟫_ℂ) l (𝓝 ⟪coherent e,v₀⟫_ℂ)) :
    Tendsto v l (𝓝 v₀) := by
  have hb : ∀ᶠ a in l, ‖v a‖ ≤ ‖v₀‖+1 :=
    (hn.eventually_lt_const (by linarith : ‖v₀‖ < ‖v₀‖+1)).mono (fun _ h => h.le)
  have hi := tendsto_inner_of_coherent_tests v v₀ (‖v₀‖+1) (by positivity) hb ht v₀
  have hr : Tendsto (fun a => (⟪v₀,v a⟫_ℂ).re) l (𝓝 (‖v₀‖^2)) := by
    have hk : (⟪v₀,v₀⟫_ℂ).re=‖v₀‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v₀).symm
    rw [← hk]
    exact (Complex.continuous_re.tendsto _).comp hi
  have hs : Tendsto (fun a => ‖v₀-v a‖^2) l (𝓝 0) := by
    simp_rw [norm_sub_sq (𝕜 := ℂ)]
    have hh := ((tendsto_const_nhds (x := ‖v₀‖^2)).sub (hr.const_mul 2)).add (hn.pow 2)
    have he0 : ‖v₀‖^2-2*‖v₀‖^2+‖v₀‖^2=(0:ℝ) := by ring
    rw [he0] at hh
    exact hh
  have hnorm : Tendsto (fun a => ‖v a-v₀‖) l (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hs
    simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm,norm_sub_rev] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

 

theorem tendsto_unitary_inverse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {α : Type*} {l : Filter α} (U : α → H ≃ₗᵢ[ℂ] H) (U₀ : H ≃ₗᵢ[ℂ] H)
    (h : ∀x : H, Tendsto (fun a => U a x) l (𝓝 (U₀ x))) (x : H) :
    Tendsto (fun a => (U a).symm x) l (𝓝 (U₀.symm x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht : Tendsto (fun a => ‖x-U a (U₀.symm x)‖) l (𝓝 0) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply,sub_self,norm_zero] using
      ((tendsto_const_nhds (x := x)).sub (h (U₀.symm x))).norm
  convert! ht using 1
  funext a
  rw [←(U a).norm_map, map_sub,LinearIsometryEquiv.apply_symm_apply]

end CoherentFock

namespace FourierDensity
open MeasureTheory Complex
open scoped InnerProductSpace Topology
variable {κ : Type*} [Fintype κ] (μ : Measure (κ → ℝ)) [IsFiniteMeasure μ]

 
theorem character_memLp (a : κ → ℝ) : MemLp (character a) 2 μ :=
  MemLp.of_bound (continuous_character a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun g => (norm_character a g).le)

def characterVector (a : κ → ℝ) : Lp ℂ 2 μ := (character_memLp μ a).toLp (character a)

theorem characterVector_ae (a : κ → ℝ) :
    (characterVector μ a : (κ → ℝ) → ℂ)=ᵐ[μ] character a :=
  (character_memLp μ a).coeFn_toLp

 

theorem character_span_dense :
    (Submodule.span ℂ (Set.range (characterVector μ))).topologicalClosure=⊤ := by
  let K := Submodule.span ℂ (Set.range (characterVector μ))
  have hbot : Kᗮ=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply Lp.ext
    have hi : Integrable (fun g => f g) μ :=
      memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))
    have hF : ∀a, (∫g, character a g*f g ∂μ)=0 := by
      intro a
      have hh := (Submodule.mem_orthogonal K f).mp hf (characterVector μ (-a))
        (Submodule.subset_span (Set.mem_range_self _))
      rw [L2.inner_def] at hh
      convert hh using 1
      apply integral_congr_ae
      filter_upwards [characterVector_ae μ (-a)] with g hg
      rw [RCLike.inner_apply',hg,character_neg,Complex.conj_conj]
    exact (ae_zero_of_fourier_zero hi hF).trans (Lp.coeFn_zero ℂ 2 μ).symm
  change K.topologicalClosure=⊤
  rw [←Submodule.orthogonal_orthogonal_eq_closure K,hbot,Submodule.bot_orthogonal_eq_top]

 

theorem exists_character_approx (f : Lp ℂ 2 μ) {ε : ℝ} (hε : 0<ε) :
    ∃c : (κ → ℝ) →₀ ℂ, ‖c.sum (fun a z => z • characterVector μ a)-f‖<ε := by
  have hd : Dense ((Submodule.span ℂ (Set.range (characterVector μ))) : Set (Lp ℂ 2 μ)) := by
    rw [dense_iff_closure_eq]
    have hh := congrArg (fun S : Submodule ℂ (Lp ℂ 2 μ) => (S : Set (Lp ℂ 2 μ)))
      (character_span_dense μ)
    simpa only [Submodule.topologicalClosure_coe,Submodule.top_coe] using hh
  obtain ⟨x,he,hx⟩ := Metric.dense_iff.mp hd f ε hε
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  exact ⟨c,by simpa only [Metric.mem_ball,dist_eq_norm] using he⟩

end FourierDensity

namespace FourierDensity
open MeasureTheory Complex
open scoped InnerProductSpace Topology
variable {κ : Type*} [Fintype κ] (μ : Measure (κ → ℝ)) [IsFiniteMeasure μ]

 
def realPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ

omit [Fintype κ] [IsFiniteMeasure μ] in
theorem realPart_ae (f : Lp ℂ 2 μ) :
    (realPart μ f : (κ → ℝ) → ℝ)=ᵐ[μ] fun g => (f g).re :=
  Complex.reCLM.coeFn_compLpL f

omit [Fintype κ] [IsFiniteMeasure μ] in
theorem realPart_norm (f : Lp ℂ 2 μ) : ‖realPart μ f‖ ≤ ‖f‖ := by
  change ‖Complex.reCLM.compLp f‖ ≤ ‖f‖
  simpa only [Complex.reCLM_norm,one_mul] using Complex.reCLM.norm_compLp_le f

 
def oddPart (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)-
    (Lp.compMeasurePreservingₗᵢ ℝ (fun g : κ → ℝ => -g) hμ).toContinuousLinearMap)

omit [Fintype κ] [IsFiniteMeasure μ] in
theorem oddPart_ae (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ)
    (f : Lp ℝ 2 μ) :
    (oddPart μ hμ f : (κ → ℝ) → ℝ)=ᵐ[μ] fun g => (f g-f (-g))/2 := by
  change (((1/2:ℝ) • (f-Lp.compMeasurePreserving (fun g : κ → ℝ => -g) hμ f) :
    Lp ℝ 2 μ) : (κ → ℝ) → ℝ)=ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul (1/2:ℝ)
    (f-Lp.compMeasurePreserving (fun g : κ → ℝ => -g) hμ f),
    Lp.coeFn_sub f (Lp.compMeasurePreserving (fun g : κ → ℝ => -g) hμ f),
    Lp.coeFn_compMeasurePreserving f hμ] with g h1 h2 h3
  rw [h1]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h2]
  simp only [Pi.sub_apply]
  rw [h3]
  simp only [Function.comp_def]
  ring

omit [Fintype κ] [IsFiniteMeasure μ] in
theorem oddPart_norm (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ)
    (f : Lp ℝ 2 μ) : ‖oddPart μ hμ f‖ ≤ ‖f‖ := by
  change ‖(1/2:ℝ) • (f-Lp.compMeasurePreserving (fun g : κ → ℝ => -g) hμ f)‖ ≤ ‖f‖
  rw [norm_smul]
  norm_num only [norm_div,norm_one,Real.norm_ofNat]
  have h := norm_sub_le f (Lp.compMeasurePreserving (fun g : κ → ℝ => -g) hμ f)
  rw [Lp.norm_compMeasurePreserving] at h
  linarith

omit [Fintype κ] [IsFiniteMeasure μ] in
theorem oddPart_eq (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ g ∂μ, f (-g)= -f g) : oddPart μ hμ f=f := by
  apply Lp.ext
  filter_upwards [oddPart_ae μ hμ f,hf] with g hg hfg
  rw [hg,hfg]
  ring

def sine (a g : κ → ℝ) : ℝ := Real.sin (∑k, a k*g k)

theorem sine_memLp (a : κ → ℝ) : MemLp (sine a) 2 μ := by
  have hc : Continuous (sine a) := by unfold sine; fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable 1
  filter_upwards [] with g
  exact Real.abs_sin_le_one (∑k, a k*g k)

def sineVector (a : κ → ℝ) : Lp ℝ 2 μ := (sine_memLp μ a).toLp (sine a)

theorem sineVector_ae (a : κ → ℝ) :
    (sineVector μ a : (κ → ℝ) → ℝ)=ᵐ[μ] sine a :=
  (sine_memLp μ a).coeFn_toLp

 
theorem oddPart_realPart_character (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ)
    (a : κ → ℝ) (z : ℂ) :
    oddPart μ hμ (realPart μ (z • characterVector μ a))=(-z.im) • sineVector μ a := by
  apply Lp.ext
  have hre := realPart_ae μ (z • characterVector μ a)
  have hsm := Lp.coeFn_smul z (characterVector μ a)
  have hcv := characterVector_ae μ a
  have hrneg := hμ.quasiMeasurePreserving.ae (hre.and (hsm.and hcv))
  filter_upwards [oddPart_ae μ hμ (realPart μ (z • characterVector μ a)),
    hre,hsm,hcv,hrneg,Lp.coeFn_smul (-z.im) (sineVector μ a),sineVector_ae μ a]
    with g ho hr hs hc hn hss hsin
  rw [ho,hr,hs,hn.1,hn.2.1,hss]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hc,hn.2.2,hsin]
  simp [character,sine,Complex.exp_re,Complex.exp_im,Finset.sum_neg_distrib]
  ring

end FourierDensity

namespace FourierDensity
open MeasureTheory Complex
open scoped InnerProductSpace Topology
variable {κ : Type*} [Fintype κ] (μ : Measure (κ → ℝ)) [IsFiniteMeasure μ]

 

theorem exists_odd_sine_approx
    (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ g ∂μ, f (-g)= -f g) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ,
      ‖(∑a∈s, b a • sineVector μ a)-f‖<ε := by
  classical
  let fC : Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ f
  have hr : realPart μ fC=f := by
    apply Lp.ext
    filter_upwards [realPart_ae μ fC,Complex.ofRealCLM.coeFn_compLpL f] with g hg hj
    rw [hg]
    change (fC g).re=f g
    change fC g=(f g:ℂ) at hj
    rw [hj,Complex.ofReal_re]
  obtain ⟨c,hc⟩ := exists_character_approx μ fC hε
  have hm : oddPart μ hμ (realPart μ (c.sum (fun a z => z • characterVector μ a)))=
      ∑a∈c.support, -(c a).im • sineVector μ a := by
    simp only [Finsupp.sum,map_sum,oddPart_realPart_character]
  refine ⟨c.support,fun a => -(c a).im,?_⟩
  calc
    ‖(∑a∈c.support, -(c a).im • sineVector μ a)-f‖ =
        ‖oddPart μ hμ (realPart μ (c.sum (fun a z => z • characterVector μ a)-fC))‖ := by
      rw [map_sub,map_sub,hm,hr,oddPart_eq μ hμ f hf]
    _ ≤ ‖c.sum (fun a z => z • characterVector μ a)-fC‖ :=
      (oddPart_norm μ hμ _).trans (realPart_norm μ _)
    _ < ε := hc

 

def sinePolynomial (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → ℝ) : ℝ :=
  ∑a∈s, b a*sine a g

omit [IsFiniteMeasure μ] in
theorem sinePolynomial_odd (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → ℝ) :
    sinePolynomial s b (-g)= -sinePolynomial s b g := by
  simp [sinePolynomial,sine,Finset.sum_neg_distrib]

omit [IsFiniteMeasure μ] in
theorem sinePolynomial_bounded (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → ℝ) :
    |sinePolynomial s b g| ≤ ∑a∈s, |b a| := by
  unfold sinePolynomial
  calc
    |∑a∈s, b a*sine a g| ≤ ∑a∈s, |b a*sine a g| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑a∈s, |b a| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg (b a)) (Real.abs_sin_le_one _)

omit [IsFiniteMeasure μ] in
theorem sinePolynomial_contDiff (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    ContDiff ℝ ⊤ (sinePolynomial s b) := by
  unfold sinePolynomial sine
  fun_prop

end FourierDensity

namespace FourierDensity
open MeasureTheory Complex
open scoped InnerProductSpace Topology
variable {κ : Type*} [Fintype κ] (μ : Measure (κ → ℝ)) [IsFiniteMeasure μ]

theorem sinePolynomial_ae (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    ((∑a∈s, b a • sineVector μ a : Lp ℝ 2 μ) : (κ → ℝ) → ℝ)=ᵐ[μ]
      sinePolynomial s b := by
  classical
  unfold sinePolynomial
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Pi.zero_def] using Lp.coeFn_zero ℝ 2 μ
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (b a • sineVector μ a) (∑j∈s, b j • sineVector μ j),
      Lp.coeFn_smul (b a) (sineVector μ a),sineVector_ae μ a,ih] with g h1 h2 h3 h4
    rw [h1]
    simp only [Pi.add_apply]
    rw [h2]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [h3,h4]

def sineOutput (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → ℝ) : ℝ :=
  Real.sin (2*sinePolynomial s b g)

theorem sineOutput_memLp (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    MemLp (sineOutput s b) 2 μ := by
  have hc : Continuous (sineOutput s b) := by
    exact Real.continuous_sin.comp (continuous_const.mul (sinePolynomial_contDiff s b).continuous)
  exact MemLp.of_bound hc.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun g => Real.abs_sin_le_one _)

def sineOutputVector (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) : Lp ℝ 2 μ :=
  (sineOutput_memLp μ s b).toLp (sineOutput s b)

theorem sineOutputVector_ae (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    (sineOutputVector μ s b : (κ → ℝ) → ℝ)=ᵐ[μ] sineOutput s b :=
  (sineOutput_memLp μ s b).coeFn_toLp

 

theorem exists_sine_angle_approx
    (hμ : MeasurePreserving (fun g : κ → ℝ => -g) μ μ)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ g ∂μ, f (-g)= -f g)
    (hb : ∀ᵐ g ∂μ, |f g|≤1) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ,
      ‖sineOutputVector μ s b-f‖<ε := by
  classical
  let θ : (κ → ℝ) → ℝ := fun g => Real.arcsin (f g)/2
  have hθ : MemLp θ 2 μ := by
    apply MemLp.of_bound
      ((Real.continuous_arcsin.div_const 2).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
      (Real.pi/4)
    filter_upwards [] with g
    change |Real.arcsin (f g)/2|≤Real.pi/4
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs := abs_le.mpr (Real.arcsin_mem_Icc (f g))
    linarith
  let θv : Lp ℝ 2 μ := hθ.toLp θ
  have hθae : (θv : (κ → ℝ) → ℝ)=ᵐ[μ] θ := hθ.coeFn_toLp
  have hθn := hμ.quasiMeasurePreserving.ae hθae
  have hodd : ∀ᵐ g ∂μ, θv (-g)= -θv g := by
    filter_upwards [hθae,hθn,hf] with g hg hng hfg
    rw [hg,hng]
    change Real.arcsin (f (-g))/2= -(Real.arcsin (f g)/2)
    rw [hfg,Real.arcsin_neg,neg_div]
  obtain ⟨s,b,happrox⟩ := exists_odd_sine_approx μ hμ θv hodd (half_pos hε)
  refine ⟨s,b,?_⟩
  have hnorm : ‖sineOutputVector μ s b-f‖ ≤
      2*‖(∑a∈s, b a • sineVector μ a)-θv‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (sineOutputVector μ s b) f,
      Lp.coeFn_sub (∑a∈s, b a • sineVector μ a) θv,sineOutputVector_ae μ s b,
      sinePolynomial_ae μ s b,hθae,hb] with g h1 h2 h3 h4 h5 h6
    rw [h1,h2]
    simp only [Pi.sub_apply,Real.norm_eq_abs]
    rw [h3,h4,h5]
    have hs : f g=Real.sin (2*θ g) := by
      dsimp [θ]
      rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
      exact (Real.sin_arcsin (abs_le.mp h6).1 (abs_le.mp h6).2).symm
    change |Real.sin (2*sinePolynomial s b g)-f g|≤2*|sinePolynomial s b g-θ g|
    calc
      _ = |Real.sin (2*sinePolynomial s b g)-Real.sin (2*θ g)| := by rw [←hs]
      _ ≤ |2*sinePolynomial s b g-2*θ g| := Real.abs_sin_sub_sin_le _ _
      _ = _ := by rw [←mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact hnorm.trans_lt (by linarith)

end FourierDensity

namespace FourierDensity
open MeasureTheory Complex
open scoped InnerProductSpace Topology
variable {κ : Type*} [Fintype κ]

 
def frequency (a : κ → ℝ) : (κ → ℝ) →L[ℝ] ℝ :=
  ∑k, a k • ContinuousLinearMap.proj k

@[simp] theorem frequency_apply (a g : κ → ℝ) : frequency a g=∑k, a k*g k := by
  simp [frequency]

theorem sine_norm_sub_le (a g h : κ → ℝ) :
    |sine a g-sine a h| ≤ ‖frequency a‖*‖g-h‖ := by
  calc
    _ ≤ |frequency a g-frequency a h| := by
      simpa only [frequency_apply,sine] using Real.abs_sin_sub_sin_le (frequency a g) (frequency a h)
    _ = ‖frequency a (g-h)‖ := by rw [map_sub,Real.norm_eq_abs]
    _ ≤ _ := (frequency a).le_opNorm _

 
theorem sinePolynomial_lipschitz_bound (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ)
    (g h : κ → ℝ) :
    |sinePolynomial s b g-sinePolynomial s b h| ≤
      (∑a∈s, |b a| *‖frequency a‖)*‖g-h‖ := by
  simp only [sinePolynomial,←Finset.sum_sub_distrib,Finset.sum_mul]
  calc
    |∑a∈s, (b a*sine a g-b a*sine a h)| ≤ ∑a∈s, |b a*sine a g-b a*sine a h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑a∈s, |b a| *‖frequency a‖*‖g-h‖ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [←mul_sub,abs_mul]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (sine_norm_sub_le a g h) (abs_nonneg (b a))

omit [Fintype κ] in
theorem iterated_sine_cosine_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n Real.sin x|≤1 ∧ |iteratedDeriv n Real.cos x|≤1 := by
  induction n with
  | zero => exact ⟨Real.abs_sin_le_one x,Real.abs_cos_le_one x⟩
  | succ n ih =>
    simp only [Real.iteratedDeriv_add_one_sin,Real.iteratedDeriv_add_one_cos,
      Pi.neg_apply,abs_neg]
    exact ih.symm

 
theorem sine_derivative_bound (a g : κ → ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (sine a) g‖ ≤ ‖frequency a‖^n := by
  have hf : sine a=Real.sin ∘ frequency a := by funext g; simp [sine]
  rw [hf,(frequency a).iteratedFDeriv_comp_right
    (Real.contDiff_sin : ContDiff ℝ ⊤ Real.sin) g (by exact le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n Real.sin (frequency a g)‖*∏_ : Fin n, ‖frequency a‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1*∏_ : Fin n, ‖frequency a‖ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
      exact (iterated_sine_cosine_bound n _).1
    _ = _ := by simp

 

theorem sinePolynomial_derivative_bound (s : Finset (κ → ℝ))
    (b : (κ → ℝ) → ℝ) (n : ℕ) (g : κ → ℝ) :
    ‖iteratedFDeriv ℝ n (sinePolynomial s b) g‖ ≤
      ∑a∈s, |b a| *‖frequency a‖^n := by
  have hc (a : κ → ℝ) : ContDiff ℝ n (sine a) := by unfold sine; fun_prop
  unfold sinePolynomial
  rw [iteratedFDeriv_fun_sum_apply (fun a ha => (contDiff_const.mul (hc a)).contDiffAt)]
  calc
    _ ≤ ∑a∈s, ‖iteratedFDeriv ℝ n (fun g => b a*sine a g) g‖ := norm_sum_le _ _
    _ ≤ ∑a∈s, |b a| *‖frequency a‖^n := by
      apply Finset.sum_le_sum
      intro a ha
      change ‖iteratedFDeriv ℝ n (fun g => b a • sine a g) g‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply' (hc a).contDiffAt,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (sine_derivative_bound a g n) (abs_nonneg (b a))

end FourierDensity

end

end OAI
