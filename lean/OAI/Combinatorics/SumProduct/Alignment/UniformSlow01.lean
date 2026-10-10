import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughKernel03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
open scoped NNReal
namespace UniformParameterTests
variable {A Y Z : Type*} [PseudoMetricSpace A] [CompactSpace A]
variable [PseudoMetricSpace Y] [CompactSpace Y] [PseudoMetricSpace Z]

 
theorem common_modulus (H : C(A×Y,Z)) (K : ℝ≥0) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (a b : A),dist a b<δ →
      ∀ (F : Z → ℂ),LipschitzWith K F → ∀ y : Y,
        ‖F (H (a,y))-F (H (b,y))‖<ε := by
  have hp : 0<(K:ℝ)+1:=by positivity
  obtain ⟨δ,hδ,hd⟩:=Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous H.continuous)
    (ε/((K:ℝ)+1)) (div_pos hε hp)
  refine ⟨δ,hδ,fun a b hab F hF y=>?_⟩
  have hab' : dist (a,y) (b,y)<δ:=by simpa [Prod.dist_eq] using hab
  have hh:=hd hab'
  have hf:=hF.dist_le_mul (H (a,y)) (H (b,y))
  rw [dist_eq_norm] at hf
  have hx : ((K:ℝ)+1)*dist (H (a,y)) (H (b,y))<ε := by
    have ht:=mul_lt_mul_of_pos_left hh hp
    have hc : ((K:ℝ)+1)*(ε/((K:ℝ)+1))=ε:=mul_div_cancel₀ _ hp.ne'
    rwa [hc] at ht
  have hn:=dist_nonneg (x:=H (a,y)) (y:=H (b,y))
  nlinarith

end UniformParameterTests
end
 
end

section
 

 

noncomputable section
open scoped NNReal
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)
variable (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZ : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)
variable {X : Type*} [PseudoMetricSpace X] (e : (G⧸Γ) ≃ₜ X)

include hΓ hcont hZ in
 

theorem uniform_finite_kernel_tests {J : Type*} [Fintype J] (σ : J → G)
    (T : ℝ) (K : ℝ≥0) (B : ℝ) (hB : 0≤B) (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ≥0,∀ j : J,
      letI := kernelCompatibleMetric χ Γ (σ j) c hsk R hΓ hcont hZ
      ∀ (a : Set.Icc (-T) T) (F : X → ℂ),LipschitzWith K F → (∀ x,‖F x‖≤B) →
        ∃ g : (χ.ker⧸kernelLattice χ Γ (σ j)) → ℂ,LipschitzWith L g ∧
          (∀ y,‖g y-F (e (kernelTestMap χ Γ (σ j)
            (R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)) y))‖<ε) ∧
          ∀ y,‖g y‖≤B+ε := by
  classical
  have hall:=fun j : J=>uniform_kernel_tests χ Γ (σ j) c hsk R hΓ hcont hZ e T K B hB ε hε
  choose L hL using hall
  refine ⟨Finset.univ.sup L,fun j a F hF hb=>?_⟩
  let := kernelCompatibleMetric χ Γ (σ j) c hsk R hΓ hcont hZ
  obtain ⟨g,hg,he,hb'⟩:=hL j a F hF hb
  refine ⟨g,?_,he,hb'⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (hg.dist_le_mul x y).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  exact_mod_cast (Finset.le_sup (f:=L) (Finset.mem_univ j))

include hΓ in
 

theorem uniform_slow_freezing (T : ℝ) (K : ℝ≥0) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (a b : Set.Icc (-T) T),|a.val-b.val|<δ →
      ∀ (F : X → ℂ),LipschitzWith K F → ∀ y : G⧸Γ,
        ‖F (e ((R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)) • y))-
          F (e ((R.flow c hsk χ Γ (Multiplicative.ofAdd b.val)) • y))‖<ε := by
  let : CompactSpace (G⧸Γ):=by
    obtain ⟨S,hS,hrep⟩:=compact_reps_of_integerCoordinates c Γ hΓ
    exact (show CompactGroupProducts.HasCompactReps ⊤ Γ from
      ⟨S,hS,Set.subset_univ _,fun g _=>hrep g⟩).quotient_compactSpace
  let : CompactSpace X:=e.surjective.compactSpace e.continuous
  let H : C((Set.Icc (-T) T) × X,X):=
    { toFun:=fun x=>e ((R.flow c hsk χ Γ (Multiplicative.ofAdd x.1.val)) • e.symm x.2)
      continuous_toFun:=by
        apply e.continuous.comp
        have hf : Continuous (fun x : (Set.Icc (-T) T) × X=>
            R.flow c hsk χ Γ (Multiplicative.ofAdd x.1.val)):=
          (sectionFlow_continuous c hsk R.k R.p).comp
            (continuous_ofAdd.comp (continuous_subtype_val.comp continuous_fst))
        have hq : Continuous (fun x : (Set.Icc (-T) T) × X=>e.symm x.2):=
          e.symm.continuous.comp continuous_snd
        exact hf.smul hq }
  obtain ⟨δ,hδ,hd⟩:=UniformParameterTests.common_modulus H K ε hε
  refine ⟨δ,hδ,fun a b hab F hF y=>?_⟩
  have hh:=hd a b (by simpa [Subtype.dist_eq,Real.dist_eq] using hab) F hF (e y)
  simpa only [H,ContinuousMap.coe_mk,e.symm_apply_apply] using hh

end RoughKernelFactorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace UniformSlowPolynomials
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def form (e : κ → ι → ℕ) (a : κ → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ k, a k * ∏ i, x i ^ e k i

lemma continuous_form (e : κ → ι → ℕ) :
    Continuous (fun p : (κ → ℝ) × (ι → ℝ) => form e p.1 p.2) := by
  unfold form
  fun_prop

lemma rescale (e : κ → ι → ℕ) (a : κ → ℝ) (x : ι → ℝ) (Z : ℝ) (hZ : Z≠0) :
    form e a x = form e (fun k=>a k*Z^(∑ i,e k i)) (fun i=>x i/Z) := by
  unfold form
  apply Finset.sum_congr rfl
  intro k _
  rw [show (∏ i,(x i/Z)^e k i)=(∏ i,x i^e k i)/Z^(∑ i,e k i) by
    simp only [div_pow,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]]
  field_simp

 

theorem normalized_uniformity (e : κ → ι → ℕ) (A C : ℝ)
    (hA : 0≤A) (hC : 0≤C) (ε : ℝ) (hε : 0<ε) :
    ∃ T δ : ℝ,0<T ∧ 0<δ ∧
      ∀ (a : κ → ℝ),(∀ k,|a k|≤A) →
      ∀ (x y : ι → ℝ),(∀ i,|x i|≤C) → (∀ i,|y i|≤C) →
        (|form e a x|≤T ∧ ((∀ i,|x i-y i|<δ) → |form e a x-form e a y|<ε)) := by
  let B := κ → Set.Icc (-A) A
  let X := ι → Set.Icc (-C) C
  let F : C(B×X,ℝ):=
    { toFun:=fun p=>form e (fun k=>(p.1 k).val) (fun i=>(p.2 i).val)
      continuous_toFun:=by unfold form; fun_prop }
  obtain ⟨T,hT⟩:=IsCompact.exists_bound_of_continuousOn (s:=Set.univ) isCompact_univ F.continuous.continuousOn
  obtain ⟨δ,hδ,hd⟩:=Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous F.continuous) ε hε
  refine ⟨max T (A+C)+1,δ,?_,hδ,?_⟩
  · have hAC := add_nonneg hA hC
    linarith [le_max_right T (A+C)]
  intro a ha x y hx hy
  let a' : B:=fun k=>⟨a k,abs_le.mp (ha k)⟩
  let x' : X:=fun i=>⟨x i,abs_le.mp (hx i)⟩
  let y' : X:=fun i=>⟨y i,abs_le.mp (hy i)⟩
  constructor
  · have hh:=hT (a',x') (Set.mem_univ _)
    change ‖form e a x‖≤T at hh
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by linarith [le_max_left T (A+C)])
  · intro hxy
    have hxy' : dist x' y'<δ := by
      apply (dist_pi_lt_iff hδ).mpr
      intro i
      simpa only [Subtype.dist_eq,Real.dist_eq] using hxy i
    have hp : dist (a',x') (a',y')<δ:=by simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hxy'
    have hh:=hd hp
    simpa only [F,ContinuousMap.coe_mk,Real.dist_eq] using hh

 

theorem scaled_uniformity (e : κ → ι → ℕ) (A C : ℝ)
    (hA : 0≤A) (hC : 0≤C) (ε : ℝ) (hε : 0<ε) :
    ∃ T δ : ℝ,0<T ∧ 0<δ ∧
      ∀ (Z : ℝ),0<Z → ∀ (a : κ → ℝ),(∀ k,|a k| * Z^(∑ i,e k i)≤A) →
      ∀ (x y : ι → ℝ),(∀ i,|x i|≤C*Z) → (∀ i,|y i|≤C*Z) →
        (|form e a x|≤T ∧ ((∀ i,|x i-y i|<δ*Z) → |form e a x-form e a y|<ε)) := by
  obtain ⟨T,δ,hT,hδ,h⟩:=normalized_uniformity e A C hA hC ε hε
  refine ⟨T,δ,hT,hδ,?_⟩
  intro Z hZ a ha x y hx hy
  have ha' : ∀ k,|a k*Z^(∑ i,e k i)|≤A:=by
    intro k
    rw [abs_mul,abs_of_pos (pow_pos hZ _)]
    exact ha k
  have hx' : ∀ i,|x i/Z|≤C:=by
    intro i
    rw [abs_div,abs_of_pos hZ]
    exact (div_le_iff₀ hZ).mpr (hx i)
  have hy' : ∀ i,|y i/Z|≤C:=by
    intro i
    rw [abs_div,abs_of_pos hZ]
    exact (div_le_iff₀ hZ).mpr (hy i)
  obtain ⟨hb,hd⟩:=h (fun k=>a k*Z^(∑ i,e k i)) ha' (fun i=>x i/Z) (fun i=>y i/Z) hx' hy'
  rw [←rescale e a x Z hZ.ne'] at hb
  refine ⟨hb,fun hxy=>?_⟩
  rw [rescale e a x Z hZ.ne',rescale e a y Z hZ.ne']
  apply hd
  intro i
  rw [←sub_div,abs_div,abs_of_pos hZ]
  exact (div_lt_iff₀ hZ).mpr (hxy i)

end UniformSlowPolynomials
end
 
end

section
 

 

noncomputable section
open scoped NNReal
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters UniformSlowPolynomials
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)
variable (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable {X : Type*} [PseudoMetricSpace X] (v : (G⧸Γ) ≃ₜ X)

include hΓ in
 

theorem polynomial_slow_freezing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι → ℕ) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (K : ℝ≥0) (ε : ℝ) (hε : 0<ε) :
    ∃ T lam : ℝ,0<T ∧ 0<lam ∧
      ∀ (Z : ℝ),0<Z → ∀ (a : κ → ℝ),
      (∀ k,|a k| * Z^(∑ i,e k i)≤A) →
      ∀ (x y : ι → ℝ),(∀ i,|x i|≤C*Z) → (∀ i,|y i|≤C*Z) →
        |form e a x|≤T ∧ ((∀ i,|x i-y i|<lam*Z) →
          ∀ (F : X → ℂ),LipschitzWith K F → ∀ z : G⧸Γ,
            ‖F (v ((R.flow c hsk χ Γ (Multiplicative.ofAdd (form e a x))) • z))-
              F (v ((R.flow c hsk χ Γ (Multiplicative.ofAdd (form e a y))) • z))‖<ε) := by
  obtain ⟨T,δ,hT,hδ,h⟩:=scaled_uniformity e A C hA hC 1 (by norm_num)
  obtain ⟨δa,hδa,hfreeze⟩:=uniform_slow_freezing c hsk χ Γ R hΓ v T K ε hε
  obtain ⟨T',lam,hT',hlam,hslow⟩:=scaled_uniformity e A C hA hC δa hδa
  refine ⟨T,lam,hT,hlam,?_⟩
  intro Z hZ a ha x y hx hy
  have hxb:= (h Z hZ a ha x x hx hx).1
  have hyb:= (h Z hZ a ha y y hy hy).1
  refine ⟨hxb,fun hxy F hF z=>?_⟩
  have hs:=(hslow Z hZ a ha x y hx hy).2 hxy
  exact hfreeze ⟨form e a x,abs_le.mp hxb⟩ ⟨form e a y,abs_le.mp hyb⟩ hs F hF z

end RoughKernelFactorization

end
end
end
end

end OAI
