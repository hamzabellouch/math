import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughKernel02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped NNReal
end
 
end

section
 

 

noncomputable section
open scoped NNReal
namespace UniformLipschitzApproximation
variable {A Y Z : Type*} [PseudoMetricSpace A] [CompactSpace A]
variable [PseudoMetricSpace Y] [CompactSpace Y] [Nonempty Y] [PseudoMetricSpace Z]
variable (H : C(A×Y,Z)) (K : ℝ≥0) (B : ℝ) (hB : 0≤B)

include hB in
theorem compact_pullback (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ≥0,∀ (a : A) (F : Z → ℝ),LipschitzWith K F → (∀ z,|F z|≤B) →
      ∃ g : Y → ℝ,LipschitzWith L g ∧
        (∀ y,|g y-F (H (a,y))|<ε) ∧ ∀ y,|g y|≤B+ε := by
  let J:=A × {F : Z → ℝ // LipschitzWith K F ∧ ∀ z,|F z|≤B}
  let f (j : J) (y : Y):=j.2.val (H (j.1,y))
  have hbound : ∀ j y,|f j y|≤B:=fun j y=>j.2.property.2 _
  have hmod : ∀ η : ℝ,0<η → ∃ δ : ℝ,0<δ ∧
      ∀ j y z,dist y z<δ → |f j y-f j z|<η := by
    intro η hη
    have hp : 0<(K:ℝ)+1:=by positivity
    obtain ⟨δ,hδ,hd⟩:=Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous H.continuous)
      (η/((K:ℝ)+1)) (div_pos hη hp)
    refine ⟨δ,hδ,fun j y z hyz=>?_⟩
    have he : dist (j.1,y) (j.1,z)<δ := by simpa [Prod.dist_eq] using hyz
    have hh:=hd he
    have hf:=j.2.property.1.dist_le_mul (H (j.1,y)) (H (j.1,z))
    change |f j y-f j z|≤(K:ℝ)*dist (H (j.1,y)) (H (j.1,z)) at hf
    have hx : ((K:ℝ)+1)*dist (H (j.1,y)) (H (j.1,z))<η := by
      have ht:=mul_lt_mul_of_pos_left hh hp
      have hc : ((K:ℝ)+1)*(η/((K:ℝ)+1))=η:=mul_div_cancel₀ _ hp.ne'
      rwa [hc] at ht
    have hn:=dist_nonneg (x:=H (j.1,y)) (y:=H (j.1,z))
    nlinarith
  obtain ⟨L,hL⟩:=exists_common_bound f B hB hbound hmod ε hε
  exact ⟨L,fun a F hF hb=>hL (a,⟨F,hF,hb⟩)⟩

end UniformLipschitzApproximation
end
 
end

section
 

noncomputable section
open scoped NNReal
namespace UniformLipschitzApproximation
variable {A Y Z : Type*} [PseudoMetricSpace A] [CompactSpace A]
variable [PseudoMetricSpace Y] [CompactSpace Y] [Nonempty Y] [PseudoMetricSpace Z]
variable (H : C(A×Y,Z)) (K : ℝ≥0) (B : ℝ) (hB : 0≤B)

include hB in
theorem compact_pullback_complex (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ≥0,∀ (a : A) (F : Z → ℂ),LipschitzWith K F → (∀ z,‖F z‖≤B) →
      ∃ g : Y → ℂ,LipschitzWith L g ∧
        (∀ y,‖g y-F (H (a,y))‖<ε) ∧ ∀ y,‖g y‖≤B+ε := by
  obtain ⟨L,hL⟩:=compact_pullback H K B hB (ε/2) (by linarith)
  refine ⟨L+L,fun a F hF hb=>?_⟩
  have hRe : LipschitzWith K (fun z=>(F z).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (F x).re (F y).re=|(F x-F y).re|:=by simp [Real.dist_eq]
      _≤‖F x-F y‖:=Complex.abs_re_le_norm _
      _≤(K:ℝ)*dist x y:=by simpa [dist_eq_norm] using hF.dist_le_mul x y
  have hIm : LipschitzWith K (fun z=>(F z).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (F x).im (F y).im=|(F x-F y).im|:=by simp [Real.dist_eq]
      _≤‖F x-F y‖:=Complex.abs_im_le_norm _
      _≤(K:ℝ)*dist x y:=by simpa [dist_eq_norm] using hF.dist_le_mul x y
  obtain ⟨u,hu,hue,_⟩:=hL a (fun z=>(F z).re) hRe
    (fun z=>(Complex.abs_re_le_norm _).trans (hb z))
  obtain ⟨v,hv,hve,_⟩:=hL a (fun z=>(F z).im) hIm
    (fun z=>(Complex.abs_im_le_norm _).trans (hb z))
  let g (y : Y) : ℂ:=⟨u y,v y⟩
  have hg : LipschitzWith (L+L) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh:=Complex.norm_le_abs_re_add_abs_im (g x-g y)
    have h₁:=hu.dist_le_mul x y
    have h₂:=hv.dist_le_mul x y
    simp only [Real.dist_eq] at h₁ h₂
    rw [dist_eq_norm]
    change ‖g x-g y‖≤|u x-u y|+|v x-v y| at hh
    push_cast
    nlinarith
  have he (y : Y) : ‖g y-F (H (a,y))‖<ε := by
    have hh:=Complex.norm_le_abs_re_add_abs_im (g y-F (H (a,y)))
    change ‖g y-F (H (a,y))‖≤|u y-(F (H (a,y))).re|+|v y-(F (H (a,y))).im| at hh
    linarith [hue y,hve y]
  refine ⟨g,hg,he,fun y=>?_⟩
  have hh:=norm_add_le (g y-F (H (a,y))) (F (H (a,y)))
  rw [sub_add_cancel] at hh
  linarith [he y,hb (H (a,y))]

end UniformLipschitzApproximation
end
 
end

section
 

 

noncomputable section
open scoped NNReal
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G) (σ : G)

def kernelTestJoint : C(G×(χ.ker⧸kernelLattice χ Γ σ),G⧸Γ) where
  toFun x:=kernelTestMap χ Γ σ x.1 x.2
  continuous_toFun:=by
    change Continuous (fun x : G×(χ.ker⧸kernelLattice χ Γ σ)=>
      (x.1*σ) • NonnormalCoset.map (kernelLattice χ Γ σ) Γ
        (kernelInclusion χ σ) (kernelInclusion_continuous χ σ) (fun _ h=>h) x.2)
    exact (continuous_fst.mul continuous_const).smul
      ((NonnormalCoset.map (kernelLattice χ Γ σ) Γ
        (kernelInclusion χ σ) (kernelInclusion_continuous χ σ) (fun _ h=>h)).continuous.comp
          continuous_snd)

variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZ : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)

noncomputable abbrev kernelCompatibleMetric : MetricSpace (χ.ker⧸kernelLattice χ Γ σ) := by
  letI : T2Space G:=c.coord.symm.t2Space
  letI : SecondCountableTopology χ.ker:=(R.chart c hsk χ Γ).coord.secondCountableTopology
  letI : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  have hinj : Function.Injective (kernelInclusion χ σ) :=
    (MulAut.conj σ⁻¹).injective.comp Subtype.val_injective
  letI : DiscreteTopology (kernelLattice χ Γ σ):=
    DiscreteTopology.preimage_of_continuous_injective (Γ:Set G)
      (kernelInclusion_continuous χ σ) hinj
  letI : IsClosed (kernelLattice χ Γ σ:Set χ.ker):=Subgroup.isClosed_of_discreteTopology
  letI : CompactSpace (χ.ker⧸kernelLattice χ Γ σ):=
    integer_kernel_quotient_compact χ Γ σ hcont hZ c hΓ
  exact TopologicalSpace.metrizableSpaceMetric _

variable {X : Type*} [PseudoMetricSpace X] (e : (G⧸Γ) ≃ₜ X)
include hΓ hcont hZ in
 

theorem uniform_kernel_tests (T : ℝ) (K : ℝ≥0) (B : ℝ) (hB : 0≤B) :
    letI := kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZ
    ∀ ε : ℝ,0<ε → ∃ L : ℝ≥0,∀ (a : Set.Icc (-T) T) (F : X → ℂ),
      LipschitzWith K F → (∀ x,‖F x‖≤B) →
      ∃ g : (χ.ker⧸kernelLattice χ Γ σ) → ℂ,LipschitzWith L g ∧
        (∀ y,‖g y-F (e (kernelTestMap χ Γ σ
          (R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)) y))‖<ε) ∧
        ∀ y,‖g y‖≤B+ε := by
  let := kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZ
  let : CompactSpace (χ.ker⧸kernelLattice χ Γ σ):=
    integer_kernel_quotient_compact χ Γ σ hcont hZ c hΓ
  let H : C((Set.Icc (-T) T) × (χ.ker⧸kernelLattice χ Γ σ),X):=
    { toFun:=fun x=>e (kernelTestMap χ Γ σ
        (R.flow c hsk χ Γ (Multiplicative.ofAdd x.1.val)) x.2)
      continuous_toFun:=by
        apply e.continuous.comp
        change Continuous ((kernelTestJoint χ Γ σ) ∘
          (fun x : (Set.Icc (-T) T) × (χ.ker⧸kernelLattice χ Γ σ)=>
            (R.flow c hsk χ Γ (Multiplicative.ofAdd x.1.val),x.2)))
        apply (kernelTestJoint χ Γ σ).continuous.comp
        apply Continuous.prodMk _ continuous_snd
        exact (sectionFlow_continuous c hsk R.k R.p).comp
          (continuous_ofAdd.comp (continuous_subtype_val.comp continuous_fst)) }
  exact UniformLipschitzApproximation.compact_pullback_complex H K B hB

end RoughKernelFactorization
end
 
end

section
 

 

noncomputable section
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters

lemma integer_eval_modEq {V : Type*} (K : ℤ) (m : MvPolynomial V ℤ)
    (x u : V → ℤ) (hx : ∀ i,Int.ModEq K (x i) (u i)) :
    Int.ModEq K (MvPolynomial.eval x m) (MvPolynomial.eval u m) := by
  induction m using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using (Int.ModEq.refl (n:=K) a)
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval_mul,MvPolynomial.eval_X] using hp.mul (hx i)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)
variable (R : Reduction c hsk χ Γ)

 

lemma polynomial_residue_coset {V : Type*} (m : MvPolynomial V ℤ)
    (x u : V → ℤ) (hx : ∀ i,Int.ModEq (R.period:ℤ) (x i) (u i)) :
    let j:=MvPolynomial.eval u m % (R.period:ℤ)
    (QuotientGroup.mk (R.flow c hsk χ Γ
      (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))) : G⧸Γ)=
      QuotientGroup.mk (R.flow c hsk χ Γ (Multiplicative.ofAdd (j:ℝ))) := by
  dsimp only
  apply R.coset_period c hsk χ Γ
  exact ((integer_eval_modEq (R.period:ℤ) m x u hx).trans
    (Int.mod_modEq (MvPolynomial.eval u m) (R.period:ℤ)).symm).symm.dvd

 
theorem factorization_on_residue {V : Type*} (m : MvPolynomial V ℤ)
    (x u : V → ℤ) (hx : ∀ i,Int.ModEq (R.period:ℤ) (x i) (u i))
    (P ℓ : G) (Q : χ.ker)
    (hP : P=ℓ*Q.val*R.flow c hsk χ Γ
      (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))) :
    let j:=MvPolynomial.eval u m % (R.period:ℤ)
    (QuotientGroup.mk P : G⧸Γ)=kernelTestMap χ Γ
      (R.flow c hsk χ Γ (Multiplicative.ofAdd (j:ℝ))) ℓ (QuotientGroup.mk Q) := by
  dsimp only
  rw [hP,kernelTestMap_mk]
  change (ℓ*Q.val) • (QuotientGroup.mk (R.flow c hsk χ Γ
    (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))) : G⧸Γ)=
    (ℓ*Q.val) • QuotientGroup.mk (R.flow c hsk χ Γ
      (Multiplicative.ofAdd ((MvPolynomial.eval u m % (R.period:ℤ):ℤ):ℝ)))
  rw [polynomial_residue_coset c hsk χ Γ R m x u hx]

omit [IsTopologicalGroup G] in
lemma residue_range [IsTopologicalGroup G] {V : Type*} (m : MvPolynomial V ℤ) (u : V → ℤ) :
    0≤MvPolynomial.eval u m % (R.period:ℤ) ∧
      MvPolynomial.eval u m % (R.period:ℤ)<R.period := by
  have hK : (0:ℤ)<R.period:=by exact_mod_cast R.period_pos
  exact ⟨Int.emod_nonneg _ (ne_of_gt hK),Int.emod_lt_of_pos _ hK⟩

end RoughKernelFactorization

end
end
end
end

end OAI
