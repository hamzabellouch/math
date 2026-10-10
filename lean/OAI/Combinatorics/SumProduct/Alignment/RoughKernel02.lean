import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughKernel01
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
open scoped BigOperators
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters IntegerHyperplane
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)

structure Reduction where
  k : Fin (n+1) → ℤ
  p : Fin (n+1)
  pivot : k p≠0
  last : ∀ j : Fin (n+1),p<j → k j=0
  character : ∀ g : G,(χ g).toAdd=form k (c.coord g)
  period : ℕ
  period_pos : 0<period
  periodic : sectionFlow c hsk k p (Multiplicative.ofAdd (period:ℝ))∈Γ

variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZ : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z) (hne : χ≠1)
include hΓ hcont hZ hne in
theorem exists_reduction : Nonempty (Reduction c hsk χ Γ) := by
  obtain ⟨k,hk⟩:=integer_character_coordinates c hsk χ Γ hΓ hcont hZ
  have hχ : ∀ g : G,(χ g).toAdd=form k (c.coord g) := by
    intro g
    rw [hk]
    exact Finset.sum_congr rfl (fun i _=>mul_comm _ _)
  have hk0 : k≠0 := by
    intro he
    apply hne
    ext g
    apply Multiplicative.toAdd.injective
    change (χ g).toAdd=0
    rw [hχ,he]
    simp [form]
  obtain ⟨p,hp,hlast⟩:=exists_last_nonzero k hk0
  obtain ⟨K,hK,hperiod⟩:=sectionFlow_period c hsk k p hp Γ hΓ
  exact ⟨⟨k,p,hp,hlast,hχ,K,hK,hperiod⟩⟩

namespace Reduction
variable (R : Reduction c hsk χ Γ)

def chart : RealCoordinates χ.ker n :=
  RationalCharacterKernel.kernelCoordinates c χ R.k R.p R.pivot R.character R.last

def flow : Multiplicative ℝ →* G := sectionFlow c hsk R.k R.p

lemma flow_character (t : ℝ) : (χ (R.flow c hsk χ Γ (Multiplicative.ofAdd t))).toAdd=t :=
  sectionFlow_character c hsk χ R.k R.p R.pivot R.character t

lemma flow_rational (t : ℚ) :
    IsRational c (R.flow c hsk χ Γ (Multiplicative.ofAdd (t:ℝ))) :=
  sectionFlow_rational c hsk R.k R.p t

lemma coset_period (z j : ℤ) (hmod : (R.period:ℤ)∣z-j) :
    (QuotientGroup.mk (R.flow c hsk χ Γ (Multiplicative.ofAdd (z:ℝ))) : G⧸Γ)=
      QuotientGroup.mk (R.flow c hsk χ Γ (Multiplicative.ofAdd (j:ℝ))) :=
  same_coset_of_mod c hsk R.k R.p Γ R.period R.periodic z j hmod

 

theorem lower_dimensional_factorization : ∃ B : ℕ,0<B ∧
    ∀ (v d : ℕ) (P : (Fin v → ℝ) → G) (a m : (Fin v → ℝ) → ℝ),
      (∀ x,(χ (P x)).toAdd=a x+m x) →
      (∀ i,RealPolynomialDegree.HasDegree (fun x=>c.coord (P x) i) d) →
      RealPolynomialDegree.HasDegree a d → RealPolynomialDegree.HasDegree m d →
      ∃ Q : (Fin v → ℝ) → χ.ker,
        (∀ x,P x=R.flow c hsk χ Γ (Multiplicative.ofAdd (a x))*
          (Q x).val*R.flow c hsk χ Γ (Multiplicative.ofAdd (m x))) ∧
        ∀ i,RealPolynomialDegree.HasDegree (fun x=>(R.chart c hsk χ Γ).coord (Q x) i) (B*d) := by
  obtain ⟨B,hB,hdeg⟩:=residual_degree_uniform c hsk χ R.k R.p R.pivot R.character R.last
  refine ⟨B,hB,fun v d P a m hP hpoly ha hm=>?_⟩
  refine ⟨residual c hsk χ R.k R.p R.pivot R.character P a m hP,?_,?_⟩
  · exact residual_factorization c hsk χ R.k R.p R.pivot R.character P a m hP
  · exact hdeg v d P a m hP hpoly ha hm

end Reduction

end RoughKernelFactorization
end
 
end

section
 

 

noncomputable section
namespace RealPolynomialDegree
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

theorem rational_map_bound {τ : Type*} [Fintype τ] {κ : Type*}
    (F : τ → (κ → ℝ) → ℝ) (hF : ∀ i,RationalPolynomialMap.IsPolynomial (F i)) :
    ∃ C : ℕ,0<C ∧ ∀ (v d : ℕ) (P : κ → (Fin v → ℝ) → ℝ),
      (∀ i,HasDegree (P i) d) → ∀ i,HasDegree (fun x=>F i (fun j=>P j x)) (C*d) := by
  classical
  choose p hp using hF
  choose M hM using fun i=>rational_eval_bound (p i)
  let C:=Finset.univ.sup M+1
  refine ⟨C,Nat.zero_lt_succ _,fun v d P hP i=>?_⟩
  have hb : M i≤C := (Finset.le_sup (f:=M) (Finset.mem_univ i)).trans (Nat.le_add_right _ 1)
  have hh:=RealPolynomialDegree.mono (hM i (Fin v) d P hP) (Nat.mul_le_mul_right d hb)
  simpa only [hp i] using hh

theorem log_degree_bound : ∃ C : ℕ,0<C ∧
    ∀ (v d : ℕ) (P : (Fin v → ℝ) → G),
      (∀ i,HasDegree (fun x=>c.coord (P x) i) d) →
      ∀ i,HasDegree (fun x=>canonicalLog c (P x) i) (C*d) := by
  obtain ⟨C,hC,hbound⟩:=rational_map_bound
    (fun i x=>canonicalLog c (c.coord.symm x) i) (canonicalLog_polynomial c)
  refine ⟨C,hC,fun v d P hP i=>?_⟩
  simpa only [Homeomorph.symm_apply_apply] using hbound v d (fun i x=>c.coord (P x) i) hP i

theorem coord_degree_bound : ∃ C : ℕ,0<C ∧
    ∀ (v d : ℕ) (P : (Fin v → ℝ) → G),
      (∀ i,HasDegree (fun x=>canonicalLog c (P x) i) d) →
      ∀ i,HasDegree (fun x=>c.coord (P x) i) (C*d) := by
  obtain ⟨C,hC,hbound⟩:=rational_map_bound
    (fun i x=>c.coord (canonicalExp c x) i) (canonicalExp_polynomial c)
  refine ⟨C,hC,fun v d P hP i=>?_⟩
  simpa only [canonicalExp_log] using hbound v d (fun i x=>canonicalLog c (P x) i) hP i

end RealPolynomialDegree
end
 
end

section
 

 

noncomputable section
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters IntegerHyperplane RealPolynomialDegree
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)

namespace Reduction
variable (R : Reduction c hsk χ Γ)

include R in
omit [IsTopologicalGroup G] in
lemma kernel_connected [IsTopologicalGroup G] : ConnectedSpace χ.ker :=
  coordinates_connected (R.chart c hsk χ Γ)

include R in
omit [IsTopologicalGroup G] in
lemma kernel_simplyConnected [IsTopologicalGroup G] : SimplyConnectedSpace χ.ker :=
  coordinates_simplyConnected (R.chart c hsk χ Γ)

 

theorem logarithmic_factorization : ∃ B : ℕ,0<B ∧
    ∀ (v d : ℕ) (P : (Fin v → ℝ) → G) (a m : (Fin v → ℝ) → ℝ),
      (∀ x,(χ (P x)).toAdd=a x+m x) →
      (∀ i,HasDegree (fun x=>canonicalLog c (P x) i) d) →
      HasDegree a d → HasDegree m d →
      ∃ Q : (Fin v → ℝ) → χ.ker,
        (∀ x,P x=R.flow c hsk χ Γ (Multiplicative.ofAdd (a x))*
          (Q x).val*R.flow c hsk χ Γ (Multiplicative.ofAdd (m x))) ∧
        ∀ i,HasDegree (fun x=>canonicalLog (R.chart c hsk χ Γ) (Q x) i) (B*d) := by
  obtain ⟨E,hE,hcoord⟩:=coord_degree_bound c
  obtain ⟨L,hL,hlog⟩:=log_degree_bound (R.chart c hsk χ Γ)
  obtain ⟨B,hB,hfactor⟩:=R.lower_dimensional_factorization c hsk χ Γ
  refine ⟨L*(B*E),Nat.mul_pos hL (Nat.mul_pos hB hE),fun v d P a m hP hpoly ha hm=>?_⟩
  have hd : d≤E*d := by simpa using Nat.mul_le_mul_right d hE
  obtain ⟨Q,hQ,hdeg⟩:=hfactor v (E*d) P a m hP (hcoord v d P hpoly)
    (RealPolynomialDegree.mono ha hd) (RealPolynomialDegree.mono hm hd)
  refine ⟨Q,hQ,fun i=>?_⟩
  simpa only [Nat.mul_assoc] using hlog v (B*(E*d)) Q hdeg i

end Reduction
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZ : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z) (hne : χ≠1)
include hΓ hcont hZ hne in
 

theorem exists_logarithmic_kernel_reduction :
    ∃ R : Reduction c hsk χ Γ,
      ConnectedSpace χ.ker ∧ SimplyConnectedSpace χ.ker ∧
      (∀ σ : G,CompactSpace (χ.ker⧸kernelLattice χ Γ σ)) ∧
      ∃ B : ℕ,0<B ∧
        ∀ (v d : ℕ) (P : (Fin v → ℝ) → G) (a m : (Fin v → ℝ) → ℝ),
          (∀ x,(χ (P x)).toAdd=a x+m x) →
          (∀ i,HasDegree (fun x=>canonicalLog c (P x) i) d) →
          HasDegree a d → HasDegree m d →
          ∃ Q : (Fin v → ℝ) → χ.ker,
            (∀ x,P x=R.flow c hsk χ Γ (Multiplicative.ofAdd (a x))*
              (Q x).val*R.flow c hsk χ Γ (Multiplicative.ofAdd (m x))) ∧
            ∀ i,HasDegree (fun x=>canonicalLog (R.chart c hsk χ Γ) (Q x) i) (B*d) := by
  obtain ⟨R⟩:=exists_reduction c hsk χ Γ hΓ hcont hZ hne
  exact ⟨R,R.kernel_connected c hsk χ Γ,R.kernel_simplyConnected c hsk χ Γ,
    fun σ=>integer_kernel_quotient_compact χ Γ σ hcont hZ c hΓ,
    R.logarithmic_factorization c hsk χ Γ⟩

end RoughKernelFactorization
end
 
end

section
 

 

noncomputable section
open scoped NNReal
namespace UniformLipschitzApproximation
variable {I X : Type*} [PseudoMetricSpace X] [Nonempty X]
variable (f : I → X → ℝ) (B : ℝ) (hB : 0≤B)
variable (hf : ∀ i x,|f i x|≤B)
variable (hmod : ∀ ε : ℝ,0<ε → ∃ δ : ℝ,0<δ ∧
  ∀ i x y,dist x y<δ → |f i x-f i y|<ε)

include hB hf hmod in
theorem exists_common_bound (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ≥0,∀ i,∃ g : X → ℝ,LipschitzWith K g ∧
      (∀ x,|g x-f i x|<ε) ∧ ∀ x,|g x|≤B+ε := by
  obtain ⟨δ,hδ,hclose⟩:=hmod (ε/2) (by linarith)
  let K : ℝ≥0:=⟨2*B/δ,div_nonneg (by positivity) hδ.le⟩
  have hKδ : (K:ℝ)*δ=2*B := by
    change (2*B/δ)*δ=2*B
    exact div_mul_cancel₀ _ hδ.ne'
  refine ⟨K,fun i=>?_⟩
  let A (x z : X):=f i z+(K:ℝ)*dist x z
  let g (x : X):=⨅ z,A x z
  have hbdd (x : X) : BddBelow (Set.range (A x)) := by
    refine ⟨-B,?_⟩
    rintro _ ⟨z,rfl⟩
    have hp : 0≤(K:ℝ)*dist x z:=mul_nonneg K.coe_nonneg dist_nonneg
    dsimp [A]
    linarith [(abs_le.mp (hf i z)).1]
  have hle (x z : X) : g x≤A x z:=ciInf_le (hbdd x) z
  have hdiff (x y : X) : g x-g y≤(K:ℝ)*dist x y := by
    have hh : g x-(K:ℝ)*dist x y≤g y := by
      apply le_ciInf
      intro z
      have ht:=dist_triangle x y z
      have hm:=mul_le_mul_of_nonneg_left ht K.coe_nonneg
      have hl:=hle x z
      dsimp [A] at hl ⊢
      linarith
    linarith
  have hLip : LipschitzWith K g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,abs_le]
    exact ⟨by have hh:=hdiff y x; rw [dist_comm y x] at hh; linarith,hdiff x y⟩
  have happ (x : X) : |g x-f i x|<ε := by
    have hu : g x≤f i x := by simpa [A] using hle x x
    have hl : f i x-ε/2≤g x := by
      apply le_ciInf
      intro z
      by_cases hz : dist x z<δ
      · have hh:=hclose i x z hz
        have hp:=mul_nonneg K.coe_nonneg (dist_nonneg (x:=x) (y:=z))
        dsimp [A]
        linarith [(abs_lt.mp hh).2]
      · have hh : 2*B≤(K:ℝ)*dist x z := by
          rw [←hKδ]
          exact mul_le_mul_of_nonneg_left (le_of_not_gt hz) K.coe_nonneg
        dsimp [A]
        linarith [(abs_le.mp (hf i x)).2,(abs_le.mp (hf i z)).1]
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    linarith
  refine ⟨g,hLip,happ,fun x=>?_⟩
  have hh:=abs_add_le (g x-f i x) (f i x)
  have he : g x-f i x+f i x=g x:=by ring
  rw [he] at hh
  linarith [happ x,hf i x]

end UniformLipschitzApproximation

end
end
end
end

end OAI
