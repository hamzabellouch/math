import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice12
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
namespace RealPolynomialDegree
universe u v
variable {σ : Type u} {τ : Type v}

def HasDegree (f : (σ → ℝ) → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial σ ℝ,p.totalDegree ≤ d ∧ ∀ x,f x=MvPolynomial.eval x p

lemma const (a : ℝ) (d : ℕ) : HasDegree (fun _ : σ → ℝ=>a) d :=
  ⟨MvPolynomial.C a,by simp,by simp⟩

lemma mono {f : (σ → ℝ) → ℝ} {d e : ℕ} (hf : HasDegree f d) (hde : d ≤ e) :
    HasDegree f e := by
  obtain ⟨p,hp,he⟩:=hf
  exact ⟨p,hp.trans hde,he⟩

lemma add {f g : (σ → ℝ) → ℝ} {d e : ℕ}
    (hf : HasDegree f d) (hg : HasDegree g e) : HasDegree (fun x=>f x+g x) (max d e) := by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,hqv⟩:=hg
  exact ⟨p+q,(MvPolynomial.totalDegree_add p q).trans (max_le_max hp hq),by simp [he,hqv]⟩

lemma mul {f g : (σ → ℝ) → ℝ} {d e : ℕ}
    (hf : HasDegree f d) (hg : HasDegree g e) : HasDegree (fun x=>f x*g x) (d+e) := by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,hqv⟩:=hg
  exact ⟨p*q,(MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq),by simp [he,hqv]⟩

lemma scale {f : (σ → ℝ) → ℝ} {d : ℕ} (hf : HasDegree f d) (a : ℝ) :
    HasDegree (fun x=>a*f x) d := by simpa using mul (const a 0) hf

lemma neg {f : (σ → ℝ) → ℝ} {d : ℕ} (hf : HasDegree f d) :
    HasDegree (fun x=>-f x) d := by simpa using scale hf (-1)

lemma rational_eval_bound (p : MvPolynomial τ ℚ) : ∃ M : ℕ,
    ∀ (σ : Type u) (d : ℕ) (f : τ → (σ → ℝ) → ℝ),
      (∀ i,HasDegree (f i) d) → HasDegree
        (fun x=>MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i=>f i x) p) (M*d) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0,fun σ d f hf=>by simpa using const (σ:=σ) (a:ℝ) 0⟩
  | add p q hp hq =>
    obtain ⟨M,hM⟩:=hp
    obtain ⟨N,hN⟩:=hq
    refine ⟨max M N,fun σ d f hf=>?_⟩
    have he:=add (hM σ d f hf) (hN σ d f hf)
    have hb : max (M*d) (N*d) ≤ max M N*d := max_le
      (Nat.mul_le_mul_right d (le_max_left M N))
      (Nat.mul_le_mul_right d (le_max_right M N))
    have he' := RealPolynomialDegree.mono he hb
    simpa only [MvPolynomial.eval₂_add] using he'
  | mul_X p i hp =>
    obtain ⟨M,hM⟩:=hp
    refine ⟨M+1,fun σ d f hf=>?_⟩
    have he:=mul (hM σ d f hf) (hf i)
    simpa only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,Nat.add_mul,Nat.one_mul] using he

end RealPolynomialDegree
end
 
end

section
 

 

noncomputable section
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters IntegerHyperplane RealPolynomialDegree
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1))

omit [IsTopologicalGroup G] in
lemma multiplication_degree [IsTopologicalGroup G] : ∃ C : ℕ,0 < C ∧
    ∀ (v d : ℕ) (P Q : (Fin v → ℝ) → G),
      (∀ i,HasDegree (fun x=>c.coord (P x) i) d) →
      (∀ i,HasDegree (fun x=>c.coord (Q x) i) d) →
      ∀ i,HasDegree (fun x=>c.coord (P x*Q x) i) (C*d) := by
  classical
  choose M hM using fun i=>rational_eval_bound (c.correction i)
  let C := Finset.univ.sup M+1
  have hC : 0 < C := Nat.zero_lt_succ _
  have hMC (i : Fin (n+1)) : M i ≤ C :=
    (Finset.le_sup (f:=M) (Finset.mem_univ i)).trans (Nat.le_add_right _ 1)
  refine ⟨C,hC,fun v d P Q hP hQ i=>?_⟩
  have hc:=hM i (Fin v) d
    (Sum.elim (fun j : Fin i.val=>fun x=>c.coord (P x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val=>fun x=>c.coord (Q x) ⟨j.val,lt_trans j.isLt i.isLt⟩)) (by
        intro j
        cases j with
        | inl j=>exact hP _
        | inr j=>exact hQ _)
  have ha : HasDegree (fun x=>c.coord (P x) i+c.coord (Q x) i) d := by
    simpa using RealPolynomialDegree.add (hP i) (hQ i)
  have he:=RealPolynomialDegree.add ha hc
  have hd : d ≤ C*d := by simpa using Nat.mul_le_mul_right d hC
  have hb : max d (M i*d) ≤ C*d := max_le hd (Nat.mul_le_mul_right d (hMC i))
  have heval (x : Fin v → ℝ) :
      (fun j=>Sum.elim
        (fun j : Fin i.val=>fun x=>c.coord (P x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val=>fun x=>c.coord (Q x) ⟨j.val,lt_trans j.isLt i.isLt⟩) j x)=
      Sum.elim (fun j : Fin i.val=>c.coord (P x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val=>c.coord (Q x) ⟨j.val,lt_trans j.isLt i.isLt⟩) := by
    funext j
    cases j <;> rfl
  simpa only [c.mul_coord,heval] using RealPolynomialDegree.mono he hb

variable (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (k : Fin (n+1) → ℤ) (p : Fin (n+1))
variable (hp : k p ≠ 0) (hχ : ∀ g : G,(χ g).toAdd=form k (c.coord g))
variable (hlast : ∀ j : Fin (n+1),p < j → k j=0)

omit [IsTopologicalGroup G] in
lemma sectionFlow_degree [IsTopologicalGroup G] {v d : ℕ} {a : (Fin v → ℝ) → ℝ} (ha : HasDegree a d) :
    ∀ i,HasDegree
      (fun x=>c.coord (sectionFlow c hsk k p (Multiplicative.ofAdd (a x))) i) d := by
  classical
  intro i
  change HasDegree (fun x=>c.coord (axis c p (a x/(k p:ℝ))) i) d
  simp only [coord_axis,Pi.single_apply]
  split_ifs
  · simpa [div_eq_mul_inv,mul_comm] using RealPolynomialDegree.scale ha (k p:ℝ)⁻¹
  · exact RealPolynomialDegree.const 0 d

 

theorem residual_degree_uniform : ∃ B : ℕ,0 < B ∧
    ∀ (v d : ℕ) (P : (Fin v → ℝ) → G) (a m : (Fin v → ℝ) → ℝ)
      (hP : ∀ x,(χ (P x)).toAdd=a x+m x),
      (∀ i,HasDegree (fun x=>c.coord (P x) i) d) → HasDegree a d → HasDegree m d →
      ∀ i,HasDegree (fun x=>(RationalCharacterKernel.kernelCoordinates c χ k p hp hχ hlast).coord
        (residual c hsk χ k p hp hχ P a m hP x) i) (B*d) := by
  obtain ⟨C,hC,hMul⟩:=multiplication_degree c
  refine ⟨C*C,Nat.mul_pos hC hC,fun v d P a m hP hpoly ha hm i=>?_⟩
  have h₁:=hMul v d _ _ (sectionFlow_degree c hsk k p (RealPolynomialDegree.neg ha)) hpoly
  have h₂:=hMul v (C*d) _ _ h₁ (fun i=>
    RealPolynomialDegree.mono (sectionFlow_degree c hsk k p (RealPolynomialDegree.neg hm) i)
      (by simpa using Nat.mul_le_mul_right d hC))
  change HasDegree (fun x=>c.coord
    (sectionFlow c hsk k p (Multiplicative.ofAdd (-a x))*P x*
      sectionFlow c hsk k p (Multiplicative.ofAdd (-m x))) (p.succAbove i)) ((C*C)*d)
  simpa only [Nat.mul_assoc] using h₂ (p.succAbove i)

end RoughKernelFactorization
end
 
end

section
 

 
noncomputable section
namespace NonnormalCoset
variable {G A : Type*} [Group G] [Group A]
variable [TopologicalSpace G] [TopologicalSpace A]
variable [IsTopologicalGroup G] [IsTopologicalGroup A]
variable (Γ : Subgroup G) (Λ : Subgroup A) (p : G →* A)
variable (hp : Continuous p) (hΓ : ∀ g∈Γ,p g∈Λ)

def map : C(G⧸Γ,A⧸Λ) where
  toFun:=Quotient.lift (fun g=>QuotientGroup.mk (p g)) (by
    intro g h he
    apply QuotientGroup.eq.mpr
    rw [←map_inv,←map_mul]
    exact hΓ _ (QuotientGroup.leftRel_apply.mp he))
  continuous_toFun:=
    (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp hp)

omit [IsTopologicalGroup G] [IsTopologicalGroup A] in
@[simp] lemma map_mk [IsTopologicalGroup G] [IsTopologicalGroup A] (g : G) : map Γ Λ p hp hΓ (QuotientGroup.mk g)=QuotientGroup.mk (p g):=rfl
end NonnormalCoset

namespace PhysicalCubeMaps
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type*} [DecidableEq ι]

def vertices (p : C(X,Y)) : C((Finset ι → X),(Finset ι → Y)) where
  toFun x w:=p (x w)
  continuous_toFun:=continuous_pi (fun w=>p.continuous.comp (continuous_apply w))

def upperFace (i : ι) (S : C(Y,Y)) : C((Finset ι → Y),(Finset ι → Y)) where
  toFun y w:=if i∈w then S (y w) else y w
  continuous_toFun:=continuous_pi (fun w=>by
    by_cases h : i∈w
    · simpa only [h,ite_true,Function.comp_def] using S.continuous.comp (continuous_apply w)
    · simpa only [h,ite_false] using (continuous_apply w : Continuous (fun y : Finset ι → Y=>y w)))

omit [DecidableEq ι] in
@[simp] lemma vertices_apply [DecidableEq ι] (p : C(X,Y)) (x : Finset ι → X) (w : Finset ι) :
    vertices p x w=p (x w):=rfl
@[simp] lemma upperFace_apply (i : ι) (S : C(Y,Y)) (x : Finset ι → Y) (w : Finset ι) :
    upperFace i S x w=if i∈w then S (x w) else x w:=rfl

end PhysicalCubeMaps
end
 
end

section
 

 

noncomputable section
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G) (σ : G)

def kernelInclusion : χ.ker →* G :=
  (MulAut.conj σ⁻¹).toMonoidHom.comp χ.ker.subtype

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma kernelInclusion_apply [TopologicalSpace G] [IsTopologicalGroup G] (h : χ.ker) :
    kernelInclusion χ σ h=σ⁻¹*h.val*σ := by simp [kernelInclusion]

lemma kernelInclusion_continuous : Continuous (kernelInclusion χ σ) := by
  change Continuous (fun h : χ.ker=>kernelInclusion χ σ h)
  simp only [kernelInclusion_apply]
  exact
    ((continuous_const.mul continuous_subtype_val).mul continuous_const :
      Continuous (fun h : χ.ker=>σ⁻¹*h.val*σ))

def kernelLattice : Subgroup χ.ker := Γ.comap (kernelInclusion χ σ)

@[simp] lemma mem_kernelLattice (h : χ.ker) :
    h∈kernelLattice χ Γ σ ↔ σ⁻¹*h.val*σ∈Γ := by
  change kernelInclusion χ σ h∈Γ ↔ _
  rw [kernelInclusion_apply]

 

def kernelTestMap (ℓ : G) : C(χ.ker⧸kernelLattice χ Γ σ,G⧸Γ) where
  toFun x:=(ℓ*σ) • NonnormalCoset.map (kernelLattice χ Γ σ) Γ
    (kernelInclusion χ σ) (kernelInclusion_continuous χ σ) (fun _ h=>h) x
  continuous_toFun:=(continuous_const : Continuous
    (fun _ : χ.ker⧸kernelLattice χ Γ σ=>ℓ*σ)).smul
    (NonnormalCoset.map (kernelLattice χ Γ σ) Γ
      (kernelInclusion χ σ) (kernelInclusion_continuous χ σ) (fun _ h=>h)).continuous

@[simp] lemma kernelTestMap_mk (ℓ : G) (h : χ.ker) :
    kernelTestMap χ Γ σ ℓ (QuotientGroup.mk h)=
      QuotientGroup.mk (ℓ*h.val*σ) := by
  change (ℓ*σ) • (QuotientGroup.mk (kernelInclusion χ σ h) : G⧸Γ)=_
  rw [kernelInclusion_apply]
  change QuotientGroup.mk ((ℓ*σ)*(σ⁻¹*h.val*σ))=_
  congr 1
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma character_conjugate [TopologicalSpace G] [IsTopologicalGroup G] (x : G) : χ (σ*x*σ⁻¹)=χ x := by
  simp only [map_mul,map_inv]
  apply Multiplicative.toAdd.injective
  change (χ σ).toAdd+(χ x).toAdd+(-(χ σ).toAdd)=(χ x).toAdd
  ring

variable (hcont : Continuous χ)
variable (hZ : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)
variable (C : Set G) (hC : IsCompact C) (hrep : ∀ g : G,∃ c∈C,c⁻¹*g∈Γ)

include hcont hZ hC hrep in
 
theorem kernel_quotient_compact : CompactSpace (χ.ker⧸kernelLattice χ Γ σ) := by
  let Γσ:=Γ.map (MulAut.conj σ).toMonoidHom
  let Cσ:=(fun x : G=>σ*x*σ⁻¹) '' C
  have hCσ : IsCompact Cσ:=hC.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hrepσ : ∀ g : G,∃ c∈Cσ,c⁻¹*g∈Γσ := by
    intro g
    obtain ⟨c,hc,hg⟩:=hrep (σ⁻¹*g*σ)
    refine ⟨σ*c*σ⁻¹,⟨c,hc,rfl⟩,?_⟩
    apply Subgroup.mem_map.mpr
    refine ⟨c⁻¹*(σ⁻¹*g*σ),hg,?_⟩
    change σ*(c⁻¹*(σ⁻¹*g*σ))*σ⁻¹=(σ*c*σ⁻¹)⁻¹*g
    group
  have hZσ : ∀ g∈Γσ,∃ z : ℤ,(χ g).toAdd=z := by
    rintro g ⟨a,ha,rfl⟩
    obtain ⟨z,hz⟩:=hZ a ha
    refine ⟨z,?_⟩
    change (χ (σ*a*σ⁻¹)).toAdd=(z:ℝ)
    rw [character_conjugate]
    exact hz
  obtain ⟨D,hD,hDker,hDrep⟩:=CharacterKernelLattice.compact_kernel_representatives
    χ hcont Γσ Cσ hCσ hrepσ hZσ
  have hcompact : IsCompact ((Subtype.val : χ.ker → G) ⁻¹' D) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hD
    intro x hx
    exact ⟨⟨x,hDker hx⟩,rfl⟩
  apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
  refine ⟨(Subtype.val : χ.ker → G) ⁻¹' D,hcompact,by intro x _; trivial,?_⟩
  intro g _
  obtain ⟨d,hd,hg⟩:=hDrep g.val g.property
  refine ⟨⟨d,hDker hd⟩,hd,?_⟩
  rw [mem_kernelLattice]
  change σ⁻¹*(d⁻¹*g.val)*σ∈Γ
  obtain ⟨a,ha,he⟩:=Subgroup.mem_map.mp hg
  have hh : σ⁻¹*(d⁻¹*g.val)*σ=a := by
    change σ*a*σ⁻¹=d⁻¹*g.val at he
    rw [←he]
    group
  rwa [hh]

variable {n : ℕ} (c : RealCoordinates G n)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
include hcont hZ hΓ in
theorem integer_kernel_quotient_compact : CompactSpace (χ.ker⧸kernelLattice χ Γ σ) := by
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates c Γ hΓ
  exact kernel_quotient_compact χ Γ σ hcont hZ C hC hrep

end RoughKernelFactorization

end
end
end
end

end OAI
