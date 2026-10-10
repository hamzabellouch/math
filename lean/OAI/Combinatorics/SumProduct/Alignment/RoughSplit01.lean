import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughKernel05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughCommonKernelCover
open RationalLattice MalcevCharacters RoughKernelFactorization RealPolynomialDegree
open RoughKernelCover
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
include hΓ in
 

theorem common_kernel_cover :
    ∃ Λ : Subgroup χ.ker,∃ e : RealCoordinates χ.ker n,SecondKind e ∧
      (∀ g : χ.ker,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      (∀ j : Fin R.period,Λ≤kernelLattice χ Γ (residueSigma c hsk χ Γ R j)) ∧
      ∃ E : ℕ,0<E ∧ ∀ v D : ℕ,∀ P : (Fin v→ℝ)→χ.ker,
        (∀ i,HasDegree (fun x=>canonicalLog (R.chart c hsk χ Γ) (P x) i) D) →
        ∀ i,HasDegree (fun x=>canonicalLog e (P x) i) (E*D) := by
  classical
  let d:=R.chart c hsk χ Γ
  have hpoly (j : Fin R.period) : ∀ i,RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>
      c.coord (kernelInclusion χ (residueSigma c hsk χ Γ R j) (d.coord.symm x)) i):=by
    apply kernel_embedding_polynomial c hsk χ Γ R
    simpa only [residueSigma,Rat.cast_natCast] using R.flow_rational c hsk χ Γ (j.val:ℚ)
  choose A hA hgrid using fun j=>rationalHom_origin_grid c d
    (kernelInclusion χ (residueSigma c hsk χ Γ R j)) (hpoly j)
  let T:=∏ j,A j
  have hT : 0<T:=Finset.prod_pos (fun j _=>hA j)
  obtain ⟨w,hw,hTw,hcl⟩:=exists_lattice_weights d T hT
  let Λ:=weightedLattice d w hcl
  let d':=scaledCoordinates d w hw
  let e:=secondCoordinates d'
  have hΛ : ∀ g : χ.ker,g∈Λ ↔ ∀ i,∃ z : ℤ,d'.coord g i=z:=weightedLattice_iff d w hcl hw
  have hle (j : Fin R.period) : Λ≤kernelLattice χ Γ (residueSigma c hsk χ Γ R j):=by
    intro g hg
    apply (hΓ _).mpr
    have hAw (i) : A j∣w i:=(Finset.dvd_prod_of_mem A (Finset.mem_univ j)).trans (hTw i)
    have hx : ∀ i,∃ z : ℤ,d.coord g i=(A j:ℝ)*(z:ℝ):=by
      intro i
      obtain ⟨a,ha⟩:=hg i
      obtain ⟨b,hb⟩:=hAw i
      refine ⟨(b:ℤ)*a,?_⟩
      rw [ha,hb]
      push_cast
      ring
    simpa using hgrid j (d.coord g) hx
  have he : ∀ i,RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>e.coord (d.coord.symm x) i):=by
    intro i
    apply polynomial_expCoordinates d'
    intro j
    change RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>d.coord (d.coord.symm x) j/(w j:ℝ))
    simpa only [Homeomorph.apply_symm_apply,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast] using
      RationalPolynomialMap.mul (RationalPolynomialMap.coordinate j) (RationalPolynomialMap.const (w j:ℚ)⁻¹)
  obtain ⟨C,hC,hcoord⟩:=coord_degree_bound d
  obtain ⟨L,hL,hlog⟩:=log_degree_bound e
  obtain ⟨U,hU,htransfer⟩:=rational_map_bound (fun i x=>e.coord (d.coord.symm x) i) he
  refine ⟨Λ,e,secondCoordinates_secondKind d',expCoordinates_lattice d' Λ hΛ,hle,
    L*(U*C),Nat.mul_pos hL (Nat.mul_pos hU hC),?_⟩
  intro v D P hP i
  have hc:=hcoord v D P hP
  have ht : ∀ j,HasDegree (fun x=>e.coord (P x) j) (U*(C*D)):=by
    intro j
    simpa only [Homeomorph.symm_apply_apply] using htransfer v (C*D) (fun j x=>d.coord (P x) j) hc j
  simpa only [Nat.mul_assoc] using hlog v (U*(C*D)) P ht i

end RoughCommonKernelCover

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughCommonKernelDiscrepancy
open RationalLattice MalcevCharacters RoughKernelFactorization UniformSlowPolynomials
open RoughSamplingWeights FinitePieceAverages RoughKernelDiscrepancy RoughCoverTests
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZint : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)
variable (Λ : Subgroup χ.ker) (d : RealCoordinates χ.ker n)
variable (hΛ : ∀ g : χ.ker,g∈Λ ↔ ∀ i,∃ z : ℤ,d.coord g i=z)
variable (hle : ∀ j : Fin R.period,Λ≤kernelLattice χ Γ (residueSigma c hsk χ Γ R j))
variable {X : Type*} [PseudoMetricSpace X] (V : (G⧸Γ) ≃ₜ X)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
include hΓ hcont hZint hle in
 
theorem source_common_kernel_discrepancy (e : κ→ι→ℕ) (A C side B : ℝ)
    (hA : 0≤A) (hC : 0≤C) (hside : 0<side) (hB : 0≤B)
    (L : NNReal) (ε : ℝ) (hε : 0<ε) :
    letI :=coordinateQuotientMetric d Λ hΛ
    ∃ M : ℕ,0<M ∧ ∃ L' : NNReal,0<L' ∧ ∃ δ : ℝ,0<δ ∧
    ∀ Z : ℝ,(R.period:ℝ)≤Z →∀ coeff : κ→ℝ,(∀ k,|coeff k| * Z^(∑i,e k i)≤A) →
    ∀ (lo hi : ι→ℝ),(∀ i,-(C*Z)≤lo i ∧ hi i≤C*Z) →(∀ i,side*Z≤hi i-lo i) →
    ∀ (res : ι→ℤ) (t : ℕ),0<t →t.Coprime R.period →1+(t:ℝ)≤δ*Z →
    ∀ F : X→ℂ,LipschitzWith L F →(∀ x,‖F x‖≤B) →
    ∀ (P : (ι→ℤ)→G) (Q : (ι→ℤ)→χ.ker) (m : MvPolynomial ι ℤ),
      (∀ x,P x=R.flow c hsk χ Γ (Multiplicative.ofAdd (form e coeff (fun i=>(x i:ℝ))))*
        (Q x).val*R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))) →
    ∀ η : ℝ,η≤‖mean (boxIndices lo hi (fun _=>0) 1) (fun x=>F (V (QuotientGroup.mk (P x))))-
      mean (physicalResidueBox lo hi res t) (fun x=>F (V (QuotientGroup.mk (P x))))‖ →
    ∃ u : ι→Fin R.period,∃ (lo' hi' : ι→ℝ) (res' : ι→ℤ) (g : (χ.ker⧸Λ)→ℂ),
      LipschitzWith L' g ∧ (∀ y,‖g y‖≤L') ∧
      (∀ i,-(C+1)*(Z/R.period)≤lo' i ∧ hi' i≤(C+1)*(Z/R.period)) ∧
      (∀ i,(side/M)*(Z/R.period)≤hi' i-lo' i) ∧
      η-7*ε≤‖mean (boxIndices lo' hi' (fun _=>0) 1)
        (fun y=>g (QuotientGroup.mk (Q (integerAffine (fun i=>((u i).val:ℤ)) R.period y))))-
      mean (physicalResidueBox lo' hi' res' t)
        (fun y=>g (QuotientGroup.mk (Q (integerAffine (fun i=>((u i).val:ℤ)) R.period y))))‖ := by
  classical
  let :=coordinateQuotientMetric d Λ hΛ
  obtain ⟨M,hM,L₀,δ,hδ,hsrc⟩:=source_kernel_discrepancy c hsk χ Γ R hΓ hcont hZint V
    e A C side B hA hC hside hB L ε hε
  have hall (j : Fin R.period) :
      let σ:=residueSigma c hsk χ Γ R j
      letI :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZint
      ∃ L₁ : NNReal,∀ F : (χ.ker⧸kernelLattice χ Γ σ)→ℂ,LipschitzWith L₀ F →
        (∀ y,‖F y‖≤B+ε) →∃ g : (χ.ker⧸Λ)→ℂ,LipschitzWith L₁ g ∧ (∀ y,‖g y‖≤B+ε+ε) ∧
        ∀ (S T : Finset (ι→ℤ)) (P : (ι→ℤ)→χ.ker) (η : ℝ),
          η≤‖mean S (fun x=>F (QuotientGroup.mk (P x)))-mean T (fun x=>F (QuotientGroup.mk (P x)))‖ →
          η-2*ε≤‖mean S (fun x=>g (QuotientGroup.mk (P x)))-mean T (fun x=>g (QuotientGroup.mk (P x)))‖:=by
    let σ:=residueSigma c hsk χ Γ R j
    let :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZint
    obtain ⟨K,hK⟩:=uniform_cover_tests d Λ (kernelLattice χ Γ σ) hΛ (hle j) (Homeomorph.refl _)
      L₀ (B+ε) ε (by linarith) hε
    refine ⟨K,?_⟩
    intro F hF hFB
    obtain ⟨g,hg,hgB,hd⟩:=hK F hF hFB
    exact ⟨g,hg,hgB,hd (ι→ℤ)⟩
  choose L₁ hL₁ using hall
  let L' : NNReal:=max (Finset.univ.sup L₁) ⟨B+ε+ε,by linarith⟩+1
  have hpos : 0<L':=by dsimp [L']; positivity
  refine ⟨M,hM,L',hpos,δ,hδ,?_⟩
  intro Z hZ coeff hcoeff lo hi hbox hside' res t ht htK hsmall F hF hFB P Q m hP η hbad
  obtain ⟨u,j,lo',hi',res',g,hg,hgB,hbox',hside'',hbad'⟩:=
    hsrc Z hZ coeff hcoeff lo hi hbox hside' res t ht htK hsmall F hF hFB P Q m hP η hbad
  let σ:=residueSigma c hsk χ Γ R j
  let :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZint
  obtain ⟨f,hf,hfB,hfd⟩:=hL₁ j g hg hgB
  have hLL : L₁ j≤L':=(Finset.le_sup (f:=L₁) (Finset.mem_univ j)).trans
    ((le_max_left _ _).trans (le_add_of_nonneg_right (by positivity)))
  have hB' : B+ε+ε≤(L':ℝ):=by
    exact_mod_cast (show (⟨B+ε+ε,by linarith⟩ : NNReal)≤L' from
      (le_max_right (Finset.univ.sup L₁) _).trans (le_add_of_nonneg_right (show (0:NNReal)≤1 by norm_num)))
  refine ⟨u,lo',hi',res',f,hf.weaken hLL,fun y=>(hfB y).trans hB',hbox',hside'',?_⟩
  have hh:=hfd (boxIndices lo' hi' (fun _=>0) 1) (physicalResidueBox lo' hi' res' t)
    (fun y=>Q (integerAffine (fun i=>((u i).val:ℤ)) R.period y)) (η-5*ε) hbad'
  linarith

end RoughCommonKernelDiscrepancy

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughSplitBlockReduction
open RationalLattice MalcevCharacters RoughKernelFactorization RealPolynomialDegree
open RoughBadBlock RoughRationalKernel RoughRationalBlock RoughScales
open RoughCharacterThinning RoughCommonKernelDiscrepancy RoughCommonKernelCover
open RoughSamplingWeights FinitePieceAverages PolynomialLineCoefficients CorrectedBoxLeibman

lemma spatial_affine {v d : ℕ} {f : (Fin (v+1)→ℝ)→ℝ} (hf : HasDegree f d)
    (u : Fin v→ℝ) (K : ℝ) :
    HasDegree (fun y : Fin (v+1)→ℝ=>f (Fin.cons (y 0) (fun i=>u i+K*(Fin.tail y i)))) d:=by
  let T (y : Fin (v+1)→ℝ) : Fin (v+1)→ℝ:=Fin.cons (y 0) (fun j=>u j+K*(Fin.tail y j))
  have hg (i : Fin (v+1)) : HasDegree (fun y=>T y i) 1:=by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact RoughPolynomialDegree.coordinate (0 : Fin (v+1))
    · simpa only [T,Fin.cons_succ,Fin.tail,max_self] using RealPolynomialDegree.add
        (RealPolynomialDegree.const (σ:=Fin (v+1)) (u j) 1)
        (RealPolynomialDegree.scale (RoughPolynomialDegree.coordinate j.succ) K)
  have h:=RoughPolynomialDegree.compose hf (fun i y=>T y i) hg
  simpa only [one_mul,T] using h

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZint : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ):=mtr.toUniformSpace.toTopologicalSpace

private def metricIdentity :
    @Homeomorph (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) mtr.toUniformSpace.toTopologicalSpace := by
  refine @Homeomorph.mk _ _ (QuotientGroup.instTopologicalSpace Γ) mtr.toUniformSpace.toTopologicalSpace
    (Equiv.refl _) ?_ ?_
  · rw [htop]; exact @continuous_id (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
  · rw [htop]; exact @continuous_id (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)

include hΓ hcont hZint htop in
 

theorem reduce_split_blocks (v D s : ℕ) (c₀ C₀ A : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hA : 0≤A) (hη : 0<η) :
    ∃ Λ : Subgroup χ.ker,∃ d : RealCoordinates χ.ker n,SecondKind d ∧
      ∃ hΛ : ∀ g : χ.ker,g∈Λ ↔ ∀ i,∃ z : ℤ,d.coord g i=z,
      ∃ D' : ℕ,∃ c' : ℝ,0<c' ∧ ∃ B' : NNReal,0<B' ∧ ∃ δ : ℝ,0<δ ∧
      letI :=coordinateQuotientMetric d Λ hΛ
      ∀ H : ℕ,0<H →∃ N : ℕ,∀ (w : ℕ) (S Z : ℝ),N≤w →R.period≤w →
        0<S →(R.period:ℝ)≤Z →1+2*S≤δ*Z →
        ∀ b₀ : Block c Γ v D c₀ C₀ B η w S Z N,
        ∀ (θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ)
          (M : PolynomialLineCoefficients.Grid v s→Polynomial ℚ),
        (∀ I,(θ I).natDegree ≤ s) →
        (∀ z : ℝ,∀ x : Fin v→ℝ,gridEval (fun I=>(θ I).eval z) x=(χ (b₀.P (Fin.cons z x))).toAdd) →
        Split w N Z A θ 0 1 M →
        Nonempty (Block d Λ v D' c' (C₀+1) B' (η/2) w S (Z/R.period) H) := by
  classical
  obtain ⟨Λ,d,hd,hΛ,hle,E,hE,hdegree⟩:=common_kernel_cover c hsk χ Γ R hΓ
  let :=coordinateQuotientMetric d Λ hΛ
  obtain ⟨J,hJ,hkernel⟩:=kernel_polynomial c hsk χ Γ R
  let ε : ℝ:=η/14
  have hε : 0<ε:=by dsimp [ε]; positivity
  obtain ⟨M₀,hM₀,B',hB',δ,hδ,hdisc⟩:=source_common_kernel_discrepancy c hsk χ Γ R hΓ hcont hZint
    Λ d hΛ hle (metricIdentity Γ htop) (fun (I : PolynomialLineCoefficients.Grid v s) i=>(I i).val)
    A C₀ c₀ (B:ℝ) hA hC₀.le hc₀ B.coe_nonneg B ε hε
  let D':=E*(J*max D ((v+1)*s+v*s))
  refine ⟨Λ,d,hd,hΛ,D',c₀/(M₀:ℝ),div_pos hc₀ (by exact_mod_cast hM₀),B',hB',δ,hδ,?_⟩
  intro H hH
  obtain ⟨N,hN⟩:=ConstantCoefficientRationalization.finite_van_der_waerden
    (Fintype.card (Fin v→Fin R.period)) H
  refine ⟨N,?_⟩
  intro w S Z hw hwp hS hZ hsmall b₀ θ M hθ he hM
  obtain ⟨Q,hQP,hQdeg⟩:=hkernel v D s b₀.P θ M b₀.degree hθ hM.1 he
  have hQd : ∀ i,HasDegree (fun y=>canonicalLog d (Q y) i) D':=
    hdegree (v+1) _ Q hQdeg
  have hfib (j : Fin (N+1)) :
      ∃ u : Fin v→Fin R.period,∃ (lo hi : Fin v→ℝ) (res : Fin v→ℤ) (f : (χ.ker⧸Λ)→ℂ),
        LipschitzWith B' f ∧ (∀ y,‖f y‖≤B') ∧
        (∀ i,-(C₀+1)*(Z/R.period)≤lo i ∧ hi i≤(C₀+1)*(Z/R.period)) ∧
        (∀ i,(c₀/M₀)*(Z/R.period)≤hi i-lo i) ∧
        η/2≤‖mean (boxIndices lo hi (fun _=>0) 1)
          (fun y=>f (QuotientGroup.mk (Q (Fin.cons (j.val:ℝ)
            (fun i=>((integerAffine (fun i=>((u i).val:ℤ)) R.period y i:ℤ):ℝ))))))-
          mean (physicalResidueBox lo hi res (b₀.start+b₀.step*(j.val:ℤ)).natAbs)
          (fun y=>f (QuotientGroup.mk (Q (Fin.cons (j.val:ℝ)
            (fun i=>((integerAffine (fun i=>((u i).val:ℤ)) R.period y i:ℤ):ℝ))))))‖:=by
    have hj : (j.val:ℤ)≤N:=by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hscale:=b₀.scales (j.val:ℤ) (by positivity) hj
    have htpos : 0<(b₀.start+b₀.step*(j.val:ℤ):ℤ):=by exact_mod_cast hS.trans_le hscale.1
    have hcast : (((b₀.start+b₀.step*(j.val:ℤ)).natAbs:ℕ):ℝ)=((b₀.start+b₀.step*(j.val:ℤ):ℤ):ℝ):=by
      simp only [Nat.cast_natAbs,abs_of_nonneg (by exact_mod_cast htpos.le)]
    have htK : (b₀.start+b₀.step*(j.val:ℤ)).natAbs.Coprime R.period:=
      (period_coprime_of_rough w R.period _ R.period_pos hwp
        ((rough_iff_coprime w _).mp (b₀.rough _ (by positivity) hj))).symm
    obtain ⟨m,hm⟩:=integer_spatial_on_lattice M j.val (fun I=>hM.2.2.1 I j.val (by omega))
    have hfactor (x : Fin v→ℤ) :
        b₀.P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ)))=
          R.flow c hsk χ Γ (Multiplicative.ofAdd (UniformSlowPolynomials.form
            (fun (I : PolynomialLineCoefficients.Grid v s) i=>(I i).val)
            (errorCoefficients θ M (j.val:ℝ)) (fun i=>(x i:ℝ))))*
            (Q (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ)))).val*
            R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ)):=by
      rw [hm]
      exact hQP _
    obtain ⟨u,lo,hi,res,f,hf,hfB,hbox,hside,hbad⟩:=hdisc Z hZ
      (errorCoefficients θ M (j.val:ℝ)) (split_error_bound hM j.val (by omega))
      (b₀.lo j) (b₀.hi j) (by simpa only [neg_mul] using b₀.box j) (b₀.side j)
      (b₀.res j) _ (Int.natAbs_pos.mpr htpos.ne') htK (by rw [hcast]; linarith)
      (b₀.test j) (b₀.lip j) (b₀.bound j)
      (fun x=>b₀.P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ))))
      (fun x=>Q (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ)))) m hfactor η (b₀.bad j)
    refine ⟨u,lo,hi,res,f,hf,hfB,hbox,hside,?_⟩
    convert hbad using 1; dsimp [ε]; ring
  choose u lo hi res f hf hfB hbox hside hbad using hfib
  let e:=Fintype.equivFin (Fin v→Fin R.period)
  obtain ⟨a,b,hb,hab,hmono⟩:=hN (fun j=>e (u j))
  let j₀ : Fin (N+1):=⟨a,Nat.lt_succ_of_le ((Nat.le_add_right _ _).trans hab)⟩
  have hu (j : Fin (H+1)) : u (progressionIndex a b hab j)=u j₀:=e.injective (hmono j)
  have hbN : b≤N:=by nlinarith
  have hsm : Smooth w (b₀.step*(b:ℤ)):=smooth_mul b₀.smooth
    (smooth_of_abs_le (by exact_mod_cast hb.ne') (by simpa using hbN.trans hw))
  let b₁:=b₀.affine a b hb hab hsm
  let P' : (Fin (v+1)→ℝ)→χ.ker:=fun y=>Q
    (Fin.cons ((a:ℝ)+(b:ℝ)*y 0) (fun i=>((u j₀ i).val:ℝ)+(R.period:ℝ)*(Fin.tail y i)))
  have hP' (i) : HasDegree (fun y=>canonicalLog d (P' y) i) D':=by
    simpa only [Fin.cons_zero,Fin.tail_cons] using
      RoughPolynomialDegree.time_affine (spatial_affine (hQd i) (fun i=>((u j₀ i).val:ℝ)) R.period) a b
  refine ⟨{
    start:=b₁.start
    step:=b₁.step
    positive:=b₁.positive
    smooth:=b₁.smooth
    scales:=b₁.scales
    rough:=b₁.rough
    P:=P'
    degree:=hP'
    lo:=fun j=>lo (progressionIndex a b hab j)
    hi:=fun j=>hi (progressionIndex a b hab j)
    res:=fun j=>res (progressionIndex a b hab j)
    test:=fun j=>f (progressionIndex a b hab j)
    side:=fun j=>hside _
    box:=fun j=>hbox _
    lip:=fun j=>hf _
    bound:=fun j=>hfB _
    bad:=?_ }⟩
  intro j
  have heq : b₁.start+b₁.step*(j.val:ℤ)=b₀.start+b₀.step*((progressionIndex a b hab j).val:ℤ):=by
    simp only [b₁,Block.affine,progressionIndex_val,Nat.cast_add,Nat.cast_mul]
    ring
  simpa only [P',Fin.cons_zero,Fin.tail_cons,integerAffine,hu j,Int.cast_add,Int.cast_mul,
    Int.cast_natCast,progressionIndex_val,Nat.cast_add,Nat.cast_mul,heq]
    using hbad (progressionIndex a b hab j)

end RoughSplitBlockReduction

end
end
end

end OAI
