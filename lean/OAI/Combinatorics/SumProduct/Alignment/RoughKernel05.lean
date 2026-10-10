import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughPhysical01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughKernelDiscrepancy
open RationalLattice MalcevCharacters RoughKernelFactorization UniformSlowPolynomials
open RoughSamplingWeights RegularBoxPartition RegularResiduePieces FinitePieceAverages
open RoughPhysicalSelection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZint : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)
variable {X : Type*} [PseudoMetricSpace X] (V : (G⧸Γ) ≃ₜ X)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

include hΓ hcont hZint in
 

theorem source_kernel_discrepancy (e : κ→ι→ℕ) (A C side B : ℝ)
    (hA : 0≤A) (hC : 0≤C) (hside : 0<side) (hB : 0≤B)
    (L : NNReal) (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ,0<M ∧ ∃ L' : NNReal,∃ δ : ℝ,0<δ ∧
    ∀ Z : ℝ,(R.period:ℝ)≤Z →∀ coeff : κ→ℝ,(∀ k,|coeff k| * Z^(∑i,e k i)≤A) →
    ∀ (lo hi : ι→ℝ),
      (∀ i,-(C*Z)≤lo i ∧ hi i≤C*Z) →(∀ i,side*Z≤hi i-lo i) →
    ∀ (res : ι→ℤ) (t : ℕ),0<t →t.Coprime R.period →1+(t:ℝ)≤δ*Z →
    ∀ F : X→ℂ,LipschitzWith L F →(∀ x,‖F x‖≤B) →
    ∀ (P : (ι→ℤ)→G) (Q : (ι→ℤ)→χ.ker) (m : MvPolynomial ι ℤ),
      (∀ x,P x=R.flow c hsk χ Γ (Multiplicative.ofAdd (form e coeff (fun i=>(x i:ℝ))))*
        (Q x).val*R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))) →
    ∀ η : ℝ,η≤‖mean (boxIndices lo hi (fun _=>0) 1) (fun x=>F (V (QuotientGroup.mk (P x))))-
      mean (physicalResidueBox lo hi res t) (fun x=>F (V (QuotientGroup.mk (P x))))‖ →
    ∃ u : ι→Fin R.period,∃ j : Fin R.period,
      let σ:=residueSigma c hsk χ Γ R j
      letI :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZint
      ∃ (lo' hi' : ι→ℝ) (res' : ι→ℤ) (g : (χ.ker⧸kernelLattice χ Γ σ)→ℂ),
        LipschitzWith L' g ∧ (∀ y,‖g y‖≤B+ε) ∧
        (∀ i,-(C+1)*(Z/R.period)≤lo' i ∧ hi' i≤(C+1)*(Z/R.period)) ∧
        (∀ i,(side/M)*(Z/R.period)≤hi' i-lo' i) ∧
        η-5*ε≤‖mean (boxIndices lo' hi' (fun _=>0) 1)
          (fun y=>g (QuotientGroup.mk (Q (integerAffine (fun i=>((u i).val:ℤ)) R.period y))))-
        mean (physicalResidueBox lo' hi' res' t)
          (fun y=>g (QuotientGroup.mk (Q (integerAffine (fun i=>((u i).val:ℤ)) R.period y))))‖ := by
  classical
  let : NeZero R.period:=⟨R.period_pos.ne'⟩
  obtain ⟨M,hM,T,δ,hT,hδ,hfreeze⟩:=physical_frozen_selection c hsk χ Γ R hΓ V e A C side B
    hA hC hside hB L ε hε
  obtain ⟨L',hreduce⟩:=finite_residue_kernel_reduction c hsk χ Γ R hΓ hcont hZint V T L B hB ε hε
  refine ⟨M,hM,L',δ,hδ,?_⟩
  intro Z hKZ coeff hcoeff lo hi hbox hside' res t ht htK hsmall F hF hFB P Q m hP η hbad
  have hZ : 0<Z:=lt_of_lt_of_le (by exact_mod_cast R.period_pos) hKZ
  have hL : ∀ i,lo i<hi i:=fun i=>sub_pos.mp (lt_of_lt_of_le (mul_pos hside hZ) (hside' i))
  let tail : (ι→ℤ)→G⧸Γ:=fun x=>QuotientGroup.mk ((Q x).val*
    R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ)))
  have hval (a : ℝ) (x : ι→ℤ) :
      F (V ((R.flow c hsk χ Γ (Multiplicative.ofAdd a)) • tail x))=
      F (V (QuotientGroup.mk (R.flow c hsk χ Γ (Multiplicative.ofAdd a)*(Q x).val*
        R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))))) := by
    congr 2
    change (QuotientGroup.mk (_*(_*_)) : G⧸Γ)=QuotientGroup.mk ((_*_)*_)
    rw [mul_assoc]
  have horig (x : ι→ℤ) : F (V ((R.flow c hsk χ Γ
      (Multiplicative.ofAdd (form e coeff (fun i=>(x i:ℝ))))) • tail x))=
      F (V (QuotientGroup.mk (P x))):=by rw [hval,←hP]
  obtain ⟨b,u,ha,hdisc⟩:=hfreeze Z hZ coeff hcoeff lo hi hL hbox hside' res t ht htK hsmall
    F hF hFB tail η (by simpa only [horig] using hbad)
  let a : Set.Icc (-T) T:=⟨form e coeff (fun i=>left (lo i) (hi i) M (b i)),abs_le.mp ha⟩
  let u' : ι→Fin R.period:=fun i=>⟨(u i).val,ZMod.val_lt (u i)⟩
  let left' : ι→ℝ:=fun i=>left (lo i) (hi i) M (b i)
  let right' : ι→ℝ:=fun i=>right (lo i) (hi i) M (b i)
  let S:=physicalResidueBox left' right' (fun i=>((u i).val:ℤ)) R.period
  let U:=S.filter (fun x=>∀ i,x i≡res i [ZMOD t])
  let frozenP : (ι→ℤ)→G:=fun x=>R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)*(Q x).val*
    R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x m:ℤ):ℝ))
  have hdisc' : η-3*ε≤‖mean S (fun x=>F (V (QuotientGroup.mk (frozenP x))))-
      mean U (fun x=>F (V (QuotientGroup.mk (frozenP x))))‖:=by
    simpa only [hval] using hdisc
  obtain ⟨j,hj⟩:=hreduce ι (ι→ℤ) m (fun i=>((u i).val:ℤ))
  let σ:=residueSigma c hsk χ Γ R j
  let :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZint
  obtain ⟨g,hg,hgB,hgd⟩:=hj a F hF hFB
  have hres : ∀ x∈S∪U,∀ i,x i≡((u i).val:ℤ) [ZMOD R.period]:=by
    intro x hx
    have hxS : x∈S:=by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hx
      · exact (Finset.mem_filter.mp hx).1
    exact (mem_physical left' right' _ _ x).mp hxS |>.2
  have hgd':=hgd S U id frozenP Q hres (by intro x hx; rfl) (η-3*ε) hdisc'
  have hgd'' : η-5*ε≤‖mean S (fun x=>g (QuotientGroup.mk (Q x)))-
      mean U (fun x=>g (QuotientGroup.mk (Q x)))‖:=by linarith
  obtain ⟨res',hrescale⟩:=rescaled_discrepancy (fun i=>((u i).val:ℤ)) res R.period t R.period_pos htK.symm
  have hfinal:= (hrescale left' right' (fun x=>g (QuotientGroup.mk (Q x))) (η-5*ε)).mp hgd''
  refine ⟨u',j,rescaledEndpoint left' (fun i=>((u i).val:ℤ)) R.period,
    rescaledEndpoint right' (fun i=>((u i).val:ℤ)) R.period,res',g,hg,hgB,?_,?_,hfinal⟩
  · have hgeom:=rescaled_geometry left' right' (fun i=>((u i).val:ℤ)) R.period R.period_pos
      Z C (side/M) hKZ hC (fun i=>⟨by positivity,by exact_mod_cast (ZMod.val_lt (u i)).le⟩)
      (fun i=>⟨(hbox i).1.trans (endpoints (lo i) (hi i) (hL i) M hM (b i)).1,
        (endpoints (lo i) (hi i) (hL i) M hM (b i)).2.2.1.trans (hbox i).2⟩) (by
        intro i
        change (side/M)*Z≤right (lo i) (hi i) M (b i)-left (lo i) (hi i) M (b i)
        rw [(endpoints (lo i) (hi i) (hL i) M hM (b i)).2.2.2]
        calc _=(side*Z)/M:=by ring
             _≤_:=div_le_div_of_nonneg_right (hside' i) (by positivity))
    exact fun i=>⟨(hgeom i).1,(hgeom i).2.1⟩
  · intro i
    change (side/M)*(Z/R.period)≤(right' i-(u i).val)/R.period-(left' i-(u i).val)/R.period
    have he:= (endpoints (lo i) (hi i) (hL i) M hM (b i)).2.2.2
    change right' i-left' i=(hi i-lo i)/M at he
    calc
      _=(side*Z/M)/R.period:=by ring
      _≤((hi i-lo i)/M)/R.period:=by gcongr; exact hside' i
      _=(right' i-left' i)/R.period:=by rw [he]
      _=_:=by ring

end RoughKernelDiscrepancy

end
 
end

section
 

 

noncomputable section
namespace RoughKernelCover
open RationalLattice MalcevCharacters RoughKernelFactorization RealPolynomialDegree

section General
variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
variable [IsTopologicalGroup G] [IsTopologicalGroup K] {m n : ℕ}
variable (c : RealCoordinates G m) (d : RealCoordinates K n)
variable (F : K→*G) (Γ : Subgroup G)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

include hΓ in
 

omit [IsTopologicalGroup G] in
theorem integer_second_cover
    (hpoly : ∀ i,RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>c.coord (F (d.coord.symm x)) i)) :
    ∃ Λ : Subgroup K,∃ e : RealCoordinates K n,SecondKind e ∧
      (∀ g : K,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧ Λ≤Γ.comap F ∧
      ∃ E : ℕ,0<E ∧ ∀ v D : ℕ,∀ P : (Fin v→ℝ)→K,
        (∀ i,HasDegree (fun x=>canonicalLog d (P x) i) D) →
        ∀ i,HasDegree (fun x=>canonicalLog e (P x) i) (E*D) := by
  classical
  obtain ⟨A,hA,hgrid⟩:=rationalHom_origin_grid c d F hpoly
  obtain ⟨w,hw,hAw,hcl⟩:=exists_lattice_weights d A hA
  let Λ:=weightedLattice d w hcl
  let d':=scaledCoordinates d w hw
  have hΛ : ∀ g : K,g∈Λ ↔ ∀ i,∃ z : ℤ,d'.coord g i=z:=weightedLattice_iff d w hcl hw
  have hle : Λ≤Γ.comap F:=by
    intro g hg
    apply (hΓ _).mpr
    have hh : ∀ i,∃ z : ℤ,d.coord g i=(A:ℝ)*(z:ℝ):=by
      intro i
      obtain ⟨a,ha⟩:=hg i
      obtain ⟨b,hb⟩:=hAw i
      refine ⟨(b:ℤ)*a,?_⟩
      rw [ha,hb]
      push_cast
      ring
    simpa using hgrid (d.coord g) hh
  let e:=secondCoordinates d'
  have he : ∀ i,RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>e.coord (d.coord.symm x) i):=by
    intro i
    apply polynomial_expCoordinates d'
    intro j
    change RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>d.coord (d.coord.symm x) j/(w j:ℝ))
    simpa only [Homeomorph.apply_symm_apply,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast] using
      RationalPolynomialMap.mul (RationalPolynomialMap.coordinate j) (RationalPolynomialMap.const (w j:ℚ)⁻¹)
  obtain ⟨C,hC,hcoord⟩:=coord_degree_bound d
  obtain ⟨L,hL,hlog⟩:=log_degree_bound e
  obtain ⟨T,hT,htransfer⟩:=rational_map_bound (fun i x=>e.coord (d.coord.symm x) i) he
  refine ⟨Λ,e,secondCoordinates_secondKind d',expCoordinates_lattice d' Λ hΛ,hle,
    L*(T*C),Nat.mul_pos hL (Nat.mul_pos hT hC),?_⟩
  intro v D P hP i
  have hc:=hcoord v D P hP
  have ht : ∀ j,HasDegree (fun x=>e.coord (P x) j) (T*(C*D)):=by
    intro j
    simpa only [Homeomorph.symm_apply_apply] using htransfer v (C*D) (fun j x=>d.coord (P x) j) hc j
  simpa only [Nat.mul_assoc] using hlog v (T*(C*D)) P ht i
end General

section Kernel
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

lemma kernel_embedding_polynomial (σ : G) (hσ : IsRational c σ) :
    ∀ i,RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>
      c.coord (kernelInclusion χ σ ((R.chart c hsk χ Γ).coord.symm x)) i):=by
  have hsub : IsPolynomialMap c (fun x : Fin n→ℝ=>((R.chart c hsk χ Γ).coord.symm x).val):=by
    intro i
    change RationalPolynomialMap.IsPolynomial (fun x : Fin n→ℝ=>c.coord
      (c.coord.symm (IntegerHyperplane.lift R.k R.p x)) i)
    simpa only [Homeomorph.apply_symm_apply] using IntegerHyperplane.lift_polynomial R.k R.p i
  have hσp : IsPolynomialMap c (fun _ : Fin n→ℝ=>σ):=polynomialMap_const c hσ
  simpa only [kernelInclusion_apply,IsPolynomialMap] using polynomialMap_mul c (polynomialMap_mul c (polynomialMap_inv c hσp) hsub) hσp

include hΓ in
 

theorem kernel_integer_cover (j : Fin R.period) :
    ∃ Λ : Subgroup χ.ker,∃ e : RealCoordinates χ.ker n,SecondKind e ∧
      (∀ g : χ.ker,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Λ≤kernelLattice χ Γ (residueSigma c hsk χ Γ R j) ∧
      ∃ E : ℕ,0<E ∧ ∀ v D : ℕ,∀ P : (Fin v→ℝ)→χ.ker,
        (∀ i,HasDegree (fun x=>canonicalLog (R.chart c hsk χ Γ) (P x) i) D) →
        ∀ i,HasDegree (fun x=>canonicalLog e (P x) i) (E*D) := by
  apply integer_second_cover c (R.chart c hsk χ Γ)
    (kernelInclusion χ (residueSigma c hsk χ Γ R j)) Γ hΓ
  apply kernel_embedding_polynomial c hsk χ Γ R
  simpa only [residueSigma,Rat.cast_natCast] using R.flow_rational c hsk χ Γ (j.val:ℚ)
end Kernel

end RoughKernelCover

end
 
end

section
 

 

noncomputable section
namespace RoughCoverTests
open RationalLattice FinitePieceAverages
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Λ Γ : Subgroup G)
variable (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z) (hle : Λ≤Γ)
variable {X : Type*} [PseudoMetricSpace X] (V : (G⧸Γ) ≃ₜ X)
include hle in
 

theorem uniform_cover_tests (L : NNReal) (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    letI :=coordinateQuotientMetric c Λ hΛ
    ∃ L' : NNReal,∀ F : X→ℂ,LipschitzWith L F →(∀ x,‖F x‖≤B) →
      ∃ g : (G⧸Λ)→ℂ,LipschitzWith L' g ∧ (∀ y,‖g y‖≤B+ε) ∧
      ∀ (α : Type*) (S T : Finset α) (P : α→G) (η : ℝ),
        η≤‖mean S (fun x=>F (V (QuotientGroup.mk (P x))))-
          mean T (fun x=>F (V (QuotientGroup.mk (P x))))‖ →
        η-2*ε≤‖mean S (fun x=>g (QuotientGroup.mk (P x)))-
          mean T (fun x=>g (QuotientGroup.mk (P x)))‖ := by
  let :=coordinateQuotientMetric c Λ hΛ
  let : CompactSpace (G⧸Λ):=AbelianMalcevTorus.quotient_compact c Λ hΛ
  let p : C(G⧸Λ,X):=(⟨V,V.continuous⟩ : C(G⧸Γ,X)).comp
    (NonnormalCoset.map Λ Γ (MonoidHom.id G) continuous_id hle)
  let H : C(PUnit.{1}×(G⧸Λ),X):=p.comp ContinuousMap.snd
  obtain ⟨L',hL'⟩:=UniformLipschitzApproximation.compact_pullback_complex H L B hB ε hε
  refine ⟨L',?_⟩
  intro F hF hFB
  obtain ⟨g,hg,herr,hgB⟩:=hL' PUnit.unit F hF hFB
  refine ⟨g,hg,hgB,?_⟩
  intro α S T P η hbad
  let f : α→ℂ:=fun x=>F (V (QuotientGroup.mk (P x)))
  let f' : α→ℂ:=fun x=>g (QuotientGroup.mk (P x))
  have hp (x : α) : ‖f x-f' x‖≤ε:=by
    rw [norm_sub_rev]
    simpa only [f,f',H,p,ContinuousMap.comp_apply,ContinuousMap.coe_mk,ContinuousMap.snd_apply,NonnormalCoset.map_mk,MonoidHom.id_apply] using (herr (QuotientGroup.mk (P x))).le
  have hs:=mean_error S f f' ε hε.le (fun x _=>hp x)
  have ht:=mean_error T f f' ε hε.le (fun x _=>hp x)
  have h₁:=norm_sub_le (mean S f-mean S f') (mean T f-mean S f')
  have h₂:=norm_sub_le (mean T f-mean T f') (mean S f'-mean T f')
  have he₁ : (mean S f-mean S f')-(mean T f-mean S f')=mean S f-mean T f:=by ring
  have he₂ : (mean T f-mean T f')-(mean S f'-mean T f')=mean T f-mean S f':=by ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  change η≤‖mean S f-mean T f‖ at hbad
  change η-2*ε≤‖mean S f'-mean T f'‖
  linarith

end RoughCoverTests

end
end
end

end OAI
