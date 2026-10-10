import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughKernel04
import OAI.Combinatorics.SumProduct.Alignment.RoughRational01
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
namespace RoughBadBlock
open RationalLattice RealPolynomialDegree RoughScales
open FinitePieceAverages RoughSamplingWeights RoughCharacterThinning
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance : TopologicalSpace (G⧸Γ):=mtr.toUniformSpace.toTopologicalSpace

 

structure Block (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ) (w : ℕ) (S Z : ℝ) (H : ℕ) where
  start : ℤ
  step : ℤ
  positive : 0<step
  smooth : Smooth w step
  scales : ∀ z : ℤ,0≤z →z≤H →S≤((start+step*z:ℤ):ℝ) ∧ ((start+step*z:ℤ):ℝ)<2*S
  rough : ∀ z : ℤ,0≤z →z≤H →Rough w (start+step*z)
  P : (Fin (v+1)→ℝ)→G
  degree : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D
  lo : Fin (H+1)→Fin v→ℝ
  hi : Fin (H+1)→Fin v→ℝ
  res : Fin (H+1)→Fin v→ℤ
  test : Fin (H+1)→(G⧸Γ)→ℂ
  side : ∀ j i,c₀*Z≤hi j i-lo j i
  box : ∀ j i,-C₀*Z≤lo j i ∧ hi j i≤C₀*Z
  lip : ∀ j,LipschitzWith B (test j)
  bound : ∀ j y,‖test j y‖≤B
  bad : ∀ j,η≤‖mean (boxIndices (lo j) (hi j) (fun _=>0) 1)
      (fun x=>test j (QuotientGroup.mk (P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ))))))-
    mean (physicalResidueBox (lo j) (hi j) (res j) (start+step*(j.val:ℤ)).natAbs)
      (fun x=>test j (QuotientGroup.mk (P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ))))))‖

namespace Block
variable {c Γ} {v D : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η : ℝ} {w : ℕ} {S Z : ℝ} {N H : ℕ}
variable (b₀ : Block c Γ v D c₀ C₀ B η w S Z N)

 

def affine (a b : ℕ) (hb : 0<b) (hab : a+b*H≤N) (hs : Smooth w (b₀.step*(b:ℤ))) :
    Block c Γ v D c₀ C₀ B η w S Z H where
  start:=b₀.start+b₀.step*(a:ℤ)
  step:=b₀.step*(b:ℤ)
  positive:=mul_pos b₀.positive (by exact_mod_cast hb)
  smooth:=hs
  scales:=by
    intro z hz hzH
    have hza : 0≤(a:ℤ)+(b:ℤ)*z:=by positivity
    have hzb : (a:ℤ)+(b:ℤ)*z≤N:=by
      have hh : (a:ℤ)+(b:ℤ)*(H:ℤ)≤N:=by exact_mod_cast hab
      nlinarith
    have h:=b₀.scales _ hza hzb
    convert h using 1 <;> push_cast <;> ring_nf
  rough:=by
    intro z hz hzH
    have hza : 0≤(a:ℤ)+(b:ℤ)*z:=by positivity
    have hzb : (a:ℤ)+(b:ℤ)*z≤N:=by
      have hh : (a:ℤ)+(b:ℤ)*(H:ℤ)≤N:=by exact_mod_cast hab
      nlinarith
    convert b₀.rough _ hza hzb using 1; ring
  P:=fun y=>b₀.P (Fin.cons ((a:ℝ)+(b:ℝ)*y 0) (Fin.tail y))
  degree:=fun i=>RoughPolynomialDegree.time_affine (b₀.degree i) _ _
  lo:=fun j=>b₀.lo (progressionIndex a b hab j)
  hi:=fun j=>b₀.hi (progressionIndex a b hab j)
  res:=fun j=>b₀.res (progressionIndex a b hab j)
  test:=fun j=>b₀.test (progressionIndex a b hab j)
  side:=fun j=>b₀.side _
  box:=fun j=>b₀.box _
  lip:=fun j=>b₀.lip _
  bound:=fun j=>b₀.bound _
  bad:=by
    intro j
    have he : b₀.start+b₀.step*(a:ℤ)+b₀.step*(b:ℤ)*(j.val:ℤ)=
        b₀.start+b₀.step*((progressionIndex a b hab j).val:ℤ):=by
      simp only [progressionIndex_val,Nat.cast_add,Nat.cast_mul]
      ring
    simpa only [Fin.cons_zero,Fin.tail_cons,he,progressionIndex_val,Nat.cast_add,Nat.cast_mul]
      using b₀.bad (progressionIndex a b hab j)

def restrict (hHN : H≤N) : Block c Γ v D c₀ C₀ B η w S Z H :=
  b₀.affine 0 1 (by norm_num) (by simpa using hHN) (by simpa using b₀.smooth)

end Block

end RoughBadBlock

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughBlockRationalization
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales
open RoughBadBlock RoughRealRationalization RoughRationalBlock
open PolynomialLineCoefficients CorrectedBoxLeibman Filter MeasureTheory AbelianMalcevTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {r : ℕ}
variable (c : RealCoordinates G r) (hsk : SecondKind c) (Γ : Subgroup G)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ):=mtr.toUniformSpace.toTopologicalSpace

include hsk hΓ htop in
 

theorem rationalized_block (v D : ℕ) (c₀ C₀ : ℝ) (B₀ : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB₀ : 0<B₀) (hη : 0<η)
    {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    ∃ s : ℕ,∃ U : Finset (G→*Multiplicative ℝ),∃ A : ℝ,1≤A ∧
      ∀ H : ℕ,2*((v+1)*s+1)≤H →∃ N : ℕ,∀ᶠ n in atTop,
      ∀ _ : Block c Γ v D c₀ C₀ B₀ η (w n) (S n) (Z n) N,
        ∃ b : Block c Γ v D c₀ C₀ B₀ η (w n) (S n) (Z n) H,
        ∃ ξ∈U,ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ, (∀ I,(θ I).natDegree ≤ s) ∧
          (∀ z : ℝ,∀ x : Fin v→ℝ,gridEval (fun I=>(θ I).eval z) x=(ξ (b.P (Fin.cons z x))).toAdd) ∧
          ∃ M : PolynomialLineCoefficients.Grid v s→Polynomial ℚ,Split (w n) H (Z n) A θ 0 1 M := by
  classical
  let : MeasurableSpace (G⧸Γ):=borel (G⧸Γ)
  let : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance:=by
    rw [←htop]
    exact ⟨rfl⟩
  let : BorelSpace (G⧸Γ):=by
    change @BorelSpace (G⧸Γ) mtr.toUniformSpace.toTopologicalSpace inferInstance
    exact ⟨rfl⟩
  let : CompactSpace (G⧸Γ):=metric_compact c Γ hΓ mtr htop
  let : Group.IsNilpotent G:=nilpotent_of_coordinates c
  let : ContinuousConstSMul G (G⧸Γ):=by
    change @ContinuousConstSMul G (G⧸Γ) mtr.toUniformSpace.toTopologicalSpace inferInstance
    rw [htop]
    infer_instance
  obtain ⟨μ,hinv⟩:=SolvableInvariantMeasure.exists_invariant_measure (G:=G) (X:=G⧸Γ)
  let :=hinv
  obtain ⟨s,U,A,hA,hprod⟩:=real_rational_split c hsk Γ hΓ htop (μ:Measure (G⧸Γ))
    v D c₀ C₀ B₀ η hc₀ hC₀ hB₀ hη hw hS hZ
  refine ⟨s,U,A,hA,?_⟩
  intro H hH
  obtain ⟨N,hN⟩:=hprod H hH
  refine ⟨N,?_⟩
  filter_upwards [hN] with n hn
  intro b₀
  let F : Fin (N+1)→C(G⧸Γ,ℂ):=fun j=>⟨b₀.test j,(b₀.lip j).continuous⟩
  have hF (j) : LipschitzWith B₀ (F j) ∧ ‖F j‖≤B₀:=
    ⟨b₀.lip j,(ContinuousMap.norm_le (F j) B₀.coe_nonneg).mpr (b₀.bound j)⟩
  obtain ⟨a,b,hb,hab,hsm,ξ,hξ,hne,hcont,hint,θ,hθ,he,M,hM⟩:=
    hn b₀.start b₀.step b₀.positive b₀.smooth b₀.scales b₀.rough b₀.P b₀.degree
      b₀.lo b₀.hi b₀.res F b₀.side b₀.box hF b₀.bad
  let b' :=b₀.affine a b hb hab hsm
  refine ⟨b',ξ,hξ,hne,hcont,hint,θ,hθ,?_,M,hM⟩
  intro z x
  simpa only [b',Block.affine,Fin.cons_zero,Fin.tail_cons] using he z x

end RoughBlockRationalization

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughPhysicalSelection
open RoughSamplingWeights RegularBoxPartition RegularResiduePieces FinitePieceAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_physical (lo hi : ι→ℝ) (u : ι→ℤ) (K : ℕ) (x : ι→ℤ) :
    x∈physicalResidueBox lo hi u K ↔
      (∀ i,lo i≤(x i:ℝ) ∧ (x i:ℝ)<hi i) ∧ ∀ i,x i≡u i [ZMOD K]:=by
  simp only [physicalResidueBox,Finset.mem_filter,
    mem_boxIndices _ _ _ _ zero_lt_one,zero_add,one_mul]

lemma physical_image (lo hi : ι→ℝ) (a : ι→ℤ) (q : ℕ) (hq : 0<q) :
    physicalResidueBox lo hi a q=(boxIndices lo hi (fun i=>(a i:ℝ)) q).image (integerAffine a q):=by
  rw [rescaled_box lo hi a q hq]
  exact physical_residue_reparametrization lo hi a q hq

lemma physical_mean (lo hi : ι→ℝ) (a : ι→ℤ) (q : ℕ) (hq : 0<q) (f : (ι→ℤ)→ℂ) :
    mean (physicalResidueBox lo hi a q) f=
      mean (boxIndices lo hi (fun i=>(a i:ℝ)) q) (fun x=>f (integerAffine a q x)):=by
  rw [physical_image lo hi a q hq]
  exact mean_image _ _ (affine_injective a q hq) f

omit [Fintype ι] [DecidableEq ι] in
lemma affine_mod (a : ι→ℤ) (q : ℕ) (x : ι→ℤ) : ∀ i,integerAffine a q x i≡a i [ZMOD q]:=by
  intro i
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-x i,by dsimp [integerAffine]; ring⟩

omit [Fintype ι] [DecidableEq ι] in
lemma affine_zero_one (x : ι→ℤ) : integerAffine (fun _=>0) 1 x=x:=by
  ext i
  simp [integerAffine]

 

lemma physical_fiber_image (lo hi : ι→ℝ) (hL : ∀ i,lo i<hi i)
    (M : ℕ) (hM : 0<M) (a : ι→ℤ) (q K : ℕ) (hq : 0<q) [NeZero K]
    (b : ι→Fin M) (u : ι→ZMod K) :
    (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) (b,u)).image
      (integerAffine a q)=
    (physicalResidueBox (fun i=>left (lo i) (hi i) M (b i))
      (fun i=>right (lo i) (hi i) M (b i)) (fun i=>((u i).val:ℤ)) K).filter
      (fun x=>∀ i,x i≡a i [ZMOD q]) := by
  classical
  ext x
  rw [Finset.mem_filter,mem_physical]
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨hy,he⟩:=Finset.mem_filter.mp hy
    obtain ⟨hb,hu⟩:=(label_correct lo hi hL M hM a q K hq y hy b u).mp he
    refine ⟨⟨?_,?_⟩,affine_mod a q y⟩
    · intro i
      simpa only [integerAffine,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hb i
    · intro i
      apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
      simpa only [Int.cast_natCast,ZMod.natCast_zmod_val,integerAffine] using hu i
  · rintro ⟨⟨hb,hu⟩,hxq⟩
    have hx : x∈physicalResidueBox lo hi a q:=by
      rw [mem_physical]
      refine ⟨fun i=>?_,hxq⟩
      have he:=endpoints (lo i) (hi i) (hL i) M hM (b i)
      exact ⟨he.1.trans (hb i).1,(hb i).2.trans_le he.2.2.1⟩
    rw [physical_image lo hi a q hq] at hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨y,Finset.mem_filter.mpr ⟨hy,?_⟩,rfl⟩
    apply (label_correct lo hi hL M hM a q K hq y hy b u).mpr
    constructor
    · intro i
      simpa only [integerAffine,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hb i
    · intro i
      have h:=(ZMod.intCast_eq_intCast_iff _ _ _).mpr (hu i)
      simpa only [integerAffine,Int.cast_natCast,ZMod.natCast_zmod_val] using h

lemma physical_fiber_mean (lo hi : ι→ℝ) (hL : ∀ i,lo i<hi i)
    (M : ℕ) (hM : 0<M) (a : ι→ℤ) (q K : ℕ) (hq : 0<q) [NeZero K]
    (b : ι→Fin M) (u : ι→ZMod K) (f : (ι→ℤ)→ℂ) :
    mean (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) (b,u))
      (fun x=>f (integerAffine a q x))=
    mean ((physicalResidueBox (fun i=>left (lo i) (hi i) M (b i))
      (fun i=>right (lo i) (hi i) M (b i)) (fun i=>((u i).val:ℤ)) K).filter
      (fun x=>∀ i,x i≡a i [ZMOD q])) f := by
  rw [←physical_fiber_image lo hi hL M hM a q K hq b u]
  exact (mean_image _ _ (affine_injective a q hq) f).symm

lemma mean_congr {α : Type*} (S : Finset α) (f g : α→ℂ) (h : ∀ x∈S,f x=g x) :
    mean S f=mean S g:=by
  simp only [mean]
  rw [Finset.sum_congr rfl h]

section Freezing
open RationalLattice MalcevCharacters RoughKernelFactorization UniformSlowPolynomials
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable {X : Type*} [PseudoMetricSpace X] (V : (G⧸Γ) ≃ₜ X)
variable {κ : Type*} [Fintype κ]

include hΓ in
 

theorem physical_frozen_selection (e : κ→ι→ℕ) (A C side B : ℝ)
    (hA : 0≤A) (hC : 0≤C) (hside : 0<side) (hB : 0≤B)
    (L : NNReal) (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ,∃ _ : 0<M,∃ T δ : ℝ,0<T ∧ 0<δ ∧
    ∀ Z : ℝ,0<Z →∀ coeff : κ→ℝ,(∀ k,|coeff k| * Z^(∑i,e k i)≤A) →
    ∀ (lo hi : ι→ℝ) (_ : ∀ i,lo i<hi i),
      (∀ i,-(C*Z)≤lo i ∧ hi i≤C*Z) →(∀ i,side*Z≤hi i-lo i) →
    ∀ (res : ι→ℤ) (t : ℕ),0<t →t.Coprime R.period →1+(t:ℝ)≤δ*Z →
    ∀ F : X→ℂ,LipschitzWith L F →(∀ x,‖F x‖≤B) →∀ tail : (ι→ℤ)→G⧸Γ,
    ∀ η : ℝ,
      η≤‖mean (boxIndices lo hi (fun _=>0) 1)
        (fun x=>F (V ((R.flow c hsk χ Γ (Multiplicative.ofAdd
          (form e coeff (fun i=>(x i:ℝ))))) • tail x)))-
      mean (physicalResidueBox lo hi res t)
        (fun x=>F (V ((R.flow c hsk χ Γ (Multiplicative.ofAdd
          (form e coeff (fun i=>(x i:ℝ))))) • tail x)))‖ →
    ∃ b : ι→Fin M,∃ u : ι→ZMod R.period,
      |form e coeff (fun i=>left (lo i) (hi i) M (b i))|≤T ∧
      η-3*ε≤‖mean (physicalResidueBox
        (fun i=>left (lo i) (hi i) M (b i)) (fun i=>right (lo i) (hi i) M (b i))
        (fun i=>((u i).val:ℤ)) R.period)
        (fun x=>F (V ((R.flow c hsk χ Γ (Multiplicative.ofAdd
          (form e coeff (fun i=>left (lo i) (hi i) M (b i))))) • tail x)))-
      mean ((physicalResidueBox
        (fun i=>left (lo i) (hi i) M (b i)) (fun i=>right (lo i) (hi i) M (b i))
        (fun i=>((u i).val:ℤ)) R.period).filter (fun x=>∀ i,x i≡res i [ZMOD t]))
        (fun x=>F (V ((R.flow c hsk χ Γ (Multiplicative.ofAdd
          (form e coeff (fun i=>left (lo i) (hi i) M (b i))))) • tail x)))‖ := by
  classical
  let : NeZero R.period:=⟨R.period_pos.ne'⟩
  obtain ⟨M,hM,δ,hδ,hselect⟩:=regular_sample_select_frozen c hsk χ Γ R hΓ V e A C side B
    hA hC hside hB L R.period R.period_pos ε hε
  obtain ⟨T,δ₀,hT,hδ₀,hbound⟩:=scaled_uniformity e A C hA hC 1 (by norm_num)
  refine ⟨M,hM,T,δ,hT,hδ,?_⟩
  intro Z hZ coeff hcoeff lo hi hL hbox hside' res t ht htK hsmall F hF hFB tail η hbad
  let f : (ι→ℤ)→ℂ:=fun x=>F (V ((R.flow c hsk χ Γ
    (Multiplicative.ofAdd (form e coeff (fun i=>(x i:ℝ))))) • tail x))
  have hbad' : η≤‖mean (boxIndices lo hi (fun i=>((0:ℤ):ℝ)) 1)
      (sampledTest c hsk χ Γ R V e coeff (fun _=>0) 1 F (fun x=>tail (integerAffine (fun _=>0) 1 x)))-
    mean (boxIndices lo hi (fun i=>(res i:ℝ)) t)
      (sampledTest c hsk χ Γ R V e coeff res t F (fun x=>tail (integerAffine res t x)))‖:=by
    rw [physical_mean lo hi res t ht] at hbad
    unfold sampledTest
    simpa [affine_zero_one,integerAffine] using hbad
  obtain ⟨z,hz,hdisc⟩:=hselect Z hZ coeff coeff hcoeff hcoeff lo hi hL hbox hside'
    (fun _=>0) res 1 t (by norm_num) ht (Nat.coprime_one_left _) htK (by simpa using hsmall)
    F F hF hF hFB (fun x=>tail (integerAffine (fun _=>0) 1 x))
    (fun x=>tail (integerAffine res t x)) η (by simpa only [Nat.cast_one] using hbad')
  let b:=z.1
  let u:=z.2
  let frozen : (ι→ℤ)→ℂ:=fun x=>F (V ((R.flow c hsk χ Γ
    (Multiplicative.ofAdd (form e coeff (fun i=>left (lo i) (hi i) M (b i))))) • tail x))
  have hmean (a : ι→ℤ) (q : ℕ) (hq : 0<q) :
      mean (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q R.period) z)
        (frozenSampledTest c hsk χ Γ R V e coeff lo hi hL M hM a q F
          (fun x=>tail (integerAffine a q x))) =
      mean ((physicalResidueBox (fun i=>left (lo i) (hi i) M (b i))
        (fun i=>right (lo i) (hi i) M (b i)) (fun i=>((u i).val:ℤ)) R.period).filter
        (fun x=>∀ i,x i≡a i [ZMOD q])) frozen := by
    calc
      _=mean (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q R.period) z)
          (fun x=>frozen (integerAffine a q x)):=by
        apply mean_congr
        intro x hx
        have he:=(Finset.mem_filter.mp hx).2
        have hc : cell lo hi hL M hM (fun i=>(a i:ℝ)+q*x i)=b:=congrArg Prod.fst he
        simp only [frozenSampledTest,hc,frozen]
      _=_:=physical_fiber_mean lo hi hL M hM a q R.period hq b u frozen
  rw [hmean (fun _=>0) 1 (by norm_num),hmean res t ht] at hdisc
  refine ⟨b,u,?_,?_⟩
  · have hc (i : ι) : |left (lo i) (hi i) M (b i)|≤C*Z:=by
      have he:=endpoints (lo i) (hi i) (hL i) M hM (b i)
      exact abs_le.mpr ⟨(hbox i).1.trans he.1,he.2.1.le.trans (he.2.2.1.trans (hbox i).2)⟩
    exact (hbound Z hZ coeff hcoeff _ _ hc hc).1
  · simpa only [Nat.cast_one,Int.modEq_one,implies_true,Finset.filter_true,frozen] using hdisc

end Freezing
end RoughPhysicalSelection

end
end
end

end OAI
