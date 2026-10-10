import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughDyadic01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators commutatorElement
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughPolynomialDegree
open RealPolynomialDegree PolynomialLineCoefficients CorrectedBoxLeibman
variable {σ ι : Type*}

lemma coordinate (i : σ) : HasDegree (fun x : σ→ℝ=>x i) 1:=
  ⟨MvPolynomial.X i,by simp,by simp⟩

lemma power {f : (σ→ℝ)→ℝ} {d : ℕ} (hf : HasDegree f d) (k : ℕ) :
    HasDegree (fun x=>f x^k) (d*k):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ⟨p^k,(MvPolynomial.totalDegree_pow p k).trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left k hp),by simp [he]⟩

lemma finite_sum (S : Finset ι) (f : ι→(σ→ℝ)→ℝ) (d : ℕ)
    (hf : ∀ i∈S,HasDegree (f i) d) : HasDegree (fun x=>∑i∈S,f i x) d:=by
  classical
  induction S using Finset.induction_on with
  | empty=>simpa using RealPolynomialDegree.const (σ:=σ) 0 d
  | @insert i S hi ih=>
    simp only [Finset.sum_insert hi]
    simpa only [max_self] using RealPolynomialDegree.add
      (hf i (by simp)) (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

lemma finite_prod (S : Finset ι) (f : ι→(σ→ℝ)→ℝ) (d : ι→ℕ)
    (hf : ∀ i∈S,HasDegree (f i) (d i)) :
    HasDegree (fun x=>∏i∈S,f i x) (∑i∈S,d i):=by
  classical
  induction S using Finset.induction_on with
  | empty=>simpa using RealPolynomialDegree.const (σ:=σ) 1 0
  | @insert i S hi ih=>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    exact RealPolynomialDegree.mul (hf i (by simp))
      (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

lemma polynomial_eval {f : (σ→ℝ)→ℝ} {d q : ℕ} (hf : HasDegree f d)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ q) :
    HasDegree (fun x=>p.eval (f x)) (d*q):=by
  have he (x) : p.eval (f x)=∑j∈Finset.range (q+1),p.coeff j*(f x)^j:=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) _
  simp_rw [he]
  apply finite_sum
  intro j hj
  exact RealPolynomialDegree.mono (RealPolynomialDegree.scale (power hf j) (p.coeff j))
    (Nat.mul_le_mul_left d (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

 

lemma mv_eval {τ : Type*} (p : MvPolynomial τ ℝ) (d : ℕ)
    (g : τ→(σ→ℝ)→ℝ) (hg : ∀ i,HasDegree (g i) d) :
    HasDegree (fun x=>MvPolynomial.eval (fun i=>g i x) p) (d*p.totalDegree):=by
  classical
  have he (x) : MvPolynomial.eval (fun i=>g i x) p=
      ∑m∈p.support,p.coeff m*∏i∈m.support,g i x^m i:=by
    conv_lhs=>rw [p.as_sum]
    simp only [map_sum,MvPolynomial.eval_monomial,Finsupp.prod]
  simp_rw [he]
  apply finite_sum
  intro m hm
  have hprod:=finite_prod m.support (fun i x=>g i x^m i) (fun i=>d*m i)
    (fun i _=>power (hg i) (m i))
  have hsum : (∑i∈m.support,d*m i)=d*m.sum (fun _ k=>k):=by
    simp only [Finsupp.sum,Finset.mul_sum]
  rw [hsum] at hprod
  exact RealPolynomialDegree.mono (RealPolynomialDegree.scale hprod _)
    (Nat.mul_le_mul_left d (MvPolynomial.le_totalDegree hm))

lemma compose {τ : Type*} {f : (τ→ℝ)→ℝ} {d e : ℕ}
    (hf : HasDegree f d) (g : τ→(σ→ℝ)→ℝ) (hg : ∀ i,HasDegree (g i) e) :
    HasDegree (fun x=>f (fun i=>g i x)) (e*d):=by
  obtain ⟨p,hp,he⟩:=hf
  simp_rw [he]
  exact RealPolynomialDegree.mono (mv_eval p e g hg) (Nat.mul_le_mul_left e hp)

lemma time_affine {v d : ℕ} {f : (Fin (v+1)→ℝ)→ℝ} (hf : HasDegree f d) (a b : ℝ) :
    HasDegree (fun y : Fin (v+1)→ℝ=>f (Fin.cons (a+b*y 0) (Fin.tail y))) d:=by
  have h:=compose hf (fun i y=>(Fin.cons (a+b*y 0) (Fin.tail y)) i) (e:=1) (by
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · simpa only [Fin.cons_zero,max_self] using RealPolynomialDegree.add
        (RealPolynomialDegree.const (σ:=Fin (v+1)) a 1)
        (RealPolynomialDegree.scale (coordinate (0:Fin (v+1))) b)
    · exact coordinate j.succ)
  simpa only [one_mul] using h

 

lemma joint_grid {v s q : ℕ} (θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ)
    (hθ : ∀ I,(θ I).natDegree ≤ q) :
    HasDegree (fun y : Fin (v+1)→ℝ=>gridEval (fun I=>(θ I).eval (y 0)) (Fin.tail y)) (q+v*s):=by
  classical
  apply finite_sum
  intro I _
  have htime : HasDegree (fun y : Fin (v+1)→ℝ=>(θ I).eval (y 0)) q:=by
    simpa only [one_mul] using polynomial_eval (coordinate (0:Fin (v+1))) (θ I) (hθ I)
  have hspace : HasDegree (fun y : Fin (v+1)→ℝ=>∏i,(Fin.tail y i)^(I i).val) (totalDegree I):=by
    simpa only [one_mul,totalDegree] using finite_prod Finset.univ
      (fun i (y : Fin (v+1)→ℝ)=>(Fin.tail y i)^(I i).val) (fun i=>1*(I i).val)
      (fun i _=>power (coordinate i.succ) (I i).val)
  exact RealPolynomialDegree.mono (RealPolynomialDegree.mul htime hspace)
    (Nat.add_le_add_left (PolynomialLineCoefficients.totalDegree_le I) q)

end RoughPolynomialDegree

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughRealRationalization
open _root_.Polynomial _root_.OAI.Polynomial Filter Finset RoughScales RealPolynomialDegree
open RoughRationalBlock RoughAnalyticRationalization RoughDyadicFiltration
open FinitePieceAverages RoughSamplingWeights ComparableBoxLeibman
open CorrectedBoxLeibman PolynomialLineCoefficients TriangularLatticeRecovery
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r : ℕ} (c : RealCoordinates G r) (hsk : SecondKind c)
variable (Γ : Subgroup G) (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)]
variable [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ):=mtr.toUniformSpace.toTopologicalSpace

include hsk hΓ htop in
 

theorem real_rational_split
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v d : ℕ) (c₀ C₀ : ℝ) (B₀ : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB₀ : 0<B₀) (hη : 0<η)
    {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    letI : CompactSpace (G⧸Γ):=metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ):=metric_borelSpace Γ mtr htop
    ∃ s : ℕ,∃ U : Finset (G→*Multiplicative ℝ),∃ B : ℝ,1 ≤ B ∧
      ∀ h : ℕ,2*((v+1)*s+1)≤h →∃ N : ℕ,∀ᶠ n in atTop,
      ∀ (a₀ m : ℤ),0 < m →Smooth (w n) m →
      (∀ z : ℤ,0≤z →z≤N →S n≤((a₀+m*z:ℤ):ℝ) ∧ ((a₀+m*z:ℤ):ℝ)<2*S n)→
      (∀ z : ℤ,0≤z →z≤N →Rough (w n) (a₀+m*z))→
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) d)→
      ∀ (lo hi : Fin (N+1)→Fin v→ℝ) (res : Fin (N+1)→Fin v→ℤ)
        (F : Fin (N+1)→C(G⧸Γ,ℂ)),
      (∀ j i,c₀*Z n≤hi j i-lo j i)→
      (∀ j i,-C₀*Z n≤lo j i ∧ hi j i≤C₀*Z n)→
      (∀ j,LipschitzWith B₀ (F j) ∧ ‖F j‖≤B₀)→
      (∀ j,η≤‖mean (boxIndices (lo j) (hi j) (fun _=>0) 1)
          (fun x=>F j (QuotientGroup.mk (P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ)))))) -
        mean (physicalResidueBox (lo j) (hi j) (res j) (a₀+m*(j.val:ℤ)).natAbs)
          (fun x=>F j (QuotientGroup.mk (P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ))))))‖) →
      ∃ a b : ℕ,0 < b ∧ a+b*h≤N ∧ Smooth (w n) (m*(b:ℤ)) ∧
        ∃ ξ∈U,ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ θ : PolynomialLineCoefficients.Grid v s→ℝ[X],
          (∀ I,(θ I).natDegree ≤ s) ∧
          (∀ z : ℝ,∀ x : Fin v→ℝ,
            gridEval (fun I=>(θ I).eval z) x =
              (ξ (P (Fin.cons ((a:ℝ)+(b:ℝ)*z) x))).toAdd) ∧
          ∃ M : PolynomialLineCoefficients.Grid v s→ℚ[X],Split (w n) h (Z n) B θ 0 1 M := by
  classical
  let : CompactSpace (G⧸Γ):=metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ):=metric_borelSpace Γ mtr htop
  obtain ⟨C,hC,hA⟩:=RoughDyadicFiltration.logarithmic_adapted c hsk
  let D:=max 1 (C*d)
  let s:=D*2^r
  obtain ⟨h0,h1,hs,hqb,hq,hpoly⟩:=hA (v+1) d
  obtain ⟨U,B,hB,hout⟩:=rational_split_from_discrepancies (t:=r) (d:=0)
    c hsk (filtration c D) h0 h1 s hs (cutoff r D) hqb hq Γ hΓ htop
    μ v c₀ C₀ B₀ η hc₀ hC₀ hB₀ hη hw hS hZ
  refine ⟨s,U,B,hB,?_⟩
  intro h hh
  obtain ⟨N,hN⟩:=hout h hh
  refine ⟨N,?_⟩
  filter_upwards [hN] with n hn
  intro a₀ m hm hms hscale hrough P hP lo hi res F hside hbox hF hbad
  let f : (Fin (v+1)→ℤ)→G:=fun y=>P (fun i=>(y i:ℝ))
  have hf : LeibmanSquare.Polynomial (filtration c D) 0 f:=(hpoly P hP).2
  have hfcons (z : ℤ) (x : Fin v→ℤ) : f (Fin.cons z x)=P (Fin.cons (z:ℝ) (fun i=>(x i:ℝ))):=by
    dsimp only [f]
    congr 1
    ext i
    exact Fin.cases rfl (fun _=>rfl) i
  obtain ⟨a,b,hb,hab,hmb,ξ,hξ,hξn,hξc,hξZ,θ,hθ,he,M,hM⟩:=hn a₀ m hm hms hscale hrough
    f hf lo hi res F hside hbox hF (by simpa only [hfcons,Int.cast_natCast] using hbad)
  refine ⟨a,b,hb,hab,hmb,ξ,hξ,hξn,hξc,hξZ,θ,hθ,?_,M,hM⟩
  let P' : (Fin (v+1)→ℝ)→G:=fun y=>P (Fin.cons ((a:ℝ)+(b:ℝ)*y 0) (Fin.tail y))
  have hP' : ∀ i,HasDegree (fun y=>canonicalLog c (P' y) i) d:=
    fun i=>RoughPolynomialDegree.time_affine (hP i) _ _
  have hreal:=RoughRealCharacterIdentity.character_identity_real c hsk ξ hξc P' hP' θ hθ (by
    intro z x
    simpa only [P',Fin.cons_zero,Fin.tail_cons,hfcons,Int.cast_add,Int.cast_mul,Int.cast_natCast]
      using he z x)
  intro z x
  exact hreal z x

end RoughRealRationalization

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughRationalKernel
open _root_.Polynomial _root_.OAI.Polynomial RealPolynomialDegree RoughPolynomialDegree
open CorrectedBoxLeibman PolynomialLineCoefficients RoughRationalBlock
open RoughRealCharacterIdentity RoughCoefficientDescentBridge

variable {v s : ℕ}
def rationalValue (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) (y : Fin (v+1)→ℝ) : ℝ:=
  gridEval (fun I=>((M I).map (algebraMap ℚ ℝ)).eval (y 0)) (Fin.tail y)
def errorCoefficients (θ : PolynomialLineCoefficients.Grid v s→ℝ[X])
    (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) (z : ℝ) : PolynomialLineCoefficients.Grid v s→ℝ:=
  fun I=>(θ I).eval z-((M I).map (algebraMap ℚ ℝ)).eval z
def errorValue (θ : PolynomialLineCoefficients.Grid v s→ℝ[X])
    (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) (y : Fin (v+1)→ℝ) : ℝ:=
  gridEval (errorCoefficients θ M (y 0)) (Fin.tail y)

lemma error_eq (θ : PolynomialLineCoefficients.Grid v s→ℝ[X])
    (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) (y : Fin (v+1)→ℝ) :
    errorValue θ M y=gridEval (fun I=>(θ I).eval (y 0)) (Fin.tail y)-rationalValue M y:=by
  simp only [errorValue,errorCoefficients,rationalValue,gridEval,sub_mul,Finset.sum_sub_distrib]

lemma rational_degree (M : PolynomialLineCoefficients.Grid v s→ℚ[X])
    (hM : ∀ I,(M I).natDegree ≤ (v+1)*s) :
    HasDegree (rationalValue M) ((v+1)*s+v*s):=
  joint_grid _ (fun I=>Polynomial.natDegree_map_le.trans (hM I))

lemma error_degree (θ : PolynomialLineCoefficients.Grid v s→ℝ[X])
    (M : PolynomialLineCoefficients.Grid v s→ℚ[X])
    (hθ : ∀ I,(θ I).natDegree ≤ s) (hM : ∀ I,(M I).natDegree ≤ (v+1)*s) :
    HasDegree (errorValue θ M) ((v+1)*s+v*s):=by
  have hθ' : ∀ I,(θ I).natDegree ≤ (v+1)*s:=fun I=>(hθ I).trans (by nlinarith)
  have h:=RealPolynomialDegree.add (joint_grid θ hθ') (RealPolynomialDegree.neg (rational_degree M hM))
  simpa only [max_self,← sub_eq_add_neg,← error_eq] using h

lemma split_error_bound {w H : ℕ} {Z B : ℝ}
    {θ : PolynomialLineCoefficients.Grid v s→ℝ[X]} {M : PolynomialLineCoefficients.Grid v s→ℚ[X]}
    (h : Split w H Z B θ 0 1 M) (z : ℕ) (hz : z≤H) :
    ∀ I,|errorCoefficients θ M (z:ℝ) I| *Z^∑i,(I i).val≤B:=by
  intro I
  simpa only [errorCoefficients,zero_add,one_mul,totalDegree] using h.2.2.2.1 I z hz

 

lemma integer_spatial (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) (z : ℕ)
    (hM : ∀ I,RoughInterpolation.Integral ((M I).eval (z:ℚ))) :
    ∃ m : MvPolynomial (Fin v) ℤ,∀ x : Fin v→ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x m = rationalValue M (Fin.cons (z:ℝ) x) := by
  classical
  choose b hb using hM
  let m : MvPolynomial (Fin v) ℤ:=∑I,MvPolynomial.monomial (gridExponent I) (b I)
  refine ⟨m,?_⟩
  intro x
  simp only [m,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial,rationalValue,Fin.cons_zero,Fin.tail_cons,gridEval]
  apply Finset.sum_congr rfl
  intro I _
  have he : ((M I).map (algebraMap ℚ ℝ)).eval (z:ℝ)=(b I:ℝ):=by
    rw [Polynomial.eval_map]
    calc
      _ = (((M I).eval (z:ℚ):ℚ):ℝ):=by
        simp
      _ = (b I:ℝ):=by exact_mod_cast (hb I).symm
  rw [he]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  rfl

lemma integer_spatial_on_lattice (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) (z : ℕ)
    (hM : ∀ I,RoughInterpolation.Integral ((M I).eval (z:ℚ))) :
    ∃ m : MvPolynomial (Fin v) ℤ,∀ x : Fin v→ℤ,
      ((MvPolynomial.eval x m:ℤ):ℝ)=rationalValue M (Fin.cons (z:ℝ) (fun i=>(x i:ℝ))) := by
  obtain ⟨m,hm⟩:=integer_spatial M z hM
  refine ⟨m,fun x=>?_⟩
  rw [←hm]
  exact MvPolynomial.eval₂_comp (Int.castRingHom ℝ) x m

section Kernel
open RationalLattice MalcevCharacters RoughKernelFactorization
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G→*Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)

 

theorem kernel_polynomial : ∃ E : ℕ,0<E ∧ ∀ v d s : ℕ,
    ∀ (P : (Fin (v+1)→ℝ)→G) (θ : PolynomialLineCoefficients.Grid v s→ℝ[X])
      (M : PolynomialLineCoefficients.Grid v s→ℚ[X]),
    (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) d) →
    (∀ I,(θ I).natDegree ≤ s) → (∀ I,(M I).natDegree ≤ (v+1)*s) →
    (∀ z : ℝ,∀ x : Fin v→ℝ,gridEval (fun I=>(θ I).eval z) x=(χ (P (Fin.cons z x))).toAdd) →
    ∃ Q : (Fin (v+1)→ℝ)→χ.ker,
      (∀ y,P y=R.flow c hsk χ Γ (Multiplicative.ofAdd (errorValue θ M y))*
        (Q y).val*R.flow c hsk χ Γ (Multiplicative.ofAdd (rationalValue M y))) ∧
      ∀ i,HasDegree (fun y=>canonicalLog (R.chart c hsk χ Γ) (Q y) i)
        (E*max d ((v+1)*s+v*s)) := by
  obtain ⟨E,hE,hfactor⟩:=R.logarithmic_factorization c hsk χ Γ
  refine ⟨E,hE,?_⟩
  intro v d s P θ M hP hθ hM he
  apply hfactor (v+1) (max d ((v+1)*s+v*s)) P (errorValue θ M) (rationalValue M)
  · intro y
    rw [error_eq,sub_add_cancel]
    simpa only [Fin.cons_self_tail] using (he (y 0) (Fin.tail y)).symm
  · exact fun i=>RealPolynomialDegree.mono (hP i) (le_max_left _ _)
  · exact RealPolynomialDegree.mono (error_degree θ M hθ hM) (le_max_right _ _)
  · exact RealPolynomialDegree.mono (rational_degree M hM) (le_max_right _ _)

end Kernel
end RoughRationalKernel

end
end
end

end OAI
