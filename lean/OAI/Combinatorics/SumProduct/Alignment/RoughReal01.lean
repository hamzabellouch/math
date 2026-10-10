import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughLog01
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
namespace RoughRealCharacterIdentity
open PolynomialLineCoefficients CorrectedBoxLeibman
open RoughJointCoefficients RoughCoefficientDescentBridge RealPolynomialDegree

lemma sum_degree {v : ℕ} {ι : Type*} (S : Finset ι) (f : ι→(Fin v→ℝ)→ℝ)
    (d : ℕ) (hf : ∀ i∈S,HasDegree (f i) d) :
    HasDegree (fun x=>∑ i∈S,f i x) d := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RealPolynomialDegree.const (σ:=Fin v) 0 d
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    simpa only [max_self] using RealPolynomialDegree.add
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

 
lemma eq_of_integer_agree {v d e : ℕ} {f g : (Fin v→ℝ)→ℝ}
    (hf : HasDegree f d) (hg : HasDegree g e)
    (h : ∀ x : Fin v→ℤ,f (fun i=>(x i:ℝ))=g (fun i=>(x i:ℝ))) : f=g := by
  classical
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,hqv⟩:=hg
  have hpq : p=q := by
    apply MvPolynomial.funext_set (fun _=>Set.range (Int.cast : ℤ→ℝ))
      (fun _=>Set.infinite_range_of_injective (Int.cast_injective))
    intro x hx
    have hx' (i : Fin v) : ∃ z : ℤ,(z:ℝ)=x i := hx i (Set.mem_univ i)
    choose z hz using hx'
    have hzv : (fun i=>(z i:ℝ))=x := funext hz
    rw [← he x,← hqv x,← hzv]
    exact h z
  funext x
  rw [he,hqv,hpq]

 
def gridMv {v s : ℕ} (a : PolynomialLineCoefficients.Grid v s→ℝ) : MvPolynomial (Fin v) ℝ :=
  ∑ I,MvPolynomial.monomial (gridExponent I) (a I)

lemma eval_gridMv {v s : ℕ} (a : PolynomialLineCoefficients.Grid v s→ℝ) (x : Fin v→ℝ) :
    MvPolynomial.eval x (gridMv a)=gridEval a x := by
  classical
  simp only [gridMv,map_sum,MvPolynomial.eval_monomial,gridEval]
  apply Finset.sum_congr rfl
  intro I hI
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  rfl

lemma gridMv_degree {v s : ℕ} (a : PolynomialLineCoefficients.Grid v s→ℝ) :
    (gridMv a).totalDegree≤v*s := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro I _
  exact (MvPolynomial.totalDegree_monomial_le (gridExponent I) (a I)).trans
    (by
      change (gridExponent I).sum (fun _ k=>k) ≤ v*s
      rw [gridExponent_degree]
      exact PolynomialLineCoefficients.totalDegree_le I)

 

def jointArray {v s : ℕ} (θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ) :
    PolynomialLineCoefficients.Grid (v+1) s→ℝ :=
  fun K=>(θ (Fin.tail K)).coeff (K 0).val

lemma timeCoefficient_jointArray {v s : ℕ}
    (θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ)
    (hθ : ∀ I,(θ I).natDegree ≤ s) (I : PolynomialLineCoefficients.Grid v s) (z : ℝ) :
    (timeCoefficient (jointArray θ) I).eval z=(θ I).eval z := by
  classical
  simp only [timeCoefficient,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,jointArray,Fin.tail_cons,Fin.cons_zero]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hθ I))]
  exact Fin.sum_univ_eq_sum_range (fun j=>(θ I).coeff j*z^j) (s+1)

lemma joint_grid_degree {v s : ℕ}
    (θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ)
    (hθ : ∀ I,(θ I).natDegree ≤ s) :
    HasDegree (fun y : Fin (v+1)→ℝ=>gridEval (fun I=>(θ I).eval (y 0)) (Fin.tail y)) ((v+1)*s) := by
  refine ⟨gridMv (jointArray θ),gridMv_degree _,?_⟩
  intro y
  rw [eval_gridMv]
  have h:=gridEval_timeCoefficient (jointArray θ) (y 0) (Fin.tail y)
  simpa only [timeCoefficient_jointArray θ hθ,Fin.cons_self_tail] using h

section Character
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)

include hsk in
omit [IsTopologicalGroup G] in
lemma character_degree {v d : ℕ} (χ : G→*Multiplicative ℝ) (hχ : Continuous χ)
    (P : (Fin v→ℝ)→G) (hP : ∀ i,HasDegree (fun x=>c.coord (P x) i) d) :
    HasDegree (fun x=>(χ (P x)).toAdd) d := by
  have h:=sum_degree Finset.univ
    (fun i x=>(χ (axis c i 1)).toAdd*c.coord (P x) i) d
    (fun i _=>RealPolynomialDegree.scale (hP i) _)
  convert h using 1
  funext x
  simpa only [mul_comm] using character_coordinates c hsk χ hχ (P x)

include hsk in
 

omit [IsTopologicalGroup G] in
theorem character_identity_real {v d s : ℕ} (χ : G→*Multiplicative ℝ) (hχ : Continuous χ)
    (P : (Fin (v+1)→ℝ)→G)
    (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) d)
    (θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ)
    (hθ : ∀ I,(θ I).natDegree ≤ s)
    (he : ∀ z : ℤ,∀ x : Fin v→ℤ,
      gridEval (fun I=>(θ I).eval (z:ℝ)) (fun i=>(x i:ℝ)) =
        (χ (P (Fin.cons (z:ℝ) (fun i=>(x i:ℝ))))).toAdd) :
    ∀ z : ℝ,∀ x : Fin v→ℝ,
      gridEval (fun I=>(θ I).eval z) x=(χ (P (Fin.cons z x))).toAdd := by
  obtain ⟨C,hC,hcoord⟩:=coord_degree_bound c
  have hchar:=character_degree c hsk χ hχ P (hcoord (v+1) d P hP)
  have heq:=eq_of_integer_agree (joint_grid_degree θ hθ) hchar (by
    intro y
    have hcons : Fin.cons (y 0:ℝ) (fun i=>(Fin.tail y i:ℝ))=(fun i=>(y i:ℝ)) := by
      ext i
      exact Fin.cases rfl (fun _=>rfl) i
    change gridEval (fun I=>(θ I).eval (y 0:ℝ)) (fun i=>(Fin.tail y i:ℝ)) = _
    simpa only [hcons] using he (y 0) (Fin.tail y))
  intro z x
  have h:=congrFun heq (Fin.cons z x)
  simpa only [Fin.cons_zero,Fin.tail_cons] using h

end Character
end RoughRealCharacterIdentity

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughRationalBlock
open _root_.Polynomial _root_.OAI.Polynomial Filter Finset
open RoughScales RoughInterpolation PositiveCoefficientDescent
open RoughCoefficientDescentBridge CorrectedBoxLeibman PolynomialLineCoefficients TriangularLatticeRecovery

lemma smooth_mul {w : ℕ} {a b : ℤ} (ha : Smooth w a) (hb : Smooth w b) :
    Smooth w (a*b) := by
  intro p hp hd
  have hp' : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  rcases hp'.dvd_mul.mp hd with h | h
  · exact ha p hp h
  · exact hb p hp h

lemma affine_degree {p : ℝ[X]} {s : ℕ} (hp : p.natDegree ≤ s) (a b : ℝ) :
    (p.comp (C a+C b*X)).natDegree ≤ s := by
  have hlin : (C a+C b*X).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (by simpa using hp))

lemma int_interval_card (N : ℕ) : (Finset.Icc (0:ℤ) (N:ℤ)).card=N+1 := by
  rw [Int.card_Icc]
  omega

 

def Split {v s : ℕ} (w H : ℕ) (Z B : ℝ)
    (θ : PolynomialLineCoefficients.Grid v s→ℝ[X]) (a b : ℕ)
    (M : PolynomialLineCoefficients.Grid v s→ℚ[X]) : Prop :=
  (∀ I,(M I).natDegree ≤ (v+1)*s) ∧
  (∀ I j p,p.Prime→p∣((M I).coeff j).den → p≤w) ∧
  (∀ I,∀ z : ℕ,z≤H→Integral ((M I).eval (z:ℚ))) ∧
  (∀ I,∀ z : ℕ,z≤H→
    |(θ I).eval ((a+b*z:ℕ):ℝ)-((M I).map (algebraMap ℚ ℝ)).eval (z:ℝ)| *
      Z^totalDegree I ≤ B) ∧
  ∀ z : ℕ,z≤H→
    0≤(θ 0).eval ((a+b*z:ℕ):ℝ)-((M 0).map (algebraMap ℚ ℝ)).eval (z:ℝ) ∧
    (θ 0).eval ((a+b*z:ℕ):ℝ)-((M 0).map (algebraMap ℚ ℝ)).eval (z:ℝ)<1

 

theorem eventual_split (v s : ℕ) {A : ℝ} (hA : 0<A)
    {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    ∃ B : ℝ,1≤B ∧ ∀ H : ℕ,2*((v+1)*s+1)≤H→
      ∃ N : ℕ,0<N ∧ ∀ᶠ n in atTop,
      ∀ (a b : ℤ),0<b→Smooth (w n) b→
      (∀ z : ℤ,0≤z→z≤N→S n≤((a+b*z:ℤ):ℝ) ∧ ((a+b*z:ℤ):ℝ)<2*S n)→
      (∀ z : ℤ,0≤z→z≤N→Rough (w n) (a+b*z))→
      ∀ θ : PolynomialLineCoefficients.Grid v s→ℝ[X],(∀ I,(θ I).natDegree ≤ s)→
      ∀ (p : ℤ→ℕ) (u : ℤ→Fin v→ℤ),
      (∀ z : ℤ,0≤z→z≤N→0<p z)→
      (∀ z : ℤ,0≤z→z≤N→p z=1 ∨ p z=(a+b*z).natAbs)→
      (∀ z : ℤ,0≤z→z≤N→∀ i,0≤u z i ∧ u z i<p z)→
      (∀ z : ℤ,0≤z→z≤N→∀ I,0<totalDegree I→
        circleNorm (gridDilate (p z) (gridTranslate (fun I=>(θ I).eval (z:ℝ)) (u z)) I)
          ≤ A*((p z:ℝ)/Z n)^totalDegree I)→
      ∃ c d : ℕ,0<d ∧ d≤N ∧ c+d*H≤N ∧
        Smooth (w n) (b*(d:ℤ)) ∧
        ∃ M : PolynomialLineCoefficients.Grid v s→ℚ[X],Split (w n) H (Z n) B θ c d M := by
  classical
  obtain ⟨B,hB,hpos⟩:=eventual_multivariate_coefficients v s (α:=1) (by norm_num) hA hw hS hZ
  refine ⟨B,hB,?_⟩
  intro H hH
  obtain ⟨N₀,hconst⟩:=ConstantCoefficientRationalization.constant_coefficient_after_thinning s H
  let N:=max 1 N₀
  have hN : 0<N:=lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  filter_upwards [hpos H (by omega),hw.eventually (eventually_ge_atTop N),
    hw.eventually (eventually_ge_atTop s.factorial)] with n hn hnN hnfac
  intro a b hb hbsm hscale hrough θ hθ p u hp hsteps hu hobs
  obtain ⟨c,d,hd,hdN,hcd,M₀,hM₀,hM₀den,hM₀eval⟩:=hconst (θ 0) (hθ 0)
  have hN₀ : N₀≤N:=le_max_right _ _
  have hcdN : c+d*H≤N:=hcd.trans hN₀
  have hds : Smooth (w n) (d:ℤ):=smooth_of_abs_le (by exact_mod_cast hd.ne')
    (by simpa using hdN.trans (hN₀.trans hnN))
  have hbds : Smooth (w n) (b*(d:ℤ)):=smooth_mul hbsm hds
  let E:=Finset.Icc (0:ℤ) (H:ℤ)
  have hE (z) (hz : z∈E) : 0≤z ∧ z≤H:=Finset.mem_Icc.mp hz
  have hcard : 2*((v+1)*s+1)≤E.card:=by rw [int_interval_card]; omega
  have hdense : (1:ℝ)*H≤E.card:=by rw [int_interval_card]; simp
  let θ' : PolynomialLineCoefficients.Grid v s→ℝ[X]:=fun I=>(θ I).comp (C (c:ℝ)+C (d:ℝ)*X)
  have hθ' (I) : (θ' I).natDegree ≤ s:=affine_degree (hθ I) _ _
  have hindex (z : ℤ) (hz : 0≤z) (hzH : z≤H) :
      0≤(c:ℤ)+(d:ℤ)*z ∧ (c:ℤ)+(d:ℤ)*z≤N := by
    constructor
    · positivity
    · have h:=mul_le_mul_of_nonneg_left hzH (Int.natCast_nonneg d)
      have hn : (c:ℤ)+(d:ℤ)*(H:ℤ)≤N:=by exact_mod_cast hcdN
      omega
  have ht (z : ℤ) : a+b*((c:ℤ)+(d:ℤ)*z)=(a+b*(c:ℤ))+(b*(d:ℤ))*z:=by ring
  have heval (I) (z : ℤ) : (θ' I).eval (z:ℝ)=(θ I).eval (((c:ℤ)+(d:ℤ)*z):ℝ):=by
    simp [θ']
  obtain ⟨Mp,hMp⟩:=hn E hE hcard hdense (a+b*(c:ℤ)) (b*(d:ℤ))
    (mul_pos hb (by exact_mod_cast hd)) hbds
    (fun z hz hzH=>by simpa only [ht] using hscale _ (hindex z hz hzH).1 (hindex z hz hzH).2)
    (fun z hz=>by
      simpa only [ht] using (hrough _ (hindex z (hE z hz).1 (hE z hz).2).1
        (hindex z (hE z hz).1 (hE z hz).2).2))
    θ' hθ' (fun z=>p ((c:ℤ)+(d:ℤ)*z)) (fun z=>u ((c:ℤ)+(d:ℤ)*z))
    (fun z hz=>hp _ (hindex z (hE z hz).1 (hE z hz).2).1 (hindex z (hE z hz).1 (hE z hz).2).2)
    (fun z hz=>by
      simpa only [ht] using (hsteps _ (hindex z (hE z hz).1 (hE z hz).2).1
        (hindex z (hE z hz).1 (hE z hz).2).2))
    (fun z hz=>hu _ (hindex z (hE z hz).1 (hE z hz).2).1 (hindex z (hE z hz).1 (hE z hz).2).2)
    (fun z hz I hI=>by
      simpa only [heval,Int.cast_add,Int.cast_mul,Int.cast_natCast] using (hobs _ (hindex z (hE z hz).1 (hE z hz).2).1
        (hindex z (hE z hz).1 (hE z hz).2).2 I hI))
  let M : PolynomialLineCoefficients.Grid v s→ℚ[X]:=fun I=>
    if hI : 0<totalDegree I then Mp ⟨I,hI⟩ else M₀
  have hzero : totalDegree (0 : PolynomialLineCoefficients.Grid v s)=0:=by simp [totalDegree]
  have hMzero : M 0=M₀:=by simp [M,hzero]
  have hz (I : PolynomialLineCoefficients.Grid v s) (hI : ¬0<totalDegree I) : I=0:=
    (DenseBoxComplete.degree_eq_zero I).mp (by omega)
  have hM₀real (z : ℕ) (hzH : z≤H) :
      (M₀.map (algebraMap ℚ ℝ)).eval (z:ℝ)=(⌊(θ 0).eval ((c+d*z:ℕ):ℝ)⌋:ℤ):=by
    have h:=congrArg (algebraMap ℚ ℝ) (hM₀eval z hzH)
    rw [eval_map,show (z:ℝ)=algebraMap ℚ ℝ (z:ℚ) by simp,eval₂_at_apply]
    simpa using h
  have hM₀sm:=coefficients_smooth (D:=(s.factorial:ℤ))
    (by exact_mod_cast (Nat.factorial_pos s).ne')
    (smooth_of_abs_le (by exact_mod_cast (Nat.factorial_pos s).ne') (by simpa using hnfac)) hM₀den
  refine ⟨c,d,hd,hdN.trans hN₀,hcdN,hbds,M,?_,?_,?_,?_,?_⟩
  · intro I
    by_cases hI : 0<totalDegree I
    · simpa only [M,dite_eq_left hI] using ((hMp ⟨I,hI⟩).1.trans (Nat.sub_le ((v+1)*s) _))
    · simp only [M,dite_eq_right hI]
      exact hM₀.trans (by nlinarith)
  · intro I j p hp hpd
    by_cases hI : 0<totalDegree I
    · exact (hMp ⟨I,hI⟩).2.1 j p hp (by simpa only [M,dite_eq_left hI] using hpd)
    · exact hM₀sm j p hp (by simpa only [M,dite_eq_right hI] using hpd)
  · intro I z hzH
    by_cases hI : 0<totalDegree I
    · simpa only [M,dite_eq_left hI,Int.cast_natCast] using
        ((hMp ⟨I,hI⟩).2.2.1 (z:ℤ) (Finset.mem_Icc.mpr ⟨by positivity,by exact_mod_cast hzH⟩))
    · refine ⟨⌊(θ 0).eval ((c+d*z:ℕ):ℝ)⌋,?_⟩
      simpa only [M,dite_eq_right hI] using (hM₀eval z hzH).symm
  · intro I z hzH
    by_cases hI : 0<totalDegree I
    · have h:=(hMp ⟨I,hI⟩).2.2.2 (z:ℤ) (by positivity) (by exact_mod_cast hzH)
      simpa [M,hI,θ',Nat.cast_add,Nat.cast_mul] using h
    · have he:=hz I hI
      subst I
      rw [hMzero,hzero,pow_zero,mul_one,hM₀real z hzH]
      rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
      exact (Int.fract_lt_one _).le.trans hB
  · intro z hzH
    rw [hMzero,hM₀real z hzH]
    exact ⟨sub_nonneg.mpr (Int.floor_le _),Int.fract_lt_one _⟩

end RoughRationalBlock

end
end
end

end OAI
