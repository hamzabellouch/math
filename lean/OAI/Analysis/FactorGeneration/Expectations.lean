import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import OAI.Analysis.FactorGeneration.SpectralTruncation
import OAI.Analysis.FactorGeneration.Subfactors

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem selfAdjoint_pairing_im (τ : TracialRepresentation M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (τ.trace (a*b)).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  have hi := inner_conj_symm (𝕜 := ℂ) (baseVector τ a) (baseVector τ b)
  rw [baseVector_inner_trace,baseVector_inner_trace,ha.star_eq,hb.star_eq] at hi
  simpa only [τ.trace_mul_comm b a] using hi

theorem exists_selfAdjoint_expectation (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ ‖x‖ ∧
      TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-coordinateInclusion hNM c) := by
  obtain ⟨c,hc,hcR,hmin,hvar⟩ := exists_selfAdjoint_ball_variational τ hNM x (‖x‖+1)
    (by positivity)
  have hcn := selfAdjoint_ball_minimum_norm τ hNM x hx (‖x‖+1) c hc hcR hmin
  let r := x-coordinateInclusion hNM c
  have hr : IsSelfAdjoint r := hx.sub (included_selfAdjoint hNM c hc)
  have hreal (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      (τ.trace (coordinateInclusion hNM a*r)).re=0 := by
    let t : ℝ := 1/(‖a‖+1)
    have ht : 0<t := by dsimp [t]; positivity
    have hta : ‖t • a‖ ≤ 1 := by
      rw [norm_smul,Real.norm_of_nonneg ht.le]
      dsimp [t]
      rw [one_div_mul_eq_div,div_le_one (by positivity)]
      linarith [norm_nonneg a]
    have hp := hvar (c+t • a) (hc.add ((IsSelfAdjoint.all t).smul ha))
      ((norm_add_le _ _).trans (by linarith))
    have hm := hvar (c-t • a) (hc.sub ((IsSelfAdjoint.all t).smul ha))
      ((norm_sub_le _ _).trans (by linarith))
    have hep : c+t • a-c=t • a := by abel
    have hem : c-t • a-c=-(t • a) := by abel
    rw [hep,← Complex.coe_smul,map_smul,map_smul,inner_smul_right] at hp
    rw [hem,map_neg,map_neg,inner_neg_right,← Complex.coe_smul,map_smul,map_smul,inner_smul_right] at hm
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.neg_re] at hp hm
    change t*(inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re ≤ 0 at hp
    change -(t*(inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re) ≤ 0 at hm
    have hzero : (inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re=0 := by
      nlinarith
    rw [baseVector_inner_trace,hr.star_eq,τ.trace_mul_comm] at hzero
    exact hzero
  have hSA (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      τ.trace (coordinateInclusion hNM a*r)=0 :=
    Complex.ext (hreal a ha) (selfAdjoint_pairing_im τ _ r (included_selfAdjoint hNM a ha) hr)
  refine ⟨c,hc,hcn,?_⟩
  intro a
  let aN : N.toStarSubalgebra := ⟨(a : M.toStarSubalgebra).val,a.property⟩
  have hd := realPart_add_I_smul_imaginaryPart aN
  have he : (a : M.toStarSubalgebra)=coordinateInclusion hNM
      ((ℜ aN : N.toStarSubalgebra)+Complex.I • (ℑ aN : N.toStarSubalgebra)) := by
    rw [hd]; rfl
  change τ.trace ((a : M.toStarSubalgebra)*r)=0
  rw [he,map_add,map_smul,add_mul,smul_mul_assoc,cornerTrace_add,cornerTrace_smul,
    hSA _ (ℜ aN).property,hSA _ (ℑ aN).property,mul_zero,add_zero]

end

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem add (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x+y) := by
  intro a
  rw [mul_add,cornerTrace_add,hx a,hy a,add_zero]
theorem sub (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x-y) := by
  intro a
  rw [mul_sub,trace_sub,hx a,hy a,sub_self]
theorem smul (hx : TraceOrthogonal τ P x) (z : ℂ) : TraceOrthogonal τ P (z • x) := by
  intro a
  rw [mul_smul_comm,cornerTrace_smul,hx a,mul_zero]
theorem eq_zero (hx : TraceOrthogonal τ P x) (hP : x ∈ P) : x=0 := by
  have h := hx ⟨star x,P.star_mem' hP⟩
  change τ.trace (star x*x)=0 at h
  have hr := congrArg Complex.re h
  rw [← norm₂_sq_trace τ] at hr
  exact (τ.norm₂_eq_zero_iff x).mp (sq_eq_zero_iff.mp hr)
end TraceOrthogonal

theorem exists_bounded_subalgebra_representative (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ∃ y : M.toStarSubalgebra, y.val ∈ N ∧ ‖y‖ ≤ 2*‖x‖ ∧
      TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y) := by
  obtain ⟨a,ha,hna,hoa⟩ := exists_selfAdjoint_expectation τ hNM (ℜ x) (ℜ x).property
  obtain ⟨b,hb,hnb,hob⟩ := exists_selfAdjoint_expectation τ hNM (ℑ x) (ℑ x).property
  let y := coordinateInclusion hNM a+Complex.I • coordinateInclusion hNM b
  refine ⟨y,N.add_mem a.property (N.smul_mem b.property _),?_,?_⟩
  · calc ‖y‖ ≤ ‖a‖+‖b‖ := by
           change ‖y‖ ≤ ‖coordinateInclusion hNM a‖+‖coordinateInclusion hNM b‖
           simpa only [y,norm_smul,Complex.norm_I,one_mul] using
             norm_add_le (coordinateInclusion hNM a) (Complex.I • coordinateInclusion hNM b)
         _ ≤ 2*‖x‖ := by
           have hr := hna.trans (realPart.norm_le x)
           have hi := hnb.trans (imaginaryPart.norm_le x)
           linarith
  · have h := hoa.add τ (hob.smul τ Complex.I)
    convert h using 1
    dsimp [y]
    rw [smul_sub]
    nth_rw 1 [← realPart_add_I_smul_imaginaryPart x]
    abel

theorem subalgebra_representative_unique (x y z : M.toStarSubalgebra)
    (hy : y.val ∈ N) (hz : z.val ∈ N)
    (hxy : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y))
    (hxz : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-z)) : y=z := by
  have h := hxz.sub τ hxy
  have he : (x-z)-(x-y)=y-z := by abel
  rw [he] at h
  exact sub_eq_zero.mp (h.eq_zero τ (N.sub_mem hy hz))

def conditionalExpectation (hNM : N ≤ M) (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (exists_bounded_subalgebra_representative τ hNM x).choose

theorem conditionalExpectation_mem (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    (conditionalExpectation τ hNM x).val ∈ N :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.1
theorem conditionalExpectation_bound (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖conditionalExpectation τ hNM x‖ ≤ 2*‖x‖ :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.2.1
theorem conditionalExpectation_orthogonal (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-conditionalExpectation τ hNM x) :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.2.2

theorem conditionalExpectation_eq_of_orthogonal (hNM : N ≤ M)
    (x y : M.toStarSubalgebra) (hy : y.val ∈ N)
    (h : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y)) :
    conditionalExpectation τ hNM x=y :=
  subalgebra_representative_unique τ x _ y (conditionalExpectation_mem τ hNM x) hy
    (conditionalExpectation_orthogonal τ hNM x) h

theorem conditionalExpectation_add (hNM : N ≤ M) (x y : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (x+y)=conditionalExpectation τ hNM x+conditionalExpectation τ hNM y := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.add_mem (conditionalExpectation_mem τ hNM x) (conditionalExpectation_mem τ hNM y)
  · have h := (conditionalExpectation_orthogonal τ hNM x).add τ
      (conditionalExpectation_orthogonal τ hNM y)
    convert h using 1
    abel

theorem conditionalExpectation_smul (hNM : N ≤ M) (z : ℂ) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (z • x)=z • conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.smul_mem (conditionalExpectation_mem τ hNM x) z
  · simpa only [smul_sub] using (conditionalExpectation_orthogonal τ hNM x).smul τ z

def conditionalExpectationCLM (hNM : N ≤ M) : M.toStarSubalgebra →L[ℂ] M.toStarSubalgebra :=
  LinearMap.mkContinuous
    { toFun := conditionalExpectation τ hNM
      map_add' := conditionalExpectation_add τ hNM
      map_smul' := conditionalExpectation_smul τ hNM }
    2 (conditionalExpectation_bound τ hNM)

theorem conditionalExpectation_fixed (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : x.val ∈ N) :
    conditionalExpectation τ hNM x=x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM x x hx
  intro a
  simp only [sub_self,mul_zero]
  exact inner_zero_right _

theorem conditionalExpectation_trace (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.trace (conditionalExpectation τ hNM x)=τ.trace x := by
  have h := (conditionalExpectation_orthogonal τ hNM x).trace_zero τ
  rw [trace_sub,sub_eq_zero] at h
  exact h.symm

theorem conditionalExpectation_selfAdjoint (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (conditionalExpectation τ hNM x) ∧ ‖conditionalExpectation τ hNM x‖ ≤ ‖x‖ := by
  obtain ⟨c,hc,hn,ho⟩ := exists_selfAdjoint_expectation τ hNM x hx
  rw [conditionalExpectation_eq_of_orthogonal τ hNM x (coordinateInclusion hNM c) c.property ho]
  exact ⟨included_selfAdjoint hNM c hc,hn⟩

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem expectation_trace_adjoint (x : M.toStarSubalgebra) : τ.trace (star x)=star (τ.trace x) := by
  change τ.trace (star x)=(starRingEnd ℂ) (τ.trace x)
  have h := inner_conj_symm (𝕜 := ℂ) (baseVector τ x) (baseVector τ 1)
  simpa only [baseVector_inner_trace,star_one,one_mul,mul_one] using h.symm

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
theorem mul_left (hx : TraceOrthogonal τ P x) (a : M.toStarSubalgebra) (ha : a ∈ P) :
    TraceOrthogonal τ P (a*x) := by
  intro b
  exact mul_assoc (b : M.toStarSubalgebra) a x ▸ hx ⟨(b : M.toStarSubalgebra)*a,P.mul_mem b.property ha⟩
theorem mul_right (hx : TraceOrthogonal τ P x) (a : M.toStarSubalgebra) (ha : a ∈ P) :
    TraceOrthogonal τ P (x*a) := by
  intro b
  rw [← mul_assoc,τ.trace_mul_comm,← mul_assoc]
  exact hx ⟨a*(b : M.toStarSubalgebra),P.mul_mem ha b.property⟩
theorem adjoint (hx : TraceOrthogonal τ P x) : TraceOrthogonal τ P (star x) := by
  intro a
  have h := congrArg star (hx ⟨star (a : M.toStarSubalgebra),P.star_mem' a.property⟩)
  change star (τ.trace (star (a : M.toStarSubalgebra)*x))=star (0 : ℂ) at h
  rw [← expectation_trace_adjoint,star_mul,star_star,star_zero,τ.trace_mul_comm] at h
  exact h
end TraceOrthogonal

theorem conditionalExpectation_mul_left (hNM : N ≤ M) (a x : M.toStarSubalgebra)
    (ha : a.val ∈ N) : conditionalExpectation τ hNM (a*x)=a*conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.mul_mem ha (conditionalExpectation_mem τ hNM x)
  · simpa only [mul_sub] using (conditionalExpectation_orthogonal τ hNM x).mul_left τ a ha

theorem conditionalExpectation_mul_right (hNM : N ≤ M) (a x : M.toStarSubalgebra)
    (ha : a.val ∈ N) : conditionalExpectation τ hNM (x*a)=conditionalExpectation τ hNM x*a := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.mul_mem (conditionalExpectation_mem τ hNM x) ha
  · simpa only [sub_mul] using (conditionalExpectation_orthogonal τ hNM x).mul_right τ a ha

theorem conditionalExpectation_star (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (star x)=star (conditionalExpectation τ hNM x) := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact star_mem (conditionalExpectation_mem τ hNM x)
  · simpa only [star_sub] using (conditionalExpectation_orthogonal τ hNM x).adjoint τ

theorem conditionalExpectation_pythagoras (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x)^2+
      τ.norm₂ (x-conditionalExpectation τ hNM x)^2=τ.norm₂ x^2 := by
  have ho := conditionalExpectation_orthogonal τ hNM x
    ⟨star (conditionalExpectation τ hNM x),star_mem (conditionalExpectation_mem τ hNM x)⟩
  have hi : inner ℂ (baseVector τ (conditionalExpectation τ hNM x))
      (baseVector τ (x-conditionalExpectation τ hNM x))=0 := by
    rw [baseVector_inner_trace]; exact ho
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  rw [← map_add,add_sub_cancel] at h
  change τ.norm₂ x*τ.norm₂ x=τ.norm₂ (conditionalExpectation τ hNM x)*τ.norm₂ (conditionalExpectation τ hNM x)+
    τ.norm₂ (x-conditionalExpectation τ hNM x)*τ.norm₂ (x-conditionalExpectation τ hNM x) at h
  simpa only [pow_two] using h.symm

theorem conditionalExpectation_norm₂_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x) ≤ τ.norm₂ x := by
  have h := conditionalExpectation_pythagoras τ hNM x
  nlinarith [sq_nonneg (τ.norm₂ (x-conditionalExpectation τ hNM x)),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationPosCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationPosOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationPosPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationPosLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance expectationPosStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem negPart_mem_inside (c : M.toStarSubalgebra) (hc : c.val ∈ N) :
    c⁻ ∈ insideAlgebra (M := M) (P := N) := by
  rw [CFC.negPart_def,cfcₙ_eq_cfc]
  let : IsClosed (insideAlgebra (M := M) (P := N) : Set M.toStarSubalgebra) :=
    insideAlgebra_closed (M := M) (P := N)
  exact cfc_mem (𝕜' := ℂ) (s := insideAlgebra (M := M) (P := N)) (fun t : ℝ => t⁻) hc

theorem conditionalExpectation_nonneg (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ conditionalExpectation τ hNM x := by
  let c := conditionalExpectation τ hNM x
  have hc : IsSelfAdjoint c := (conditionalExpectation_selfAdjoint τ hNM x hx.isSelfAdjoint).1
  have hd := CFC.negPart_nonneg c
  have hmem := negPart_mem_inside c (conditionalExpectation_mem τ hNM x)
  have ho := conditionalExpectation_orthogonal τ hNM x ⟨c⁻,hmem⟩
  change τ.trace (c⁻*(x-c))=0 at ho
  rw [mul_sub,trace_sub,sub_eq_zero] at ho
  have hprod : c⁻*c= -(c⁻*c⁻) := by
    nth_rw 2 [← CFC.posPart_sub_negPart c hc]
    rw [mul_sub,CFC.negPart_mul_posPart,zero_sub]
  have hp := trace_mul_nonneg τ c⁻ x hd hx
  rw [ho,hprod] at hp
  have htrace : τ.trace (-(c⁻*c⁻))= -τ.trace (c⁻*c⁻) := map_neg (coordinateTraceLinear τ) _
  have hsq : (τ.trace (c⁻*c⁻)).re=τ.norm₂ c⁻^2 := by
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
  rw [htrace,Complex.neg_re,hsq] at hp
  have hz := (τ.norm₂_eq_zero_iff c⁻).mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (τ.norm₂ c⁻)]))
  exact (CFC.negPart_eq_zero_iff c hc).mp hz

theorem conditionalExpectation_mono (hNM : N ≤ M) (x y : M.toStarSubalgebra) (hxy : x ≤ y) :
    conditionalExpectation τ hNM x ≤ conditionalExpectation τ hNM y := by
  have h := conditionalExpectation_nonneg τ hNM (y-x) (sub_nonneg.mpr hxy)
  change 0 ≤ conditionalExpectationCLM τ hNM (y-x) at h
  rw [map_sub] at h
  exact sub_nonneg.mp h

end

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationContractiveCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationContractiveOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationContractivePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationContractiveLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance expectationContractiveStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem conditionalExpectation_schwarz (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    star (conditionalExpectation τ hNM x)*conditionalExpectation τ hNM x ≤
      conditionalExpectation τ hNM (star x*x) := by
  let y := conditionalExpectation τ hNM x
  have hy : y.val ∈ N := conditionalExpectation_mem τ hNM x
  have hys : (star y).val ∈ N := star_mem hy
  have hp := conditionalExpectation_nonneg τ hNM (star (x-y)*(x-y)) (star_mul_self_nonneg _)
  have he : conditionalExpectation τ hNM (star (x-y)*(x-y))=
      conditionalExpectation τ hNM (star x*x)-star y*y := by
    simp only [star_sub,sub_mul,mul_sub]
    change conditionalExpectationCLM τ hNM _= _
    rw [map_sub,map_sub,map_sub]
    change conditionalExpectation τ hNM (star x*x)-conditionalExpectation τ hNM (star y*x)-
      (conditionalExpectation τ hNM (star x*y)-conditionalExpectation τ hNM (star y*y))= _
    rw [conditionalExpectation_mul_right τ hNM y (star x) hy,
      conditionalExpectation_star τ hNM,
      conditionalExpectation_mul_left τ hNM (star y) x hys,
      conditionalExpectation_fixed τ hNM (star y*y) (N.mul_mem hys hy)]
    change conditionalExpectation τ hNM (star x*x)-star y*y-(star y*y-star y*y)=
      conditionalExpectation τ hNM (star x*x)-star y*y
    abel
  rw [he] at hp
  exact sub_nonneg.mp hp

theorem conditionalExpectation_norm_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖conditionalExpectation τ hNM x‖ ≤ ‖x‖ := by
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (conditionalExpectation_schwarz τ hNM x) (star_mul_self_nonneg (conditionalExpectation τ hNM x))
  have hn := (conditionalExpectation_selfAdjoint τ hNM (star x*x)
    (star_mul_self_nonneg x).isSelfAdjoint).2
  rw [CStarRing.norm_star_mul_self] at h hn
  nlinarith [norm_nonneg x,norm_nonneg (conditionalExpectation τ hNM x)]

theorem conditionalExpectation_opNorm_le (hNM : N ≤ M) :
    ‖conditionalExpectationCLM τ hNM‖ ≤ 1 := by
  apply (conditionalExpectationCLM τ hNM).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  change ‖conditionalExpectation τ hNM x‖ ≤ 1*‖x‖
  rw [one_mul]
  exact conditionalExpectation_norm_le τ hNM x

theorem conditionalExpectation_idempotent (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (conditionalExpectation τ hNM x)=conditionalExpectation τ hNM x :=
  conditionalExpectation_fixed τ hNM _ (conditionalExpectation_mem τ hNM x)

end

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N P M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_tower (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (conditionalExpectation τ hPM x)=conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact conditionalExpectation_mem τ hNM x
  · have hP : TraceOrthogonal τ (insideAlgebra (M := M) (P := N))
        (x-conditionalExpectation τ hPM x) := by
      intro a
      exact conditionalExpectation_orthogonal τ hPM x
        ⟨(a : M.toStarSubalgebra),hNP a.property⟩
    have h := (conditionalExpectation_orthogonal τ hNM x).sub τ hP
    convert h using 1
    abel

theorem conditionalExpectation_nested_energy (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x)^2+
      τ.norm₂ (conditionalExpectation τ hPM x-conditionalExpectation τ hNM x)^2=
        τ.norm₂ (conditionalExpectation τ hPM x)^2 := by
  have h := conditionalExpectation_pythagoras τ hNM (conditionalExpectation τ hPM x)
  rwa [conditionalExpectation_tower τ hNM hPM hNP x] at h

theorem conditionalExpectation_nested_norm₂ (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x) ≤ τ.norm₂ (conditionalExpectation τ hPM x) := by
  rw [← conditionalExpectation_tower τ hNM hPM hNP x]
  exact conditionalExpectation_norm₂_le τ hNM _

end

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem bounded_trace_limit_inside (hNM : N ≤ M) (a : ℕ → M.toStarSubalgebra)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n,‖a n‖ ≤ C)
    (hN : ∀ᶠ n in atTop,(a n).val ∈ N) (ξ : H)
    (hξ : Tendsto (fun n => baseVector τ (a n)) atTop (𝓝 ξ)) :
    ∃ b : M.toStarSubalgebra,b.val ∈ N ∧ ‖b‖ ≤ C ∧ baseVector τ b=ξ := by
  classical
  let aN : ℕ → N.toStarSubalgebra := fun n => if h : (a n).val ∈ N then ⟨(a n).val,h⟩ else 0
  have hb : ∀ n,‖aN n‖ ≤ C := by
    intro n
    dsimp [aN]
    split_ifs with h
    · exact ha n
    · change ‖(0 : H →L[ℂ] H)‖ ≤ C
      simpa only [norm_zero] using hC
  have he : ∀ᶠ n in atTop,baseVector (restrictedTrace τ hNM) (aN n)=baseVector τ (a n) := by
    filter_upwards [hN] with n hn
    simp only [aN,dite_eq_left hn]
    rfl
  obtain ⟨b,hb,hbe⟩ := bounded_trace_limit (restrictedTrace τ hNM) aN C hC hb ξ
    (hξ.congr' (by filter_upwards [he] with n hn; exact hn.symm))
  exact ⟨coordinateInclusion hNM b,b.property,hb,hbe⟩

theorem decreasing_expectations_converge (A : ℕ → VonNeumannAlgebra H)
    (hAM : ∀ n,A n ≤ M) (hA : Antitone A) (x : M.toStarSubalgebra) :
    ∃ c : M.toStarSubalgebra,(∀ n,c.val ∈ A n) ∧ ‖c‖ ≤ ‖x‖ ∧ τ.trace c=τ.trace x ∧
      Tendsto (fun n => τ.norm₂ (conditionalExpectation τ (hAM n) x-c)) atTop (𝓝 0) := by
  let e : ℕ → M.toStarSubalgebra := fun n => conditionalExpectation τ (hAM n) x
  let f : ℕ → ℝ := fun n => τ.norm₂ (e n)^2
  have hf : Antitone f := by
    intro m n hmn
    have h := conditionalExpectation_nested_energy τ (hAM n) (hAM m) (hA hmn) x
    change f n+τ.norm₂ (e m-e n)^2=f m at h
    linarith [sq_nonneg (τ.norm₂ (e m-e n))]
  have hft : Tendsto f atTop (𝓝 (⨅ n,f n)) := tendsto_atTop_ciInf hf
    ⟨0,by rintro _ ⟨n,rfl⟩; exact sq_nonneg _⟩
  have hfc := hft.cauchySeq
  have hcv : CauchySeq (fun n => baseVector τ (e n)) := by
    rw [Metric.cauchySeq_iff] at hfc ⊢
    intro ε hε
    obtain ⟨k,hk⟩ := hfc (ε^2) (sq_pos_of_pos hε)
    have hb (m n : ℕ) (hm : k ≤ m) (hn : k ≤ n) (hmn : m ≤ n) :
        dist (baseVector τ (e m)) (baseVector τ (e n)) < ε := by
      have hdist := hk m hm n hn
      have hid := conditionalExpectation_nested_energy τ (hAM n) (hAM m) (hA hmn) x
      change f n+τ.norm₂ (e m-e n)^2=f m at hid
      rw [Real.dist_eq] at hdist
      rw [dist_eq_norm,← map_sub]
      change τ.norm₂ (e m-e n)<ε
      nlinarith [le_abs_self (f m-f n),show 0 ≤ τ.norm₂ (e m-e n) from norm_nonneg _]
    refine ⟨k,fun m hm n hn => ?_⟩
    rcases le_total m n with h | h
    · exact hb m n hm hn h
    · simpa only [dist_comm] using hb n m hn hm h
  obtain ⟨ξ,hξ⟩ := cauchySeq_tendsto_of_complete hcv
  obtain ⟨c,hcn,hcξ⟩ := bounded_trace_limit τ e ‖x‖ (norm_nonneg x)
    (fun n => conditionalExpectation_norm_le τ (hAM n) x) ξ hξ
  have hcN (n : ℕ) : c.val ∈ A n := by
    have hmem : ∀ᶠ k in atTop,(e k).val ∈ A n := by
      filter_upwards [eventually_ge_atTop n] with k hk
      exact hA hk (conditionalExpectation_mem τ (hAM k) x)
    obtain ⟨b,hb,_,hbξ⟩ := bounded_trace_limit_inside τ (hAM n) e ‖x‖ (norm_nonneg _)
      (fun k => conditionalExpectation_norm_le τ (hAM k) x) hmem ξ hξ
    have he : c=b := baseVector_injective τ (hcξ.trans hbξ.symm)
    rw [he]
    exact hb
  have hlim : Tendsto (fun n => τ.norm₂ (e n-c)) atTop (𝓝 0) :=
    (tendsto_vector_iff_norm₂ τ atTop e c).mp (by rw [hcξ]; exact hξ)
  refine ⟨c,hcN,hcn,?_,hlim⟩
  have ht := norm₂_limit_trace τ e c hlim
  have he : ∀ n,τ.trace (e n)=τ.trace x := fun n => conditionalExpectation_trace τ (hAM n) x
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem decreasing_expectations_scalar_limit (A : ℕ → VonNeumannAlgebra H)
    (hAM : ∀ n,A n ≤ M) (hA : Antitone A)
    (hscalar : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ A n) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) (x : M.toStarSubalgebra) :
    Tendsto (fun n => τ.norm₂ (conditionalExpectation τ (hAM n) x-
      τ.trace x • (1 : M.toStarSubalgebra))) atTop (𝓝 0) := by
  obtain ⟨c,hc,_,htrace,hlim⟩ := decreasing_expectations_converge τ A hAM hA x
  obtain ⟨z,hz⟩ := hscalar c hc
  rw [hz,cornerTrace_smul,τ.trace_one,mul_one] at htrace
  simpa only [hz,htrace] using hlim

theorem decreasing_expectations_finite_centered_budget (A : ℕ → VonNeumannAlgebra H)
    (hAM : ∀ n,A n ≤ M) (hA : Antitone A)
    (hscalar : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ A n) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,(∑ i ∈ F,τ.norm₂ (conditionalExpectation τ (hAM n) (x i))^2) < ε := by
  have hi (i : ι) (hi : i ∈ F) :
      Tendsto (fun n => τ.norm₂ (conditionalExpectation τ (hAM n) (x i))^2) atTop (𝓝 0) := by
    have h := decreasing_expectations_scalar_limit τ A hAM hA hscalar (x i)
    rw [hx i hi] at h
    simpa only [zero_smul,sub_zero,zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  have ht : Tendsto (fun n => ∑ i ∈ F,τ.norm₂ (conditionalExpectation τ (hAM n) (x i))^2)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum F hi
  exact (ht.eventually (gt_mem_nhds hε)).exists

end Generator.Tracial

end

end OAI
