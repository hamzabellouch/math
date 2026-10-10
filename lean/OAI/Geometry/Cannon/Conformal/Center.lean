import Mathlib
import OAI.Geometry.Cannon.Conformal.SphereMeasure

namespace OAI

section
section
section
section
section
section
section
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

lemma determinant_continuous : Continuous determinant := by
  unfold determinant
  fun_prop

lemma evaluate_continuous (x y : ℝ) : Continuous (fun q : Form => evaluate q x y) := by
  unfold evaluate
  fun_prop

lemma evaluate_add (p q : Form) (x y : ℝ) :
    evaluate (p+q) x y=evaluate p x y+evaluate q x y := by
  simp only [evaluate,Pi.add_apply]
  ring

lemma evaluate_smul (a : ℝ) (p : Form) (x y : ℝ) :
    evaluate (a • p) x y=a*evaluate p x y := by
  simp only [evaluate,Pi.smul_apply,smul_eq_mul]
  ring

lemma lowerBound_positive {ε : ℝ} (hε : 0 < ε) {q : Form} (hq : LowerBound ε q) :
    Positive q := by
  have ha : ε ≤ q 0 := by simpa [evaluate] using hq 1 0
  have hap : 0 < q 0 := hε.trans_le ha
  refine ⟨hap,?_⟩
  have hp := hq (q 1) (-(q 0))
  have hid : evaluate q (q 1) (-(q 0))=q 0*determinant q := by
    simp only [evaluate,determinant]
    ring
  rw [hid] at hp
  have hsum : 0 < (q 1)^2+(-(q 0))^2 := by nlinarith [sq_nonneg (q 1)]
  have hpos := (mul_pos hε hsum).trans_le hp
  exact (mul_pos_iff_of_pos_left hap).mp hpos

lemma lowerBound_closed (ε : ℝ) : IsClosed {q : Form | LowerBound ε q} := by
  simp only [LowerBound,ofPred_forall]
  exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_le continuous_const (evaluate_continuous x y)))

lemma lowerBound_convex (ε : ℝ) : Convex ℝ {q : Form | LowerBound ε q} := by
  intro p hp q hq a b ha hb hab x y
  rw [evaluate_add,evaluate_smul,evaluate_smul]
  have h₁ := mul_le_mul_of_nonneg_left (hp x y) ha
  have h₂ := mul_le_mul_of_nonneg_left (hq x y) hb
  calc
    ε*(x^2+y^2) = (a+b)*(ε*(x^2+y^2)) := by rw [hab,one_mul]
    _ = a*(ε*(x^2+y^2))+b*(ε*(x^2+y^2)) := by ring
    _ ≤ a*evaluate p x y+b*evaluate q x y := add_le_add h₁ h₂

lemma determinant_midpoint_identity (p q : Form) :
    4*p 0*q 0*determinant ((1/2:ℝ) • p+(1/2:ℝ) • q) =
      (p 0+q 0)*(q 0*determinant p+p 0*determinant q)+
      (p 0*q 1-q 0*p 1)^2 := by
  simp only [determinant,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma determinant_midpoint_strict {p q : Form} (hp : Positive p) (hq : Positive q)
    (heq : determinant p=determinant q) (hne : p ≠ q) :
    determinant p < determinant ((1/2:ℝ) • p+(1/2:ℝ) • q) := by
  by_contra! hle
  have hid := determinant_midpoint_identity p q
  rw [← heq] at hid
  have hprod : 0 < 4*p 0*q 0 := mul_pos (mul_pos (by norm_num) hp.1) hq.1
  have hm := mul_le_mul_of_nonneg_left hle hprod.le
  have hsquare := sq_nonneg (p 0*q 1-q 0*p 1)
  have hid' : 4*p 0*q 0*(determinant ((1/2:ℝ) • p+(1/2:ℝ) • q)-determinant p) =
      (p 0-q 0)^2*determinant p+(p 0*q 1-q 0*p 1)^2 := by nlinarith only [hid]
  have hz : (p 0-q 0)^2*determinant p ≤ 0 := by nlinarith only [hid',hm,hsquare]
  have hs0 : (p 0-q 0)^2=0 := by nlinarith [sq_nonneg (p 0-q 0),hp.2]
  have h0 : p 0=q 0 := by nlinarith only [hs0]
  have hcross : p 0*q 1-q 0*p 1=0 := by
    rw [hs0,zero_mul,zero_add] at hid'
    have hh : (p 0*q 1-q 0*p 1)^2=0 := by nlinarith only [hid',hm,hsquare]
    exact sq_eq_zero_iff.mp hh
  have h1 : p 1=q 1 := by rw [← h0] at hcross; nlinarith [hp.1]
  have h2 : p 2=q 2 := by
    simp only [determinant,← h0,← h1] at heq
    nlinarith [hp.1]
  apply hne
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma determinant_max_unique {K : Set Form} (hconv : Convex ℝ K)
    (hpos : ∀ q ∈ K, Positive q) {p q : Form} (hp : p ∈ K) (hq : q ∈ K)
    (hmaxp : IsMaxOn determinant K p) (hmaxq : IsMaxOn determinant K q) : p=q := by
  by_contra hne
  have heq : determinant p=determinant q := le_antisymm (hmaxq hp) (hmaxp hq)
  have hmid := hconv hp hq (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  exact not_lt_of_ge (hmaxp hmid) (determinant_midpoint_strict (hpos p hp) (hpos q hq) heq hne)

theorem exists_unique_maxdet {S : Set Form} (hne : S.Nonempty)
    (hbounded : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ q ∈ S, LowerBound ε q) :
    ∃! q : Form, q ∈ closedConvexHull ℝ S ∧ IsMaxOn determinant (closedConvexHull ℝ S) q := by
  have hl : closedConvexHull ℝ S ⊆ {q | LowerBound ε q} :=
    closedConvexHull_min hlower (lowerBound_convex ε) (lowerBound_closed ε)
  have hb : Bornology.IsBounded (closedConvexHull ℝ S) := by
    rw [closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hbounded).closure
  have hc : IsCompact (closedConvexHull ℝ S) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closedConvexHull,hb⟩
  obtain ⟨q,hq,hm⟩ := hc.exists_isMaxOn (hne.mono subset_closedConvexHull) determinant_continuous.continuousOn
  refine ⟨q,⟨hq,hm⟩,?_⟩
  rintro p ⟨hp,hpm⟩
  exact determinant_max_unique convex_closedConvexHull (fun z hz => lowerBound_positive hε (hl hz)) hp hq hpm hm

def center (S : Set Form) : Form :=
  Classical.epsilon (fun q => q ∈ closedConvexHull ℝ S ∧
    IsMaxOn determinant (closedConvexHull ℝ S) q)

lemma center_spec {S : Set Form} (hne : S.Nonempty)
    (hb : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ q ∈ S, LowerBound ε q) :
    center S ∈ closedConvexHull ℝ S ∧ IsMaxOn determinant (closedConvexHull ℝ S) (center S) :=
  Classical.epsilon_spec (exists_unique_maxdet hne hb hε hl).exists

lemma center_eq {S : Set Form} (hne : S.Nonempty)
    (hb : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ q ∈ S, LowerBound ε q) {p : Form}
    (hp : p ∈ closedConvexHull ℝ S) (hmax : IsMaxOn determinant (closedConvexHull ℝ S) p) :
    center S = p := by
  have hc := center_spec hne hb hε hl
  exact (exists_unique_maxdet hne hb hε hl).unique hc ⟨hp,hmax⟩

lemma image_closedConvexHull (L : Form ≃L[ℝ] Form) (S : Set Form) :
    L '' closedConvexHull ℝ S = closedConvexHull ℝ (L '' S) := by
  rw [closedConvexHull_eq_closure_convexHull,closedConvexHull_eq_closure_convexHull]
  change L.toHomeomorph '' closure (convexHull ℝ S) = _
  rw [L.toHomeomorph.image_closure]
  congr 1
  exact L.toLinearMap.image_convexHull S

theorem center_equivariant (L : Form ≃L[ℝ] Form)
    (hdet : ∀ q, determinant (L q)=determinant q)
    {S T : Set Form} (hST : L '' S = T)
    (hS : S.Nonempty) (hbS : Bornology.IsBounded S)
    (hT : T.Nonempty) (hbT : Bornology.IsBounded T)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hlS : ∀ q ∈ S, LowerBound ε q) (hlT : ∀ q ∈ T, LowerBound δ q) :
    L (center S)=center T := by
  have hmap : L '' closedConvexHull ℝ S=closedConvexHull ℝ T := by
    rw [image_closedConvexHull,hST]
  have hc := center_spec hS hbS hε hlS
  symm
  apply center_eq hT hbT hδ hlT
  · rw [← hmap]
    exact mem_image_of_mem L hc.1
  · intro p hp
    rw [← hmap] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    dsimp
    rw [hdet,hdet]
    exact hc.2 hq

abbrev PlaneLinear := Fin 4 → ℝ

def planeDet (A : PlaneLinear) : ℝ := A 0*A 3-A 1*A 2

def adjugate (A : PlaneLinear) : PlaneLinear := ![A 3,-A 1,-A 2,A 0]

def pullForm (A : PlaneLinear) : Form →ₗ[ℝ] Form where
  toFun q := ![q 0*(A 0)^2+2*q 1*A 0*A 2+q 2*(A 2)^2,
    q 0*A 0*A 1+q 1*(A 0*A 3+A 1*A 2)+q 2*A 2*A 3,
    q 0*(A 1)^2+2*q 1*A 1*A 3+q 2*(A 3)^2]
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c q := by
    ext i
    fin_cases i <;> simp <;> ring

lemma determinant_pullForm (A : PlaneLinear) (q : Form) :
    determinant (pullForm A q)=(planeDet A)^2*determinant q := by
  simp [determinant,pullForm,planeDet]
  ring

lemma determinant_smul (r : ℝ) (q : Form) :
    determinant (r • q)=r^2*determinant q := by
  simp [determinant]
  ring

lemma evaluate_pullForm (A : PlaneLinear) (q : Form) (x y : ℝ) :
    evaluate (pullForm A q) x y=evaluate q (A 0*x+A 1*y) (A 2*x+A 3*y) := by
  simp [evaluate,pullForm]
  ring

lemma planeDet_adjugate (A : PlaneLinear) : planeDet (adjugate A)=planeDet A := by
  simp [planeDet,adjugate]
  ring

lemma adjugate_adjugate (A : PlaneLinear) : adjugate (adjugate A)=A := by
  ext i
  fin_cases i <;> simp [adjugate]

lemma pullForm_adjugate (A : PlaneLinear) (q : Form) :
    pullForm (adjugate A) (pullForm A q)=(planeDet A)^2 • q := by
  ext i
  fin_cases i <;> simp [pullForm,adjugate,planeDet] <;> ring

def normalizedPull (A : PlaneLinear) : Form →ₗ[ℝ] Form :=
  |planeDet A|⁻¹ • pullForm A

lemma normalizedPull_apply (A : PlaneLinear) (q : Form) :
    normalizedPull A q=|planeDet A|⁻¹ • pullForm A q := rfl

lemma normalizedPull_det (A : PlaneLinear) (hA : planeDet A ≠ 0) (q : Form) :
    determinant (normalizedPull A q)=determinant q := by
  rw [normalizedPull_apply,determinant_smul,determinant_pullForm]
  have ha : |planeDet A| ≠ 0 := abs_ne_zero.mpr hA
  have he : (|planeDet A|⁻¹)^2*(planeDet A)^2=1 := by
    rw [← sq_abs (planeDet A)]
    field_simp
  rw [← mul_assoc,he,one_mul]

lemma normalizedPull_adjugate (A : PlaneLinear) (hA : planeDet A ≠ 0) (q : Form) :
    normalizedPull (adjugate A) (normalizedPull A q)=q := by
  rw [normalizedPull_apply,normalizedPull_apply,map_smul,pullForm_adjugate,planeDet_adjugate]
  simp only [smul_smul]
  have ha : |planeDet A| ≠ 0 := abs_ne_zero.mpr hA
  have he : |planeDet A|⁻¹*(|planeDet A|⁻¹*(planeDet A)^2)=1 := by
    rw [← sq_abs (planeDet A)]
    field_simp
  rw [he,one_smul]

def pullbackEquiv (A : PlaneLinear) (hA : planeDet A ≠ 0) : Form ≃L[ℝ] Form :=
  LinearEquiv.toContinuousLinearEquiv
    { normalizedPull A with
      invFun := normalizedPull (adjugate A)
      left_inv := normalizedPull_adjugate A hA
      right_inv := by
        intro q
        change normalizedPull A (normalizedPull (adjugate A) q)=q
        simpa only [adjugate_adjugate] using
          normalizedPull_adjugate (adjugate A) (by simpa only [planeDet_adjugate] using hA) q }

lemma pullbackEquiv_det (A : PlaneLinear) (hA : planeDet A ≠ 0) (q : Form) :
    determinant (pullbackEquiv A hA q)=determinant q := normalizedPull_det A hA q

def planeMul (A B : PlaneLinear) : PlaneLinear :=
  ![A 0*B 0+A 1*B 2,A 0*B 1+A 1*B 3,A 2*B 0+A 3*B 2,A 2*B 1+A 3*B 3]

lemma planeDet_mul (A B : PlaneLinear) : planeDet (planeMul A B)=planeDet A*planeDet B := by
  simp [planeDet,planeMul]
  ring

lemma pullForm_mul (A B : PlaneLinear) (q : Form) :
    pullForm (planeMul A B) q=pullForm B (pullForm A q) := by
  ext i
  fin_cases i <;> simp [pullForm,planeMul] <;> ring

lemma normalizedPull_mul (A B : PlaneLinear) (q : Form) :
    normalizedPull (planeMul A B) q=normalizedPull B (normalizedPull A q) := by
  simp only [normalizedPull_apply,planeDet_mul,abs_mul,mul_inv_rev,pullForm_mul,map_smul,smul_smul]
  rw [mul_comm]

end CannonConformal

end
end
noncomputable section
namespace CannonConformal
open CannonMetricQC

def roundForm : Form := ![1,0,1]

lemma derivativeMatrix_comp (A B : ℂ →L[ℝ] ℂ) :
    derivativeMatrix (A.comp B)=planeMul (derivativeMatrix A) (derivativeMatrix B) := by
  have h1 := derivative_apply A (B 1)
  have hI := derivative_apply A (B Complex.I)
  ext i
  fin_cases i <;> simp [derivativeMatrix,planeMul,ContinuousLinearMap.comp_apply,
    h1,hI,Complex.add_re,Complex.add_im] <;> ring

lemma derivativeDet_comp (A B : ℂ →L[ℝ] ℂ) :
    derivativeDet (A.comp B)=derivativeDet A*derivativeDet B := by
  change planeDet (derivativeMatrix (A.comp B))=
    planeDet (derivativeMatrix A)*planeDet (derivativeMatrix B)
  rw [derivativeMatrix_comp,planeDet_mul]

lemma pull_round_derivative (A : ℂ →L[ℝ] ℂ) :
    pullForm (derivativeMatrix A) roundForm=derivativeForm A := by
  ext i
  fin_cases i <;> simp [pullForm,derivativeMatrix,roundForm,derivativeForm,
    Complex.sq_norm,Complex.normSq_apply] <;> ring

lemma evaluate_normalized_round (A : ℂ →L[ℝ] ℂ) (x y : ℝ) :
    evaluate (normalizedPull (derivativeMatrix A) roundForm) x y=
      |derivativeDet A|⁻¹*‖A (⟨x,y⟩ : ℂ)‖^2 := by
  rw [normalizedPull_apply,evaluate_smul,pull_round_derivative,derivativeForm_evaluate]
  rfl

theorem normalized_derivative_bounds (A B : ℂ →L[ℝ] ℂ) {H : ℝ}
    (hH : 0 < H) (hA : Function.Bijective A) (hBA : B.comp A=ContinuousLinearMap.id ℝ ℂ)
    (hu : ∀ v : ℂ, ‖A v‖^2 ≤ H^2*|derivativeDet A| * ‖v‖^2)
    (hi : ∀ v : ℂ, ‖B v‖^2 ≤ H^2*|derivativeDet B| * ‖v‖^2) :
    LowerBound ((H^2)⁻¹) (normalizedPull (derivativeMatrix A) roundForm) ∧
      UpperBound (H^2) (normalizedPull (derivativeMatrix A) roundForm) := by
  have ha : 0 < |derivativeDet A| := abs_pos.mpr (derivativeDet_ne_zero hA)
  have hH2 : 0 < H^2 := sq_pos_of_pos hH
  have hprod : |derivativeDet A| * |derivativeDet B|=1 := by
    have hh := congrArg derivativeDet hBA
    rw [derivativeDet_comp] at hh
    have hid : derivativeDet (ContinuousLinearMap.id ℝ ℂ)=1 := by norm_num [derivativeDet]
    rw [hid] at hh
    have haa := congrArg abs hh
    simpa only [abs_mul,abs_one,mul_comm] using haa
  have hleft (v : ℂ) : B (A v)=v := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hBA
  constructor
  · intro x y
    rw [evaluate_normalized_round]
    let v : ℂ := ⟨x,y⟩
    have hv : ‖v‖^2=x^2+y^2 := by
      rw [Complex.sq_norm]
      simp [v,Complex.normSq_apply,pow_two]
    have hh := hi (A v)
    rw [hleft] at hh
    have hmul := mul_le_mul_of_nonneg_right hh ha.le
    have hr : (H^2*|derivativeDet B| * ‖A v‖^2)*|derivativeDet A|=H^2*‖A v‖^2 := by
      calc
        _ = (|derivativeDet A| * |derivativeDet B|)*(H^2*‖A v‖^2) := by ring
        _ = _ := by rw [hprod,one_mul]
    rw [hr,hv] at hmul
    rw [← div_eq_inv_mul,← div_eq_inv_mul]
    exact (div_le_div_iff₀ hH2 ha).mpr (by simpa only [mul_comm] using hmul)
  · intro x y
    rw [evaluate_normalized_round,← div_eq_inv_mul]
    have hh := hu (⟨x,y⟩ : ℂ)
    have hv : ‖(⟨x,y⟩ : ℂ)‖^2=x^2+y^2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply,pow_two]
    rw [hv] at hh
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hh]

end CannonConformal

end
end
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

theorem continuous_unique_max_image {X C Y : Type*}
    [TopologicalSpace X] [TopologicalSpace C] [CompactSpace C]
    [TopologicalSpace Y] (F : X × C → Y) (hF : Continuous F)
    (V : Y → ℝ) (hV : Continuous V) (s : X → Y)
    (hs : ∀ x, ∃ c, F (x,c)=s x ∧ ∀ d, V (F (x,d)) ≤ V (s x))
    (hunique : ∀ x c, (∀ d, V (F (x,d)) ≤ V (F (x,c))) → F (x,c)=s x) :
    Continuous s := by
  rw [continuous_iff_isClosed]
  intro T hT
  let K : Set (X × C) := {p | F p ∈ T ∧ ∀ d : C, V (F (p.1,d)) ≤ V (F p)}
  have hK : IsClosed K := by
    change IsClosed ({p | F p ∈ T} ∩ {p | ∀ d : C, V (F (p.1,d)) ≤ V (F p)})
    refine (hT.preimage hF).inter ?_
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro d
    exact isClosed_le (hV.comp (hF.comp (continuous_fst.prodMk continuous_const))) (hV.comp hF)
  have heq : s ⁻¹' T=Prod.fst '' K := by
    ext x
    constructor
    · intro hx
      obtain ⟨c,hc,hmax⟩ := hs x
      exact ⟨(x,c),⟨hc ▸ hx,by simpa only [hc] using hmax⟩,rfl⟩
    · rintro ⟨⟨y,c⟩,⟨hy,hmax⟩,rfl⟩
      change s y ∈ T
      rw [← hunique y c hmax]
      exact hy
  rw [heq]
  exact isClosedMap_fst_of_compactSpace K hK

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def combination (q : ι → Form) : (ι → ℝ) →ₗ[ℝ] Form :=
  ∑ i, (LinearMap.proj i).smulRight (q i)

omit [Nonempty ι] in
lemma combination_apply (q : ι → Form) (w : ι → ℝ) :
    combination q w=∑ i, w i • q i := by simp [combination]

omit [Nonempty ι] in
lemma combination_image (q : ι → Form) :
    combination q '' {weights : ι → ℝ | (∀ index, 0 ≤ weights index) ∧
      ∑ index, weights index = 1}=convexHull ℝ (range q) := by
  classical
  have hconvex : Convex ℝ {weights : ι → ℝ | (∀ index, 0 ≤ weights index) ∧
      ∑ index, weights index = 1} := by
    intro weights hweights other hother left right hleft hright htotal
    constructor
    · intro index
      exact add_nonneg (mul_nonneg hleft (hweights.1 index))
        (mul_nonneg hright (hother.1 index))
    · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
        ← Finset.mul_sum,hweights.2,hother.2,mul_one,htotal]
  apply subset_antisymm
  · rintro _ ⟨weights,hweights,rfl⟩
    rw [combination_apply]
    exact (convex_convexHull ℝ (range q)).sum_mem
      (fun index _ => hweights.1 index) hweights.2
      (fun index _ => subset_convexHull ℝ (range q) (mem_range_self index))
  · apply convexHull_min _ (hconvex.linear_image (combination q))
    rintro _ ⟨index,rfl⟩
    refine ⟨Pi.single index 1,?_,?_⟩
    · simp [Pi.single_apply]
      intro coordinate
      split_ifs <;> norm_num
    · simp [combination_apply,Pi.single_apply]

omit [Nonempty ι] in
lemma closedConvexHull_finite_range (q : ι → Form) :
    closedConvexHull ℝ (range q)=convexHull ℝ (range q) := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact (finite_range q).isClosed_convexHull ℝ |>.closure_eq

abbrev FiniteForms (ε : ℝ) (ι : Type*) := {q : ι → Form | ∀ i, LowerBound ε (q i)}

lemma continuous_finite_center {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun q : FiniteForms ε ι => center (range q.val)) := by
  let weightsSet : Set (ι → ℝ) :=
    {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}
  have hcompact : IsCompact weightsSet := by
    have hcompact := isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous
    simpa only [Convexity.StdSimplex.range_toFun_comp_weights,weightsSet,
      ofPred_forall,ofPred_and] using hcompact
  let : CompactSpace weightsSet := isCompact_iff_compactSpace.mp hcompact
  let F : FiniteForms ε ι × weightsSet → Form :=
    fun p => combination p.1.val p.2.val
  have hF : Continuous F := by
    dsimp only [F]
    simp_rw [combination_apply]
    apply continuous_finsetSum
    intro i _hi
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))
  apply continuous_unique_max_image F hF determinant determinant_continuous
  · intro q
    have hc := center_spec (range_nonempty q.val) (finite_range q.val).isBounded hε
      (by rintro _ ⟨i,rfl⟩; exact q.property i)
    rw [closedConvexHull_finite_range,← combination_image] at hc
    obtain ⟨w,hw,hweq⟩ := hc.1
    refine ⟨⟨w,hw⟩,hweq,?_⟩
    intro w
    exact hc.2 (mem_image_of_mem _ w.property)
  · intro q w hmax
    symm
    apply center_eq (range_nonempty q.val) (finite_range q.val).isBounded hε
      (by rintro _ ⟨i,rfl⟩; exact q.property i)
    · rw [closedConvexHull_finite_range,← combination_image]
      exact mem_image_of_mem _ w.property
    · intro p hp
      rw [closedConvexHull_finite_range,← combination_image] at hp
      obtain ⟨v,hv,rfl⟩ := hp
      exact hmax ⟨v,hv⟩

end Finite

open Filter

def orbitPrefix (q : ℕ → Form) (n : ℕ) : Set Form := range (fun i : Fin (n+1) => q i.val)

lemma prefix_nonempty (q : ℕ → Form) (n : ℕ) : (orbitPrefix q n).Nonempty :=
  ⟨q 0,⟨⟨0,Nat.zero_lt_succ _⟩,rfl⟩⟩

lemma prefix_subset_range (q : ℕ → Form) (n : ℕ) : orbitPrefix q n ⊆ range q := by
  rintro p ⟨i,rfl⟩
  exact mem_range_self i.val

lemma prefix_monotone (q : ℕ → Form) : Monotone (orbitPrefix q) := by
  intro n m hnm p hp
  obtain ⟨i,rfl⟩ := hp
  exact ⟨⟨i.val,lt_of_lt_of_le i.isLt (Nat.add_le_add_right hnm 1)⟩,rfl⟩

lemma prefix_closure_union (q : ℕ → Form) :
    closure (⋃ n, closedConvexHull ℝ (orbitPrefix q n))=closedConvexHull ℝ (range q) := by
  let K := fun n => closedConvexHull ℝ (orbitPrefix q n)
  have hmono : Monotone K := (closedConvexHull ℝ).monotone.comp (prefix_monotone q)
  apply le_antisymm
  · apply closure_minimal _ isClosed_closedConvexHull
    exact iUnion_subset (fun n => (closedConvexHull ℝ).monotone (prefix_subset_range q n))
  · apply closedConvexHull_min _ (hmono.directed_le.convex_iUnion (fun n => convex_closedConvexHull)).closure isClosed_closure
    rintro p ⟨n,rfl⟩
    apply subset_closure
    apply mem_iUnion_of_mem n
    exact subset_closedConvexHull ⟨⟨n,Nat.lt_succ_self n⟩,rfl⟩

theorem prefix_center_tendsto (q : ℕ → Form)
    (hb : Bornology.IsBounded (range q)) {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ n, LowerBound ε (q n)) :
    Tendsto (fun n => center (orbitPrefix q n)) atTop (𝓝 (center (range q))) := by
  let K := closedConvexHull ℝ (range q)
  have hbd : Bornology.IsBounded K := by
    dsimp [K]
    rw [closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hb).closure
  have hK : IsCompact K := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closedConvexHull,hbd⟩
  have hspec (n : ℕ) := center_spec (prefix_nonempty q n)
    (hb.subset (prefix_subset_range q n)) hε
    (fun p hp => by obtain ⟨i,rfl⟩ := hp; exact hl i.val)
  have hsub (n : ℕ) : closedConvexHull ℝ (orbitPrefix q n) ⊆ K :=
    (closedConvexHull ℝ).monotone (prefix_subset_range q n)
  apply hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall (fun n => hsub n (hspec n).1))
  intro p hp hcl
  symm
  apply center_eq (range_nonempty q) hb hε (by rintro _ ⟨n,rfl⟩; exact hl n) hp
  intro z hz
  have hD : IsClosed {z : Form | determinant z ≤ determinant p} :=
    isClosed_le determinant_continuous continuous_const
  have hall : closure (⋃ n, closedConvexHull ℝ (orbitPrefix q n)) ⊆
      {z : Form | determinant z ≤ determinant p} := by
    apply closure_minimal _ hD
    intro y hy
    obtain ⟨m,hm⟩ := mem_iUnion.mp hy
    have hclosed : IsClosed {r : Form | determinant y ≤ determinant r} :=
      isClosed_le continuous_const determinant_continuous
    apply hclosed.mem_of_mapClusterPt hcl
    filter_upwards [eventually_ge_atTop m] with n hmn
    exact (hspec n).2 ((closedConvexHull ℝ).monotone (prefix_monotone q hmn) hm)
  rw [prefix_closure_union] at hall
  exact hall hz

open MeasureTheory

lemma measurable_finite_center {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [Nonempty ι] {ε : ℝ} (hε : 0 < ε)
    (q : ι → X → Form) (hq : ∀ i, Measurable (q i))
    (hl : ∀ i x, LowerBound ε (q i x)) :
    Measurable (fun x => center (range (fun i => q i x))) := by
  let f : X → FiniteForms ε ι := fun x => ⟨fun i => q i x,fun i => hl i x⟩
  have hf : Measurable f := (Measurable.of_eval hq).subtype_mk
  have H : Measurable (fun q : FiniteForms ε ι => center (range q.val)) :=
    (continuous_finite_center (ι:=ι) hε).measurable
  change Measurable ((fun q : FiniteForms ε ι => center (range q.val)) ∘ f)
  exact H.comp hf

theorem measurable_countable_center {X : Type*} [MeasurableSpace X]
    (q : ℕ → X → Form) (hq : ∀ n, Measurable (q n))
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ n x, LowerBound ε (q n x))
    (hb : ∀ x, Bornology.IsBounded (range (fun n => q n x))) :
    Measurable (fun x => center (range (fun n => q n x))) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x => center (orbitPrefix (fun k => q k x) n))
  · intro n
    exact measurable_finite_center hε (fun i : Fin (n+1) => q i.val)
      (fun i => hq i.val) (fun i x => hl i.val x)
  · apply tendsto_pi_nhds.mpr
    intro x
    exact prefix_center_tendsto (fun n => q n x) (hb x) hε (fun n => hl n x)

lemma upperBound_closed (K : ℝ) : IsClosed {q : Form | UpperBound K q} := by
  simp only [UpperBound,ofPred_forall]
  exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_le (evaluate_continuous x y) continuous_const))

lemma upperBound_convex (K : ℝ) : Convex ℝ {q : Form | UpperBound K q} := by
  intro p hp q hq a b ha hb hab x y
  rw [evaluate_add,evaluate_smul,evaluate_smul]
  calc
    a*evaluate p x y+b*evaluate q x y ≤ a*(K*(x^2+y^2))+b*(K*(x^2+y^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hp x y) ha)
        (mul_le_mul_of_nonneg_left (hq x y) hb)
    _ = (a+b)*(K*(x^2+y^2)) := by ring
    _ = K*(x^2+y^2) := by rw [hab,one_mul]

lemma norm_le_of_bounds {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) {q : Form}
    (hl : LowerBound ε q) (hu : UpperBound K q) : ‖q‖ ≤ K := by
  have h0l : ε ≤ q 0 := by simpa [evaluate] using hl 1 0
  have h2l : ε ≤ q 2 := by simpa [evaluate] using hl 0 1
  have h0u : q 0 ≤ K := by simpa [evaluate] using hu 1 0
  have h2u : q 2 ≤ K := by simpa [evaluate] using hu 0 1
  have hp : q 0+2*q 1+q 2 ≤ 2*K := by
    have h := hu 1 1
    norm_num [evaluate] at h
    nlinarith
  have hn : q 0-2*q 1+q 2 ≤ 2*K := by
    have h := hu 1 (-1)
    norm_num [evaluate] at h
    nlinarith
  apply (pi_norm_le_iff_of_nonneg hK).mpr
  intro i
  rw [Real.norm_eq_abs,abs_le]
  fin_cases i
  · change -K ≤ q 0 ∧ q 0 ≤ K
    constructor <;> linarith
  · change -K ≤ q 1 ∧ q 1 ≤ K
    constructor <;> linarith
  · change -K ≤ q 2 ∧ q 2 ≤ K
    constructor <;> linarith

lemma bounded_of_bounds {S : Set Form} {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hl : ∀ q ∈ S, LowerBound ε q) (hu : ∀ q ∈ S, UpperBound K q) :
    Bornology.IsBounded S := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : Form)).mpr
  refine ⟨K,?_⟩
  intro q hq
  simpa only [mem_closedBall,dist_zero_right] using norm_le_of_bounds hε hK (hl q hq) (hu q hq)

lemma center_bounds {S : Set Form} (hne : S.Nonempty)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hl : ∀ q ∈ S, LowerBound ε q) (hu : ∀ q ∈ S, UpperBound K q) :
    LowerBound ε (center S) ∧ UpperBound K (center S) := by
  have hc := center_spec hne (bounded_of_bounds hε.le hK hl hu) hε hl
  exact ⟨closedConvexHull_min hl (lowerBound_convex ε) (lowerBound_closed ε) hc.1,
    closedConvexHull_min hu (upperBound_convex K) (upperBound_closed K) hc.1⟩

lemma measurable_indexed_center {X ι : Type*} [MeasurableSpace X] [Countable ι] [Nonempty ι]
    (q : ι → X → Form) (hq : ∀ i, Measurable (q i))
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ i x, LowerBound ε (q i x))
    (hb : ∀ x, Bornology.IsBounded (range (fun i => q i x))) :
    Measurable (fun x => center (range (fun i => q i x))) := by
  obtain ⟨e,he⟩ := exists_surjective_nat ι
  have hr (x : X) : range (fun n => q (e n) x)=range (fun i => q i x) :=
    he.range_comp (fun i => q i x)
  have hm := measurable_countable_center (fun n => q (e n)) (fun n => hq (e n)) hε
    (fun n => hl (e n)) (fun x => by rw [hr]; exact hb x)
  simpa only [hr] using hm

theorem invariant_measurable_form {Γ X : Type*} [Group Γ] [Countable Γ]
    [MeasurableSpace X] (A : Γ →* Equiv.Perm X)
    (L : Γ → X → Form ≃L[ℝ] Form) (round : X → Form)
    (hdet : ∀ g x q, determinant (L g x q)=determinant q)
    (hcocycle : ∀ g h x q, L (g*h) x q=L h x (L g (A h x) q))
    (hq : ∀ g, Measurable (fun x => L g x (round (A g x))))
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hl : ∀ g x, LowerBound ε (L g x (round (A g x))))
    (hu : ∀ g x, UpperBound K (L g x (round (A g x)))) :
    ∃ q : X → Form, Measurable q ∧ (∀ x, LowerBound ε (q x) ∧ UpperBound K (q x)) ∧
      ∀ g x, L g x (q (A g x))=q x := by
  let Q : Γ → X → Form := fun g x => L g x (round (A g x))
  let S : X → Set Form := fun x => range (fun g => Q g x)
  have hlow (x : X) : ∀ p ∈ S x, LowerBound ε p := by
    rintro p ⟨g,rfl⟩
    exact hl g x
  have hupp (x : X) : ∀ p ∈ S x, UpperBound K p := by
    rintro p ⟨g,rfl⟩
    exact hu g x
  have hb (x : X) := bounded_of_bounds hε.le hK (hlow x) (hupp x)
  refine ⟨fun x => center (S x),measurable_indexed_center Q hq hε hl hb,
    fun x => center_bounds (range_nonempty _) hε hK (hlow x) (hupp x),?_⟩
  intro h x
  apply center_equivariant (L h x) (hdet h x) _ (range_nonempty _) (hb _) (range_nonempty _) (hb _)
    hε hε (hlow _) (hlow _)
  ext p
  constructor
  · rintro ⟨q,⟨g,rfl⟩,rfl⟩
    refine ⟨g*h,?_⟩
    dsimp [Q]
    rw [hcocycle]
    simp only [map_mul,Equiv.Perm.mul_apply]
  · rintro ⟨g,rfl⟩
    refine ⟨Q (g*h⁻¹) (A h x),mem_range_self _,?_⟩
    dsimp only [Q]
    rw [← hcocycle]
    simp only [inv_mul_cancel_right,map_mul,Equiv.Perm.mul_apply,map_inv,Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]

end CannonConformal

end
end
end
end
end
end
end
end

end OAI
