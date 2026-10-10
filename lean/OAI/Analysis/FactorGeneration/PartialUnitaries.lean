import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

structure PartialUnitary (M : VonNeumannAlgebra H) where
  support : AlgebraProjection M
  unitary : CornerUnitary support

namespace PartialUnitary
abbrev val (v : PartialUnitary M) := v.unitary.val

def Extends (v w : PartialUnitary M) : Prop := w.val*v.support.val=v.val

theorem support_le_of_extends {v w : PartialUnitary M} (h : Extends v w) :
    v.support ≤ w.support := by
  have hv : w.support.val*v.val=v.val := by
    calc w.support.val*v.val = w.support.val*(w.val*v.support.val) := by rw [h]
         _ = v.val := by rw [← mul_assoc,w.unitary.support_mul]; exact h
  change w.support.val*v.support.val=v.support.val
  calc w.support.val*v.support.val = w.support.val*(v.val*star v.val) := by rw [v.unitary.final]
       _ = v.support.val := by rw [← mul_assoc,hv,v.unitary.final]

theorem cross_initial {v w : PartialUnitary M} (h : Extends v w) :
    star w.val*v.val=v.support.val := by
  calc star w.val*v.val = star w.val*(w.val*v.support.val) := by rw [h]
       _ = v.support.val := by rw [← mul_assoc,w.unitary.initial]; exact support_le_of_extends h

theorem cross_initial_rev {v w : PartialUnitary M} (h : Extends v w) :
    star v.val*w.val=v.support.val := by
  simpa only [star_mul,star_star,v.support.property.isSelfAdjoint.star_eq]
    using congrArg star (cross_initial h)

theorem left_extends {v w : PartialUnitary M} (h : Extends v w) :
    v.support.val*w.val=v.val := by
  calc v.support.val*w.val = (v.val*star v.val)*w.val := by rw [v.unitary.final]
       _ = v.val := by rw [mul_assoc,cross_initial_rev h,v.unitary.mul_support]

theorem extends_refl (v : PartialUnitary M) : Extends v v := v.unitary.mul_support

theorem extends_trans {u v w : PartialUnitary M} (huv : Extends u v) (hvw : Extends v w) :
    Extends u w := by
  change w.val*u.support.val=u.val
  calc w.val*u.support.val = w.val*(v.support.val*u.support.val) := by
         rw [show v.support.val*u.support.val=u.support.val from support_le_of_extends huv]
       _ = u.val := by rw [← mul_assoc,hvw,huv]

@[ext] theorem ext {v w : PartialUnitary M} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by
    apply Subtype.ext
    calc v.support.val = star v.val*v.val := v.unitary.initial.symm
         _ = star w.val*w.val := by rw [h]
         _ = w.support.val := w.unitary.initial
  cases v with | mk p v =>
    cases w with | mk q w =>
      dsimp at hp
      subst q
      congr 1
      cases v
      cases w
      congr 1

instance : PartialOrder (PartialUnitary M) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm v w hvw hwv := by
    apply ext
    have hs := le_antisymm (support_le_of_extends hvw) (support_le_of_extends hwv)
    change w.val*v.support.val=v.val at hvw
    rw [hs,w.unitary.mul_support] at hvw
    exact hvw.symm

theorem support_mono {v w : PartialUnitary M} (h : v ≤ w) : v.support ≤ w.support :=
  support_le_of_extends h

theorem difference_square {v w : PartialUnitary M} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support.val-v.support.val := by
  simp only [star_sub,sub_mul,mul_sub,w.unitary.initial,v.unitary.initial,
    cross_initial h,cross_initial_rev h,sub_self,sub_zero]

theorem distance_sq (τ : TracialRepresentation M) {v w : PartialUnitary M} (h : v ≤ w) :
    τ.norm₂ (w.val-v.val)^2=(τ.trace w.support.val).re-(τ.trace v.support.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul (w.val-v.val))
  rw [difference_square h,trace_sub,Complex.sub_re] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

theorem support_trace_mono (τ : TracialRepresentation M) {v w : PartialUnitary M} (h : v ≤ w) :
    (τ.trace v.support.val).re ≤ (τ.trace w.support.val).re := by
  have he := distance_sq τ h
  nlinarith [sq_nonneg (τ.norm₂ (w.val-v.val))]

end PartialUnitary

end

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialUnitary

theorem support_trace_le_one (v : PartialUnitary M) : (τ.trace v.support.val).re ≤ 1 := by
  rw [projection_trace_sq τ _ v.support.property]
  have h := (τ.norm₂_le_norm v.support.val).trans v.support.property.norm_le
  nlinarith [show 0 ≤ τ.norm₂ v.support.val from norm_nonneg _]

theorem monotone_cauchy (a : ℕ → PartialUnitary M) (ha : Monotone a) :
    CauchySeq (fun n => ((a n).val : H →L[ℂ] H) τ.vector) := by
  let t : ℕ → ℝ := fun n => (τ.trace (a n).support.val).re
  have ht : Monotone t := fun i j hij => support_trace_mono τ (ha hij)
  have hb : BddAbove (Set.range t) := ⟨1,by rintro _ ⟨n,rfl⟩; exact support_trace_le_one τ (a n)⟩
  have hc := tendsto_atTop_ciSup ht hb
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc (Ioi_mem_nhds (show (⨆ n, t n)-ε^2 < ⨆ n,t n by nlinarith)))
  refine ⟨N,fun n hn => ?_⟩
  have hupper : t n ≤ ⨆ n,t n := le_ciSup hb n
  have hsmall : (⨆ n,t n)-ε^2 < t N := hN N le_rfl
  have he := distance_sq τ (ha hn)
  change τ.norm₂ ((a n).val-(a N).val)^2=t n-t N at he
  rw [dist_eq_norm]
  change τ.norm₂ ((a n).val-(a N).val)<ε
  nlinarith [show 0 ≤ τ.norm₂ ((a n).val-(a N).val) from norm_nonneg _]

/-- Closedness of actual partial unitaries in the operator norm unit ball
for L2 convergence. -/
theorem of_L2_limit (a : ℕ → PartialUnitary M) (b : M.toStarSubalgebra)
    (hb : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0)) :
    ∃ v : PartialUnitary M, v.val=b := by
  let p : M.toStarSubalgebra := star b*b
  have hp : Tendsto (fun n => τ.norm₂ ((a n).support.val-p)) atTop (𝓝 0) := by
    have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
      (star b) b 1 (fun n => (a n).unitary.adjoint.norm_le_one)
      (norm₂_limit_star τ _ _ hb) hb
    simpa only [(a _).unitary.initial] using ht
  have hfinal : b*star b=p := by
    have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun n => star (a n).val)
      b (star b) 1 (fun n => (a n).unitary.norm_le_one) hb (norm₂_limit_star τ _ _ hb)
    have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-b*star b)) atTop (𝓝 0) := by
      simpa only [(a _).unitary.final] using ht
    exact norm₂_limit_unique τ _ ht' hp
  have hproj : IsStarProjection p := by
    constructor
    · have ht := norm₂_limit_mul τ (fun n => (a n).support.val) (fun n => (a n).support.val)
        p p 1 (fun n => (a n).support.property.norm_le) hp hp
      have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-p*p)) atTop (𝓝 0) := by
        simpa only [(a _).support.property.isIdempotentElem.eq] using ht
      exact norm₂_limit_unique τ _ ht' hp
    · change star (star b*b)=star b*b
      simp only [star_mul,star_star]
  exact ⟨⟨⟨p,hproj⟩,⟨b,rfl,hfinal⟩⟩,rfl⟩

/-- A bounded L2 limit retains every eventually fixed extension. -/
theorem le_of_eventually_le_limit (a : ℕ → PartialUnitary M) (v w : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, w ≤ a n) : w ≤ v := by
  have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => w.support.val)
    v.val w.support.val 1 (fun n => (a n).unitary.norm_le_one) hv
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
  have hc : Tendsto (fun n => τ.norm₂ ((a n).val*w.support.val-w.val)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hw] with n hn
    rw [show (a n).val*w.support.val=w.val from hn,sub_self,τ.norm₂_zero]
  exact norm₂_limit_unique τ _ ht hc

theorem monotone_limit (a : ℕ → PartialUnitary M) (ha : Monotone a) :
    ∃ v : PartialUnitary M, (∀ n, a n ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  obtain ⟨ξ,hξ⟩ := cauchySeq_tendsto_of_complete (monotone_cauchy τ a ha)
  obtain ⟨b,hb,hbξ⟩ := bounded_trace_limit τ (fun n => (a n).val) 1 (by norm_num)
    (fun n => (a n).unitary.norm_le_one) ξ hξ
  have ht : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ b).mp
    simpa only [hbξ] using hξ
  obtain ⟨v,hv⟩ := of_L2_limit τ a b ht
  rw [← hv] at ht
  refine ⟨v,fun n => ?_,ht⟩
  apply le_of_eventually_le_limit τ a v (a n) ht
  exact (eventually_ge_atTop n).mono (fun m hm => ha hm)

/-! Every nonempty chain of actual partial unitaries has an upper bound which
is an L2 limit of a sequence from the chain. This is the analytic chain
construction underlying the error-constrained Zorn argument. -/

theorem eq_of_le_of_trace_eq {v w : PartialUnitary M} (h : v ≤ w)
    (ht : (τ.trace v.support.val).re=(τ.trace w.support.val).re) : v=w := by
  have he := distance_sq τ h
  rw [ht,sub_self] at he
  have hz := (τ.norm₂_eq_zero_iff _).mp (sq_eq_zero_iff.mp he)
  exact ext (sub_eq_zero.mp hz).symm

theorem support_limit (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => τ.norm₂ ((a n).support.val-v.support.val)) atTop (𝓝 0) := by
  have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
    (star v.val) v.val 1 (fun n => (a n).unitary.adjoint.norm_le_one)
    (norm₂_limit_star τ _ _ hv) hv
  simpa only [(a _).unitary.initial,v.unitary.initial] using ht

theorem support_trace_limit (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => (τ.trace (a n).support.val).re) atTop (𝓝 (τ.trace v.support.val).re) :=
  (Complex.continuous_re.tendsto _).comp (norm₂_limit_trace τ _ _ (support_limit τ a v hv))

theorem limit_le_of_le (a : ℕ → PartialUnitary M) (v w : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ n, a n ≤ w) : v ≤ w := by
  have ht := norm₂_limit_mul τ (fun _ => w.val) (fun n => (a n).support.val)
    w.val v.support.val 1 (fun _ => w.unitary.norm_le_one)
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    (support_limit τ a v hv)
  have he : (fun n => w.val*(a n).support.val)=(fun n => (a n).val) := funext hw
  simp only [show ∀ n, w.val*(a n).support.val=(a n).val from hw] at ht
  exact norm₂_limit_unique τ _ ht hv

/-- A nonempty chain has a sequential L2 upper bound; no countability of the
chain and no cyclicity of the trace vector are assumed. -/
theorem chain_limit (c : Set (PartialUnitary M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ (a : ℕ → PartialUnitary M) (v : PartialUnitary M),
      (∀ n, a n ∈ c) ∧ Monotone a ∧ (∀ w ∈ c, w ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  classical
  let t : PartialUnitary M → ℝ := fun v => (τ.trace v.support.val).re
  have hb : BddAbove (t '' c) := ⟨1,by rintro _ ⟨w,hw,rfl⟩; exact support_trace_le_one τ w⟩
  obtain ⟨r,hrmono,hrlim,hrmem⟩ := exists_seq_tendsto_sSup (hne.image t) hb
  choose a hac har using hrmem
  have htotal : ∀ u ∈ c, ∀ v ∈ c, u ≤ v ∨ v ≤ u := by
    intro u hu v hv
    by_cases he : u=v
    · exact Or.inl he.le
    · exact hc hu hv he
  have hmono : Monotone a := by
    intro i j hij
    rcases htotal (a i) (hac i) (a j) (hac j) with h | h
    · exact h
    · have he : t (a j)=t (a i) := le_antisymm (support_trace_mono τ h)
        (by rw [har,har]; exact hrmono hij)
      exact (eq_of_le_of_trace_eq τ h he).symm.le
  obtain ⟨v,hav,hlim⟩ := monotone_limit τ a hmono
  have htv : t v=sSup (t '' c) := by
    apply tendsto_nhds_unique (support_trace_limit τ a v hlim)
    change Tendsto (fun n => t (a n)) atTop (𝓝 (sSup (t '' c)))
    simpa only [har] using hrlim
  refine ⟨a,v,hac,hmono,?_,hlim⟩
  intro w hw
  by_cases hex : ∃ n, w ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (hav n)
  · have haw : ∀ n, a n ≤ w := by
      intro n
      exact (htotal (a n) (hac n) w hw).resolve_right (fun h => hex ⟨n,h⟩)
    have hvw := limit_le_of_le τ a v w hlim haw
    have htw : t w ≤ t v := by rw [htv]; exact le_csSup hb ⟨w,hw,rfl⟩
    have he : t v=t w := le_antisymm (support_trace_mono τ hvw) htw
    exact (eq_of_le_of_trace_eq τ hvw he).symm.le

end PartialUnitary

end

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/
section
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

def dyadicSign (n : ℕ) (i : DyadicIndex (n+1)) : ℂ := if i.2 then -1 else 1

def dyadicRademacher (p : AlgebraProjection M) (n : ℕ) : M.toStarSubalgebra :=
  dyadicEval τ hdiff p (n+1) (dyadicSign n)

theorem dyadicRademacher_star (p : AlgebraProjection M) (n : ℕ) :
    star (dyadicRademacher τ hdiff p n)=dyadicRademacher τ hdiff p n := by
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_star]
  congr 1
  funext i
  cases h : i.2 <;> simp [dyadicSign,h]

theorem dyadicRademacher_sq (p : AlgebraProjection M) (n : ℕ) :
    dyadicRademacher τ hdiff p n*dyadicRademacher τ hdiff p n=p.val := by
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_mul _ (dyadicProjection_orthogonal τ hdiff p (n+1))]
  have he : (fun i : DyadicIndex (n+1) => dyadicSign n i*dyadicSign n i) = fun _ => 1 := by
    funext i
    cases h : i.2 <;> simp [dyadicSign,h]
  rw [he]
  exact dyadicEval_one τ hdiff p (n+1)

def dyadicCornerUnitary (p : AlgebraProjection M) (n : ℕ) : CornerUnitary p where
  val := dyadicRademacher τ hdiff p n
  initial := by rw [dyadicRademacher_star,dyadicRademacher_sq]
  final := by rw [dyadicRademacher_star,dyadicRademacher_sq]

/-- The next sign is centered even after multiplication by an arbitrary
member of the previous finite dyadic algebra. -/
theorem dyadicRademacher_centered_over_previous (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    τ.trace (dyadicEval τ hdiff p n c*dyadicRademacher τ hdiff p n)=0 := by
  rw [← dyadicEval_refine τ hdiff p n c]
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_mul _ (dyadicProjection_orthogonal τ hdiff p (n+1))]
  rw [dyadicEval_trace]
  change (∑ i : DyadicIndex n × Bool,
    (c i.1*dyadicSign n i)*((τ.trace p.val).re/(2:ℝ)^(n+1) : ℝ))=0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fintype.sum_bool]
  simp [dyadicSign]

theorem dyadicRademacher_trace_mul_of_lt (p : AlgebraProjection M) {m n : ℕ} (hmn : m < n) :
    τ.trace (dyadicRademacher τ hdiff p m*dyadicRademacher τ hdiff p n)=0 := by
  obtain ⟨c,hc⟩ := dyadicEval_lift τ hdiff p (Nat.succ_le_iff.mpr hmn) (dyadicSign m)
  change τ.trace (dyadicEval τ hdiff p (m+1) (dyadicSign m)*_)=0
  rw [hc]
  exact dyadicRademacher_centered_over_previous τ hdiff p n c

theorem dyadicRademacher_trace_mul_of_ne (p : AlgebraProjection M) {m n : ℕ} (hmn : m ≠ n) :
    τ.trace (dyadicRademacher τ hdiff p m*dyadicRademacher τ hdiff p n)=0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact dyadicRademacher_trace_mul_of_lt τ hdiff p h
  · rw [τ.trace_mul_comm]
    exact dyadicRademacher_trace_mul_of_lt τ hdiff p h

theorem coordinate_inner_eq_trace (a b : M.toStarSubalgebra) :
    inner ℂ ((a : H →L[ℂ] H) τ.vector) ((b : H →L[ℂ] H) τ.vector)=τ.trace (star a*b) := by
  change _ = inner ℂ τ.vector (star (a : H →L[ℂ] H) ((b : H →L[ℂ] H) τ.vector))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem dyadicRademacher_norm₂ (p : AlgebraProjection M) (n : ℕ) :
    τ.norm₂ (dyadicRademacher τ hdiff p n)=τ.norm₂ p.val := by
  have he := (dyadicCornerUnitary τ hdiff p n).trace_norm_sq τ
  rw [projection_trace_sq τ p.val p.property] at he
  change τ.norm₂ (dyadicRademacher τ hdiff p n)^2=τ.norm₂ p.val^2 at he
  have h₁ : 0 ≤ τ.norm₂ (dyadicRademacher τ hdiff p n) := norm_nonneg _
  have h₂ : 0 ≤ τ.norm₂ p.val := norm_nonneg _
  nlinarith

end

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
/-- Bessel's inequality makes the coefficients of an orthonormal sequence vanish. -/
theorem orthonormal_inner_tendsto_zero (v : ℕ → H) (hv : Orthonormal ℂ v) (x : H) :
    Tendsto (fun n => inner ℂ x (v n)) atTop (𝓝 0) := by
  have ht := (hv.inner_products_summable x).tendsto_atTop_zero
  have hh : Tendsto (fun n => inner ℂ (v n) x) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have he := ht (Iio_mem_nhds (sq_pos_of_pos hε))
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    refine ⟨N,fun n hn => ?_⟩
    rw [dist_zero_right]
    have h : ‖inner ℂ (v n) x‖^2 < ε^2 := hN n hn
    nlinarith [norm_nonneg (inner ℂ (v n) x)]
  have hs := hh.star
  simp only [star_zero] at hs
  change Tendsto (fun n => (starRingEnd ℂ) (inner ℂ (v n) x)) atTop (𝓝 0) at hs
  simpa only [inner_conj_symm] using hs

variable (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem dyadicRademacher_weak_trace_zero (p : AlgebraProjection M) (hp : p.val ≠ 0) (x : H) :
    Tendsto (fun n => inner ℂ x ((dyadicRademacher τ hdiff p n : H →L[ℂ] H) τ.vector))
      atTop (𝓝 0) := by
  let s : ℝ := τ.norm₂ p.val
  have hs : 0 < s := lt_of_le_of_ne (norm_nonneg _) (fun h => hp ((τ.norm₂_eq_zero_iff p.val).mp h.symm))
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  let v : ℕ → H := fun n => (s : ℂ)⁻¹ • ((dyadicRademacher τ hdiff p n : H →L[ℂ] H) τ.vector)
  have hv : Orthonormal ℂ v := by
    constructor
    · intro n
      change ‖(s : ℂ)⁻¹ • ((dyadicRademacher τ hdiff p n : H →L[ℂ] H) τ.vector)‖=1
      rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hs.le]
      change s⁻¹*τ.norm₂ (dyadicRademacher τ hdiff p n)=1
      rw [dyadicRademacher_norm₂]
      exact inv_mul_cancel₀ hs.ne'
    · intro m n hmn
      dsimp [v]
      rw [inner_smul_left,inner_smul_right,coordinate_inner_eq_trace,
        dyadicRademacher_star,dyadicRademacher_trace_mul_of_ne τ hdiff p hmn,mul_zero,mul_zero]
  have ht := (orthonormal_inner_tendsto_zero v hv x).const_mul (s : ℂ)
  simp only [mul_zero] at ht
  apply ht.congr
  intro n
  dsimp [v]
  rw [inner_smul_right,← mul_assoc,mul_inv_cancel₀ hsC,one_mul]

theorem dyadicRademacher_mixed_trace_zero (p : AlgebraProjection M) (hp : p.val ≠ 0)
    (x y : M.toStarSubalgebra) :
    Tendsto (fun n => τ.trace (x*dyadicRademacher τ hdiff p n*y)) atTop (𝓝 0) := by
  have ht := dyadicRademacher_weak_trace_zero τ hdiff p hp
    (((star (y*x) : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
  apply ht.congr
  intro n
  rw [coordinate_inner_eq_trace,star_star,τ.trace_mul_comm (x*dyadicRademacher τ hdiff p n) y,← mul_assoc]

/-- The same sequence has vanishing ambient mixed traces, even when the
coefficients belong to M and the partial unitaries belong to P. -/
theorem inclusion_corner_mixed_trace_zero {P : VonNeumannAlgebra H} (hPM : P ≤ M)
    (hdiffP : ∀ p : P.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : P.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : AlgebraProjection P) (hp : p.val ≠ 0) (x y : M.toStarSubalgebra) :
    Tendsto (fun n => τ.trace (x*coordinateInclusion hPM
      (dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n).val*y)) atTop (𝓝 0) := by
  have ht := dyadicRademacher_weak_trace_zero (restrictedTrace τ hPM) hdiffP p hp
    (((star (y*x) : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
  apply ht.congr
  intro n
  change inner ℂ (((star (y*x) : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
    ((coordinateInclusion hPM (dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n).val : H →L[ℂ] H) τ.vector)=_
  rw [coordinate_inner_eq_trace,star_star,τ.trace_mul_comm (x*_) y,← mul_assoc]

/-- Actual simultaneous scalar nonintertwining choices in every nonzero
corner, with arbitrary finite sets of ambient left and right coefficients. -/
theorem exists_cornerUnitary_small_mixed_traces {P : VonNeumannAlgebra H} (hPM : P ≤ M)
    (hdiffP : ∀ p : P.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : P.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : AlgebraProjection P) (hp : p.val ≠ 0)
    (F G : Finset M.toStarSubalgebra) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : CornerUnitary p, ∀ x ∈ F, ∀ y ∈ G,
      ‖τ.trace (x*coordinateInclusion hPM v.val*y)‖ < ε := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ x ∈ F, ∀ y ∈ G,
      ‖τ.trace (x*coordinateInclusion hPM
        (dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n).val*y)‖ < ε := by
    rw [eventually_all_finset]
    intro x hx
    rw [eventually_all_finset]
    intro y hy
    have ht := (inclusion_corner_mixed_trace_zero τ hPM hdiffP p hp x y).norm
    simp only [norm_zero] at ht
    exact ht (Iio_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  exact ⟨dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n,hn⟩

end Generator.Tracial

end

end OAI
