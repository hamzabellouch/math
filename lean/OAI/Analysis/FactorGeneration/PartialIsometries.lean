import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

structure PartialIsometry (M : VonNeumannAlgebra H) where
  support : AlgebraProjection M
  val : M.toStarSubalgebra
  initial : star val*val=support.val

namespace PartialIsometry

theorem mul_support (v : PartialIsometry M) : v.val*v.support.val=v.val := by
  have htr : star v.val*(v.val*v.support.val)=v.support.val := by
    rw [← mul_assoc,v.initial,v.support.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*v.support.val)*(v.val-v.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,v.support.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

def target (v : PartialIsometry M) : AlgebraProjection M :=
  ⟨v.val*star v.val,⟨by
    change (v.val*star v.val)*(v.val*star v.val)=v.val*star v.val
    calc _ = (v.val*(star v.val*v.val))*star v.val := by simp only [mul_assoc]
         _ = v.val*star v.val := by rw [v.initial,v.mul_support],
    IsSelfAdjoint.mul_star_self _⟩⟩

theorem target_mul (v : PartialIsometry M) : v.target.val*v.val=v.val := by
  change (v.val*star v.val)*v.val=v.val
  rw [mul_assoc,v.initial,v.mul_support]

def adjoint (v : PartialIsometry M) : PartialIsometry M :=
  ⟨v.target,star v.val,by simp only [star_star]; rfl⟩

theorem norm_le_one (v : PartialIsometry M) : ‖v.val‖ ≤ 1 := by
  have he : ‖v.val‖*‖v.val‖=‖v.support.val‖ := by
    rw [← CStarRing.norm_star_mul_self,v.initial]
  have hp := v.support.property.norm_le
  nlinarith [norm_nonneg v.val]

theorem trace_support_eq_target (τ : TracialRepresentation M) (v : PartialIsometry M) :
    τ.trace v.support.val=τ.trace v.target.val := by
  rw [← v.initial]
  exact τ.trace_mul_comm _ _

def Extends (v w : PartialIsometry M) : Prop := w.val*v.support.val=v.val

theorem support_le_of_extends {v w : PartialIsometry M} (h : Extends v w) :
    v.support ≤ w.support := by
  have hh := congrArg (fun z : M.toStarSubalgebra => star z*z) h
  have hcomp : v.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(star w.val*w.val)*v.support.val := by rw [w.initial]
         _ = star (w.val*v.support.val)*(w.val*v.support.val) := by
           simp only [star_mul,v.support.property.isSelfAdjoint.star_eq,mul_assoc]
         _ = v.support.val := hh.trans v.initial
  have hdouble : v.support.val*w.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(w.support.val*w.support.val)*v.support.val := by
           simp only [mul_assoc]
         _ = v.support.val := by rw [w.support.property.isIdempotentElem.eq,hcomp]
  have hz : star (v.support.val-w.support.val*v.support.val)*
      (v.support.val-w.support.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,
      w.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub]
    simp only [← mul_assoc,v.support.property.isIdempotentElem.eq,hcomp,hdouble,
      sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)).symm

theorem cross_initial {v w : PartialIsometry M} (h : Extends v w) :
    star w.val*v.val=v.support.val := by
  calc star w.val*v.val = star w.val*(w.val*v.support.val) := by rw [h]
       _ = v.support.val := by rw [← mul_assoc,w.initial]; exact support_le_of_extends h

theorem cross_initial_rev {v w : PartialIsometry M} (h : Extends v w) :
    star v.val*w.val=v.support.val := by
  simpa only [star_mul,star_star,v.support.property.isSelfAdjoint.star_eq]
    using congrArg star (cross_initial h)

theorem extends_refl (v : PartialIsometry M) : Extends v v := v.mul_support

theorem extends_trans {u v w : PartialIsometry M} (huv : Extends u v) (hvw : Extends v w) :
    Extends u w := by
  change w.val*u.support.val=u.val
  calc w.val*u.support.val = w.val*(v.support.val*u.support.val) := by
         rw [show v.support.val*u.support.val=u.support.val from support_le_of_extends huv]
       _ = u.val := by rw [← mul_assoc,hvw,huv]

@[ext] theorem ext {v w : PartialIsometry M} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by
    apply Subtype.ext
    calc v.support.val = star v.val*v.val := v.initial.symm
         _ = star w.val*w.val := by rw [h]
         _ = w.support.val := w.initial
  cases v
  cases w
  cases hp
  cases h
  rfl

instance : PartialOrder (PartialIsometry M) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm v w hvw hwv := by
    apply ext
    have hs := le_antisymm (support_le_of_extends hvw) (support_le_of_extends hwv)
    change w.val*v.support.val=v.val at hvw
    rw [hs,w.mul_support] at hvw
    exact hvw.symm

theorem support_mono {v w : PartialIsometry M} (h : v ≤ w) : v.support ≤ w.support :=
  support_le_of_extends h

theorem difference_square {v w : PartialIsometry M} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support.val-v.support.val := by
  simp only [star_sub,sub_mul,mul_sub,w.initial,v.initial,
    cross_initial h,cross_initial_rev h,sub_self,sub_zero]

theorem distance_sq (τ : TracialRepresentation M) {v w : PartialIsometry M} (h : v ≤ w) :
    τ.norm₂ (w.val-v.val)^2=(τ.trace w.support.val).re-(τ.trace v.support.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul (w.val-v.val))
  rw [difference_square h,trace_sub,Complex.sub_re] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

theorem support_trace_mono (τ : TracialRepresentation M) {v w : PartialIsometry M} (h : v ≤ w) :
    (τ.trace v.support.val).re ≤ (τ.trace w.support.val).re := by
  have he := distance_sq τ h
  nlinarith [sq_nonneg (τ.norm₂ (w.val-v.val))]

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialIsometry

theorem support_trace_le_one (v : PartialIsometry M) : (τ.trace v.support.val).re ≤ 1 := by
  rw [projection_trace_sq τ _ v.support.property]
  have h := (τ.norm₂_le_norm v.support.val).trans v.support.property.norm_le
  nlinarith [show 0 ≤ τ.norm₂ v.support.val from norm_nonneg _]

theorem monotone_cauchy (a : ℕ → PartialIsometry M) (ha : Monotone a) :
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

/-- Closedness of actual partial isometries in the operator norm unit ball
for L2 convergence. -/
theorem of_L2_limit (a : ℕ → PartialIsometry M) (b : M.toStarSubalgebra)
    (hb : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0)) :
    ∃ v : PartialIsometry M, v.val=b := by
  let p : M.toStarSubalgebra := star b*b
  have hp : Tendsto (fun n => τ.norm₂ ((a n).support.val-p)) atTop (𝓝 0) := by
    have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
      (star b) b 1 (fun n => (a n).adjoint.norm_le_one)
      (norm₂_limit_star τ _ _ hb) hb
    simpa only [(a _).initial] using ht
  have hproj : IsStarProjection p := by
    constructor
    · have ht := norm₂_limit_mul τ (fun n => (a n).support.val) (fun n => (a n).support.val)
        p p 1 (fun n => (a n).support.property.norm_le) hp hp
      have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-p*p)) atTop (𝓝 0) := by
        simpa only [(a _).support.property.isIdempotentElem.eq] using ht
      exact norm₂_limit_unique τ _ ht' hp
    · change star (star b*b)=star b*b
      simp only [star_mul,star_star]
  exact ⟨⟨⟨p,hproj⟩,b,rfl⟩,rfl⟩

/-- A bounded L2 limit retains every eventually fixed extension. -/
theorem le_of_eventually_le_limit (a : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, w ≤ a n) : w ≤ v := by
  have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => w.support.val)
    v.val w.support.val 1 (fun n => (a n).norm_le_one) hv
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
  have hc : Tendsto (fun n => τ.norm₂ ((a n).val*w.support.val-w.val)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hw] with n hn
    rw [show (a n).val*w.support.val=w.val from hn,sub_self,τ.norm₂_zero]
  exact norm₂_limit_unique τ _ ht hc

theorem monotone_limit (a : ℕ → PartialIsometry M) (ha : Monotone a) :
    ∃ v : PartialIsometry M, (∀ n, a n ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  obtain ⟨ξ,hξ⟩ := cauchySeq_tendsto_of_complete (monotone_cauchy τ a ha)
  obtain ⟨b,hb,hbξ⟩ := bounded_trace_limit τ (fun n => (a n).val) 1 (by norm_num)
    (fun n => (a n).norm_le_one) ξ hξ
  have ht : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ b).mp
    simpa only [hbξ] using hξ
  obtain ⟨v,hv⟩ := of_L2_limit τ a b ht
  rw [← hv] at ht
  refine ⟨v,fun n => ?_,ht⟩
  apply le_of_eventually_le_limit τ a v (a n) ht
  exact (eventually_ge_atTop n).mono (fun m hm => ha hm)

/-! Every nonempty chain of actual partial isometries has an upper bound which
is an L2 limit of a sequence from the chain. This is the analytic chain
construction underlying the projection-comparison Zorn argument. -/

theorem eq_of_le_of_trace_eq {v w : PartialIsometry M} (h : v ≤ w)
    (ht : (τ.trace v.support.val).re=(τ.trace w.support.val).re) : v=w := by
  have he := distance_sq τ h
  rw [ht,sub_self] at he
  have hz := (τ.norm₂_eq_zero_iff _).mp (sq_eq_zero_iff.mp he)
  exact ext (sub_eq_zero.mp hz).symm

theorem support_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => τ.norm₂ ((a n).support.val-v.support.val)) atTop (𝓝 0) := by
  have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
    (star v.val) v.val 1 (fun n => (a n).adjoint.norm_le_one)
    (norm₂_limit_star τ _ _ hv) hv
  simpa only [(a _).initial,v.initial] using ht

theorem support_trace_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => (τ.trace (a n).support.val).re) atTop (𝓝 (τ.trace v.support.val).re) :=
  (Complex.continuous_re.tendsto _).comp (norm₂_limit_trace τ _ _ (support_limit τ a v hv))

theorem limit_le_of_le (a : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ n, a n ≤ w) : v ≤ w := by
  have ht := norm₂_limit_mul τ (fun _ => w.val) (fun n => (a n).support.val)
    w.val v.support.val 1 (fun _ => w.norm_le_one)
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    (support_limit τ a v hv)
  have he : (fun n => w.val*(a n).support.val)=(fun n => (a n).val) := funext hw
  simp only [show ∀ n, w.val*(a n).support.val=(a n).val from hw] at ht
  exact norm₂_limit_unique τ _ ht hv

/-- A nonempty chain has a sequential L2 upper bound; no countability of the
chain and no cyclicity of the trace vector are assumed. -/
theorem chain_limit (c : Set (PartialIsometry M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ (a : ℕ → PartialIsometry M) (v : PartialIsometry M),
      (∀ n, a n ∈ c) ∧ Monotone a ∧ (∀ w ∈ c, w ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  classical
  let t : PartialIsometry M → ℝ := fun v => (τ.trace v.support.val).re
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

end PartialIsometry

end

/-! Orthogonal patching with distinct source and target supports. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

def zero : PartialIsometry M := ⟨⟨0,IsStarProjection.zero _⟩,0,by simp⟩

theorem support_le_iff_mul (v : PartialIsometry M) (p : AlgebraProjection M) :
    v.support ≤ p ↔ v.val*p.val=v.val := by
  constructor
  · intro h
    calc _ = (v.val*v.support.val)*p.val := by rw [v.mul_support]
         _ = v.val := by rw [mul_assoc,projection_mul_of_le h,v.mul_support]
  · intro h
    have he : v.support.val*p.val=v.support.val := by
      rw [← v.initial,mul_assoc,h]
    change p.val*v.support.val=v.support.val
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      v.support.property.isSelfAdjoint.star_eq] using congrArg star he

theorem target_le_iff_mul (v : PartialIsometry M) (q : AlgebraProjection M) :
    v.target ≤ q ↔ q.val*v.val=v.val := by
  constructor
  · intro h
    calc _ = q.val*(v.target.val*v.val) := by rw [v.target_mul]
         _ = v.val := by rw [← mul_assoc,h,v.target_mul]
  · intro h
    change q.val*(v.val*star v.val)=v.val*star v.val
    rw [← mul_assoc,h]

theorem mul_eq_zero (v w : PartialIsometry M) (h : v.support.val*w.target.val=0) :
    v.val*w.val=0 := by
  calc _ = (v.val*v.support.val)*(w.target.val*w.val) := by
         rw [v.mul_support,w.target_mul]
       _ = v.val*(v.support.val*w.target.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

theorem orthogonal_reverse (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q.val*p.val=0 := by
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    PartialIsometry M where
  support := ⟨v.support.val+w.support.val,v.support.property.add w.support.property hp⟩
  val := v.val+w.val
  initial := by
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hq
    have h₂ : star w.val*v.val=0 :=
      w.adjoint.mul_eq_zero v (orthogonal_reverse _ _ hq)
    simp only [star_add,add_mul,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]

theorem patch_target (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    (patch v w hp hq).target.val=v.target.val+w.target.val := by
  have hwt : w.adjoint.target=w.support := Subtype.ext (by
    change star w.val*star (star w.val)=w.support.val
    rw [star_star,w.initial])
  have hvt : v.adjoint.target=v.support := Subtype.ext (by
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial])
  have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint (by rw [hwt]; exact hp)
  have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint (by
    rw [hvt]; exact orthogonal_reverse _ _ hp)
  change (v.val+w.val)*star (v.val+w.val)=v.val*star v.val+w.val*star w.val
  simp only [star_add,add_mul,mul_add,h₁,h₂,add_zero,zero_add]

theorem le_patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    v ≤ patch v w hp hq := by
  have hw : w.val*v.support.val=0 := by
    calc _ = (w.val*w.support.val)*v.support.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,orthogonal_reverse _ _ hp,mul_zero]
  change (v.val+w.val)*v.support.val=v.val
  rw [add_mul,v.mul_support,hw,add_zero]

theorem patch_ne (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0)
    (hw : w.support.val≠0) : patch v w hp hq ≠ v := by
  intro he
  have hh := congrArg (fun z : PartialIsometry M => z.support.val) he
  change v.support.val+w.support.val=v.support.val at hh
  exact hw (add_left_cancel (hh.trans (add_zero _).symm))

end PartialIsometry

end

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialIsometry

theorem supports_of_L2_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (p q : AlgebraProjection M)
    (hp : ∀ n, (a n).support ≤ p) (hq : ∀ n, (a n).target ≤ q) :
    v.support ≤ p ∧ v.target ≤ q := by
  constructor
  · apply (v.support_le_iff_mul p).mpr
    have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => p.val)
      v.val p.val 1 (fun n => (a n).norm_le_one) hv
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    have he : ∀ n, (a n).val*p.val=(a n).val := fun n =>
      ((a n).support_le_iff_mul p).mp (hp n)
    simp only [he] at ht
    exact norm₂_limit_unique τ _ ht hv
  · apply (v.target_le_iff_mul q).mpr
    have ht := norm₂_limit_mul τ (fun _ => q.val) (fun n => (a n).val)
      q.val v.val 1 (fun _ => q.property.norm_le)
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds) hv
    have he : ∀ n, q.val*(a n).val=(a n).val := fun n =>
      ((a n).target_le_iff_mul q).mp (hq n)
    simp only [he] at ht
    exact norm₂_limit_unique τ _ ht hv

include τ in
theorem exists_maximal_between (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ q → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) := {v | v.support ≤ p ∧ v.target ≤ q}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨a,v,ha,_,hcv,hlim⟩ := chain_limit τ c hchain hne
      exact ⟨v,supports_of_L2_limit τ a v hlim p q
        (fun n => (hc (ha n)).1) (fun n => (hc (ha n)).2),hcv⟩
    · refine ⟨zero,⟨?_,?_⟩,?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul q).mpr
        exact mul_zero _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2,fun w hp hq h => hv.2 ⟨hp,hq⟩ h⟩

end PartialIsometry

end Generator.Tracial

end

end OAI
