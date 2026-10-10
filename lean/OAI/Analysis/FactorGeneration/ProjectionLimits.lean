import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Zorn
import OAI.Analysis.FactorGeneration.TraceTopology

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem projection_trace_sq (p : M.toStarSubalgebra) (hp : IsStarProjection p) :
    (τ.trace p).re = τ.norm₂ p ^ 2 := by
  have h := congrArg Complex.re (τ.trace_star_mul p)
  simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem projection_trace_pos (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) :
    0 < (τ.trace p).re := by
  rw [projection_trace_sq τ p hp]
  exact sq_pos_of_ne_zero (fun h => hne ((τ.norm₂_eq_zero_iff p).mp h))

theorem exists_half_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ p*q = q ∧ q*p = q ∧
      (τ.trace q).re ≤ (τ.trace p).re/2 := by
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hdiff p hp hne
  by_cases hsmall : (τ.trace q).re ≤ (τ.trace p).re/2
  · exact ⟨q,hq,hq0,hpq,hqp',hsmall⟩
  · refine ⟨p-q, ?_, sub_ne_zero.mpr hqp.symm, ?_, ?_, ?_⟩
    · exact hq.sub_of_mul_eq_right hp hpq
    · rw [mul_sub, hp.isIdempotentElem.eq, hpq]
    · rw [sub_mul, hp.isIdempotentElem.eq, hqp']
    · have ht : τ.trace (p-q) = τ.trace p-τ.trace q := inner_sub_right _ _ _
      rw [ht, Complex.sub_re]
      linarith

theorem exists_geometric_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) (n : ℕ) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ p*q = q ∧ q*p = q ∧
      (τ.trace q).re ≤ (1/2 : ℝ)^n * (τ.trace p).re := by
  induction n with
  | zero => exact ⟨p,hp,hne,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq,by simp⟩
  | succ n ih =>
    obtain ⟨q,hq,hq0,hpq,hqp,htq⟩ := ih
    obtain ⟨r,hr,hr0,hqr,hrq,htr⟩ := exists_half_trace_subprojection τ hdiff q hq hq0
    refine ⟨r,hr,hr0,?_,?_,?_⟩
    · calc p*r = p*(q*r) := by rw [hqr]
           _ = (p*q)*r := (mul_assoc _ _ _).symm
           _ = r := by rw [hpq,hqr]
    · calc r*p = (r*q)*p := by rw [hrq]
           _ = r*(q*p) := mul_assoc _ _ _
           _ = r := by rw [hqp,hrq]
    · rw [pow_succ]
      nlinarith

theorem exists_small_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ p*q = q ∧ q*p = q ∧
      0 < (τ.trace q).re ∧ (τ.trace q).re < ε := by
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n * (τ.trace p).re) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_const (τ.trace p).re
  have he : ∀ᶠ n : ℕ in atTop, (1/2 : ℝ)^n * (τ.trace p).re < ε := ht (Iio_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  obtain ⟨q,hq,hq0,hpq,hqp,hbound⟩ := exists_geometric_trace_subprojection τ hdiff p hp hne n
  exact ⟨q,hq,hq0,hpq,hqp,projection_trace_pos τ q hq hq0,hbound.trans_lt hn⟩

end

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Projections with their algebraic range-inclusion order. -/
def AlgebraProjection (M : VonNeumannAlgebra H) :=
  {p : M.toStarSubalgebra // IsStarProjection p}

instance algebraProjectionPartialOrder : PartialOrder (AlgebraProjection M) where
  le p q := q.val * p.val = p.val
  le_refl p := p.property.isIdempotentElem.eq
  le_trans a b c hab hbc := by
    calc c.val * a.val = c.val * (b.val * a.val) := by rw [hab]
         _ = (c.val * b.val) * a.val := (mul_assoc _ _ _).symm
         _ = a.val := by rw [hbc, hab]
  le_antisymm a b hab hba := by
    apply Subtype.ext
    have h := congrArg star hab
    simp only [star_mul, a.property.isSelfAdjoint.star_eq,
      b.property.isSelfAdjoint.star_eq] at h
    exact h.symm.trans hba

theorem projection_mul_of_le {p q : AlgebraProjection M} (h : p ≤ q) :
    p.val * q.val = p.val := by
  have he := congrArg star h
  simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq] using he

/-- A bounded increasing net of actual projections has a projection upper bound
with the same trace bound. No projection-lattice completeness is assumed. -/
theorem monotone_projection_upper_bound (τ : TracialRepresentation M)
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a) (r : ℝ)
    (hr : ∀ i, (τ.trace (a i).val).re ≤ r) :
    ∃ b : AlgebraProjection M, (∀ i, a i ≤ b) ∧ (τ.trace b.val).re ≤ r ∧
      ∀ p : AlgebraProjection M, (∀ i, a i ≤ p) → b ≤ p := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, hT, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => ((a i).val : H →L[ℂ] H)) 1 (by norm_num)
    (fun i => (a i).property.norm_le)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb (x y : H) : Tendsto (fun i => inner ℂ y (((a i).val : H →L[ℂ] H) x))
    (ω : Filter ι) (𝓝 (inner ℂ y ((b : H →L[ℂ] H) x))) := ht x y
  have hadj (i : ι) (x y : H) :
      inner ℂ x (((a i).val : H →L[ℂ] H) y) =
      inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
    have hs : star (((a i).val : H →L[ℂ] H)) = ((a i).val : H →L[ℂ] H) :=
      congrArg Subtype.val (a i).property.isSelfAdjoint.star_eq
    calc inner ℂ x (((a i).val : H →L[ℂ] H) y) =
          inner ℂ x (star (((a i).val : H →L[ℂ] H)) y) := by rw [hs]
         _ = inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
           rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hself : star b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hh := (hb y x).star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ x (((a i).val : H →L[ℂ] H) y)))
      (ω : Filter ι) (𝓝 ((starRingEnd ℂ) (inner ℂ x ((b : H →L[ℂ] H) y)))) at hh
    simp only [inner_conj_symm] at hh
    have eq := tendsto_nhds_unique (hb x y) (hh.congr (fun i => (hadj i y x).symm))
    change inner ℂ y (star (b : H →L[ℂ] H) x) = inner ℂ y ((b : H →L[ℂ] H) x)
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact eq.symm
  have hba (i : ι) : b * (a i).val = (a i).val := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb (((a i).val : H →L[ℂ] H) x) y)
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (ha hj)).symm
  have hab (i : ι) : (a i).val * b = (a i).val := by
    have h := congrArg star (hba i)
    simpa only [star_mul, hself, (a i).property.isSelfAdjoint.star_eq] using h
  have hid : b * b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb ((b : H →L[ℂ] H) x) y)
    exact (hb x y).congr (fun i =>
      (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (hab i)).symm)
  refine ⟨⟨b, ⟨hid, hself⟩⟩, hba, ?_, ?_⟩
  · exact le_of_tendsto ((Complex.continuous_re.tendsto _).comp (hb τ.vector τ.vector))
      (Eventually.of_forall hr)
  · intro p hp
    change p.val * b = b
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hh := hb x (star (p.val : H →L[ℂ] H) y)
    simp only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hh
    exact tendsto_nhds_unique hh ((hb x y).congr (fun i =>
      (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (hp i)).symm))

end

/-! Exact trace cuts in a diffuse coordinate algebra. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_maximal_trace_subprojection (p : AlgebraProjection M)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ (τ.trace q.val).re ≤ r ∧
      ∀ s : AlgebraProjection M, s ≤ p → (τ.trace s.val).re ≤ r → q ≤ s → s ≤ q := by
  let S : Set (AlgebraProjection M) := {q | q ≤ p ∧ (τ.trace q.val).re ≤ r}
  obtain ⟨q,hq⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · let : Nonempty c := hne.to_subtype
      let : IsDirected c (· ≤ ·) := ⟨by
        intro x y
        obtain ⟨z,hz,hxz,hyz⟩ := hchain.directedOn x.val x.property y.val y.property
        exact ⟨⟨z,hz⟩,hxz,hyz⟩⟩
      obtain ⟨b,hb,hbr,hmin⟩ := monotone_projection_upper_bound τ
        (fun x : c => x.val) (fun _ _ h => h) r (fun x => (hc x.property).2)
      exact ⟨b, ⟨hmin p (fun x => (hc x.property).1),hbr⟩,
        fun z hz => hb ⟨z,hz⟩⟩
    · refine ⟨⟨0,IsStarProjection.zero _⟩, ⟨?_,?_⟩, ?_⟩
      · change p.val * 0 = 0
        exact mul_zero _
      · simpa [TracialRepresentation.trace] using hr
      · intro z hz
        exact (hne ⟨z,hz⟩).elim)
  exact ⟨q,hq.1.1,hq.1.2,fun s hsp hsr hqs => hq.2 ⟨hsp,hsr⟩ hqs⟩

/-- Every projection can be cut to any smaller prescribed real trace. -/
theorem exists_exact_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (r : ℝ) (hr : 0 ≤ r) (hrp : r ≤ (τ.trace p).re) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ p*q = q ∧ q*p = q ∧
      τ.trace q = (r : ℂ) := by
  obtain ⟨q,hqp,hqr,hmax⟩ := exists_maximal_trace_subprojection τ ⟨p,hp⟩ r hr
  have hpq : p*q.val = q.val := hqp
  have hqp' : q.val*p = q.val := projection_mul_of_le hqp
  have htrace : (τ.trace q.val).re = r := by
    by_contra hne
    have hlt : (τ.trace q.val).re < r := lt_of_le_of_ne hqr hne
    have hres : IsStarProjection (p-q.val) := q.property.sub_of_mul_eq_right hp hpq
    have hres0 : p-q.val ≠ 0 := by
      intro he
      have he' : p=q.val := sub_eq_zero.mp he
      rw [he'] at hrp
      exact (not_lt_of_ge hrp) hlt
    obtain ⟨s,hs,hs0,hps,hsp,hst,hsmall⟩ := exists_small_trace_subprojection τ hdiff
      (p-q.val) hres hres0 (r-(τ.trace q.val).re) (sub_pos.mpr hlt)
    have hqs : q.val*s = 0 := by
      calc q.val*s = q.val*((p-q.val)*s) := by rw [hps]
           _ = (q.val*(p-q.val))*s := (mul_assoc _ _ _).symm
           _ = 0 := by rw [mul_sub,hqp',q.property.isIdempotentElem.eq,sub_self,zero_mul]
    have hsq : s*q.val = 0 := by
      simpa only [star_mul,hs.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hqs
    have hps' : p*s=s := by
      have he : p*(p-q.val)=p-q.val := by rw [mul_sub,hp.isIdempotentElem.eq,hpq]
      calc p*s = p*((p-q.val)*s) := by rw [hps]
           _ = (p*(p-q.val))*s := (mul_assoc _ _ _).symm
           _ = s := by rw [he,hps]
    let t : AlgebraProjection M := ⟨q.val+s,q.property.add hs hqs⟩
    have htp : t ≤ ⟨p,hp⟩ := by
      change p*(q.val+s)=q.val+s
      rw [mul_add,hpq,hps']
    have hqt : q ≤ t := by
      change (q.val+s)*q.val=q.val
      rw [add_mul,q.property.isIdempotentElem.eq,hsq,add_zero]
    have htt : (τ.trace t.val).re ≤ r := by
      change (τ.trace (q.val+s)).re ≤ r
      have he : τ.trace (q.val+s)=τ.trace q.val+τ.trace s := inner_add_right _ _ _
      rw [he,Complex.add_re]
      linarith
    have heq : t=q := le_antisymm (hmax t htp htt hqt) hqt
    have he : q.val+s=q.val := congrArg Subtype.val heq
    have : s=0 := add_left_cancel (he.trans (add_zero q.val).symm)
    exact hs0 this
  refine ⟨q.val,q.property,hpq,hqp',?_⟩
  have he := τ.trace_star_mul q.val
  rw [q.property.isSelfAdjoint.star_eq,q.property.isIdempotentElem.eq] at he
  rw [he,← Complex.ofReal_pow]
  congr 1
  rw [← projection_trace_sq τ q.val q.property,htrace]

end

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- An actual operator with identical initial and final support p. -/
structure CornerUnitary (p : AlgebraProjection M) where
  val : M.toStarSubalgebra
  initial : star val * val = p.val
  final : val * star val = p.val

namespace CornerUnitary
variable {p q : AlgebraProjection M}

theorem mul_support (v : CornerUnitary p) : v.val*p.val=v.val := by
  have htr : star v.val*(v.val*p.val)=p.val := by
    rw [← mul_assoc,v.initial,p.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*p.val)*(v.val-v.val*p.val)=0 := by
    simp only [star_sub,star_mul,p.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,p.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

theorem support_mul (v : CornerUnitary p) : p.val*v.val=v.val := by
  calc p.val*v.val = (v.val*star v.val)*v.val := by rw [v.final]
       _ = v.val*(star v.val*v.val) := mul_assoc _ _ _
       _ = v.val := by rw [v.initial,v.mul_support]

def adjoint (v : CornerUnitary p) : CornerUnitary p :=
  ⟨star v.val,by simpa only [star_star] using v.final,
    by simpa only [star_star] using v.initial⟩

theorem mul_eq_zero (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    v.val*w.val=0 := by
  calc v.val*w.val = (v.val*p.val)*(q.val*w.val) := by rw [v.mul_support,w.support_mul]
       _ = v.val*(p.val*q.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

def patch (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    CornerUnitary ⟨p.val+q.val,p.property.add q.property hpq⟩ where
  val := v.val+w.val
  initial := by
    have hqp : q.val*p.val=0 := by
      simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hpq
    have h₂ : star w.val*v.val=0 := w.adjoint.mul_eq_zero v hqp
    change star (v.val+w.val)*(v.val+w.val)=p.val+q.val
    rw [star_add,add_mul,mul_add,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]
  final := by
    have hqp : q.val*p.val=0 := by
      simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint hpq
    have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint hqp
    change (v.val+w.val)*star (v.val+w.val)=p.val+q.val
    rw [star_add,add_mul,mul_add,mul_add,v.final,w.final,h₁,h₂,add_zero,zero_add]

theorem patch_extends (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    (patch v w hpq).val*(star v.val*v.val)=v.val := by
  have hqp : q.val*p.val=0 := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
      using congrArg star hpq
  change (v.val+w.val)*(star v.val*v.val)=v.val
  rw [v.initial,add_mul,v.mul_support]
  have he : w.val*p.val=0 := by
    calc w.val*p.val=(w.val*q.val)*p.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,hqp,mul_zero]
  rw [he,add_zero]

theorem norm_sq (v : CornerUnitary p) : ‖v.val‖*‖v.val‖=‖p.val‖ := by
  rw [← CStarRing.norm_star_mul_self,v.initial]

theorem norm_le_one (v : CornerUnitary p) : ‖v.val‖ ≤ 1 := by
  have he := v.norm_sq
  have hp := p.property.norm_le
  nlinarith [norm_nonneg v.val]

theorem trace_norm_sq (τ : TracialRepresentation M) (v : CornerUnitary p) :
    τ.norm₂ v.val ^ 2 = (τ.trace p.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul v.val)
  rw [v.initial] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

theorem patch_trace_increases (τ : TracialRepresentation M)
    (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) (hq : q.val ≠ 0) :
    (τ.trace (star v.val*v.val)).re <
      (τ.trace (star (patch v w hpq).val*(patch v w hpq).val)).re := by
  rw [v.initial,(patch v w hpq).initial]
  have he : τ.trace (p.val+q.val)=τ.trace p.val+τ.trace q.val := inner_add_right _ _ _
  rw [he,Complex.add_re]
  exact lt_add_of_pos_right _ (projection_trace_pos τ q.val q.property hq)

end CornerUnitary

end

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- At depth n there are 2^n indices; a successor appends a binary branch. -/
def DyadicIndex : ℕ → Type
  | 0 => Unit
  | n+1 => DyadicIndex n × Bool

instance dyadicIndexFintype : (n : ℕ) → Fintype (DyadicIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd _ _ (dyadicIndexFintype n) inferInstance

instance dyadicIndexDecidableEq (n : ℕ) : DecidableEq (DyadicIndex n) := Classical.decEq _

theorem card_dyadicIndex (n : ℕ) : Fintype.card (DyadicIndex n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => change Fintype.card (DyadicIndex n × Bool) = _; simp [ih,pow_succ]

variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

include hdiff in
theorem exists_half_trace_cut (p : AlgebraProjection M) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ τ.trace q.val = ((τ.trace p.val).re/2 : ℝ) := by
  have ht : 0 ≤ (τ.trace p.val).re := by
    rw [projection_trace_sq τ p.val p.property]
    positivity
  obtain ⟨q,hq,hpq,hqp,htr⟩ := exists_exact_trace_subprojection τ hdiff p.val p.property
    ((τ.trace p.val).re/2) (by positivity) (by linarith)
  exact ⟨⟨q,hq⟩,hpq,htr⟩

def halfTraceCut (p : AlgebraProjection M) : AlgebraProjection M :=
  (exists_half_trace_cut τ hdiff p).choose

theorem halfTraceCut_le (p : AlgebraProjection M) : halfTraceCut τ hdiff p ≤ p :=
  (exists_half_trace_cut τ hdiff p).choose_spec.1

theorem halfTraceCut_trace (p : AlgebraProjection M) :
    τ.trace (halfTraceCut τ hdiff p).val = ((τ.trace p.val).re/2 : ℝ) :=
  (exists_half_trace_cut τ hdiff p).choose_spec.2

/-- Both halves belong to the original algebra. -/
def splitProjection (p : AlgebraProjection M) (b : Bool) : AlgebraProjection M :=
  if b then ⟨p.val-(halfTraceCut τ hdiff p).val,
    (halfTraceCut τ hdiff p).property.sub_of_mul_eq_right p.property (halfTraceCut_le τ hdiff p)⟩
  else halfTraceCut τ hdiff p

theorem splitProjection_le (p : AlgebraProjection M) (b : Bool) :
    splitProjection τ hdiff p b ≤ p := by
  cases b
  · exact halfTraceCut_le τ hdiff p
  · change p.val*(p.val-(halfTraceCut τ hdiff p).val)=p.val-(halfTraceCut τ hdiff p).val
    rw [mul_sub,p.property.isIdempotentElem.eq,halfTraceCut_le τ hdiff p]

theorem splitProjection_sum (p : AlgebraProjection M) :
    (splitProjection τ hdiff p false).val+(splitProjection τ hdiff p true).val=p.val := by
  simp [splitProjection]

theorem splitProjection_orthogonal (p : AlgebraProjection M) :
    (splitProjection τ hdiff p false).val*(splitProjection τ hdiff p true).val=0 := by
  change (halfTraceCut τ hdiff p).val*(p.val-(halfTraceCut τ hdiff p).val)=0
  rw [mul_sub,projection_mul_of_le (halfTraceCut_le τ hdiff p),
    (halfTraceCut τ hdiff p).property.isIdempotentElem.eq,sub_self]

theorem splitProjection_trace (p : AlgebraProjection M) (b : Bool) :
    τ.trace (splitProjection τ hdiff p b).val = ((τ.trace p.val).re/2 : ℝ) := by
  cases b
  · exact halfTraceCut_trace τ hdiff p
  · change τ.trace (p.val-(halfTraceCut τ hdiff p).val)=_
    have he : τ.trace (p.val-(halfTraceCut τ hdiff p).val)=
        τ.trace p.val-τ.trace (halfTraceCut τ hdiff p).val := inner_sub_right _ _ _
    have hreal : τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
      have h := τ.trace_star_mul p.val
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
      rw [h,← Complex.ofReal_pow,Complex.ofReal_re]
    rw [he,halfTraceCut_trace,hreal]
    simp only [Complex.ofReal_re]
    push_cast
    ring

def dyadicProjection (p : AlgebraProjection M) : (n : ℕ) → DyadicIndex n → AlgebraProjection M
  | 0, _ => p
  | n+1, i => splitProjection τ hdiff (dyadicProjection p n i.1) i.2

theorem dyadicProjection_le_parent (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex (n+1)) :
    dyadicProjection τ hdiff p (n+1) i ≤ dyadicProjection τ hdiff p n i.1 :=
  splitProjection_le τ hdiff _ _

theorem dyadicProjection_trace (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex n) :
    (τ.trace (dyadicProjection τ hdiff p n i).val).re = (τ.trace p.val).re/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicProjection]
  | succ n ih =>
    change (τ.trace (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val).re = _
    rw [splitProjection_trace,Complex.ofReal_re,ih,pow_succ]
    ring

theorem dyadicProjection_sum (p : AlgebraProjection M) (n : ℕ) :
    ∑ i : DyadicIndex n, (dyadicProjection τ hdiff p n i).val = p.val := by
  induction n with
  | zero => change (∑ _ : Unit, p.val)=p.val; simp
  | succ n ih =>
    change (∑ i : DyadicIndex n × Bool,
      (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val)=p.val
    rw [Fintype.sum_prod_type]
    simpa only [Fintype.sum_bool,add_comm,splitProjection_sum] using ih

theorem orthogonal_subprojections {p q a b : AlgebraProjection M}
    (hpq : p.val*q.val=0) (ha : a ≤ p) (hb : b ≤ q) : a.val*b.val=0 := by
  calc a.val*b.val = (a.val*p.val)*(q.val*b.val) := by rw [projection_mul_of_le ha,hb]
       _ = a.val*(p.val*q.val)*b.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

theorem dyadicProjection_orthogonal (p : AlgebraProjection M) (n : ℕ)
    (i j : DyadicIndex n) (hij : i ≠ j) :
    (dyadicProjection τ hdiff p n i).val*(dyadicProjection τ hdiff p n j).val=0 := by
  induction n with
  | zero => exact (hij (@Subsingleton.elim Unit _ i j)).elim
  | succ n ih =>
    by_cases he : i.1=j.1
    · obtain ⟨i,b⟩ := i
      obtain ⟨j,c⟩ := j
      dsimp at he
      subst j
      cases b <;> cases c
      · exact (hij rfl).elim
      · exact splitProjection_orthogonal τ hdiff _
      · have h := congrArg star (splitProjection_orthogonal τ hdiff (dyadicProjection τ hdiff p n i))
        simpa only [dyadicProjection,star_mul,star_zero,(splitProjection τ hdiff _ false).property.isSelfAdjoint.star_eq,
          (splitProjection τ hdiff _ true).property.isSelfAdjoint.star_eq] using h
      · exact (hij rfl).elim
    · exact orthogonal_subprojections (ih i.1 j.1 he)
        (dyadicProjection_le_parent τ hdiff p n i) (dyadicProjection_le_parent τ hdiff p n j)

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def coordinateTraceLinear (τ : TracialRepresentation M) : M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun := τ.trace
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

theorem projection_trace_real (τ : TracialRepresentation M) (p : AlgebraProjection M) :
    τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
  have h := τ.trace_star_mul p.val
  rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
  rw [h,← Complex.ofReal_pow,Complex.ofReal_re]

variable {ι : Type*} [Fintype ι]

def projectionSum (a : ι → AlgebraProjection M) (c : ι → ℂ) : M.toStarSubalgebra :=
  ∑ i, c i • (a i).val

theorem projectionSum_star (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    star (projectionSum a c)=projectionSum a (fun i => star (c i)) := by
  simp only [projectionSum,star_sum,star_smul,(a _).property.isSelfAdjoint.star_eq]

theorem projectionSum_mul (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0) (c d : ι → ℂ) :
    projectionSum a c*projectionSum a d=projectionSum a (fun i => c i*d i) := by
  classical
  unfold projectionSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_assoc,mul_smul_comm,smul_smul,(a i).property.isIdempotentElem.eq]
  · intro j _ hji
    rw [smul_mul_assoc,mul_smul_comm,ha i j hji.symm,smul_zero,smul_zero]
  · simp

theorem projectionSum_trace (τ : TracialRepresentation M)
    (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    τ.trace (projectionSum a c)=∑ i, c i*τ.trace (a i).val := by
  change coordinateTraceLinear τ (∑ i, c i • (a i).val)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coordinateTraceLinear τ).map_smul (c i) (a i).val

variable (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

abbrev dyadicEval (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :=
  projectionSum (dyadicProjection τ hdiff p n) c

theorem dyadicEval_one (p : AlgebraProjection M) (n : ℕ) :
    dyadicEval τ hdiff p n (fun _ => 1)=p.val := by
  simpa only [dyadicEval,projectionSum,one_smul] using dyadicProjection_sum τ hdiff p n

theorem dyadicEval_refine (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :
    dyadicEval τ hdiff p (n+1) (fun i => c i.1)=dyadicEval τ hdiff p n c := by
  change (∑ i : DyadicIndex n × Bool, c i.1 •
    (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool,add_comm,← smul_add,splitProjection_sum]

theorem dyadicEval_lift (p : AlgebraProjection M) {m n : ℕ} (hmn : m ≤ n)
    (c : DyadicIndex m → ℂ) :
    ∃ d : DyadicIndex n → ℂ, dyadicEval τ hdiff p m c=dyadicEval τ hdiff p n d := by
  induction n,hmn using Nat.le_induction with
  | base => exact ⟨c,rfl⟩
  | succ n hmn ih =>
    obtain ⟨d,hd⟩ := ih
    exact ⟨fun i => d i.1,hd.trans (dyadicEval_refine τ hdiff p n d).symm⟩

theorem dyadicEval_trace (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :
    τ.trace (dyadicEval τ hdiff p n c)=
      ∑ i, c i*((τ.trace p.val).re/(2:ℝ)^n : ℝ) := by
  rw [projectionSum_trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [projection_trace_real,dyadicProjection_trace]

end Generator.Tracial

end

end OAI
