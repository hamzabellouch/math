import OAI.Analysis.FactorGeneration.HaarIndependence
import OAI.Analysis.FactorGeneration.Words

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def traceClosedSpan (S : Set (Q τ ω)) : Submodule ℂ (Q τ ω) :=
  (Submodule.span ℂ S).topologicalClosure

theorem sandwich_trace_inner (a z b : Q τ ω) :
    quotientTrace τ ω (a*z*b)=inner ℂ (star (b*a)) z := by
  rw [inner_eq_trace,star_star,quotientTrace_mul_comm τ ω (a*z),← mul_assoc]

theorem sandwich_trace_closedSpan (S : Set (Q τ ω)) (a b z : Q τ ω)
    (hz : z ∈ traceClosedSpan τ ω S)
    (h : ∀ y ∈ S,quotientTrace τ ω (a*y*b)=0) :
    quotientTrace τ ω (a*z*b)=0 := by
  let f : Q τ ω →L[ℂ] ℂ := innerSL ℂ (star (b*a))
  have hs : Submodule.span ℂ S ≤ LinearMap.ker f.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    change inner ℂ (star (b*a)) y=0
    rw [← sandwich_trace_inner]
    exact h y hy
  have hc := (Submodule.span ℂ S).topologicalClosure_minimal hs f.isClosed_ker
  have hh := hc hz
  change inner ℂ (star (b*a)) z=0 at hh
  rwa [← sandwich_trace_inner] at hh

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

def integerValueWord (v : unitary (Q τ ω)) (n : ℤ) : List (Q τ ω × ℤ) → Q τ ω → Q τ ω
  | [],b => (↑(v^n) : Q τ ω)*b
  | (d,m)::xs,b => (↑(v^n) : Q τ ω)*d*integerValueWord v m xs b

theorem integerValueWord_indexed (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (n : ℤ) (xs : List (ℕ × ℤ)) (b : Q τ ω) :
    integerValueWord τ ω v n (xs.map (fun z => (x z.1,z.2))) b=integerWord v x n xs b := by
  induction xs generalizing n with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,integerValueWord,integerWord,ih]

/-- All internal coefficients are extended one at a time, with the other
factors fixed. Uniform bounds on simultaneous approximants are unnecessary. -/
theorem integerValueWord_closedSpan (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (a b : Q τ ω) (n : ℤ) (xs : List (Q τ ω × ℤ))
    (hxs : ∀ z ∈ xs,z.1 ∈ traceClosedSpan τ ω (Set.range x))
    (hm : ∀ is : List ℕ,is.length=xs.length →
      quotientTrace τ ω (a*integerWord v x n (is.zip (xs.map Prod.snd)) b)=0) :
    quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0 := by
  induction xs generalizing a n with
  | nil => exact hm [] rfl
  | cons z xs ih =>
    have hi (i : ℕ) : quotientTrace τ ω
        ((a*(↑(v^n) : Q τ ω)*x i)*integerValueWord τ ω v z.2 xs b)=0 := by
      apply ih (a*(↑(v^n) : Q τ ω)*x i) z.2
      · exact fun y hy => hxs y (by simp [hy])
      · intro is his
        have hh := hm (i::is) (by simp [his])
        simpa only [List.map_cons,List.zip_cons_cons,integerWord,mul_assoc] using hh
    have hh := sandwich_trace_closedSpan τ ω (Set.range x) (a*(↑(v^n) : Q τ ω))
      (integerValueWord τ ω v z.2 xs b) z.1 (hxs z (by simp)) (by
        rintro _ ⟨i,rfl⟩
        exact hi i)
    simpa only [integerValueWord,mul_assoc] using hh

/-- The optional endpoints span the unit and the given centered family. -/
theorem optionalCoefficient_range (x : ℕ → Q τ ω) :
    Set.range (optionalCoefficient x)=insert 1 (Set.range x) := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    cases i <;> simp [optionalCoefficient]
  · intro h
    rcases Set.mem_insert_iff.mp h with rfl | ⟨i,rfl⟩
    · exact ⟨none,rfl⟩
    · exact ⟨some i,rfl⟩

theorem integerWord_right_factor {A : Type*} [Monoid A] [StarMul A]
    (v : unitary A) (x : ℕ → A) (n : ℤ) (xs : List (ℕ × ℤ)) (b : A) :
    integerWord v x n xs b=integerWord v x n xs 1*b := by
  induction xs generalizing n with
  | nil => simp only [integerWord,mul_one]
  | cons z xs ih =>
    simp only [integerWord]
    rw [ih z.2]
    simp only [mul_assoc]

theorem integerWord_closed_endpoints (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Q τ ω)
    (ha : a ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (hb : b ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (n : ℤ) (hn : n ≠ 0) (xs : List (ℕ × ℤ)) (hxs : ∀ z ∈ xs,z.2 ≠ 0) :
    quotientTrace τ ω (a*integerWord v x n xs b)=0 := by
  have hright (i : Option ℕ) :
      quotientTrace τ ω (optionalCoefficient x i*integerWord v x n xs b)=0 := by
    have htail := integerWord_right_factor v x n xs
    rw [htail,← mul_assoc]
    have hh := sandwich_trace_closedSpan τ ω (insert 1 (Set.range x))
      (optionalCoefficient x i*integerWord v x n xs 1) 1 b hb (by
        intro y hy
        rw [← optionalCoefficient_range] at hy
        obtain ⟨j,rfl⟩ := hy
        have hj := reducedOrderedMoments_integerWord τ ω v x hm i j n hn xs hxs
        rw [htail (optionalCoefficient x j)] at hj
        simpa only [mul_one,mul_assoc] using hj)
    simpa only [mul_one] using hh
  have hh := sandwich_trace_closedSpan τ ω (insert 1 (Set.range x)) 1
    (integerWord v x n xs b) a ha (by
      intro y hy
      rw [← optionalCoefficient_range] at hy
      obtain ⟨i,rfl⟩ := hy
      simpa only [one_mul] using hright i)
  simpa only [one_mul] using hh

theorem reduced_integer_moment_closedSpan (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Q τ ω)
    (ha : a ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (hb : b ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hxs : ∀ z ∈ xs,z.1 ∈ traceClosedSpan τ ω (Set.range x) ∧ z.2 ≠ 0) :
    quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0 := by
  apply integerValueWord_closedSpan τ ω v x a b n xs (fun z hz => (hxs z hz).1)
  intro is his
  apply integerWord_closed_endpoints τ ω v x hm a b ha hb n hn
  intro z hz
  have hz' := List.of_mem_zip hz
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hz'.2
  exact he ▸ (hxs d hd).2

end

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem exists_centered_dense_quotient_family (D : Subalgebra ℂ (Q τ ω))
    (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ x : ℕ → Q τ ω,(∀ i,x i ∈ D ∧ quotientTrace τ ω (x i)=0) ∧
      ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x) := by
  let S : Set (Q τ ω) := {d | d ∈ D ∧ quotientTrace τ ω d=0}
  have hS : TopologicalSpace.IsSeparable S := hD.mono (fun _ h => h.1)
  let : TopologicalSpace.SeparableSpace S := hS.separableSpace
  let : Nonempty S := ⟨⟨0,D.zero_mem,(traceLinear τ ω).map_zero⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := S)
  refine ⟨fun i => (v i).val,fun i => (v i).property,?_⟩
  intro d hd ht
  have hh := mem_closure_image continuous_subtype_val.continuousAt (hv (⟨d,hd,ht⟩ : S))
  simpa only [← Set.range_comp,Function.comp_def] using hh

theorem subalgebra_mem_centered_closedSpan (D : Subalgebra ℂ (Q τ ω))
    (x : ℕ → Q τ ω)
    (hx : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x))
    (d : Q τ ω) (hd : d ∈ D) : d ∈ traceClosedSpan τ ω (insert 1 (Set.range x)) := by
  let z := d-quotientTrace τ ω d • (1 : Q τ ω)
  have hzD : z ∈ D := D.sub_mem hd (D.smul_mem D.one_mem _)
  have hzt : quotientTrace τ ω z=0 := by
    change (traceLinear τ ω) (d-quotientTrace τ ω d • (1 : Q τ ω))=0
    rw [map_sub,map_smul]
    change quotientTrace τ ω d-quotientTrace τ ω d*quotientTrace τ ω 1=0
    rw [quotientTrace_one,mul_one,sub_self]
  have hz : z ∈ traceClosedSpan τ ω (insert 1 (Set.range x)) := by
    apply Submodule.closure_subset_topologicalClosure_span
    exact closure_mono (Set.subset_insert _ _) (hx z hzD hzt)
  have h1 : (1 : Q τ ω) ∈ traceClosedSpan τ ω (insert 1 (Set.range x)) :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_insert _ _))
  have hh := (traceClosedSpan τ ω (insert 1 (Set.range x))).add_mem hz
    ((traceClosedSpan τ ω (insert 1 (Set.range x))).smul_mem (quotientTrace τ ω d) h1)
  simpa only [z,sub_add_cancel] using hh

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

private theorem included_haar_endpoint_moments_of_dense_family (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (x : ℕ → Q τ ω)
    (hx : ∀ i,x i ∈ D ∧ quotientTrace τ ω (x i)=0)
    (hdense : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x)) :
    ∃ t : unitary (Q τ ω),
      (∃ q : TracialQuotient (restrictedTrace τ hNM) (ω : Filter ℕ),
        quotientInclusion τ hNM (ω : Filter ℕ) q=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ a ∈ D,∀ b ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (a*integerValueWord τ ω t n xs b)=0 := by
  obtain ⟨t,ht⟩ := exists_included_reduced_unitary τ hNM hfactor hdiff hirr hsep ω hω
    x (fun i => (hx i).2)
  refine ⟨t,ht.1,reducedOrderedMoments_haar τ ω t x ht.2,?_⟩
  intro a ha b hb n hn xs hxs
  apply reduced_integer_moment_closedSpan τ ω t x ht.2 a b
    (subalgebra_mem_centered_closedSpan τ ω D x hdense a ha)
    (subalgebra_mem_centered_closedSpan τ ω D x hdense b hb) n hn xs
  intro z hz
  refine ⟨?_,(hxs z hz).2.2⟩
  exact Submodule.closure_subset_topologicalClosure_span _ (hdense z.1 (hxs z hz).1 (hxs z hz).2.1)

theorem exists_included_haar_endpoint_moments (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ t : unitary (Q τ ω),
      (∃ q : TracialQuotient (restrictedTrace τ hNM) (ω : Filter ℕ),
        quotientInclusion τ hNM (ω : Filter ℕ) q=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ a ∈ D,∀ b ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (a*integerValueWord τ ω t n xs b)=0 := by
  obtain ⟨x,hx⟩ := exists_centered_dense_quotient_family τ ω D hD
  exact included_haar_endpoint_moments_of_dense_family τ ω hNM hfactor hdiff hirr hsep
    hω D x hx.1 hx.2

end

/-! Extend a trace identity in each factor to the closed linear span of its
allowed values. This uses separate continuity only. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem trace_product_closedSpan (sets : List (Set (Q τ ω))) (xs : List (Q τ ω))
    (a : Q τ ω)
    (hxs : List.Forall₂ (fun S x => x ∈ traceClosedSpan τ ω S) sets xs)
    (hm : ∀ ys,List.Forall₂ (fun S y => y ∈ S) sets ys →
      quotientTrace τ ω (a*ys.prod)=0) :
    quotientTrace τ ω (a*xs.prod)=0 := by
  induction xs generalizing sets a with
  | nil =>
    cases hxs
    exact hm [] .nil
  | cons x xs ih =>
    cases hxs with
    | @cons S x sets xs hx hxs =>
      have hh := sandwich_trace_closedSpan τ ω S a xs.prod x hx (by
        intro y hy
        apply ih sets (a*y) hxs
        intro ys hys
        have hz := hm (y::ys) (.cons hy hys)
        simpa only [List.prod_cons,mul_assoc] using hz)
      simpa only [List.prod_cons,mul_assoc] using hh

/-! Exact mixed moments for the closed linear span of the nonzero Haar powers.
This does not identify that span with the centered part of a generated C*-algebra. -/

def nonzeroPowerSet (v : unitary (Q τ ω)) : Set (Q τ ω) :=
  {q | ∃ n : ℤ,n ≠ 0 ∧ q=(↑(v^n) : Q τ ω)}

def alternatingFactors (q : Q τ ω) : List (Q τ ω × Q τ ω) → Q τ ω → List (Q τ ω)
  | [],b => [q,b]
  | (d,p)::xs,b => q::d::alternatingFactors p xs b

def alternatingPowerSets (P : Set (Q τ ω)) : List (Q τ ω × Q τ ω) → Q τ ω → List (Set (Q τ ω))
  | [],b => [P,{b}]
  | (d,_)::xs,b => P::{d}::alternatingPowerSets P xs b

theorem alternatingFactors_closedSpan (P : Set (Q τ ω)) (q b : Q τ ω)
    (xs : List (Q τ ω × Q τ ω)) (hq : q ∈ traceClosedSpan τ ω P)
    (hxs : ∀ z ∈ xs,z.2 ∈ traceClosedSpan τ ω P) :
    List.Forall₂ (fun S x => x ∈ traceClosedSpan τ ω S)
      (alternatingPowerSets τ ω P xs b) (alternatingFactors τ ω q xs b) := by
  have hsingle (z : Q τ ω) : z ∈ traceClosedSpan τ ω {z} :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_singleton z))
  induction xs generalizing q with
  | nil => exact .cons hq (.cons (hsingle b) .nil)
  | cons z xs ih =>
    exact .cons hq (.cons (hsingle z.1)
      (ih z.2 (hxs z (by simp)) (fun y hy => hxs y (by simp [hy]))))

theorem alternatingPowerSets_integerWord (D : Subalgebra ℂ (Q τ ω))
    (v : unitary (Q τ ω)) (xs : List (Q τ ω × Q τ ω))
    (hxs : ∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0)
    (b : Q τ ω) (ys : List (Q τ ω))
    (hys : List.Forall₂ (fun S y => y ∈ S)
      (alternatingPowerSets τ ω (nonzeroPowerSet τ ω v) xs b) ys) :
    ∃ n : ℤ,n ≠ 0 ∧ ∃ zs : List (Q τ ω × ℤ),
      (∀ z ∈ zs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) ∧
      ys.prod=integerValueWord τ ω v n zs b := by
  induction xs generalizing ys with
  | nil =>
    cases hys with
    | cons hp ht =>
      cases ht with
      | cons hb ht =>
        cases ht
        obtain ⟨n,hn,rfl⟩ := hp
        obtain rfl := Set.mem_singleton_iff.mp hb
        exact ⟨n,hn,[],by simp,by simp [integerValueWord]⟩
  | cons z xs ih =>
    cases hys with
    | cons hp ht =>
      cases ht with
      | cons hd ht =>
        obtain ⟨n,hn,rfl⟩ := hp
        obtain rfl := Set.mem_singleton_iff.mp hd
        obtain ⟨m,hm,zs,hzs,he⟩ := ih (fun y hy => hxs y (by simp [hy])) _ ht
        refine ⟨n,hn,(z.1,m)::zs,?_,?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨(hxs z (by simp)).1,(hxs z (by simp)).2,hm⟩
          · exact hzs y hy
        · simp only [List.prod_cons,he,integerValueWord,mul_assoc]

/-- Extends the actual nonzero-exponent formula to arbitrary closed-span
combinations in every Haar slot, while retaining arbitrary endpoints in D. -/
theorem endpoint_moments_laurent_closure (D : Subalgebra ℂ (Q τ ω))
    (v : unitary (Q τ ω))
    (hm : ∀ a ∈ D,∀ b ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
      (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
      quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0)
    (a b q : Q τ ω) (ha : a ∈ D) (hb : b ∈ D)
    (hq : q ∈ traceClosedSpan τ ω (nonzeroPowerSet τ ω v))
    (xs : List (Q τ ω × Q τ ω))
    (hxs : ∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧
      z.2 ∈ traceClosedSpan τ ω (nonzeroPowerSet τ ω v)) :
    quotientTrace τ ω (a*(alternatingFactors τ ω q xs b).prod)=0 := by
  apply trace_product_closedSpan τ ω (alternatingPowerSets τ ω (nonzeroPowerSet τ ω v) xs b)
    _ a (alternatingFactors_closedSpan τ ω _ q b xs hq (fun z hz => (hxs z hz).2.2))
  intro ys hys
  obtain ⟨n,hn,zs,hzs,he⟩ := alternatingPowerSets_integerWord τ ω D v xs
    (fun z hz => ⟨(hxs z hz).1,(hxs z hz).2.1⟩) b ys hys
  rw [he]
  exact hm a ha b hb n hn zs hzs

end

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_included_haar_laurent_moments (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ t : unitary (Q τ ω),
      (∃ q : TracialQuotient (restrictedTrace τ hNM) (ω : Filter ℕ),
        quotientInclusion τ hNM (ω : Filter ℕ) q=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ a ∈ D,∀ b ∈ D,∀ q ∈ traceClosedSpan τ ω (nonzeroPowerSet τ ω t),
        ∀ xs : List (Q τ ω × Q τ ω),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧
          z.2 ∈ traceClosedSpan τ ω (nonzeroPowerSet τ ω t)) →
        quotientTrace τ ω (a*(alternatingFactors τ ω q xs b).prod)=0 := by
  obtain ⟨t,ht,hhaar,hm⟩ := exists_included_haar_endpoint_moments τ ω hNM hfactor hdiff hirr hsep hω D hD
  refine ⟨t,ht,hhaar,?_⟩
  intro a ha b hb q hq xs hxs
  exact endpoint_moments_laurent_closure τ ω D t hm a b q ha hb hq xs hxs

end

/-! From the endpoint formula to every alternating word shape. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem alternating_tail_normal_form (P : Set (Q τ ω)) (D : Subalgebra ℂ (Q τ ω))
    (tail : List (Q τ ω)) (q : Q τ ω)
    (ht : alternatingFrom P {d | d ∈ D ∧ quotientTrace τ ω d=0} false tail) :
    ∃ xs : List (Q τ ω × Q τ ω), ∃ b ∈ D,
      (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ∈ P) ∧
      (q::tail).prod=(alternatingFactors τ ω q xs b).prod := by
  induction tail using List.twoStepInduction generalizing q with
  | nil => exact ⟨[],1,D.one_mem,by simp,by simp [alternatingFactors]⟩
  | singleton d => exact ⟨[],d,ht.1.1,by simp,rfl⟩
  | cons_cons d p tail ih _ =>
    obtain ⟨xs,b,hb,hxs,he⟩ := ih p ht.2.2
    refine ⟨(d,p)::xs,b,hb,?_,?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨ht.1.1,ht.1.2,ht.2.1⟩
      · exact hxs z hz
    · change q*(d*(p::tail).prod)=q*(d*(alternatingFactors τ ω p xs b).prod)
      rw [he]

theorem endpoint_all_alternating (P : Set (Q τ ω)) (D : Subalgebra ℂ (Q τ ω))
    (hm : ∀ a ∈ D,∀ b ∈ D,∀ q ∈ P,∀ xs : List (Q τ ω × Q τ ω),
      (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ∈ P) →
      quotientTrace τ ω (a*(alternatingFactors τ ω q xs b).prod)=0) :
    alternatingMomentsZero (quotientTrace τ ω) P {d | d ∈ D ∧ quotientTrace τ ω d=0} := by
  intro start word hn hw
  cases word with
  | nil => exact False.elim (hn rfl)
  | cons x tail =>
    cases start with
    | true =>
      obtain ⟨xs,b,hb,hxs,he⟩ := alternating_tail_normal_form τ ω P D tail x hw.2
      rw [he]
      simpa only [one_mul] using hm 1 D.one_mem b hb x hw.1 xs hxs
    | false =>
      cases tail with
      | nil => simpa only [List.prod_cons,List.prod_nil,mul_one] using hw.1.2
      | cons q tail =>
        obtain ⟨xs,b,hb,hxs,he⟩ := alternating_tail_normal_form τ ω P D tail q hw.2.2
        change quotientTrace τ ω (x*(q::tail).prod)=0
        rw [he]
        exact hm x hw.1.1 b hb q hw.2.1 xs hxs

end Generator.Tracial

end

end OAI
