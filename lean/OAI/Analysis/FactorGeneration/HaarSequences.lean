import OAI.Analysis.FactorGeneration.RepresentedFreeness

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/
section
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Full endpoint formula; the internal factors alone must be centered. -/
def HaarEndpoints (D : Subalgebra ℂ (Q τ ω)) (t : unitary (Q τ ω)) : Prop :=
  ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
    (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
    quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0

theorem HaarEndpoints.haar {D : Subalgebra ℂ (Q τ ω)} {t : unitary (Q τ ω)}
    (h : HaarEndpoints τ ω D t) (n : ℤ) (hn : n ≠ 0) :
    quotientTrace τ ω (↑(t^n) : Q τ ω)=0 := by
  simpa only [integerValueWord,mul_one,one_mul] using
    h 1 D.one_mem 1 D.one_mem n hn [] (by simp)

theorem HaarEndpoints.representedFree {D : Subalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D t) :
    representedClosedFree τ ω t D := by
  apply represented_haar_free_interface τ ω t D (h.haar τ ω)
  apply endpoint_all_alternating τ ω _ D
  intro c hc d hd q hq xs hxs
  apply endpoint_moments_laurent_closure τ ω D t h c d q hc hd
    (Submodule.le_topologicalClosure _ (Submodule.subset_span hq)) xs
  intro z hz
  exact ⟨(hxs z hz).1,(hxs z hz).2.1,
    Submodule.le_topologicalClosure _ (Submodule.subset_span (hxs z hz).2.2)⟩

structure CoordinateHaarData (hNM : N ≤ M) (D : Subalgebra ℂ (Q τ ω)) where
  t : unitary (Q τ ω)
  coordinates : Bounded N
  unitary_coordinates : ∀ j,coordinates.val j ∈ unitary N.toStarSubalgebra
  represents : quotientInclusion τ hNM (ω : Filter ℕ)
    (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) coordinates)=(t : Q τ ω)
  endpoints : HaarEndpoints τ ω D t

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

theorem nonempty_coordinateHaarData (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    Nonempty (CoordinateHaarData τ ω hNM D) := by
  obtain ⟨t,⟨b,hb,he⟩,_,hep⟩ := exists_coordinate_haar_endpoints
    (H := H) (N := N) (M := M) τ ω hNM hfactor hdiff hirr hsep hω D hD
  exact ⟨⟨t,b,hb,he,hep⟩⟩

end

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def SamePowerSign (n m : ℤ) : Prop := (0 < n ∧ 0 < m) ∨ (n < 0 ∧ m < 0)

def ReducedIntegerGaps (D : Subalgebra ℂ (Q τ ω)) : ℤ → List (Q τ ω × ℤ) → Prop
  | _,[] => True
  | n,(d,m)::xs => d ∈ D ∧ m ≠ 0 ∧
      (quotientTrace τ ω d=0 ∨ SamePowerSign n m) ∧ ReducedIntegerGaps D m xs

theorem integerValueWord_mul_power (t : unitary (Q τ ω)) (n m : ℤ)
    (xs : List (Q τ ω × ℤ)) (b : Q τ ω) :
    (↑(t^n) : Q τ ω)*integerValueWord τ ω t m xs b=
      integerValueWord τ ω t (n+m) xs b := by
  cases xs <;> simp [integerValueWord,zpow_add,mul_assoc]

/-- Prefixes are absorbed into an arbitrary linear functional. Its centered
endpoint property is preserved when a centered gap is appended. -/
theorem reduced_integer_gap_functional (D : Subalgebra ℂ (Q τ ω))
    (t : unitary (Q τ ω)) (L : Q τ ω →ₗ[ℂ] ℂ)
    (hm : ∀ b ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
      (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
      L (integerValueWord τ ω t n xs b)=0)
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hx : ReducedIntegerGaps τ ω D n xs) (b : Q τ ω) (hb : b ∈ D) :
    L (integerValueWord τ ω t n xs b)=0 := by
  induction xs generalizing L n with
  | nil => exact hm b hb n hn [] (by simp)
  | cons z xs ih =>
    rcases z with ⟨d,m⟩
    rcases hx with ⟨hd,hm0,hgap,hxs⟩
    let d0 := d-quotientTrace τ ω d • (1 : Q τ ω)
    have hd0 : d0 ∈ D := D.sub_mem hd (D.smul_mem D.one_mem _)
    have ht0 : quotientTrace τ ω d0=0 := by
      change (traceLinear τ ω) (d-quotientTrace τ ω d • (1 : Q τ ω))=0
      rw [map_sub,map_smul]
      change quotientTrace τ ω d-quotientTrace τ ω d*quotientTrace τ ω 1=0
      rw [quotientTrace_one,mul_one,sub_self]
    let L' : Q τ ω →ₗ[ℂ] ℂ := L.comp (LinearMap.mulLeft ℂ ((↑(t^n) : Q τ ω)*d0))
    have hL' : ∀ c ∈ D,∀ k : ℤ,k ≠ 0 → ∀ ys : List (Q τ ω × ℤ),
        (∀ z ∈ ys,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        L' (integerValueWord τ ω t k ys c)=0 := by
      intro c hc k hk ys hys
      exact hm c hc n hn ((d0,k)::ys) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hd0,ht0,hk⟩
        · exact hys z hz)
    have hc := ih L' hL' m hm0 hxs
    have hs : quotientTrace τ ω d * L (integerValueWord τ ω t (n+m) xs b)=0 := by
      rcases hgap with hzero | hsign
      · rw [hzero,zero_mul]
      · have hsum : n+m ≠ 0 := by rcases hsign with h | h <;> omega
        rw [ih L hm (n+m) hsum ?_]
        · exact mul_zero _
        · cases xs with
          | nil => trivial
          | cons z ys =>
            rcases hxs with ⟨hz,hnz,hgz,hys⟩
            refine ⟨hz,hnz,?_,hys⟩
            rcases hgz with hzero | hsame
            · exact Or.inl hzero
            · right
              rcases hsign with h | h <;> rcases hsame with h' | h' <;>
                simp only [SamePowerSign] at * <;> omega
    have he : d=d0+quotientTrace τ ω d • (1 : Q τ ω) := by
      simp only [d0,sub_add_cancel]
    change L ((↑(t^n) : Q τ ω)*d*integerValueWord τ ω t m xs b)=0
    rw [he,mul_add,add_mul,map_add]
    change L' (integerValueWord τ ω t m xs b) +
      L (((↑(t^n) : Q τ ω)*(quotientTrace τ ω d • (1 : Q τ ω)))*
        integerValueWord τ ω t m xs b)=0
    rw [hc,mul_smul_comm,mul_one,smul_mul_assoc,map_smul,
      integerValueWord_mul_power,smul_eq_mul,hs,add_zero]

theorem HaarEndpoints.reduced_gaps {D : Subalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D t)
    (a : Q τ ω) (ha : a ∈ D) (b : Q τ ω) (hb : b ∈ D)
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hx : ReducedIntegerGaps τ ω D n xs) :
    quotientTrace τ ω (a*integerValueWord τ ω t n xs b)=0 := by
  apply reduced_integer_gap_functional τ ω D t
    ((traceLinear τ ω).comp (LinearMap.mulLeft ℂ a))
    (fun b hb n hn xs hxs => h a ha b hb n hn xs hxs) n hn xs hx b hb

/-! Expand nonzero integer powers into signs while retaining the exact rule:
only an equal-sign gap may have a nonzero scalar part. -/

def signExponent (s : Bool) : ℤ := if s then -1 else 1

theorem signedLetter_integer (t : unitary (Q τ ω)) (s : Bool) :
    algebraSignedLetter (t : Q τ ω) s=(↑(t^signExponent s) : Q τ ω) := by
  cases s
  · simp [signExponent,algebraSignedLetter]
  · change star (t : Q τ ω)=(↑(t^(-1 : ℤ)) : Q τ ω)
    rw [zpow_neg_one]
    rfl

def SignedReducedGaps (D : Subalgebra ℂ (Q τ ω)) : Bool → List (Q τ ω × Bool) → Prop
  | _,[] => True
  | s,(d,t)::xs => d ∈ D ∧ (s ≠ t → quotientTrace τ ω d=0) ∧ SignedReducedGaps D t xs

theorem betweenWord_integerValue (t : unitary (Q τ ω)) (s : Bool)
    (xs : List (Q τ ω × Bool)) (b : Q τ ω) :
    betweenWord (t : Q τ ω) s xs b=integerValueWord τ ω t (signExponent s)
      (xs.map (fun z => (z.1,signExponent z.2))) b := by
  induction xs generalizing s with
  | nil => simp [betweenWord,integerValueWord,signedLetter_integer]
  | cons z xs ih => simp [betweenWord,integerValueWord,signedLetter_integer,ih]

theorem signedReducedGaps_integer {D : Subalgebra ℂ (Q τ ω)}
    (s : Bool) (xs : List (Q τ ω × Bool)) (hx : SignedReducedGaps τ ω D s xs) :
    ReducedIntegerGaps τ ω D (signExponent s)
      (xs.map (fun z => (z.1,signExponent z.2))) := by
  induction xs generalizing s with
  | nil => trivial
  | cons z xs ih =>
    refine ⟨hx.1,?_,?_,ih z.2 hx.2.2⟩
    · cases z.2 <;> simp [signExponent]
    · by_cases h : s=z.2
      · right
        rw [h]
        cases z.2 <;> simp [signExponent,SamePowerSign]
      · exact Or.inl (hx.2.1 h)

theorem HaarEndpoints.signed_gaps {D : Subalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D t)
    (a : Q τ ω) (ha : a ∈ D) (b : Q τ ω) (hb : b ∈ D)
    (s : Bool) (xs : List (Q τ ω × Bool)) (hx : SignedReducedGaps τ ω D s xs) :
    quotientTrace τ ω (a*betweenWord (t : Q τ ω) s xs b)=0 := by
  rw [betweenWord_integerValue]
  apply h.reduced_gaps τ ω a ha b hb _ (by cases s <;> simp [signExponent])
  exact signedReducedGaps_integer τ ω s xs hx

theorem signedReducedGaps_repeat {D : Subalgebra ℂ (Q τ ω)}
    (s : Bool) (n : ℕ) (xs : List (Q τ ω × Bool))
    (hx : SignedReducedGaps τ ω D s xs) :
    SignedReducedGaps τ ω D s (List.replicate n (1,s)++xs) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    exact ⟨D.one_mem,fun h => (h rfl).elim,ih⟩

theorem signedReducedGaps_blocks {D : Subalgebra ℂ (Q τ ω)}
    (s : Bool) (n : ℕ) (xs : List (Q τ ω × (Bool × ℕ)))
    (hx : ∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0) :
    SignedReducedGaps τ ω D s (powerBlockGaps s n xs) := by
  induction xs generalizing s n with
  | nil =>
    simpa only [powerBlockGaps,List.append_nil] using
      signedReducedGaps_repeat τ ω (D := D) s n [] trivial
  | cons z xs ih =>
    apply signedReducedGaps_repeat
    exact ⟨(hx z (by simp)).1,fun _ => (hx z (by simp)).2,
      ih _ _ (fun w hw => hx w (by simp [hw]))⟩

theorem integerValueWord_blocks (t : unitary (Q τ ω)) (n : ℤ) (hn : n ≠ 0)
    (xs : List (Q τ ω × ℤ)) (hx : ∀ z ∈ xs,z.2 ≠ 0) (b : Q τ ω) :
    integerValueWord τ ω t n xs b=betweenWord (t : Q τ ω) (integerPowerBlock n).1
      (powerBlockGaps (integerPowerBlock n).1 (integerPowerBlock n).2
        (xs.map (fun z => (z.1,integerPowerBlock z.2)))) b := by
  rw [← powerBlockWord_expand]
  induction xs generalizing n with
  | nil => simp [integerValueWord,powerBlockWord,integerPowerBlock_eval t n hn]
  | cons z xs ih =>
    simp only [integerValueWord,List.map_cons,powerBlockWord,integerPowerBlock_eval t n hn]
    rw [ih z.2 (hx z (by simp)) (fun w hw => hx w (by simp [hw]))]

end

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def absorbedGapList (u : A) (s : Bool) : List (A × Bool) → List (A × Bool)
  | [] => []
  | (d,t)::xs => (productRight u s*d*productLeft u t,t)::absorbedGapList u t xs

theorem betweenWord_absorb_left (u v : A) (s : Bool) (xs : List (A × Bool)) (b : A) :
    betweenWord (u*v) s xs b=productLeft u s*betweenWord v s (absorbedGapList u s xs)
      (productRight u (finalWordSign s xs)*b) := by
  induction xs generalizing s with
  | nil => simp [betweenWord,absorbedGapList,finalWordSign,signed_product_split,mul_assoc]
  | cons z xs ih =>
    simp only [betweenWord,absorbedGapList,finalWordSign,signed_product_split,ih,mul_assoc]
end Algebra
section

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem absorbedGapList_reduced (D : StarSubalgebra ℂ (Q τ ω))
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D)
    (s : Bool) (xs : List (Q τ ω × Bool))
    (hx : SignedReducedGaps τ ω D.toSubalgebra s xs) :
    SignedReducedGaps τ ω D.toSubalgebra s (absorbedGapList (u : Q τ ω) s xs) := by
  induction xs generalizing s with
  | nil => trivial
  | cons z xs ih =>
    rcases z with ⟨d,r⟩
    refine ⟨?_,?_,ih r hx.2.2⟩
    · cases s <;> cases r <;> simp only [productRight,productLeft,Bool.false_eq_true,
        ↓reduceIte,mul_one,one_mul]
      · exact D.mul_mem hx.1 hu
      · exact hx.1
      · exact D.mul_mem (D.mul_mem (D.star_mem' hu) hx.1) hu
      · exact D.mul_mem (D.star_mem' hu) hx.1
    · intro hne
      cases s <;> cases r
      · exact (hne rfl).elim
      · simpa [productRight,productLeft] using hx.2.1 (by decide)
      · change quotientTrace τ ω (star (u : Q τ ω)*d*(u : Q τ ω))=0
        rw [quotientTrace_mul_comm τ ω (star (u : Q τ ω)*d),← mul_assoc,
          u.property.2,one_mul]
        exact hx.2.1 (by decide)
      · exact (hne rfl).elim

theorem HaarEndpoints.mul_left_signed {D : StarSubalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D.toSubalgebra t)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D)
    (a : Q τ ω) (ha : a ∈ D) (b : Q τ ω) (hb : b ∈ D)
    (s : Bool) (xs : List (Q τ ω × Bool))
    (hx : SignedReducedGaps τ ω D.toSubalgebra s xs) :
    quotientTrace τ ω (a*betweenWord (↑(u*t) : Q τ ω) s xs b)=0 := by
  change quotientTrace τ ω (a*betweenWord ((u : Q τ ω)*(t : Q τ ω)) s xs b)=0
  rw [betweenWord_absorb_left,← mul_assoc]
  apply h.signed_gaps τ ω _ ?_ _ ?_ s _ (absorbedGapList_reduced τ ω D u hu s xs hx)
  · cases s <;> simp only [productLeft,Bool.false_eq_true,↓reduceIte,mul_one]
    · exact D.mul_mem ha hu
    · exact ha
  · cases finalWordSign s xs <;> simp only [productRight,Bool.false_eq_true,↓reduceIte,one_mul]
    · exact hb
    · exact D.mul_mem (D.star_mem' hu) hb

theorem HaarEndpoints.mul_left {D : StarSubalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D.toSubalgebra t)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D) :
    HaarEndpoints τ ω D.toSubalgebra (u*t) := by
  intro a ha b hb n hn xs hxs
  rw [integerValueWord_blocks τ ω _ n hn xs (fun z hz => (hxs z hz).2.2)]
  apply h.mul_left_signed τ ω u hu a ha b hb
  apply signedReducedGaps_blocks
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact ⟨(hxs w hw).1,(hxs w hw).2.1⟩

theorem integerValueWord_inv (t : unitary (Q τ ω)) (n : ℤ)
    (xs : List (Q τ ω × ℤ)) (b : Q τ ω) :
    integerValueWord τ ω t⁻¹ n xs b=integerValueWord τ ω t (-n)
      (xs.map (fun z => (z.1,-z.2))) b := by
  induction xs generalizing n with
  | nil => simp [integerValueWord,zpow_neg]
  | cons z xs ih => simp [integerValueWord,zpow_neg,ih]

theorem HaarEndpoints.inv {D : Subalgebra ℂ (Q τ ω)} {t : unitary (Q τ ω)}
    (h : HaarEndpoints τ ω D t) : HaarEndpoints τ ω D t⁻¹ := by
  intro a ha b hb n hn xs hxs
  rw [integerValueWord_inv]
  apply h a ha b hb (-n) (neg_ne_zero.mpr hn)
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact ⟨(hxs w hw).1,(hxs w hw).2.1,neg_ne_zero.mpr (hxs w hw).2.2⟩

theorem HaarEndpoints.mul_right {D : StarSubalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D.toSubalgebra t)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D) :
    HaarEndpoints τ ω D.toSubalgebra (t*u) := by
  have h' := (h.inv τ ω).mul_left τ ω u⁻¹ (show (↑u⁻¹ : Q τ ω) ∈ D from D.star_mem' hu)
  simpa only [mul_inv_rev,inv_inv] using h'.inv τ ω

theorem HaarEndpoints.absorb {D : StarSubalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D.toSubalgebra t)
    (a b : unitary (Q τ ω)) (ha : (a : Q τ ω) ∈ D) (hb : (b : Q τ ω) ∈ D) :
    HaarEndpoints τ ω D.toSubalgebra (a*t*b) :=
  (h.mul_left τ ω a ha).mul_right τ ω b hb

end

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

structure SuccessiveCoordinateHaar (hNM : N ≤ M) (seed : Set (Q τ ω)) where
  algebra : ℕ → StarSubalgebra ℂ (Q τ ω)
  step : ∀ j,CoordinateHaarData τ ω hNM (algebra j).toSubalgebra
  initial : algebra 0=StarAlgebra.adjoin ℂ seed
  successor : ∀ j,algebra (j+1)=StarAlgebra.adjoin ℂ
    (insert ((step j).t : Q τ ω) (algebra j : Set (Q τ ω)))
  separable : ∀ j,TopologicalSpace.IsSeparable (algebra j : Set (Q τ ω))

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

theorem nonempty_successiveCoordinateHaar (hω : (ω : Filter ℕ) ≤ atTop)
    (seed : Set (Q τ ω)) (hseed : seed.Countable) :
    Nonempty (SuccessiveCoordinateHaar τ ω hNM seed) := by
  let : NormedSpace ℂ (Q τ ω) := (quotientInnerProductSpace τ ω).toNormedSpace
  have : IsBoundedSMul ℂ (Q τ ω) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  have : ContinuousSMul ℂ (Q τ ω) := IsBoundedSMul.continuousSMul
  let step (s : {s : Set (Q τ ω) // s.Countable}) := Classical.choice
    (nonempty_coordinateHaarData τ ω hNM hfactor hdiff hirr hsep hω
      (StarAlgebra.adjoin ℂ s.val).toSubalgebra (separable_countable_star_adjoin s.property))
  let S : ℕ → {s : Set (Q τ ω) // s.Countable} := Nat.rec ⟨seed,hseed⟩
    (fun _ s => ⟨insert ((step s).t : Q τ ω) s.val,s.property.insert _⟩)
  refine ⟨⟨fun j => StarAlgebra.adjoin ℂ (S j).val,fun j => step (S j),rfl,?_,
    fun j => separable_countable_star_adjoin (S j).property⟩⟩
  intro j
  change StarAlgebra.adjoin ℂ (insert ((step (S j)).t : Q τ ω) (S j).val)=
    StarAlgebra.adjoin ℂ (insert ((step (S j)).t : Q τ ω)
      (StarAlgebra.adjoin ℂ (S j).val : Set (Q τ ω)))
  apply le_antisymm
  · apply StarAlgebra.adjoin_mono
    exact Set.insert_subset_insert (StarAlgebra.subset_adjoin ℂ _)
  · apply StarAlgebra.adjoin_le
    apply Set.insert_subset
    · exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _)
    · exact StarAlgebra.adjoin_mono (Set.subset_insert _ _)

omit hfactor hdiff hirr hsep
variable {hNM}

theorem SuccessiveCoordinateHaar.monotone {seed : Set (Q τ ω)}
    (F : SuccessiveCoordinateHaar τ ω hNM seed) : Monotone F.algebra := by
  apply monotone_nat_of_le_succ
  intro j x hx
  rw [F.successor]
  exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ hx)

theorem SuccessiveCoordinateHaar.seed_mem {seed : Set (Q τ ω)}
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (j : ℕ) : seed ⊆ F.algebra j := by
  intro x hx
  apply F.monotone τ ω (Nat.zero_le j)
  rw [F.initial]
  exact StarAlgebra.subset_adjoin ℂ seed hx

theorem SuccessiveCoordinateHaar.previous_mem {seed : Set (Q τ ω)}
    (F : SuccessiveCoordinateHaar τ ω hNM seed) {i j : ℕ} (hij : i < j) :
    ((F.step i).t : Q τ ω) ∈ F.algebra j := by
  apply F.monotone τ ω hij
  rw [F.successor]
  exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _)

end

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def prefixVariable (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) : ℕ → unitary (Q τ ω)
  | 0 => t 0
  | j+1 => u*t (j+1)

def prefixProduct (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) : ℕ → unitary (Q τ ω)
  | 0 => 1
  | j+1 => prefixProduct u t j*prefixVariable τ ω u t j

theorem prefixProduct_formula (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) (ell : ℕ) :
    prefixProduct τ ω u t (ell+1)=t 0*((List.range ell).map (fun j => u*t (j+1))).prod := by
  induction ell with
  | zero => simp [prefixProduct,prefixVariable]
  | succ ell ih =>
    change prefixProduct τ ω u t (ell+1)*(u*t (ell+1))=_
    rw [ih]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.prod_append,
      List.prod_singleton,mul_assoc]

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.variable_mem (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) {i j : ℕ} (hij : i < j) :
    (prefixVariable τ ω u (fun k => (F.step k).t) i : Q τ ω) ∈ F.algebra j := by
  cases i with
  | zero => exact F.previous_mem τ ω hij
  | succ i => exact (F.algebra j).mul_mem (F.seed_mem τ ω j hu) (F.previous_mem τ ω hij)

theorem SuccessiveCoordinateHaar.prefix_mem (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) {k j : ℕ} (hkj : k ≤ j) :
    (prefixProduct τ ω u (fun i => (F.step i).t) k : Q τ ω) ∈ F.algebra j := by
  induction k with
  | zero => exact (F.algebra j).one_mem
  | succ k ih =>
    exact (F.algebra j).mul_mem (ih (by omega)) (F.variable_mem τ ω u hu (by omega))

theorem SuccessiveCoordinateHaar.variable_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (j : ℕ) :
    HaarEndpoints τ ω (F.algebra j).toSubalgebra
      (prefixVariable τ ω u (fun k => (F.step k).t) j) := by
  cases j with
  | zero => exact (F.step 0).endpoints
  | succ j => exact (F.step (j+1)).endpoints.mul_left τ ω u (F.seed_mem τ ω _ hu)

theorem SuccessiveCoordinateHaar.prefix_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) :
    HaarEndpoints τ ω (F.algebra ell).toSubalgebra
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)) :=
  (F.variable_endpoints τ ω u hu ell).mul_left τ ω _ (F.prefix_mem τ ω u hu le_rfl)

theorem SuccessiveCoordinateHaar.target_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (ell : ℕ) :
    HaarEndpoints τ ω (F.algebra ell).toSubalgebra
      (z*(prefixProduct τ ω u (fun k => (F.step k).t) (ell+1))⁻¹) :=
  ((F.prefix_endpoints τ ω u hu ell).inv τ ω).mul_left τ ω z (F.seed_mem τ ω _ hz)

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

theorem exists_perturbation_haar_system (hω : (ω : Filter ℕ) ≤ atTop)
    (u z : unitary (Q τ ω)) (xi : Q τ ω) :
    ∃ F : SuccessiveCoordinateHaar τ ω hNM {(u : Q τ ω),(z : Q τ ω),xi},
      (∀ j,HaarEndpoints τ ω (F.algebra j).toSubalgebra
        (prefixVariable τ ω u (fun k => (F.step k).t) j)) ∧
      ∀ ell,HaarEndpoints τ ω (F.algebra ell).toSubalgebra
        (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)) ∧
        HaarEndpoints τ ω (F.algebra ell).toSubalgebra
          (z*(prefixProduct τ ω u (fun k => (F.step k).t) (ell+1))⁻¹) := by
  let F := Classical.choice (nonempty_successiveCoordinateHaar τ ω hNM hfactor hdiff hirr hsep hω
    {(u : Q τ ω),(z : Q τ ω),xi} (((Set.countable_singleton xi).insert (z : Q τ ω)).insert (u : Q τ ω)))
  exact ⟨F,F.variable_endpoints τ ω u (by simp),fun ell =>
    ⟨F.prefix_endpoints τ ω u (by simp) ell,F.target_endpoints τ ω u z (by simp) (by simp) ell⟩⟩

end Generator.Tracial

end

end OAI
