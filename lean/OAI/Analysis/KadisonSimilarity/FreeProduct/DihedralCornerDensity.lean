import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralCornerWords
import OAI.Analysis.KadisonSimilarity.FreeProduct.EvenAlternatingWords
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerHilbert

namespace OAI

/-! Separate L²-continuity extends the positive-power corner trace tests.
Only density of their linear span in the centered corner is needed;
no uniform bound on approximants is imposed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

/-- The trace with fixed left and right factors is a continuous functional
of the middle L²-vector, by traciality and the inner-product identity. -/
theorem trace_middle_eq_inner (a x b : P) :
    G.trace (a * x * b) = inner ℂ (G.vector (star (b * a))) (G.vector x) := by
  rw [G.inner_vector, star_star]
  calc
    G.trace (a * x * b) = G.trace (b * (a * x)) := G.tracial _ _
    _ = G.trace ((b * a) * x) := by rw [mul_assoc]

/-- A middle-factor trace test that vanishes on generators vanishes on the
closed linear span of their L²-vectors. -/
theorem trace_middle_zero_of_mem_closed_span (S : Set P) (a x b : P)
    (hx : G.vector x ∈ (Submodule.span ℂ (G.vector '' S)).topologicalClosure)
    (hzero : ∀ y ∈ S, G.trace (a * y * b) = 0) :
    G.trace (a * x * b) = 0 := by
  let L : H →L[ℂ] ℂ := innerSL ℂ (G.vector (star (b * a)))
  have hspan : Submodule.span ℂ (G.vector '' S) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    change inner ℂ (G.vector (star (b * a))) (G.vector y) = 0
    rw [← G.trace_middle_eq_inner]
    exact hzero y hy
  have hclosure := (Submodule.span ℂ (G.vector '' S)).topologicalClosure_minimal
    hspan L.isClosed_ker
  have h := hclosure hx
  change inner ℂ (G.vector (star (b * a))) (G.vector x) = 0 at h
  rw [G.trace_middle_eq_inner]
  exact h

end TracialCornerGeometry

namespace DihedralCornerWords

/-- Ordered alternating products, with the first list supplying fixed
left letters and the second list supplying the variable right letters. -/
def alternatingProduct : List P → List P → P
  | a :: as, x :: xs => a * x * alternatingProduct as xs
  | _, _ => 1

@[simp] theorem alternatingProduct_nil (xs : List P) : alternatingProduct [] xs = 1 := rfl
@[simp] theorem alternatingProduct_cons (a x : P) (as xs : List P) :
    alternatingProduct (a :: as) (x :: xs) = a * x * alternatingProduct as xs := rfl

/-- Extending one variable at a time requires only L²-density. The fixed
factors may have arbitrary operator norms. -/
theorem trace_alternatingProduct_zero_of_dense
    (G : TracialCornerGeometry P H) (S : Set P) (as : List P) (a : P)
    (hzero : ∀ xs : List P, xs.length = as.length → (∀ x ∈ xs, x ∈ S) →
      G.trace (a * alternatingProduct as xs) = 0)
    (xs : List P) (hlen : xs.length = as.length)
    (hmem : ∀ x ∈ xs,
      G.vector x ∈ (Submodule.span ℂ (G.vector '' S)).topologicalClosure) :
    G.trace (a * alternatingProduct as xs) = 0 := by
  induction as generalizing a xs with
  | nil =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp hlen
    subst xs
    exact hzero [] rfl (by simp)
  | cons b bs ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      have hlen' : xs.length = bs.length := Nat.succ.inj hlen
      have htail : ∀ y ∈ xs,
          G.vector y ∈ (Submodule.span ℂ (G.vector '' S)).topologicalClosure :=
        fun y hy => hmem y (List.mem_cons_of_mem _ hy)
      have htest : ∀ y ∈ S,
          G.trace ((a * b) * y * alternatingProduct bs xs) = 0 := by
        intro y hy
        apply ih (a := a * b * y)
        · intro ys hys hysmem
          have h := hzero (y :: ys) (by simp [hys]) (by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact hysmem z hz)
          simpa only [alternatingProduct_cons, mul_assoc] using h
        · exact hlen'
        · exact htail
      have h := G.trace_middle_zero_of_mem_closed_span S (a * b) x
        (alternatingProduct bs xs) (hmem x List.mem_cons_self) htest
      simpa only [alternatingProduct_cons, mul_assoc] using h

/-- The positive compressed rotation powers spanning the centered dihedral corner. -/
def positiveCornerPowers (p w : P) : Set P :=
  Set.range fun n : {n : ℕ // 0 < n} => p * w ^ n.val * p

section Splitting
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τR : R →ₗ[ℂ] ℂ} {AR BR : StarSubalgebra ℂ R}

/-- Split an even alternating word into its two ordered lists of letters.
The product identity is valid after applying any map into the ambient algebra. -/
theorem split_even_alternating_word (f : R → P) (w : List R)
    (hw : AlternatingCenteredWord τR AR BR true w) (heven : w.length % 2 = 0) :
    ∃ as bs : List R, as.length = bs.length ∧ w.length = 2 * as.length ∧
      (∀ a ∈ as, a ∈ AR ∧ τR a = 0) ∧ (∀ b ∈ bs, b ∈ BR ∧ τR b = 0) ∧
      (w.map f).prod = alternatingProduct (as.map f) (bs.map f) := by
  induction w using List.twoStepInduction with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp, rfl⟩
  | singleton a => simp at heven
  | cons_cons a b w ih _ =>
    cases hw with
    | cons ha ha0 ht =>
      cases ht with
      | cons hb hb0 ht' =>
        have htail : AlternatingCenteredWord τR AR BR true w := by
          simpa only [Bool.not_not] using ht'
        have ht_even : w.length % 2 = 0 := by
          simp only [List.length_cons] at heven
          omega
        obtain ⟨as, bs, hlen, hwlen, hA, hB, hprod⟩ := ih htail ht_even
        refine ⟨a :: as, b :: bs, by simp only [List.length_cons, hlen], ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by simpa using ha, ha0⟩
          · exact hA x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by simpa using hb, hb0⟩
          · exact hB x hx
        · simp only [List.map_cons, List.prod_cons, alternatingProduct_cons, hprod,
            mul_assoc]

end Splitting

/-- Choosing a positive exponent for each generator converts the alternating
product to the concrete list of corner blocks. -/
theorem alternatingProduct_eq_positive_blocks (p w : P) (as xs : List P)
    (hlen : xs.length = as.length) (hsupport : ∀ a ∈ as, a * p = a)
    (hmem : ∀ x ∈ xs, x ∈ positiveCornerPowers p w) :
    ∃ bs : List (P × ℕ), bs.map Prod.fst = as ∧
      (∀ b ∈ bs, 0 < b.2) ∧
      alternatingProduct as xs = (bs.map fun b => b.1 * w ^ b.2 * p).prod := by
  induction as generalizing xs with
  | nil =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp hlen
    subst xs
    exact ⟨[], rfl, by simp, rfl⟩
  | cons a as ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨n, rfl⟩ := hmem x List.mem_cons_self
      obtain ⟨bs, hbs, hpos, heq⟩ := ih xs (Nat.succ.inj hlen)
        (fun b hb => hsupport b (List.mem_cons_of_mem _ hb))
        (fun y hy => hmem y (List.mem_cons_of_mem _ hy))
      refine ⟨(a, n.val) :: bs, ?_, ?_, ?_⟩
      · simp only [List.map_cons, hbs]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact n.property
        · exact hpos b hb
      · simp only [alternatingProduct_cons, List.map_cons, List.prod_cons, heq]
        have h := congrArg (fun z : P => z * w ^ n.val * p *
          (bs.map fun b => b.1 * w ^ b.2 * p).prod) (hsupport a List.mem_cons_self)
        simpa only [mul_assoc] using h

/-- The original scalar freeness supplies every positive-generator test,
with the support factors and exponent choices constructed explicitly. -/
theorem trace_positive_corner_generators_zero
    (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) {d s : P}
    (hd : d ∈ D) (hs : s ∈ A) (hd0 : G.trace d = 0) (hs0 : G.trace s = 0)
    (p : P) (as xs : List P) (hne : as ≠ []) (hlen : xs.length = as.length)
    (hD : ∀ a ∈ as, a ∈ D) (hzero : ∀ a ∈ as, G.trace a = 0)
    (habsorb : ∀ a ∈ as, a * d = a)
    (hleft : ∀ a ∈ as, p * a = a) (hright : ∀ a ∈ as, a * p = a)
    (hmem : ∀ x ∈ xs, x ∈ positiveCornerPowers p (d * s)) :
    G.trace (alternatingProduct as xs) = 0 := by
  obtain ⟨bs, hbs, hpos, heq⟩ :=
    alternatingProduct_eq_positive_blocks p (d * s) as xs hlen hright hmem
  have hbsne : bs ≠ [] := by
    intro hb
    apply hne
    simpa only [hb, List.map_nil] using hbs.symm
  have hfirst : ∀ b ∈ bs, b.1 ∈ as := by
    intro b hb
    rw [← hbs]
    exact List.mem_map_of_mem hb
  rw [heq]
  exact trace_corner_product_eq_zero G.trace D A hd hs hd0 hs0 hf G.tracial p bs
    hbsne (fun b hb => hD _ (hfirst b hb)) (fun b hb => hzero _ (hfirst b hb))
    hpos (fun b hb => habsorb _ (hfirst b hb)) (fun b hb => hleft _ (hfirst b hb))

/-- Every even cyclic product of centered corner letters vanishes once the
positive compressed powers have dense span in the centered second corner. -/
theorem trace_corner_alternating_zero_of_dense
    (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) {d s : P}
    (hd : d ∈ D) (hs : s ∈ A) (hd0 : G.trace d = 0) (hs0 : G.trace s = 0)
    (p : P) (as xs : List P) (hne : as ≠ []) (hlen : xs.length = as.length)
    (hD : ∀ a ∈ as, a ∈ D) (hzero : ∀ a ∈ as, G.trace a = 0)
    (habsorb : ∀ a ∈ as, a * d = a)
    (hleft : ∀ a ∈ as, p * a = a) (hright : ∀ a ∈ as, a * p = a)
    (hmem : ∀ x ∈ xs, G.vector x ∈
      (Submodule.span ℂ (G.vector '' positiveCornerPowers p (d * s))).topologicalClosure) :
    G.trace (alternatingProduct as xs) = 0 := by
  have h := trace_alternatingProduct_zero_of_dense G (positiveCornerPowers p (d * s))
    as 1 (fun ys hys hymem => by
      simp only [one_mul]
      exact trace_positive_corner_generators_zero G D A hf hd hs hd0 hs0 p as ys
        hne hys hD hzero habsorb hleft hright hymem) xs hlen hmem
  simpa only [one_mul] using h

/-- Coercing a corner product inserts the corner identity at its right end. -/
theorem coe_corner_list_prod (p : P) (hp : IsStarProjection p)
    (w : List (CStarCorner p hp)) :
    (w.prod : P) = (List.map (fun x : CStarCorner p hp => (x : P)) w).prod * p := by
  induction w with
  | nil => simp only [List.prod_nil, CStarCorner.coe_one, List.map_nil, one_mul]
  | cons x xs ih =>
    change (x : P) * (xs.prod : P) =
      (x : P) * (List.map (fun y : CStarCorner p hp => (y : P)) xs).prod * p
    rw [ih, mul_assoc]

/-- Actual corner freeness follows from the original scalar freeness and
density of the centered positive compressed rotation powers. The density
input is a geometric word-span statement, not a freeness assumption. -/
theorem scalarFree_corner_of_positive_power_density
    (G : TracialCornerGeometry P H) (D A C : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) {d s : P}
    (hd : d ∈ D) (hs : s ∈ A) (hd0 : G.trace d = 0) (hs0 : G.trace s = 0)
    (p : P) (hp : IsStarProjection p) (hpD : p ∈ D) (hpC : p ∈ C)
    (hpd : p * d = p) (ht : G.trace p ≠ 0)
    (hdense : ∀ x : CStarCorner p hp, (x : P) ∈ C → G.trace (x : P) = 0 →
      G.vector (x : P) ∈
        (Submodule.span ℂ (G.vector '' positiveCornerPowers p (d * s))).topologicalClosure) :
    ScalarFree (CStarCorner.normalizedTrace p hp G.trace)
      (CStarCorner.subalgebra p hp D hpD) (CStarCorner.subalgebra p hp C hpC) := by
  apply scalarFree_of_even_cyclic
    (CStarCorner.normalizedTrace_one p hp G.trace ht)
    (CStarCorner.normalizedTrace_tracial p hp G.trace G.tracial)
  intro x xs hw heven
  obtain ⟨as, bs, hlen, hwlen, hA, hB, hprod⟩ :=
    split_even_alternating_word (fun y : CStarCorner p hp => (y : P)) (x :: xs) hw heven
  have has : as ≠ [] := by
    intro heq
    simp only [heq, List.length_nil, mul_zero, List.length_cons] at hwlen
    omega
  have hzeroA : ∀ a ∈ as, G.trace (a : P) = 0 := by
    intro a ha
    exact (mul_eq_zero.mp (hA a ha).2).resolve_left (inv_ne_zero ht)
  have hzeroB : ∀ b ∈ bs, G.trace (b : P) = 0 := by
    intro b hb
    exact (mul_eq_zero.mp (hB b hb).2).resolve_left (inv_ne_zero ht)
  have htest := trace_corner_alternating_zero_of_dense G D A hf hd hs hd0 hs0 p
    (List.map (fun a : CStarCorner p hp => (a : P)) as) (List.map (fun b : CStarCorner p hp => (b : P)) bs)
    (by simpa only [ne_eq, List.map_eq_nil_iff] using has)
    (by simpa only [List.length_map] using hlen.symm)
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact (hA a ha').1)
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact hzeroA a ha')
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      calc
        (a : P) * d = ((a : P) * p) * d := by rw [a.property.2]
        _ = (a : P) * (p * d) := mul_assoc _ _ _
        _ = (a : P) := by rw [hpd, a.property.2])
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact a.property.1)
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact a.property.2)
    (by
      intro b hb
      obtain ⟨b, hb', rfl⟩ := (List.mem_map (f := fun b : CStarCorner p hp => (b : P))).mp hb
      exact hdense b (hB b hb').1 (hzeroB b hb'))
  rw [← hprod] at htest
  rw [CStarCorner.normalizedTrace_apply, coe_corner_list_prod]
  apply mul_eq_zero_of_right
  rw [G.tracial _ p]
  simpa only [List.map_cons, List.prod_cons, ← mul_assoc, x.property.1] using htest

end DihedralCornerWords
end KadisonSimilarity

end

end OAI
