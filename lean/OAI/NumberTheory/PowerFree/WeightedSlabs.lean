import OAI.NumberTheory.PowerFree.AffineCounting

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

def simplexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1)).biUnion Finset.HasAntidiagonal.antidiagonal

@[simp] theorem mem_simplexPairs (x : ℕ × ℕ) (N : ℕ) :
    x ∈ simplexPairs N ↔ x.1+x.2 ≤ N := by
  simp only [simplexPairs, Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro h; exact ⟨_, by omega, rfl⟩

theorem card_simplexPairs (N : ℕ) :
    2*(simplexPairs N).card = (N+1)*(N+2) := by
  rw [simplexPairs, Finset.card_biUnion]
  · simp_rw [Finset.Nat.card_antidiagonal]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      nlinarith
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.HasAntidiagonal.mem_antidiagonal.mp hi).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.mp hj))

def weightedPairs (a b T : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (T+1)) ×ˢ (Finset.range (T+1))).filter
    (fun x => a*x.1+b*x.2 ≤ T)

theorem mem_weightedPairs {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x : ℕ × ℕ) (T : ℕ) :
    x ∈ weightedPairs a b T ↔ a*x.1+b*x.2 ≤ T := by
  simp only [weightedPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x.1 ≤ a*x.1 := by nlinarith
    have hy : x.2 ≤ b*x.2 := by nlinarith
    exact ⟨⟨by omega, by omega⟩, h⟩

private theorem pair_divmod_injective (a b : ℕ) :
    Function.Injective (fun x : ℕ × ℕ => ((x.1/b,x.2/a),(x.1%b,x.2%a))) := by
  intro x y h
  have hq := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  have hr1 := congrArg Prod.fst hr
  have hr2 := congrArg Prod.snd hr
  apply Prod.ext
  · have hx := Nat.mod_add_div x.1 b
    have hy := Nat.mod_add_div y.1 b
    dsimp at hq1 hr1
    rw [hq1, hr1] at hx
    omega
  · have hx := Nat.mod_add_div x.2 a
    have hy := Nat.mod_add_div y.2 a
    dsimp at hq2 hr2
    rw [hq2, hr2] at hx
    omega

theorem weightedPairs_upper {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (T : ℕ) :
    (weightedPairs a b T).card ≤
      (simplexPairs (T/(a*b))).card * (a*b) := by
  let f := fun x : ℕ × ℕ => ((x.1/b,x.2/a),(x.1%b,x.2%a))
  have hin (x : ℕ × ℕ) (hx : x ∈ weightedPairs a b T) :
      f x ∈ (simplexPairs (T/(a*b))) ×ˢ
        ((Finset.range b) ×ˢ (Finset.range a)) := by
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · apply (mem_simplexPairs _ _).mpr
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < a*b)).mpr
      have h := (mem_weightedPairs ha hb x T).mp hx
      have hx1 := Nat.div_mul_le_self x.1 b
      have hx2 := Nat.div_mul_le_self x.2 a
      dsimp [f]
      nlinarith [Nat.mul_le_mul_left a hx1, Nat.mul_le_mul_left b hx2]
    · simp [f, Nat.mod_lt _ ha, Nat.mod_lt _ hb]
  have h := Finset.card_le_card_of_injOn f hin
    (fun _ _ _ _ he => pair_divmod_injective a b he)
  simpa [Finset.card_product, mul_comm a b] using h

theorem weightedPairs_lower {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T N : ℕ) (hTN : a*b*(N+2) ≤ T) :
    (simplexPairs N).card * (a*b) ≤ (weightedPairs a b T).card := by
  let S := (simplexPairs N) ×ˢ ((Finset.range b) ×ˢ (Finset.range a))
  let f := fun x : (ℕ × ℕ) × (ℕ × ℕ) => (b*x.1.1+x.2.1,a*x.1.2+x.2.2)
  have hin (x : (ℕ × ℕ) × (ℕ × ℕ)) (hx : x ∈ S) :
      f x ∈ weightedPairs a b T := by
    rcases Finset.mem_product.mp hx with ⟨hn, hr⟩
    have hn' := (mem_simplexPairs _ _).mp hn
    rcases Finset.mem_product.mp hr with ⟨hr1, hr2⟩
    have hr1' := Finset.mem_range.mp hr1
    have hr2' := Finset.mem_range.mp hr2
    apply (mem_weightedPairs ha hb _ T).mpr
    dsimp [f]
    nlinarith [Nat.mul_le_mul_left (a*b) hn', Nat.mul_le_mul_left a (Nat.le_of_lt hr1'),
      Nat.mul_le_mul_left b (Nat.le_of_lt hr2')]
  have hinj : Set.InjOn f (S : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    intro x hx y hy he
    have hx' := Finset.mem_product.mp (Finset.mem_product.mp hx).2
    have hy' := Finset.mem_product.mp (Finset.mem_product.mp hy).2
    have hleft := congrArg Prod.fst he
    have hright := congrArg Prod.snd he
    have hm1 := congrArg (fun n => n % b) hleft
    have hm2 := congrArg (fun n => n % a) hright
    dsimp [f] at hleft hright hm1 hm2
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx'.1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hy'.1)] at hm1
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx'.2),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hy'.2)] at hm2
    apply Prod.ext
    · apply Prod.ext <;> nlinarith
    · exact Prod.ext hm1 hm2
  have h := Finset.card_le_card_of_injOn f hin hinj
  simpa [S, Finset.card_product, mul_comm a b] using h

end

theorem weightedPairs_quadratic_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T : ℕ) :
    T^2 ≤ 2*(a*b)*(weightedPairs a b T).card + 3*(a*b)*T + 7*(a*b)^2 ∧
    2*(a*b)*(weightedPairs a b T).card ≤ T^2 + 3*(a*b)*T + 2*(a*b)^2 := by
  let L := a*b
  let q := T/L
  have hL : 0 < L := Nat.mul_pos ha hb
  have hq : L*q ≤ T := by
    dsimp [q]
    nlinarith [Nat.div_mul_le_self T L]
  have hT : T ≤ L*(q+1) := by
    have hr := Nat.mod_lt T hL
    have hm := Nat.mod_add_div T L
    dsimp [q]
    nlinarith
  constructor
  · by_cases hq2 : 2 ≤ q
    · let N := q-2
      have hN : q = N+2 := by omega
      have hTN : a*b*(N+2) ≤ T := by simpa only [L, ← hN] using hq
      have hl := weightedPairs_lower ha hb T N hTN
      have hc := card_simplexPairs N
      have h0 : L*(N+1)*(N+2) ≤ 2*(weightedPairs a b T).card := by
        dsimp [L]
        nlinarith [Nat.mul_le_mul_left 2 hl]
      have h1 := Nat.mul_le_mul_left L h0
      have h2 : T^2 ≤ (L*(N+3))^2 := by
        exact Nat.pow_le_pow_left (by nlinarith [hT]) 2
      have h3 : L*N ≤ T := by nlinarith [hq]
      have h4 := Nat.mul_le_mul_left (3*L) h3
      change T^2 ≤ 2*L*(weightedPairs a b T).card + 3*L*T+7*L^2
      nlinarith
    · have hsmall : T ≤ 2*L := by nlinarith [hT]
      have hsquare := Nat.pow_le_pow_left hsmall 2
      change T^2 ≤ 2*L*(weightedPairs a b T).card + 3*L*T+7*L^2
      nlinarith
  · have hu := weightedPairs_upper ha hb T
    have hc := card_simplexPairs q
    have h0 : 2*(weightedPairs a b T).card ≤ (q+1)*(q+2)*L := by
      change (weightedPairs a b T).card ≤ (simplexPairs q).card * L at hu
      nlinarith [Nat.mul_le_mul_left 2 hu]
    have h1 := Nat.mul_le_mul_left L h0
    have hprod := Nat.mul_le_mul (Nat.add_le_add_right hq L)
      (Nat.add_le_add_right hq (2*L))
    change 2*L*(weightedPairs a b T).card ≤ T^2+3*L*T+2*L^2
    nlinarith

theorem weightedPairs_volume_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (T : ℕ) :
    |((weightedPairs a b T).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| ≤
      3/2*(T:ℝ) + 7/2*(a*b : ℕ) := by
  have hL : (0:ℝ) < (a*b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  have ⟨hlo, hhi⟩ := weightedPairs_quadratic_bounds ha hb T
  have hlo' : (T:ℝ)^2 ≤ 2*(a*b : ℕ)*(weightedPairs a b T).card +
      3*(a*b : ℕ)*T+7*(a*b : ℕ)^2 := by exact_mod_cast hlo
  have hhi' : 2*(a*b : ℕ)*(weightedPairs a b T).card ≤ (T:ℝ)^2 +
      3*(a*b : ℕ)*T+2*(a*b : ℕ)^2 := by exact_mod_cast hhi
  have hden : (0:ℝ) < 2*(a*b : ℕ) := by positivity
  have heq := div_mul_cancel₀ ((T:ℝ)^2) (ne_of_gt hden)
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith [sq_nonneg (a*b : ℕ)]

abbrev NatTriple := ℕ × ℕ × ℕ

def tripleWeight (a b c : ℕ) (x : NatTriple) : ℕ := a*x.1+b*x.2.1+c*x.2.2

def weightedTriples (a b c T : ℕ) : Finset NatTriple :=
  ((Finset.range (T+1)) ×ˢ (Finset.range (T+1)) ×ˢ (Finset.range (T+1))).filter
    (fun x => tripleWeight a b c x ≤ T)

theorem mem_weightedTriples {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : NatTriple) (T : ℕ) : x ∈ weightedTriples a b c T ↔ tripleWeight a b c x ≤ T := by
  simp only [weightedTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x.1 ≤ a*x.1 := by nlinarith
    have hy : x.2.1 ≤ b*x.2.1 := by nlinarith
    have hz : x.2.2 ≤ c*x.2.2 := by nlinarith
    dsimp [tripleWeight] at h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

def tripleDivides (m x : NatTriple) : Prop := m.1 ≤ x.1 ∧ m.2.1 ≤ x.2.1 ∧ m.2.2 ≤ x.2.2

instance (m x : NatTriple) : Decidable (tripleDivides m x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def weightedNormal (a b c : ℕ) (m : NatTriple) (T : ℕ) : Finset NatTriple :=
  (weightedTriples a b c T).filter (fun x => ¬ tripleDivides m x)

def tripleShift (m : NatTriple) : NatTriple ↪ NatTriple where
  toFun x := (m.1+x.1,m.2.1+x.2.1,m.2.2+x.2.2)
  inj' := by
    intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x : NatTriple => x.2.1) h
    have h3 := congrArg (fun x : NatTriple => x.2.2) h
    simp only [Nat.add_left_cancel_iff] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)

theorem tripleWeight_shift (a b c : ℕ) (m x : NatTriple) :
    tripleWeight a b c (tripleShift m x) = tripleWeight a b c m + tripleWeight a b c x := by
  change a*(m.1+x.1)+b*(m.2.1+x.2.1)+c*(m.2.2+x.2.2) = _
  dsimp [tripleWeight]
  ring

theorem weightedNormal_card_add {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : tripleWeight a b c m ≤ T) :
    (weightedNormal a b c m T).card +
      (weightedTriples a b c (T-tripleWeight a b c m)).card = (weightedTriples a b c T).card := by
  have he : (weightedTriples a b c T).filter (tripleDivides m) =
      (weightedTriples a b c (T-tripleWeight a b c m)).map (tripleShift m) := by
    ext x
    simp only [Finset.mem_filter, mem_weightedTriples ha hb hc, Finset.mem_map]
    constructor
    · rintro ⟨hx, hm⟩
      let y : NatTriple := (x.1-m.1,x.2.1-m.2.1,x.2.2-m.2.2)
      have hy : tripleShift m y = x := by
        rcases hm with ⟨h1,h2,h3⟩
        change (m.1+(x.1-m.1),m.2.1+(x.2.1-m.2.1),m.2.2+(x.2.2-m.2.2)) = x
        simp [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2, Nat.add_sub_cancel' h3]
      refine ⟨y, ?_, hy⟩
      rw [← hy, tripleWeight_shift] at hx
      omega
    · rintro ⟨y, hy, rfl⟩
      constructor
      · rw [tripleWeight_shift]
        omega
      · change m.1 ≤ m.1+y.1 ∧ m.2.1 ≤ m.2.1+y.2.1 ∧ m.2.2 ≤ m.2.2+y.2.2
        omega
  have hh := Finset.card_filter_add_card_filter_not (s := weightedTriples a b c T) (p := tripleDivides m)
  rw [he, Finset.card_map] at hh
  change _ + ((weightedTriples a b c T).filter (fun x => ¬ tripleDivides m x)).card = _ at hh
  dsimp [weightedNormal]
  omega

def firstSlab (i : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (i,x)
  inj' := by intro x y h; exact congrArg Prod.snd h

def secondSlab (u j : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (u+x.1,j,x.2)
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
      (congrArg (fun z : NatTriple => z.2.2) h)

def thirdSlab (u v k : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (u+x.1,v+x.2,k)
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
      (Nat.add_left_cancel (congrArg (fun z : NatTriple => z.2.1) h))

def firstSlabs (a b c u T : ℕ) : Finset NatTriple :=
  (Finset.range u).biUnion fun i => (weightedPairs b c (T-a*i)).map (firstSlab i)

def secondSlabs (a b c u v T : ℕ) : Finset NatTriple :=
  (Finset.range v).biUnion fun j => (weightedPairs a c (T-(a*u+b*j))).map (secondSlab u j)

def thirdSlabs (a b c u v w T : ℕ) : Finset NatTriple :=
  (Finset.range w).biUnion fun k => (weightedPairs a b (T-(a*u+b*v+c*k))).map (thirdSlab u v k)

end QuarticPowerFree

end OAI
