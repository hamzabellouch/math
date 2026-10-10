import OAI.NumberTheory.TotientAsymptotic.TailBounds
import OAI.NumberTheory.TotientAsymptotic.Arithmetic

namespace OAI

/-! Finiteness and order properties of the actual arithmetic prefix mass. -/

noncomputable section
open scoped BigOperators Topology Classical

namespace TotientAsymptotic

def remainderPrimeBound (x : ℝ) (i : ℕ) : ℕ :=
  max 1 ⌈Real.exp (Real.exp ((11/10 : ℝ) * bandScale x i))⌉₊

def remainderCofactorBound (x : ℝ) (H : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp (2 * bandScale x (L x H)))⌉₊

lemma basic_remainder_prime_bound {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) (i : Fin (L x H)) :
    η.primes i ≤ remainderPrimeBound x (i.val+1) := by
  have hi : i.val+1 ∈ Finset.Icc 1 (L x H) := by simp
  have hp := hη.2.1 (i.val+1) hi
  have heq : remainderPrime η (i.val+1) = η.primes i := by
    simp [remainderPrime, i.isLt]
  have hcoord : remainderCoord x η (i.val+1) =
      Real.log (Real.log (η.primes i : ℝ)) := by
    simp only [remainderCoord, Nat.add_one_ne_zero, ↓reduceIte, heq]
  rw [heq] at hp
  have hpos : (1 : ℝ) < η.primes i := by exact_mod_cast hp.1.one_lt
  have hlog := Real.log_pos hpos
  have hu : Real.log (Real.log (η.primes i : ℝ)) ≤ (11/10 : ℝ)*bandScale x (i.val+1) := by
    simpa only [hcoord] using hp.2.2
  have hb := (Real.log_le_iff_le_exp (zero_lt_one.trans hpos)).1
    ((Real.log_le_iff_le_exp hlog).1 hu)
  have hb' : η.primes i ≤ ⌈Real.exp (Real.exp ((11/10 : ℝ)*bandScale x (i.val+1)))⌉₊ := by
    exact_mod_cast hb.trans (Nat.le_ceil _)
  exact hb'.trans (le_max_right _ _)

lemma basic_remainder_cofactor_bound {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    η.cofactor ≤ remainderCofactorBound x H := by
  have hp : (0 : ℝ) < η.cofactor := by exact_mod_cast hη.1
  have hb := (Real.log_le_iff_le_exp hp).1 hη.2.2.2.2
  exact_mod_cast hb.trans (Nat.le_ceil _)

def remainderUniverse (x : ℝ) (H : ℕ) : Set (RemainderDatum (L x H)) :=
  {η | (∀ i, η.primes i ≤ remainderPrimeBound x (i.val+1)) ∧
    η.cofactor ≤ remainderCofactorBound x H}

lemma remainderUniverse_finite (x : ℝ) (H : ℕ) : (remainderUniverse x H).Finite := by
  let F : RemainderDatum (L x H) → (Fin (L x H) → ℕ) × ℕ := fun η => (η.primes, η.cofactor)
  have hF : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa [F, Prod.mk.injEq] using h
  have hf := (Set.Finite.pi (fun i : Fin (L x H) =>
    Set.finite_Iic (remainderPrimeBound x (i.val+1)))).prod
    (Set.finite_Iic (remainderCofactorBound x H))
  have hp := hf.preimage hF.injOn
  convert hp using 1
  ext η
  simp [remainderUniverse, F, Pi.le_def]

lemma basicRemainders_finite (x : ℝ) (H : ℕ) :
    {η : RemainderDatum (L x H) | IsBasicRemainder x H η}.Finite := by
  apply (remainderUniverse_finite x H).subset
  intro η hη
  exact ⟨fun i => basic_remainder_prime_bound hη i, basic_remainder_cofactor_bound hη⟩

def prefixOfRemainder (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : PrefixDatum (R x H) :=
  ⟨fun i => remainderPrime η (i.val+1), (remainderTail x H η).totient⟩

lemma isPrefixDatum_iff (x : ℝ) (H : ℕ) (ζ : PrefixDatum (R x H)) :
    IsPrefixDatum x H ζ ↔ ∃ η : RemainderDatum (L x H),
      IsBasicRemainder x H η ∧ prefixOfRemainder x H η = ζ := by
  constructor
  · rintro ⟨η, hη, hd, hp⟩
    refine ⟨η, hη, ?_⟩
    cases ζ with
    | mk primes d =>
      simp only [prefixOfRemainder, PrefixDatum.mk.injEq]
      exact ⟨funext (fun i => (hp i).symm), hd⟩
  · rintro ⟨η, hη, rfl⟩
    exact ⟨η, hη, rfl, fun _ => rfl⟩

theorem prefixData_finite (x : ℝ) (H : ℕ) :
    {ζ : PrefixDatum (R x H) | IsPrefixDatum x H ζ}.Finite := by
  have h := (basicRemainders_finite x H).image (prefixOfRemainder x H)
  convert h using 1
  ext ζ
  simp only [Set.mem_ofPred_eq, Set.mem_image, isPrefixDatum_iff]

lemma mass_summand_support_finite (x : ℝ) (H : ℕ) (f : ℝ → ℝ) :
    (Function.support (fun ζ : PrefixDatum (R x H) =>
      if IsPrefixDatum x H ζ then
        f ((ell ζ.d : ℝ) / ζ.d) / ((ζ.d : ℝ) * ∏ i : Fin (R x H), (ζ.primes i - 1 : ℕ))
      else 0)).Finite := by
  apply (prefixData_finite x H).subset
  intro ζ hζ
  by_contra h
  change ¬ IsPrefixDatum x H ζ at h
  simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hζ

theorem mass_nonneg (x : ℝ) (H : ℕ) (f : ℝ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    0 ≤ M x H f := by
  unfold M
  apply finsum_nonneg
  intro ζ
  split_ifs
  · exact div_nonneg (hf _) (by positivity)
  · exact le_rfl

theorem mass_mono (x : ℝ) (H : ℕ) {f g : ℝ → ℝ} (hfg : ∀ r, f r ≤ g r) :
    M x H f ≤ M x H g := by
  unfold M
  apply finsum_le_finsum (mass_summand_support_finite x H f)
    (mass_summand_support_finite x H g)
  intro ζ
  dsimp only
  split_ifs
  · exact div_le_div_of_nonneg_right (hfg _) (by positivity)
  · exact le_rfl

theorem weighted_mass_bounds (x : ℝ) (H k : ℕ) :
    0 ≤ M x H (fk k) ∧ M x H (fk k) ≤ M x H (fun _ => 1) := by
  constructor
  · unfold M
    apply finsum_nonneg
    intro ζ
    split_ifs
    · apply div_nonneg
      · exact fk_nonneg k (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      · positivity
    · exact le_rfl
  · apply mass_mono
    intro r
    by_cases hr : 0 ≤ r
    · exact fk_le_one k hr
    · have hr' : r < 0 := lt_of_not_ge hr
      have hkn : ((k+1 : ℕ) : ℝ) / r ≤ (k : ℝ) / r := by
        exact div_le_div_of_nonpos_of_le hr'.le (by norm_num)
      have hmin := min_le_min_left (1 : ℝ) hkn
      unfold fk
      push_cast at hmin
      linarith

end TotientAsymptotic
end

end OAI
