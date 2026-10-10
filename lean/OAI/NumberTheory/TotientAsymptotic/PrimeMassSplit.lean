import OAI.NumberTheory.TotientAsymptotic.ProjectedMass

namespace OAI

/-! Split a finite prime family at an arbitrary coordinate without multiplying
by the number of possible prefixes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeInitial {N : ℕ} (p : Fin N → ℕ) (n : ℕ) (hn : n ≤ N) : Fin n → ℕ :=
  fun j => p (Fin.castLE hn j)

def primeFinal {N : ℕ} (p : Fin N → ℕ) (n : ℕ) : Fin (N-n) → ℕ :=
  fun j => p ⟨n+j.val,by have := j.isLt; omega⟩

lemma prime_parts_injective {N n : ℕ} (hn : n ≤ N) :
    Function.Injective (fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)) := by
  intro p q he
  funext j
  by_cases hj : j.val < n
  · exact congrFun (congrArg Prod.fst he) ⟨j.val,hj⟩
  · have hh := congrFun (congrArg Prod.snd he) ⟨j.val-n,by have := j.isLt; omega⟩
    simpa only [primeFinal,Nat.add_sub_of_le (Nat.le_of_not_gt hj)] using hh

lemma reciprocalShiftWeight_split {N n : ℕ} (hn : n ≤ N) (p : Fin N → ℕ) :
    reciprocalShiftWeight p = reciprocalShiftWeight (primeInitial p n hn)*
      reciprocalShiftWeight (primeFinal p n) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  have ht : (∏ j : Fin (n+d-n), (p ⟨n+j.val,by have := j.isLt; omega⟩-1)) =
      ∏ j : Fin d, (p (Fin.natAdd n j)-1) :=
    by
      have he := Fin.prod_congr' (a := n+d-n) (b := d)
        (fun j : Fin d => p (Fin.natAdd n j)-1) (by omega)
      simpa only [Fin.natAdd,Fin.val_cast] using he
  unfold primeInitial primeFinal reciprocalShiftWeight
  rw [ht,Fin.prod_univ_add,Nat.cast_mul,mul_inv]
  rfl

lemma prime_pi_mass {N : ℕ} (T : Fin N → Finset ℕ) :
    (∑ p ∈ Fintype.piFinset T, reciprocalShiftWeight p) =
      ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [reciprocalShiftWeight,Nat.cast_prod,Finset.prod_inv_distrib]

/-- Each suffix coordinate can have its own arithmetic restriction. The prefix
is counted once, with its original reciprocal mass. -/
theorem prime_mass_split {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (T : Fin (N-n) → Finset ℕ)
    (hT : ∀ p ∈ Q, ∀ j, primeFinal p n j ∈ T j) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
        ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  classical
  let F := fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)
  have he : (∑ p ∈ Q, reciprocalShiftWeight p) =
      ∑ z ∈ Q.image F, reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun p _ q _ he => prime_parts_injective hn he)]
    exact Finset.sum_congr rfl (fun p _ => reciprocalShiftWeight_split hn p)
  rw [he]
  have hsub : Q.image F ⊆ Q.image (fun p => primeInitial p n hn) ×ˢ Fintype.piFinset T := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Fintype.mem_piFinset.mpr (hT p hp)⟩
  calc
    _ ≤ ∑ z ∈ Q.image (fun p => primeInitial p n hn) ×ˢ Fintype.piFinset T,
        reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (reciprocalShiftWeight_nonneg _) (reciprocalShiftWeight_nonneg _))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul,prime_pi_mass]

/-- The same projected geometry used for collisions holds for every basic
remainder, independently of its largest-prime completion. -/
lemma remainderInitial_geometry {x : ℝ} {H K : ℕ} (hn : R x K ≤ L x H)
    (hL : 0 < L x H) {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    (∀ j, (primeInitial η.primes (R x K) hn j).Prime) ∧
    primePrefixCoord (primeInitial η.primes (R x K) hn) ∈ prefixBandRegion x K ∧
    primePrefixCoord (primeInitial η.primes (R x K) hn) ∈
      enlargedSimplex (R x K) (B x) (xi x 0) (fun j => xi x (j.val+1)) := by
  refine ⟨?_,?_,enlargedSimplex_project hn (basic_remainder_enlargedSimplex hL hη)⟩
  · intro j
    have hh := (hη.2.1 (j.val+1) (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)).1
    have he : remainderPrime η (j.val+1)=primeInitial η.primes (R x K) hn j := by
      simp only [remainderPrime,dite_eq_left (show 1 ≤ j.val+1 ∧ j.val+1 ≤ L x H by have := j.isLt; omega),Nat.add_sub_cancel]
      rfl
    exact he ▸ hh
  · intro j
    have hh := (hη.2.1 (j.val+1)
      (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)).2
    change (9/10 : ℝ)*bandScale x (j.val+1) ≤ remainderCoord x η ((Fin.castLE hn j).val+1) ∧
      remainderCoord x η ((Fin.castLE hn j).val+1) ≤ (11/10 : ℝ)*bandScale x (j.val+1) at hh
    rw [remainderCoord_fin] at hh
    exact hh

end TotientAsymptotic

end

end OAI
