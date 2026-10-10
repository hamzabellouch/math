import OAI.NumberTheory.DirichletL.Moments.PrimeElements

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationCount
local notation "O" => ActualEisensteinCubic.O

def eligiblePairs (rows P : Finset O) (allow : O → O → Prop) : Finset (O × O) :=
  (rows.product P).filter (fun x => allow x.1 x.2)

def outputRow (x : O × O) : O := x.2^6*x.1

theorem outputRow_norm (x : O × O) (Z M L : ℝ) (hZ : 0 < Z)
    (hh : (Ideal.absNorm (Ideal.span {x.1}) : ℝ) ≤ Z^M)
    (hp : (Ideal.absNorm (Ideal.span {x.2}) : ℝ) ≤ Z^L) :
    (Ideal.absNorm (Ideal.span {outputRow x}) : ℝ) ≤ Z^(M+6*L) := by
  calc
    _ = (Ideal.absNorm (Ideal.span {x.2}) : ℝ)^6 *
        (Ideal.absNorm (Ideal.span {x.1}) : ℝ) := by
      simp only [outputRow,← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_pow,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]
    _ ≤ (Z^L)^6 * Z^M := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 6) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = Z^(M+6*L) := by
      rw [← Real.rpow_mul_natCast hZ.le,← Real.rpow_add hZ]
      congr 1
      ring

theorem amplified_energy_pushforward (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda^2 ∣ p-1)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M)
    (H : O → ℂ) :
    (∑ x ∈ eligiblePairs rows P allow, ‖H (outputRow x)‖^2) ≤
      ((M+6*L)/ell)*∑ y ∈ (eligiblePairs rows P allow).image outputRow, ‖H y‖^2 := by
  apply positive_pushforward_bound _ outputRow (fun y => ‖H y‖^2) _ (fun _ _ => sq_nonneg _)
  intro y hy
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  have hxm := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hy0 : y ≠ 0 := by
    rw [← hxy]
    exact mul_ne_zero (pow_ne_zero _ (hp x.2 hxm.2).ne_zero) (hrows x.1 hxm.1)
  apply amplified_row_fiber_count _ y hy0
  · intro z hz
    exact hp z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact hprimary z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · exact hZ
  · exact hell
  · intro z hz
    exact hpl z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · rw [← hxy]
    exact outputRow_norm x Z M L (zero_lt_one.trans hZ) (hhu x.1 hxm.1) (hpu x.2 hxm.2)

theorem sum_eligiblePairs (rows P : Finset O) (allow : O → O → Prop) (f : O → O → ℝ) :
    (∑ h ∈ rows, ∑ p ∈ P.filter (allow h), f h p) =
      ∑ x ∈ eligiblePairs rows P allow, f x.1 x.2 := by
  simp only [eligiblePairs,Finset.sum_filter]
  exact (Finset.sum_product rows P (fun x : O × O => if allow x.1 x.2 then f x.1 x.2 else 0)).symm

def errorEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (h p : O) : ℝ :=
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2

theorem gauss_energy_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda^2 ∣ p-1)
    (hallow : ∀ h ∈ rows, ∀ p ∈ P, allow h p → ¬p ∣ h)
    (κ : ℝ) (hκ : 0 < κ) (hsize : ∀ h ∈ rows, κ ≤ (P.filter (allow h)).card)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤ (4/κ)*
      (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows P allow).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2) +
        ∑ x ∈ eligiblePairs rows P allow, errorEnergy S a ha c x.1 x.2) := by
  have hj : (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤
      (4/κ)*∑ x ∈ eligiblePairs rows P allow,
        (‖gaussPolynomial S a ha c (outputRow x)‖^2 + errorEnergy S a ha c x.1 x.2) := by
    change _ ≤ (4/κ)*∑ x ∈ eligiblePairs rows P allow,
      (‖gaussPolynomial S a ha c (x.2^6*x.1)‖^2 + errorEnergy S a ha c x.1 x.2)
    rw [← sum_eligiblePairs rows P allow (fun h p =>
      ‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hn : (P.filter (allow h)).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (hκ.trans_le (hsize h hh)))
    have hb := polynomial_pool_bound S a ha c (P.filter (allow h)) hn
      (fun p hpP => hp p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hs p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hg p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hc p (Finset.mem_filter.mp hpP).1) h
      (fun p hpP => hallow h hh p (Finset.mem_filter.mp hpP).1 (Finset.mem_filter.mp hpP).2)
    calc
      _ ≤ (4 / ((P.filter (allow h)).card : ℝ)) *
          ∑ p ∈ P.filter (allow h), (‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p) := by
        simpa only [errorEnergy,add_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hκ (hsize h hh))
        (Finset.sum_nonneg (fun p _ => add_nonneg (sq_nonneg _) (by unfold errorEnergy; positivity)))
  have hf := amplified_energy_pushforward rows P allow hrows hp hprimary Z ell M L hZ hell
    hpl hpu hhu (gaussPolynomial S a ha c)
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_add_distrib]
  exact add_le_add hf le_rfl

end SevenEighths.CenteredMomentAmplificationEnergy

end

end OAI
