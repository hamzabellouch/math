import OAI.NumberTheory.TotientAsymptotic.ExtractTail
import OAI.NumberTheory.TotientAsymptotic.FiniteCoefficient
import OAI.NumberTheory.TotientAsymptotic.PrimeGrid

namespace OAI

/-! Fixed finite tail support and exact grouping of the actual prefix mass. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma witness_w_pos {H : ℕ} {s : ℝ} {η : TailDatum H} (hη : IsWitness H s η) :
    0 < w η := by
  apply Nat.mul_pos hη.2.1
  apply Finset.prod_pos
  intro h hh
  exact (hη.2.2.1 h hh).1.pos

lemma prefix_tail_support {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (hζ : IsPrefixDatum x H ζ) :
    IsTotient ζ.d ∧ ζ.d ∈ Finset.Icc 1 (tailValueBound H) := by
  obtain ⟨η, hη, hd, _⟩ := hζ
  let η' := extractTail x H η
  have hw : IsWitness H (theta x) η' := extractTail_isWitness hη hPH hHm
  have hwd : (w η').totient = ζ.d := by
    rw [extractTail_value η hPH.le hHm]
    exact hd
  have hdt : IsTotient ζ.d := ⟨w η', witness_w_pos hw, hwd⟩
  refine ⟨hdt, Finset.mem_Icc.mpr ⟨isTotient_pos hdt, ?_⟩⟩
  exact witness_totient_bound hs η' ⟨hw, hwd⟩

def prefixDataFinset (x : ℝ) (H : ℕ) : Finset (PrefixDatum (R x H)) :=
  (prefixData_finite x H).toFinset

@[simp] lemma mem_prefixDataFinset {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)} :
    ζ ∈ prefixDataFinset x H ↔ IsPrefixDatum x H ζ := by
  simp [prefixDataFinset]

def prefixPrimeFiber (x : ℝ) (H d : ℕ) : Finset (Fin (R x H) → ℕ) :=
  ((prefixDataFinset x H).filter (fun ζ => ζ.d=d)).image PrefixDatum.primes

lemma mem_prefixPrimeFiber {x : ℝ} {H d : ℕ} {p : Fin (R x H) → ℕ} :
    p ∈ prefixPrimeFiber x H d ↔ IsPrefixDatum x H ⟨p,d⟩ := by
  constructor
  · intro hp
    obtain ⟨ζ, hζ, heq⟩ := Finset.mem_image.mp hp
    obtain ⟨hζ, hd⟩ := Finset.mem_filter.mp hζ
    have he : ζ = ⟨p,d⟩ := by cases ζ; simp_all
    simpa only [he] using (mem_prefixDataFinset.mp hζ)
  · intro hp
    exact Finset.mem_image.mpr ⟨⟨p,d⟩, Finset.mem_filter.mpr
      ⟨mem_prefixDataFinset.mpr hp, rfl⟩, rfl⟩

lemma mass_eq_sum_prefixData (x : ℝ) (H : ℕ) (f : ℝ → ℝ) :
    M x H f = ∑ ζ ∈ prefixDataFinset x H,
      f ((ell ζ.d : ℝ)/ζ.d)/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ)) := by
  unfold M
  rw [finsum_eq_sum_of_support_subset _ (s := prefixDataFinset x H)]
  · apply Finset.sum_congr rfl
    intro ζ hζ
    rw [ite_eq_left (mem_prefixDataFinset.mp hζ)]
  · intro ζ hζ
    by_contra hnot
    have h := mt mem_prefixDataFinset.mpr hnot
    simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hζ

/-- Each prime prefix is included once in its tail-totient fiber, regardless
of how many basic witnesses it admits. The outer support is fixed by `H`. -/
theorem mass_eq_finite_tail_sum {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (f : ℝ → ℝ) :
    M x H f = ∑ d ∈ Finset.Icc 1 (tailValueBound H),
      f ((ell d : ℝ)/d)/d * ∑ p ∈ prefixPrimeFiber x H d, reciprocalShiftWeight p := by
  rw [mass_eq_sum_prefixData]
  have hmaps : ∀ ζ ∈ prefixDataFinset x H, ζ.d ∈ Finset.Icc 1 (tailValueBound H) :=
    fun ζ hζ => (prefix_tail_support hPH hHm hs (mem_prefixDataFinset.mp hζ)).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  unfold prefixPrimeFiber
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ζ hζ
    have hd := (Finset.mem_filter.mp hζ).2
    rw [hd]
    unfold reciprocalShiftWeight
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · intro ζ hζ ξ hξ heq
    have hζd := (Finset.mem_filter.mp hζ).2
    have hξd := (Finset.mem_filter.mp hξ).2
    cases ζ
    cases ξ
    simp_all

end TotientAsymptotic

end

end OAI
