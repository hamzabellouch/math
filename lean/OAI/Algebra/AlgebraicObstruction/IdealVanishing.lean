import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.CoefficientData
import OAI.Algebra.AlgebraicObstruction.GraphCorrection

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {R σ : Type*} [CommRing R]

def vanishingIdeal (n : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | Vanishes n f}
  zero_mem' := Vanishes.zero n
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.mul_left c

 theorem origin_le_vanishingIdeal : originIdeal R σ ≤ vanishingIdeal 1 := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact Vanishes.one_iff.mpr (constantCoeff_X i)

 theorem vanishingIdeal_mul (a b : ℕ) :
    (vanishingIdeal a : Ideal (MvPowerSeries σ R)) * vanishingIdeal b ≤ vanishingIdeal (a+b) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg
  exact Vanishes.mul hf hg

 theorem origin_pow_vanishes {f : MvPowerSeries σ R} {n : ℕ}
    (hf : f ∈ (originIdeal R σ)^n) : Vanishes n f := by
  suffices (originIdeal R σ)^n ≤ vanishingIdeal n from this hf
  clear hf
  induction n with
  | zero => exact fun f _ => Vanishes.all f
  | succ n ih =>
    rw [pow_succ]
    exact (mul_le_mul' ih origin_le_vanishingIdeal).trans (vanishingIdeal_mul n 1)

 theorem mem_origin_iff [Fintype σ] {f : MvPowerSeries σ R} :
    f ∈ originIdeal R σ ↔ constantCoeff f = 0 := by
  constructor
  · intro hf
    exact Vanishes.one_iff.mp (origin_le_vanishingIdeal hf)
  · intro hf
    let m : σ → σ →₀ ℕ := fun i => Finsupp.single i 1
    have hh : ∀ e : σ →₀ ℕ, (¬ ∃ i, m i ≤ e) → coeff e f = 0 := by
      intro e he
      have he0 : e = 0 := by
        ext i
        by_contra hi
        apply he
        refine ⟨i, Finsupp.single_le_iff.mpr ?_⟩
        change 1 ≤ e i
        have : e i ≠ 0 := by simpa using hi
        omega
      simpa only [he0, coeff_zero_eq_constantCoeff] using hf
    rw [monomial_factorization m f hh]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_right
    change monomial (Finsupp.single i 1) 1 ∈ originIdeal R σ
    exact Ideal.subset_span ⟨i,rfl⟩

 theorem triple_transport_mem {S : Type*} [CommRing S] (I : Ideal S)
    {a b c a' b' c' : S} (ha : a'-a ∈ I) (hb : b'-b ∈ I) (hc : c'-c ∈ I)
    (h : a*b*c ∈ I) : a'*b'*c' ∈ I := by
  have hd : a'*b'*c' - a*b*c ∈ I := by
    have hh := I.add_mem (I.add_mem
      (I.mul_mem_right (b'*c') ha) (I.mul_mem_left (a*c') hb))
      (I.mul_mem_left (a*b) hc)
    convert hh using 1
    ring
  convert I.add_mem hd h using 1
  ring

 theorem Jet.pderiv_constant {f g : MvPowerSeries σ R} (h : Jet 2 f g) (i : σ) :
    constantCoeff (MvPowerSeries.pderiv i f) = constantCoeff (MvPowerSeries.pderiv i g) := by
  have hh := Vanishes.one_iff.mp (h.pderiv i)
  simpa only [Jet, map_sub, sub_eq_zero] using hh

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open Matrix
open scoped Classical
variable {R ι σ : Type*} [CommRing R] [Fintype ι]

omit [Fintype ι] in
theorem vectorIdeal_square [Fintype ι] (v : ι → MvPowerSeries σ R) :
    (vectorIdeal v)^2 = Ideal.span (Set.range fun ij : ι × ι => v ij.1 * v ij.2) := by
  rw [pow_two, vectorIdeal, Ideal.span_mul_span]
  congr 1
  ext z
  constructor
  · rintro ⟨a,⟨i,rfl⟩,b,⟨j,rfl⟩,rfl⟩
    exact ⟨(i,j),rfl⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    exact ⟨v i,⟨i,rfl⟩, v j,⟨j,rfl⟩,rfl⟩

 theorem quadratic_witness (v : ι → MvPowerSeries σ R) (f : MvPowerSeries σ R)
    (hf : f ∈ (vectorIdeal v)^2) :
    ∃ b : Matrix ι ι (MvPowerSeries σ R), f = dotProduct v (b *ᵥ v) := by
  rw [vectorIdeal_square] at hf
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  refine ⟨fun i j => c (i,j), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
