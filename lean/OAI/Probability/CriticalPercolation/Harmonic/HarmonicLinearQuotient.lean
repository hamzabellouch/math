import Mathlib
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry
import OAI.Probability.CriticalPercolation.Harmonic.AlmostHarmonicCompactness
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicDimensionBound
import OAI.Probability.CriticalPercolation.Harmonic.PolynomialHarmonicSpace

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
universe u
variable {A : Type u} [Group A] (W : WordGeometry A)

lemma harmonic_constant_of_attained_max {u : A → ℝ} (hu : W.IsHarmonic u)
    (a : A) (hmax : ∀ x, u x≤u a) : ∀ x, u x=u a := by
  have hstep (x : A) (hx : u x=u a) (s : A) (hs : s∈W.generators) : u (x*s)=u a := by
    have hn (t:A) (ht:t∈W.generators) : 0≤u x-u (x*t) := by rw [hx]; exact sub_nonneg.mpr (hmax _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hn).mp (hu x) s hs
    linarith
  have hball (n:ℕ) : ∀ b∈W.ball n, u (a*b)=u a := by
    induction n with
    | zero =>
      intro b hb
      have he : b=1 := by simpa [ball] using hb
      simp [he]
    | succ n ih =>
      intro b hb
      change b∈W.generators^(n+1) at hb
      rw [pow_succ] at hb
      obtain ⟨c,hc,s,hs,rfl⟩ := Finset.mem_mul.mp hb
      simpa only [mul_assoc] using hstep (a*c) (ih c hc) s hs
  intro x
  obtain ⟨n,hn⟩ := W.exists_mem_ball (a⁻¹*x)
  simpa using hball n (a⁻¹*x) hn

lemma harmonic_constant_of_finite_range {u : A → ℝ} (hu : W.IsHarmonic u)
    (hf : (Set.range u).Finite) : ∀ x, u x=u 1 := by
  obtain ⟨m,⟨a,rfl⟩,hm⟩ := Set.exists_max_image (Set.range u) id hf (Set.range_nonempty u)
  have he := W.harmonic_constant_of_attained_max hu a (fun x => hm (u x) ⟨x,rfl⟩)
  intro x
  exact (he x).trans (he 1).symm

def translateFunction (a : A) (u : A → ℝ) : A → ℝ := fun x => u (a⁻¹*x)

lemma translate_harmonic (a : A) {u : A → ℝ} (hu : W.IsHarmonic u) :
    W.IsHarmonic (translateFunction a u) := by
  intro x
  simpa only [translateFunction,mul_assoc] using hu (a⁻¹*x)

lemma translate_polynomial_growth (a : A) (k : ℕ) {u : A → ℝ}
    (hu : W.HasPolynomialGrowth k u) : W.HasPolynomialGrowth k (translateFunction a u) := by
  obtain ⟨C,hC,hu⟩ := (W.polynomial_growth_iff_length k u).mp hu
  apply (W.polynomial_growth_iff_length k _).mpr
  refine ⟨C*((W.length a:ℝ)+1)^k,by positivity,?_⟩
  intro x
  have hl := W.length_mul_le a⁻¹ x
  rw [W.length_inv] at hl
  have hl' : (W.length (a⁻¹*x):ℝ)≤(W.length a:ℝ)+(W.length x:ℝ) := by exact_mod_cast hl
  change |u (a⁻¹*x)|≤_
  calc
    _ ≤ C*((W.length (a⁻¹*x):ℝ)+1)^k := hu _
    _ ≤ C*(((W.length a:ℝ)+1)*((W.length x:ℝ)+1))^k := by
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) (W.length a),Nat.cast_nonneg (α:=ℝ) (W.length x)]
    _ = _ := by rw [mul_pow]; ring

def harmonicTranslation (k : ℕ) (a : A) :
    W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k where
  toFun u := ⟨translateFunction a u, W.translate_harmonic a u.property.1,
    W.translate_polynomial_growth a k u.property.2⟩
  invFun u := ⟨translateFunction a⁻¹ u, W.translate_harmonic a⁻¹ u.property.1,
    W.translate_polynomial_growth a⁻¹ k u.property.2⟩
  left_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  right_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  map_add' u v := rfl
  map_smul' c u := rfl

@[simp] lemma harmonicTranslation_apply (k : ℕ) (a : A) (u : W.polynomialHarmonicSpace k) (x : A) :
    (W.harmonicTranslation k a u:A → ℝ) x=(u:A → ℝ) (a⁻¹*x) := rfl

def harmonicRepresentation (k : ℕ) : A →*
    (W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k) where
  toFun := W.harmonicTranslation k
  map_one' := by ext u x; simp
  map_mul' a b := by ext u x; simp [mul_assoc]

lemma finite_range_of_finite_harmonic_image (k : ℕ)
    (hf : (Set.range (W.harmonicRepresentation k)).Finite) (u : W.polynomialHarmonicSpace k) :
    (Set.range (u:A → ℝ)).Finite := by
  apply (hf.image (fun e => (e u:A → ℝ) 1)).subset
  rintro y ⟨x,rfl⟩
  refine ⟨W.harmonicRepresentation k x⁻¹,⟨x⁻¹,rfl⟩,?_⟩
  change (u:A → ℝ) ((x⁻¹)⁻¹*1)=(u:A → ℝ) x
  simp

lemma infinite_harmonic_linear_image [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    (Set.range (W.harmonicRepresentation 1)).Infinite := by
  obtain ⟨u,hu,hu1,hbound,hedge,s,hs,hne⟩ := W.exists_nonconstant_lipschitz_harmonic d hg
  have hupol : W.HasPolynomialGrowth 1 u := by
    apply (W.polynomial_growth_iff_length 1 u).mpr
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [pow_one,one_mul] using (hbound x).trans (by linarith : (W.length x:ℝ)≤(W.length x:ℝ)+1)
  let v : W.polynomialHarmonicSpace 1 := ⟨u,hu,hupol⟩
  intro hf
  have hconst := W.harmonic_constant_of_finite_range hu (W.finite_range_of_finite_harmonic_image 1 hf v)
  exact hne ((hconst s).trans hu1)

theorem exists_infinite_finiteDimensional_linear_image [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V),
      FiniteDimensional ℝ V ∧ ∃ ρ : A →* (V ≃ₗ[ℝ] V), (Set.range ρ).Infinite := by
  refine ⟨W.polynomialHarmonicSpace 1,inferInstance,inferInstance,?_,W.harmonicRepresentation 1,
    W.infinite_harmonic_linear_image d hg⟩
  exact W.polynomialHarmonicSpace_finiteDimensional d 1 hg

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
