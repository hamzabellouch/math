import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Growth.HomogeneousDimension
import OAI.Probability.CriticalPercolation.Growth.HomogeneousPolynomialSpace
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteActionAverage
import OAI.Probability.CriticalPercolation.Harmonic.GraphHarmonicCompactness
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicFunctionSpace

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma harmonic_constant_of_attained_max {u : X → ℝ} (hu : W.IsHarmonic u)
    (a : X) (hmax : ∀ x, u x≤u a) : ∀ x, u x=u a := by
  have hstep {x y : X} (hx : u x=u a) (hxy : W.graph.Adj x y) : u y=u a := by
    have hn (z : X) (hz : z∈W.neighbors x) : 0≤u x-u z := by rw [hx]; exact sub_nonneg.mpr (hmax z)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp (hu x) y (W.mem_neighbors.mpr hxy)
    linarith
  have hw : ∀ {x y : X}, W.graph.Walk x y → u x=u a → u y=u a := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z h p ih => exact fun hx => ih (hstep hx h)
  intro x
  obtain ⟨p⟩ := W.connected a x
  exact hw p rfl
lemma harmonic_constant_of_finite_range {u : X → ℝ} (hu : W.IsHarmonic u)
    (hf : (Set.range u).Finite) : ∀ x, u x=u W.root := by
  let : Nonempty X := ⟨W.root⟩
  obtain ⟨m,⟨a,rfl⟩,hm⟩ := Set.exists_max_image (Set.range u) id hf (Set.range_nonempty u)
  have he := W.harmonic_constant_of_attained_max hu a (fun x => hm (u x) ⟨x,rfl⟩)
  exact fun x => (he x).trans (he W.root).symm

def translateFunction (a : W.Aut) (u : X → ℝ) : X → ℝ := fun x => u (a.symm x)
lemma translate_harmonic (a : W.Aut) {u : X → ℝ} (hu : W.IsHarmonic u) :
    W.IsHarmonic (W.translateFunction a u) := by
  intro x
  have h := hu (a.symm x)
  rw [←W.neighbors_image a.symm x,Finset.sum_image] at h
  · exact h
  · exact fun b hb c hc he => a.symm.injective he
lemma translate_polynomial_growth (a : W.Aut) (k : ℕ) {u : X → ℝ}
    (hu : W.HasPolynomialGrowth k u) : W.HasPolynomialGrowth k (W.translateFunction a u) := by
  obtain ⟨C,hC,hu⟩ := (W.polynomial_growth_iff_length k u).mp hu
  apply (W.polynomial_growth_iff_length k _).mpr
  refine ⟨C*((W.length (a.symm W.root):ℝ)+1)^k,by positivity,?_⟩
  intro x
  have hl := W.aut_length_le a.symm x
  have hl' : (W.length (a.symm x):ℝ)≤(W.length (a.symm W.root):ℝ)+(W.length x:ℝ) := by exact_mod_cast hl
  change |u (a.symm x)|≤_
  calc
    _ ≤ C*((W.length (a.symm x):ℝ)+1)^k := hu _
    _ ≤ C*(((W.length (a.symm W.root):ℝ)+1)*((W.length x:ℝ)+1))^k := by
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) (W.length (a.symm W.root)),Nat.cast_nonneg (α:=ℝ) (W.length x)]
    _ = _ := by rw [mul_pow]; ring

def harmonicTranslation (k : ℕ) (a : W.Aut) :
    W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k where
  toFun u := ⟨W.translateFunction a u,W.translate_harmonic a u.property.1,
    W.translate_polynomial_growth a k u.property.2⟩
  invFun u := ⟨W.translateFunction a.symm u,W.translate_harmonic a.symm u.property.1,
    W.translate_polynomial_growth a.symm k u.property.2⟩
  left_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  right_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  map_add' u v := rfl
  map_smul' c u := rfl
@[simp] lemma harmonicTranslation_apply (k : ℕ) (a : W.Aut) (u : W.polynomialHarmonicSpace k) (x : X) :
    (W.harmonicTranslation k a u:X → ℝ) x=(u:X → ℝ) (a.symm x) := rfl

def harmonicRepresentation (k : ℕ) : W.Aut →*
    (W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k) where
  toFun := W.harmonicTranslation k
  map_one' := by ext u x; rfl
  map_mul' a b := by ext u x; rfl

lemma harmonicTranslation_eq_of_agree (k r : ℕ)
    (hdet : ∀ u : W.polynomialHarmonicSpace k, (∀ x∈W.ball r, (u:X → ℝ) x=0) → u=0)
    (a b : W.Aut) (hab : ∀ x∈W.ball r, a.symm x=b.symm x) :
    W.harmonicRepresentation k a=W.harmonicRepresentation k b := by
  apply LinearEquiv.ext
  intro u
  apply sub_eq_zero.mp
  apply hdet
  intro x hx
  change (u:X → ℝ) (a.symm x)-(u:X → ℝ) (b.symm x)=0
  rw [hab x hx,sub_self]

lemma finite_stabilizer_harmonic_image (d k : ℕ) (hg : W.HasDegree d) :
    (Set.range (fun a : W.Stab => W.harmonicRepresentation k a.val)).Finite := by
  let _ := W.polynomialHarmonicSpace_finiteDimensional d k hg
  obtain ⟨r,hr⟩ := exists_detecting_ball (fun r => (W.ball r:Set X)) W.ball_mono W.exists_mem_ball
    (W.polynomialHarmonicSpace k)
  obtain ⟨H,iH,fH,t,ht,hs⟩ := exists_finite_restriction (G:=W.Stab) (W.ball r:Set X)
    (W.ball r).finite_toSet (W.stab_ball_preserved r)
  let _ := iH
  let _ := fH
  apply (Set.finite_range (fun h : H => W.harmonicRepresentation k (t h).val⁻¹)).subset
  rintro _ ⟨a,rfl⟩
  obtain ⟨h,hh⟩ := hs a⁻¹
  refine ⟨h,?_⟩
  apply W.harmonicTranslation_eq_of_agree k r hr
  intro x hx
  exact hh x hx

variable {G : Type*} [Group G] (τ : G →* W.Aut)
lemma finite_range_of_finite_harmonic_image (k : ℕ)
    (htrans : ∀ x, ∃ a : G, τ a W.root=x)
    (hf : (Set.range ((W.harmonicRepresentation k).comp τ)).Finite) (u : W.polynomialHarmonicSpace k) :
    (Set.range (u:X → ℝ)).Finite := by
  apply (hf.image (fun e => (e u:X → ℝ) W.root)).subset
  rintro y ⟨x,rfl⟩
  obtain ⟨a,ha⟩ := htrans x
  refine ⟨(W.harmonicRepresentation k).comp τ a⁻¹,⟨a⁻¹,rfl⟩,?_⟩
  change (u:X → ℝ) ((τ a⁻¹).symm W.root)=(u:X → ℝ) x
  rw [map_inv]
  change (u:X → ℝ) (τ a W.root)=(u:X → ℝ) x
  rw [ha]
lemma infinite_harmonic_linear_image [Infinite X] (d : ℕ) (hg : W.HasDegree d)
    (htrans : ∀ x, ∃ a : G, τ a W.root=x) :
    (Set.range ((W.harmonicRepresentation 1).comp τ)).Infinite := by
  obtain ⟨u,hu,hu1,hbound,hedge,s,hs,hne⟩ := W.exists_nonconstant_lipschitz_harmonic d hg
  have hupol : W.HasPolynomialGrowth 1 u := by
    apply (W.polynomial_growth_iff_length 1 u).mpr
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [pow_one,one_mul] using (hbound x).trans (by linarith : (W.length x:ℝ)≤(W.length x:ℝ)+1)
  let v : W.polynomialHarmonicSpace 1 := ⟨u,hu,hupol⟩
  intro hf
  have hconst := W.harmonic_constant_of_finite_range hu
    (W.finite_range_of_finite_harmonic_image τ 1 htrans hf v)
  exact hne ((hconst s).trans hu1)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
