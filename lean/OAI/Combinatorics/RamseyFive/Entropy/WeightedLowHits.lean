import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Q
import OAI.Combinatorics.RamseyFive.Entropy.EventMass

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def lowHits (w : ℙ K V → ℝ) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun y=>weightOnHyperplane w y < 1/(4*(Nat.card K:ℝ))

theorem lowHits_card (hdim : finrank K V=5) (w : ℙ K V → ℝ) (A : ℝ)
    (hA : 0≤A) (hw : ∀ x,0≤w x ∧ w x≤A)
    (hm₀ : (3:ℝ)/4≤∑ x,w x) (hm₁ : ∑ x,w x≤1) :
    ((lowHits w).card:ℝ)≤64*(Nat.card K:ℝ)^5*A := by
  let q : ℝ:=Nat.card K
  let μ : ℝ:=((Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4)*(∑ x,w x)
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hμ : 3/(8*q)≤μ := by
    have hd := mul_le_mul_of_nonneg_right (density_lower (K:=K) (d:=4) (by decide))
      (show 0≤∑ x,w x from Finset.sum_nonneg fun x _=>(hw x).1)
    have hh := mul_le_mul_of_nonneg_left hm₀ (show 0≤1/(2*q) by positivity)
    change (1/(2*q))*(∑ x,w x)≤μ at hd
    have he : (1/(2*q))*(3/4)=3/(8*q) := by ring
    rw [he] at hh
    exact hh.trans hd
  have hv := incidence_variance (d:=4) hdim (by decide) w
  have hs : ∑ x,w x^2≤A := by
    calc
      _ ≤ ∑ x,A*w x := Finset.sum_le_sum fun x _=>by nlinarith [(hw x).1,(hw x).2]
      _ = A*(∑ x,w x) := (Finset.mul_sum _ _ _).symm
      _ ≤ A := by nlinarith
  have hv' : (∑ y,(weightOnHyperplane w y-μ)^2)≤q^3*A := by
    exact hv.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hb : ((lowHits w).card:ℝ)*(1/(8*q))^2≤q^3*A := by
    calc
      _ = ∑ _y∈lowHits w,(1/(8*q))^2 := by simp
      _ ≤ ∑ y∈lowHits w,(weightOnHyperplane w y-μ)^2 := by
        apply Finset.sum_le_sum
        intro y hy
        have hh : weightOnHyperplane w y<1/(4*q) := (Finset.mem_filter.mp hy).2
        have he : 3/(8*q)-1/(4*q)=1/(8*q) := by ring
        have hh' : 1/(8*q)≤μ-weightOnHyperplane w y := by linarith
        nlinarith [show 0<1/(8*q) by positivity]
      _ ≤ ∑ y,(weightOnHyperplane w y-μ)^2 :=
        Finset.sum_le_univ_sum_of_nonneg fun _=>sq_nonneg _
      _ ≤ _ := hv'
  calc
    _ ≤ (q^3*A)/(1/(8*q))^2 := (le_div_iff₀ (by positivity)).mpr hb
    _ = 64*q^5*A := by field_simp; ring

theorem lowHits_mass (hdim : finrank K V=5) (w : ℙ K V → ℝ)
    (p : Law (ℙ K (Dual K V))) (G : Finset (ℙ K (Dual K V))) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hw : ∀ x,0≤w x ∧ w x≤A)
    (hm₀ : (3:ℝ)/4≤∑ x,w x) (hm₁ : ∑ x,w x≤1)
    (hp : ∀ y∈G,p y≤B) :
    eventMass p (G∩lowHits w)≤64*(Nat.card K:ℝ)^5*A*B := by
  calc
    _ ≤ ((G∩lowHits w).card:ℝ)*B := by
      unfold eventMass
      calc
        _ ≤ ∑ _y∈G∩lowHits w,B := Finset.sum_le_sum fun y hy=>hp y (Finset.mem_inter.mp hy).1
        _ = _ := by simp
    _ ≤ ((lowHits w).card:ℝ)*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (lowHits_card hdim w A hA hw hm₀ hm₁) hB

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
