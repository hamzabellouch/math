import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectiveTransport

namespace OAI

section
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cut (T : Finset (Projectivization K (Module.Dual K V))) (z : Projectivization K V) :
    Finset (Projectivization K (Module.Dual K V)) := T.filter (SharpLogRamsey.Incidence.Incident z)

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma cut_card_sum {n : ℕ} (hdim : Module.finrank K V = n+3)
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ∑ z, (cut T z).card = (∑ i ∈ range (n+2), Nat.card K^i)*T.card := by
  simp only [cut,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  have hh (t : Projectivization K (Module.Dual K V)) :
      (∑ z : Projectivization K V, if SharpLogRamsey.Incidence.Incident z t then 1 else 0) =
        ∑ i ∈ range (n+2), Nat.card K^i := by
    have h := card_incident_points (d := n+2) hdim t
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
    simpa only [card_eq_sum_ones,sum_filter] using h
  simp_rw [hh]
  simp [mul_comm]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma surviving_incidence_sum {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ∑ z, incidenceCount S (cut T z) =
      (∑ i ∈ range (n+2), Nat.card K^i)*incidenceCount S T := by
  simp only [incidenceCount,cut,sum_filter]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro t ht
  have hh (a : ℕ) : (∑ z : Projectivization K V, if SharpLogRamsey.Incidence.Incident z t then a else 0) =
      (∑ i ∈ range (n+2), Nat.card K^i)*a := by
    have h := card_incident_points (d := n+2) hdim t
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
    rw [← sum_filter]
    simp [h]
  exact hh _

local instance flat_JoinedProjectionCenterTools_1 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) :=
  Fintype.ofEquiv _ (bidual (K:=K) (V:=V))

lemma cut_variance {n : ℕ} (hdim : Module.finrank K V = n+3)
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ∑ z : Projectivization K V,
      ((cut T z).card-(∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)/
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i)*T.card)^2 ≤
          (Nat.card K:ℝ)^(n+1)*T.card := by
  let w : Projectivization K (Module.Dual K V) → ℝ := fun t => if t ∈ T then 1 else 0
  have hw : (∑ t, w t) = (T.card:ℝ) := by simp [w]
  have hw2 : (∑ t, w t^2) = (T.card:ℝ) := by simp [w]
  have hv := projective_variance_le
    (show Module.finrank K (Module.Dual K V) = n+3 from Subspace.dual_finrank_eq.trans hdim) w
  rw [hw,hw2,← (bidual (K:=K) (V:=V)).sum_comp] at hv
  have hcut (z : Projectivization K V) :
      weightedIncidences SharpLogRamsey.Incidence.Incident w (bidual z) = ((cut T z).card:ℝ) := by
    simp only [weightedIncidences,incident_bidual,w]
    rw [← sum_filter,← sum_filter]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    congr 2
    ext t
    simp [cut,and_comm]
  simp_rw [hcut] at hv
  exact hv

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteAveraging
open Finset
open scoped BigOperators

lemma exists_small {α : Type*} [Fintype α] (f : α → ℝ)
    (h : ∑ x, f x < Fintype.card α) : ∃ x, f x < 1 := by
  by_contra hn
  push Not at hn
  have hh : (Fintype.card α:ℝ) ≤ ∑ x, f x := by
    simpa using sum_le_sum (s := univ) (f := fun _ => (1:ℝ)) (g := f) (fun x _ => hn x)
  exact not_lt_of_ge hh h

lemma exists_five {α : Type*} [Fintype α] (f₁ f₂ f₃ f₄ f₅ : α → ℝ)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x) (hf₃ : ∀ x, 0 ≤ f₃ x)
    (hf₄ : ∀ x, 0 ≤ f₄ x) (hf₅ : ∀ x, 0 ≤ f₅ x)
    (h : (∑ x, f₁ x)+(∑ x, f₂ x)+(∑ x, f₃ x)+(∑ x, f₄ x)+(∑ x, f₅ x) <
      Fintype.card α) :
    ∃ x, f₁ x < 1 ∧ f₂ x < 1 ∧ f₃ x < 1 ∧ f₄ x < 1 ∧ f₅ x < 1 := by
  have hs : ∑ x, (f₁ x+f₂ x+f₃ x+f₄ x+f₅ x) < (Fintype.card α:ℝ) := by
    simpa only [sum_add_distrib] using h
  obtain ⟨x,hx⟩ := exists_small _ hs
  exact ⟨x,by linarith [hf₂ x,hf₃ x,hf₄ x,hf₅ x],
    by linarith [hf₁ x,hf₃ x,hf₄ x,hf₅ x],
    by linarith [hf₁ x,hf₂ x,hf₄ x,hf₅ x],
    by linarith [hf₁ x,hf₂ x,hf₃ x,hf₅ x],
    by linarith [hf₁ x,hf₂ x,hf₃ x,hf₄ x]⟩

end SharpLogRamsey.FiniteAveraging

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem exists_center {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S A : Finset (Projectivization K V))
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (δ u cS cA e : ℝ) (hδ : 0<δ) (hu : 0<u) (hcS : 0<cS) (hcA : 0<cA) (he : 0<e)
    (hbudget :
      (Nat.card K:ℝ)^(n+1)*T.card/δ^2+
      (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)*U.card/u+
      ((S.card*(S.card-1)*(Nat.card K+1):ℕ):ℝ)/cS+
      ((A.card*(A.card-1)*(Nat.card K+1):ℕ):ℝ)/cA+
      (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)*incidenceCount S T/e <
        ∑ i ∈ range (n+3), (Nat.card K:ℝ)^i) :
    ∃ z : Projectivization K V,
      |((cut T z).card:ℝ)-(∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)/
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i)*T.card| < δ ∧
      ((cut U z).card:ℝ)<u ∧ (orderedCollisions S z:ℝ)<cS ∧
      (orderedCollisions A z:ℝ)<cA ∧ (incidenceCount S (cut T z):ℝ)<e := by
  let Q : ℝ := ∑ i ∈ range (n+3), (Nat.card K:ℝ)^i
  let H : ℝ := ∑ i ∈ range (n+2), (Nat.card K:ℝ)^i
  let v (z : Projectivization K V) : ℝ := ((cut T z).card-H/Q*T.card)^2/δ^2
  let a (z : Projectivization K V) : ℝ := (cut U z).card/u
  let b (z : Projectivization K V) : ℝ := orderedCollisions S z/cS
  let c (z : Projectivization K V) : ℝ := orderedCollisions A z/cA
  let f (z : Projectivization K V) : ℝ := incidenceCount S (cut T z)/e
  have hv : ∑ z, v z ≤ (Nat.card K:ℝ)^(n+1)*T.card/δ^2 := by
    simp only [v,← sum_div]
    exact div_le_div_of_nonneg_right (cut_variance hdim T) (sq_nonneg δ)
  have ha : ∑ z, a z = H*U.card/u := by
    simp only [a,← sum_div,← Nat.cast_sum]
    rw [cut_card_sum hdim]
    simp [H]
  have hb : ∑ z, b z ≤ ((S.card*(S.card-1)*(Nat.card K+1):ℕ):ℝ)/cS := by
    simp only [b,← sum_div,← Nat.cast_sum]
    exact div_le_div_of_nonneg_right (by exact_mod_cast collision_total S) hcS.le
  have hc : ∑ z, c z ≤ ((A.card*(A.card-1)*(Nat.card K+1):ℕ):ℝ)/cA := by
    simp only [c,← sum_div,← Nat.cast_sum]
    exact div_le_div_of_nonneg_right (by exact_mod_cast collision_total A) hcA.le
  have hf : ∑ z, f z = H*incidenceCount S T/e := by
    simp only [f,← sum_div,← Nat.cast_sum]
    rw [surviving_incidence_sum hdim]
    simp [H]
  have hQ : (Fintype.card (Projectivization K V):ℝ) = Q := by
    rw [← Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
    simp [Q]
  have hall : (∑ z, v z)+(∑ z, a z)+(∑ z, b z)+(∑ z, c z)+(∑ z, f z) <
      Fintype.card (Projectivization K V) := by
    rw [ha,hf,hQ]
    exact lt_of_le_of_lt (by linarith) hbudget
  obtain ⟨z,hz₁,hz₂,hz₃,hz₄,hz₅⟩ := FiniteAveraging.exists_five v a b c f
    (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun _ => div_nonneg (by positivity) hu.le)
    (fun _ => div_nonneg (by positivity) hcS.le)
    (fun _ => div_nonneg (by positivity) hcA.le)
    (fun _ => div_nonneg (by positivity) he.le) hall
  refine ⟨z,?_,(div_lt_one hu).mp hz₂,(div_lt_one hcS).mp hz₃,
    (div_lt_one hcA).mp hz₄,(div_lt_one he).mp hz₅⟩
  have hh := (div_lt_one (sq_pos_of_pos hδ)).mp hz₁
  exact (sq_lt_sq₀ (abs_nonneg _) hδ.le).mp (by simpa [v,sq_abs] using hh)

end
end SharpLogRamsey.Projection

end

end OAI
