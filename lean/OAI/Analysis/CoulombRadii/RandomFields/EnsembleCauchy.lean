import Mathlib
import OAI.Analysis.CoulombRadii.Screening.OutCap

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma slice_ensemble_count_cauchy {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (F : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hF : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*F p s x))
    (hF2 : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2)) :
    (∑ p, (m p:ℝ)*sliceExpectation (u p) (F p))^2 ≤
      (∑ p, (m p:ℝ)^2*mass (u p))*(∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)) := by
  let N : ℝ := ∑ p, (m p:ℝ)^2*mass (u p)
  let C : ℝ := ∑ p, (m p:ℝ)*sliceExpectation (u p) (F p)
  let H : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)
  have hn (t : ℝ) : 0 ≤ N*(t*t)+(-2*C)*t+H := by
    have hp : 0 ≤ ∑ p, ∑ s : Spins (m p), ∫ x,
        mass ((u p).coreSlice s x)*(F p s x-t*(m p:ℝ))^2 :=
      Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ =>
        integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
    have he (p) (s : Spins (m p)) :
        (∫ x, mass ((u p).coreSlice s x)*(F p s x-t*(m p:ℝ))^2) =
        (∫ x, mass ((u p).coreSlice s x)*(F p s x)^2)-
          (2*t*(m p:ℝ))*(∫ x, mass ((u p).coreSlice s x)*F p s x)+
            t^2*(m p:ℝ)^2*(∫ x, mass ((u p).coreSlice s x)) := by
      have hi : Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2-
          (2*t*(m p:ℝ))*(mass ((u p).coreSlice s x)*F p s x)) :=
        (hF2 p s).sub ((hF p s).const_mul (2*t*(m p:ℝ)))
      calc
        _ = ∫ x, (mass ((u p).coreSlice s x)*(F p s x)^2-
            (2*t*(m p:ℝ))*(mass ((u p).coreSlice s x)*F p s x))+
            (t^2*(m p:ℝ)^2)*mass ((u p).coreSlice s x) :=
          integral_congr_ae (Eventually.of_forall (fun x => by ring))
        _ = _ := by
          rw [integral_add hi ((mass_coreSlice_integrable (u p) s).const_mul _),
            integral_sub (hF2 p s) ((hF p s).const_mul _),integral_const_mul,integral_const_mul]
    simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,integral_mass_coreSlice] at hp
    have hc : (∑ p, 2*t*(m p:ℝ)*(∑ s : Spins (m p), ∫ x, mass ((u p).coreSlice s x)*F p s x))=2*t*C := by
      simp only [C,sliceExpectation,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring_nf
    have hN : (∑ p, t^2*(m p:ℝ)^2*mass (u p))=t^2*N := by
      simp only [N,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hc,hN] at hp
    change 0 ≤ H-2*t*C+t^2*N at hp
    nlinarith
  have h := discrim_le_zero hn
  unfold discrim at h
  change C^2 ≤ N*H
  nlinarith

theorem conditionalOutCost_ensemble_lower {P : Type*} [Fintype P] {J : ℕ}
    (S : Nuclei J) (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖)
    (hsupp : ∀ p s, ∀ᵐ x, mass ((u p).coreSlice s x) ≠0 → ∀ i, ‖position x i-y‖ ≤ a) :
    -Real.sqrt ((∑ p, (m p:ℝ)^2*mass (u p))*
      (∑ p, sliceExpectation (u p) (fun s x => (localFarCap S ((u p).coreSlice s x).normalized x y a)^2)))-
        (∑ p, (m p:ℝ)^2*mass (u p))/(3*a) ≤ ∑ p, conditionalOutCost S (u p) := by
  let F := fun p s x => localFarCap S ((u p).coreSlice s x).normalized x y a
  let N : ℝ := ∑ p, (m p:ℝ)^2*mass (u p)
  let C : ℝ := ∑ p, (m p:ℝ)*sliceExpectation (u p) (F p)
  let H : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun s _ => integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (localFarCap_nonneg _ _ _ _ _)))))
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun p _ => mul_nonneg (sq_nonneg _) (mass_nonneg _))
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ =>
    integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have hCsq : C^2 ≤ N*H := by
    apply slice_ensemble_count_cauchy m k u F
    · intro p s
      simpa only [pow_one] using localFarCap_weight_integrable S (u p) s ha y hnuc 1
    · intro p s
      exact localFarCap_weight_integrable S (u p) s ha y hnuc 2
  have hCle : C ≤ Real.sqrt (N*H) := (Real.le_sqrt hC0 (mul_nonneg hN0 hH0)).2 hCsq
  have h := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => conditionalOutCost_lower_local S (u p) ha y hnuc (hsupp p))
  have he : (∑ p, (-(m p:ℝ)*sliceExpectation (u p) (F p)-(m p:ℝ)^2/(3*a)*mass (u p))) = -C-N/(3*a) := by
    simp only [C,N,Finset.sum_sub_distrib,Finset.sum_div,←Finset.sum_neg_distrib,neg_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  change (∑ p, (-(m p:ℝ)*sliceExpectation (u p) (F p)-(m p:ℝ)^2/(3*a)*mass (u p))) ≤ _ at h
  rw [he] at h
  change -Real.sqrt (N*H)-N/(3*a) ≤ _
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma slice_ensemble_cauchy {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (F G : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hF : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2))
    (hG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(G p s x)^2))
    (hFG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x*G p s x))) :
    (∑ p, sliceExpectation (u p) (fun s x => F p s x*G p s x))^2 ≤
      (∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2))*
      (∑ p, sliceExpectation (u p) (fun s x => (G p s x)^2)) := by
  let A : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)
  let B : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (G p s x)^2)
  let C : ℝ := ∑ p, sliceExpectation (u p) (fun s x => F p s x*G p s x)
  have hn (t : ℝ) : 0 ≤ A*(t*t)+(-2*C)*t+B := by
    have hp : 0 ≤ ∑ p, ∑ s : Spins (m p), ∫ x,
        mass ((u p).coreSlice s x)*(t*F p s x-G p s x)^2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
        integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
    have he (p) (s : Spins (m p)) :
        (∫ x, mass ((u p).coreSlice s x)*(t*F p s x-G p s x)^2) =
        t^2*(∫ x, mass ((u p).coreSlice s x)*(F p s x)^2)-
          (2*t)*(∫ x, mass ((u p).coreSlice s x)*(F p s x*G p s x))+
            (∫ x, mass ((u p).coreSlice s x)*(G p s x)^2) := by
      have hi : Integrable (fun x => t^2*(mass ((u p).coreSlice s x)*(F p s x)^2)-
          (2*t)*(mass ((u p).coreSlice s x)*(F p s x*G p s x))) :=
        ((hF p s).const_mul (t^2)).sub ((hFG p s).const_mul (2*t))
      calc
        _ = ∫ x, (t^2*(mass ((u p).coreSlice s x)*(F p s x)^2)-
            (2*t)*(mass ((u p).coreSlice s x)*(F p s x*G p s x)))+
            mass ((u p).coreSlice s x)*(G p s x)^2 :=
          integral_congr_ae (Eventually.of_forall (fun x => by ring))
        _ = _ := by
          rw [integral_add hi (hG p s),integral_sub ((hF p s).const_mul _) ((hFG p s).const_mul _),integral_const_mul,integral_const_mul]
    simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hp
    change 0 ≤ t^2*A-2*t*C+B at hp
    nlinarith
  have h := discrim_le_zero hn
  unfold discrim at h
  change C^2 ≤ A*B
  nlinarith

lemma slice_ensemble_mul_le_sqrt {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (F G : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hF : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2))
    (hG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(G p s x)^2))
    (hFG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x*G p s x))) :
    (∑ p, sliceExpectation (u p) (fun s x => F p s x*G p s x)) ≤
      Real.sqrt ((∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2))*
      (∑ p, sliceExpectation (u p) (fun s x => (G p s x)^2))) :=
  Real.le_sqrt_of_sq_le (slice_ensemble_cauchy m k u F G hF hG hFG)

end Coulomb

end

end OAI
