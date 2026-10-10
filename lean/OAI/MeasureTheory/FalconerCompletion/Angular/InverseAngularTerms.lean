import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularWordOperatorBound
import OAI.MeasureTheory.FalconerCompletion.Estimates.CasimirWords2
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormalizedAngularWord2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereLPolynomial2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped ContDiff
variable {n : ℕ} {α : Type*} [DecidableEq α]

noncomputable def inverseAngularTermsND (j : ℕ) (S : Finset α) :
    List (ℂ × (α → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))) :=
  polynomialLeibnizTermsND (sphereBasisND n) (sphereBPolynomialND n j) S

lemma inverseAngularTermsND_budget (j : ℕ) (S : Finset α)
    {a : ℂ × (α → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))}
    (ha : a ∈ inverseAngularTermsND j S) : ∑ i ∈ S, (a.2 i).length ≤ 2*j :=
  (polynomialLeibnizTermsND_budget _ _ S ha).trans (Nat.mul_le_mul_left 2 (sphereBPolynomialND_degree n j))

lemma inverseAngularTermsND_expansion (j : ℕ) (S : Finset α)
    (f : α → SmoothFunctionND (SphereAmbientND n)) : sphereBND j (smoothFinsetProductND S f) =
      ((inverseAngularTermsND j S).map (fun a =>
        a.1 • smoothFinsetProductND S (fun i => angularWordOperatorND (a.2 i) (f i)))).sum :=
  polynomialLeibnizTermsND_expansion _ _ S f

noncomputable def inverseAngularCostND (n j : ℕ) : ℝ :=
  ((casimirPolynomialTermsND (sphereBasisND n) (sphereBPolynomialND n j)).map (fun a => ‖a.1‖)).sum

lemma inverseAngularCostND_nonneg (n j : ℕ) : 0 ≤ inverseAngularCostND n j :=
  List.sum_nonneg (fun _ ha => by obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha; exact norm_nonneg _)

lemma inverseAngularTermsND_cost (j : ℕ) (S : Finset α) :
    (((inverseAngularTermsND (n := n) j S).map (fun a => ‖a.1‖)).sum) ≤
      inverseAngularCostND n j*(max 1 (S.card:ℝ))^(2*j) := by
  apply (polynomialLeibnizTermsND_cost _ _ S).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_max_left _ _)
    (Nat.mul_le_mul_left 2 (sphereBPolynomialND_degree n j))) (inverseAngularCostND_nonneg n j)

lemma inverseAngularTermsND_normalized_expansion (j : ℕ) (S : Finset α)
    (f : α → SmoothFunctionND (SphereAmbientND n)) (D : α → ℝ) (hD : ∀ i ∈ S, D i ≠ 0) :
    sphereBND j (smoothFinsetProductND S f) =
      ((inverseAngularTermsND j S).map (fun a =>
        (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ)) •
          smoothFinsetProductND S (fun i => normalizedAngularWordND (D i) (a.2 i) (f i)))).sum := by
  rw [inverseAngularTermsND_expansion]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [assignedAngularProductND_normalized S D a.2 f hD,smul_smul]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped ContDiff
variable {V ι α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq α]

lemma orderedAngularAssignmentsND_sublist (S : Finset α) (L : List (V →L[ℝ] V))
    {k : α → List (V →L[ℝ] V)} (hk : k ∈ orderedAngularAssignmentsND S L) (i : α) : List.Sublist (k i) L := by
  induction L generalizing k with
  | nil => simp only [orderedAngularAssignmentsND,List.mem_singleton] at hk; subst k; exact .refl _
  | cons A L ih =>
    obtain ⟨l,hl,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    by_cases hij : i=j
    · subst i
      simpa only [Function.update_self] using (ih hl).cons_cons A
    · simpa only [Function.update_of_ne hij] using (ih hl).cons A

noncomputable def polynomialAngularSubwordsND (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) :
    Finset (List (V →L[ℝ] V)) := by
  classical
  exact ((casimirPolynomialTermsND B p).flatMap (fun a => a.2.sublists)).toFinset

lemma polynomialLeibnizTermsND_subword (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) {a : ℂ × (α → List (V →L[ℝ] V))}
    (ha : a ∈ polynomialLeibnizTermsND B p S) (i : α) :
    a.2 i ∈ polynomialAngularSubwordsND B p := by
  classical
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨b,hb,List.mem_sublists.mpr (orderedAngularAssignmentsND_sublist S b.2 hk i)⟩

lemma polynomialAngularSubwordsND_budget (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    {L : List (V →L[ℝ] V)} (hL : L ∈ polynomialAngularSubwordsND B p) : L.length ≤ 2*p.natDegree := by
  classical
  obtain ⟨b,hb,hL⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hL)
  exact (List.mem_sublists.mp hL).length_le.trans (casimirPolynomialTermsND_budget B p hb)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma angularWordOperatorND_bound (L : List (V →L[ℝ] V)) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A : ℝ) (s : ℕ), 1 ≤ A →
      (∀ j ≤ m+L.length, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b.1 w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (angularWordOperatorND L b).1 w‖ ≤ D*A^(j+(s+L.length)) := by
  induction L generalizing m C with
  | nil =>
    refine ⟨C,hC,?_⟩
    intro b A s hA hb j hj w hw
    simpa [angularWordOperatorND] using hb j (by simpa using hj) w hw
  | cons T L ih =>
    obtain ⟨D,hD,hDb⟩ := ih (m+1) C hC
    obtain ⟨F,hF,hFb⟩ := angularDerivativeND_bound T m D hD
    refine ⟨F,hF,?_⟩
    intro b A s hA hb j hj w hw
    have hb' : ∀ k ≤ m+1+L.length, ∀ u, ‖u‖=1 →
        ‖iteratedFDeriv ℝ k b.1 u‖ ≤ C*A^(k+s) := fun k hk u hu => hb k (by simpa only [List.length_cons] using (show k ≤ m+(L.length+1) by omega)) u hu
    have hh := hFb (angularWordOperatorND L b).1 A (s+L.length)
      (smoothFunctionND_contDiff _) hA (hDb b A s hA hb') j hj w hw
    change ‖iteratedFDeriv ℝ j (angularDerivativeND T (angularWordOperatorND L b).1) w‖ ≤ _
    simpa only [List.length_cons,Nat.add_assoc] using hh

lemma normalizedAngularWordND_bound (L : List (V →L[ℝ] V)) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A : ℝ), 1 ≤ A →
      (∀ j ≤ m+L.length, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b.1 w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L b).1 w‖ ≤ D*A^j := by
  obtain ⟨D,hD,hDb⟩ := angularWordOperatorND_bound L m C hC
  refine ⟨D,hD,?_⟩
  intro b A hA hb j hj w hw
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hh := sphere_derivative_const_mul_bound ((A:ℂ)^L.length)⁻¹
    (smoothFunctionND_contDiff (angularWordOperatorND L b))
    (hDb b A 0 hA (by simpa only [Nat.add_zero] using hb)) j hj w hw
  change ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L b).1 w‖ ≤ _ at hh
  apply hh.trans
  rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hAp]
  simp only [Nat.zero_add]
  rw [pow_add]
  have hn : A^L.length ≠ 0 := pow_ne_zero _ hAp.ne'
  field_simp
  exact le_rfl

lemma normalizedAngularWordND_finite_bound (W : Finset (List (V →L[ℝ] V)))
    (m b : ℕ) (hb : ∀ L ∈ W, L.length ≤ b) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L ∈ W, ∀ (f : SmoothFunctionND V) (A : ℝ), 1 ≤ A →
      (∀ j ≤ m+b, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j f.1 w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L f).1 w‖ ≤ D*A^j := by
  choose D hD hDb using fun L => normalizedAngularWordND_bound (V := V) L m C hC
  refine ⟨∑ L ∈ W,D L,Finset.sum_nonneg (fun L _ => hD L),?_⟩
  intro L hL f A hA hf j hj w hw
  have hh := hDb L f A hA (fun k hk z hz => hf k (by have := hb L hL; omega) z hz) j hj w hw
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun L _ => hD L) hL) (pow_nonneg (by linarith) _)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
