import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.HessianTangent

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]
omit [Infinite K] in
lemma totalDegree_combination_le (Q : ι → MvPolynomial σ K) (c : ι → K) (D : ℕ)
    (h : ∀ i, (Q i).totalDegree ≤ D) :
    (∑ i, c i • Q i).totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (h i)
end SharpLogRamsey.CoprimeCombination

namespace SharpLogRamsey.NonplaneCertificate
open MvPolynomial FlatnessCore PolynomialGeometry
variable {K : Type*} [Field K]
noncomputable section

abbrev Index := (Option (Fin 2) ≃ Fin 3) × Fin 2 × Fin 2

noncomputable def flatFamily (G : MvPolynomial (Fin 3) K) (i : Index) :
    MvPolynomial (Fin 3) K :=
  renameEquiv K i.1 (flatnessPolynomial ((renameEquiv K i.1).symm G) i.2.1 i.2.2)

lemma squarefree_equiv {A B : Type*} [Monoid A] [Monoid B]
    (e : A ≃* B) {f : A} (h : Squarefree f) : Squarefree (e f) := by
  intro x hx
  have H : e.symm x*e.symm x ∣ f := by
    simpa only [map_mul,e.symm_apply_apply] using map_dvd e.symm hx
  have H' := (h _ H).map e
  simpa only [e.apply_symm_apply] using H'

lemma totalDegree_equiv_le {α β : Type*} (e : α ≃ β) (F : MvPolynomial α K) :
    (renameEquiv K e F).totalDegree ≤ F.totalDegree := totalDegree_rename_le _ _

lemma pderiv_equiv {α β : Type*} (e : α ≃ β) (F : MvPolynomial α K) (i : α) :
    pderiv (e i) (renameEquiv K e F) = renameEquiv K e (pderiv i F) :=
  pderiv_rename e.injective i F

lemma nonplane_witness {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Fin 3) K) (hG : G ≠ 0) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ i : Index, ¬F ∣ flatFamily G i := by
  obtain ⟨i,hi⟩ := exists_nonzero_pderiv F
    (totalDegree_pos_of_irreducible F hF)
    ((totalDegree_le_of_dvd_of_isDomain hdiv hG).trans_lt hdeg)
  let e : Option (Fin 2) ≃ Fin 3 := (finSuccEquiv' i).symm
  let E := renameEquiv K e
  have hen : e none = i := finSuccEquiv'_symm_none i
  have hdn : pderiv none (E.symm F) ≠ 0 := by
    have he := pderiv_equiv e.symm F i
    have hnone : e.symm i = none := by rw [← hen]; simp
    rw [hnone] at he
    change pderiv none (E.symm F) = E.symm (pderiv i F) at he
    rw [he]
    exact fun h => hi (E.symm.injective (h.trans (map_zero E.symm).symm))
  obtain ⟨a,b,hab⟩ := GlobalFlatness.nonplane_factor_not_flat
    (E.symm G) (E.symm F)
    ((totalDegree_equiv_le e.symm G).trans_lt hdeg)
    (squarefree_equiv E.symm.toMulEquiv hs)
    ((MulEquiv.irreducible_iff E.symm).mpr hF) (map_dvd E.symm hdiv) hdn
    (fun L hd hdl => by
      have hL := hn (E L) (by simpa only [E.apply_symm_apply] using map_dvd E hd)
        ((totalDegree_equiv_le e L).trans hdl)
      exact (isUnit_map_iff E L).mp hL)
  refine ⟨⟨e,a,b⟩,fun hd => hab ?_⟩
  have H := map_dvd E.symm hd
  change E.symm F ∣ E.symm (E (flatnessPolynomial (E.symm G) a b)) at H
  simpa only [E.symm_apply_apply] using H

lemma totalDegree_partial_le {α : Type*} (F : MvPolynomial α K) (i : α) :
    (pderiv i F).totalDegree ≤ F.totalDegree := by
  by_cases h : pderiv i F = 0
  · simp [h]
  · exact (totalDegree_pderiv_lt F i h).le

lemma totalDegree_tangent_le (G : MvPolynomial (Option (Fin 2)) K) (a : Fin 2)
    (i : Option (Fin 2)) :
    (scaledTangent (fun i => pderiv i G) a i).totalDegree ≤ G.totalDegree := by
  cases i with
  | none => simpa [scaledTangent] using totalDegree_partial_le G (some a)
  | some i =>
    by_cases hi : i = a
    · simpa [scaledTangent,hi] using totalDegree_partial_le G none
    · simp [scaledTangent,hi]

lemma totalDegree_flatness_le (G : MvPolynomial (Option (Fin 2)) K) (a b : Fin 2) :
    (flatnessPolynomial G a b).totalDegree ≤ 3*G.totalDegree := by
  apply totalDegree_finsetSum_le
  intro j hj
  apply totalDegree_finsetSum_le
  intro i hi
  have H := totalDegree_mul (pderiv i (pderiv j G)*scaledTangent (fun i => pderiv i G) a i)
    (scaledTangent (fun i => pderiv i G) b j)
  have H' := totalDegree_mul (pderiv i (pderiv j G)) (scaledTangent (fun i => pderiv i G) a i)
  have H'' := (totalDegree_partial_le (pderiv j G) i).trans (totalDegree_partial_le G j)
  have H1 := totalDegree_tangent_le G a i
  have H2 := totalDegree_tangent_le G b j
  omega

lemma totalDegree_family_le (G : MvPolynomial (Fin 3) K) (i : Index) :
    (flatFamily G i).totalDegree ≤ 3*G.totalDegree := by
  exact (totalDegree_equiv_le _ _).trans ((totalDegree_flatness_le _ _ _).trans
    (Nat.mul_le_mul_left _ (totalDegree_equiv_le _ _)))

theorem exists_coprime_flat_combination {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G : MvPolynomial (Fin 3) K) (hG : G ≠ 0) (hdeg : G.totalDegree < p)
    (hs : Squarefree G)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ c : Index → K, IsRelPrime G (∑ i, c i • flatFamily G i) ∧
      (∑ i, c i • flatFamily G i).totalDegree ≤ 3*G.totalDegree := by
  obtain ⟨c,hc⟩ := CoprimeCombination.exists_coprime_combination G hG (flatFamily G)
    (fun F hF hd => nonplane_witness G F hG hdeg hs hF hd hn)
  exact ⟨c,hc,CoprimeCombination.totalDegree_combination_le _ _ _ (totalDegree_family_le G)⟩
end
end SharpLogRamsey.NonplaneCertificate

open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.LineFlatness
variable {K σ R : Type*} [Field K] [Fintype σ] [DecidableEq σ]
  [CommRing R] [Algebra K R]

lemma deriv_aeval (D : Derivation K R R) (x : σ → R) (F : MvPolynomial σ K) :
    D (MvPolynomial.aeval x F) =
      ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) * D (x i) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.aeval_X,Derivation.leibniz,smul_eq_mul,
      map_add,MvPolynomial.pderiv_X]
    simp only [
      add_mul,Finset.sum_add_distrib]
    rw [hf,Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      ring

lemma deriv2_aeval (D E : Derivation K R R) (x : σ → R) (F : MvPolynomial σ K) :
    D (E (MvPolynomial.aeval x F)) =
      (∑ j, ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j F)) * D (x i) * E (x j)) +
      ∑ j, MvPolynomial.aeval x (MvPolynomial.pderiv j F) * D (E (x j)) := by
  rw [deriv_aeval E,map_sum]
  simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [deriv_aeval D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def restrictLine (x v : σ → K) (F : MvPolynomial σ K) : Polynomial K :=
  aeval (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
omit [Fintype σ] [DecidableEq σ] in

lemma eval_restrictLine (x v : σ → K) (F : MvPolynomial σ K) (t : K) :
    (restrictLine x v F).eval t = eval (fun i => x i + v i*t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [restrictLine]
  | add f g hf hg => simp_all [restrictLine]
  | mul_X f i hf => simp_all [restrictLine]

lemma derivative_restrictLine (x v : σ → K) (F : MvPolynomial σ K) :
    Polynomial.derivative (restrictLine x v F) =
      ∑ i, restrictLine x v (pderiv i F) * Polynomial.C (v i) := by
  have H := deriv_aeval Polynomial.derivative'
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
  simpa [restrictLine] using H

lemma line_tangent (x v : σ → K) (F : MvPolynomial σ K)
    (h : restrictLine x v F = 0) :
    ∑ i, eval x (pderiv i F)*v i = 0 := by
  have H := congrArg (Polynomial.eval (0 : K)) (derivative_restrictLine x v F)
  simpa [h,Polynomial.eval_finsetSum,eval_restrictLine] using H.symm

lemma line_hessian (x v : σ → K) (F : MvPolynomial σ K)
    (h : restrictLine x v F = 0) :
    ∑ j, ∑ i, eval x (pderiv i (pderiv j F))*v i*v j = 0 := by
  have H := deriv2_aeval Polynomial.derivative' Polynomial.derivative'
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
  change Polynomial.derivative (Polynomial.derivative (restrictLine x v F)) = _ at H
  simp only [show ∀ i, Polynomial.derivative'
      (Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) = Polynomial.C (v i)
      from fun i => by simp, show ∀ i, Polynomial.derivative' (Polynomial.C (v i)) = 0
      from fun i => by simp,mul_zero,sum_const_zero,add_zero] at H
  change Polynomial.derivative (Polynomial.derivative (restrictLine x v F)) =
    ∑ j, ∑ i, restrictLine x v (pderiv i (pderiv j F)) * Polynomial.C (v i) * Polynomial.C (v j) at H
  have E := congrArg (Polynomial.eval (0 : K)) H
  simpa [h,Polynomial.eval_finsetSum,eval_restrictLine] using E.symm
omit [Fintype σ] in

lemma pderiv_swap (F : MvPolynomial σ K) (i j : σ) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f k hf =>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pderiv_X,Pi.single_apply,apply_ite,hi,hj,hf,add_comm,add_left_comm]
    all_goals split_ifs <;> simp_all

lemma quadratic_vandermonde (v : Fin 3 → Fin 2 → K) :
    (Matrix.of (fun (i j : Fin 3) => ![(v i 0)^2, v i 0*v i 1, (v i 1)^2] j)).det =
      (v 0 0*v 1 1-v 0 1*v 1 0) * (v 0 0*v 2 1-v 0 1*v 2 0) *
      (v 1 0*v 2 1-v 1 1*v 2 0) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  dsimp
  ring

theorem binary_quadratic_three (v : Fin 3 → Fin 2 → K) (A B C : K)
    (h01 : v 0 0*v 1 1-v 0 1*v 1 0 ≠ 0)
    (h02 : v 0 0*v 2 1-v 0 1*v 2 0 ≠ 0)
    (h12 : v 1 0*v 2 1-v 1 1*v 2 0 ≠ 0)
    (hv : ∀ i, A*(v i 0)^2+B*(v i 0*v i 1)+C*(v i 1)^2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  let M : Matrix (Fin 3) (Fin 3) K :=
    Matrix.of (fun i j => ![(v i 0)^2,v i 0*v i 1,(v i 1)^2] j)
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,quadratic_vandermonde]
    exact mul_ne_zero (mul_ne_zero h01 h02) h12
  have hm : M.mulVec ![A,B,C] = 0 := by
    ext i
    simpa [M,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc] using hv i
  have E := congrArg (Matrix.mulVec M⁻¹) hm
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M hdet,
    Matrix.one_mulVec,Matrix.mulVec_zero] at E
  exact ⟨congrFun E 0,congrFun E 1,congrFun E 2⟩

noncomputable def hessian (x : σ → K) (F : MvPolynomial σ K) (u v : σ → K) : K :=
  ∑ j, ∑ i, eval x (pderiv i (pderiv j F))*u i*v j
omit [DecidableEq σ] in

lemma hessian_smul_left (x : σ → K) (F : MvPolynomial σ K) (a : K) (u v : σ → K) :
    hessian x F (a • u) v = a*hessian x F u v := by
  simp only [hessian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1; ext j
  congr 1; ext i
  ring
omit [DecidableEq σ] in

lemma hessian_smul_right (x : σ → K) (F : MvPolynomial σ K) (a : K) (u v : σ → K) :
    hessian x F u (a • v) = a*hessian x F u v := by
  simp only [hessian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1; ext j
  congr 1; ext i
  ring
omit [DecidableEq σ] in

lemma hessian_add_left (x : σ → K) (F : MvPolynomial σ K) (u v w : σ → K) :
    hessian x F (u+v) w = hessian x F u w+hessian x F v w := by
  simp [hessian,mul_add,add_mul,sum_add_distrib]
omit [DecidableEq σ] in

lemma hessian_add_right (x : σ → K) (F : MvPolynomial σ K) (u v w : σ → K) :
    hessian x F u (v+w) = hessian x F u v+hessian x F u w := by
  simp [hessian,mul_add,sum_add_distrib]

lemma hessian_symm (x : σ → K) (F : MvPolynomial σ K) (u v : σ → K) :
    hessian x F u v = hessian x F v u := by
  unfold hessian
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [pderiv_swap F i j]
  ring

def scaledTangent (g : Option (Fin 2) → K) (a : Fin 2) : Option (Fin 2) → K :=
  fun o => o.elim (-g (some a)) (fun i => if i = a then g none else 0)

lemma tangent_expansion (g v : Option (Fin 2) → K)
    (hv : ∑ i, g i*v i = 0) :
    g none • v = v (some 0) • scaledTangent g 0 + v (some 1) • scaledTangent g 1 := by
  ext i
  cases i with
  | none =>
    simp only [Fintype.sum_option,Fin.sum_univ_two] at hv
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,scaledTangent,Option.elim_none]
    linear_combination hv
  | some i => fin_cases i <;> simp [scaledTangent,mul_comm]

lemma tangent_projection_independent (g : Option (Fin 2) → K) (hg : g none ≠ 0)
    (v : Fin 2 → Option (Fin 2) → K) (hv : ∀ a, ∑ i, g i*v a i = 0)
    (hli : LinearIndependent K v) :
    LinearIndependent K (fun a i => v a (some i)) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  apply hli c
  ext i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Fin.sum_univ_two,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at h0 h1 ⊢
  cases i with
  | some i => fin_cases i <;> assumption
  | none =>
    apply (mul_left_cancel₀ hg)
    rw [mul_zero]
    have h2 := hv 0
    have h3 := hv 1
    simp only [Fintype.sum_option,Fin.sum_univ_two] at h2 h3
    linear_combination c 0*h2+c 1*h3-g (some 0)*h0-g (some 1)*h1

lemma tangent_projection_det (g : Option (Fin 2) → K) (hg : g none ≠ 0)
    (u v : Option (Fin 2) → K) (hu : ∑ i, g i*u i = 0) (hv : ∑ i, g i*v i = 0)
    (hli : LinearIndependent K ![u,v]) :
    u (some 0)*v (some 1)-u (some 1)*v (some 0) ≠ 0 := by
  have hl := tangent_projection_independent g hg ![u,v]
    (fun i => by fin_cases i <;> assumption) hli
  let M : Matrix (Fin 2) (Fin 2) K := Matrix.of (fun i j => ![u,v] i (some j))
  have hM : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hl
  have hD := (Matrix.isUnit_iff_isUnit_det M).mp hM
  simpa [M,Matrix.det_fin_two,isUnit_iff_ne_zero] using hD

theorem three_lines_flat (F : MvPolynomial (Option (Fin 2)) K)
    (x : Option (Fin 2) → K) (v : Fin 3 → Option (Fin 2) → K)
    (h2 : (2 : K) ≠ 0) (hz : eval x (pderiv none F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2]) :
    ∀ a b, hessian x F (scaledTangent (fun i => eval x (pderiv i F)) a)
      (scaledTangent (fun i => eval x (pderiv i F)) b) = 0 := by
  let g : Option (Fin 2) → K := fun i => eval x (pderiv i F)
  let t := scaledTangent g
  have ht (i : Fin 3) : ∑ a, g a*v i a = 0 := line_tangent x (v i) F (hlines i)
  have hH (i : Fin 3) : hessian x F (v i) (v i) = 0 := line_hessian x (v i) F (hlines i)
  have he (i : Fin 3) := tangent_expansion g (v i) (ht i)
  have hq (i : Fin 3) :
      hessian x F (t 0) (t 0)*(v i (some 0))^2 +
        (2*hessian x F (t 0) (t 1))*(v i (some 0)*v i (some 1)) +
      hessian x F (t 1) (t 1)*(v i (some 1))^2 = 0 := by
    have E : hessian x F (g none • v i) (g none • v i) = 0 := by
      rw [hessian_smul_left,hessian_smul_right,hH,mul_zero,mul_zero]
    rw [he,hessian_add_left,hessian_add_right,hessian_add_right] at E
    simp only [hessian_smul_left,hessian_smul_right] at E
    rw [hessian_symm x F (t 1) (t 0)] at E
    linear_combination E
  obtain ⟨h00,h01',h11⟩ := binary_quadratic_three
    (fun i a => v i (some a)) _ _ _
    (tangent_projection_det g hz _ _ (ht 0) (ht 1) h01)
    (tangent_projection_det g hz _ _ (ht 0) (ht 2) h02)
    (tangent_projection_det g hz _ _ (ht 1) (ht 2) h12) hq
  have h01z := (mul_eq_zero.mp h01').resolve_left h2
  intro a b
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01z
  · exact (hessian_symm x F (t 1) (t 0)).trans h01z
  · exact h11

lemma three_lines_all_tangents (F : MvPolynomial (Option (Fin 2)) K)
    (x : Option (Fin 2) → K) (v : Fin 3 → Option (Fin 2) → K)
    (h2 : (2 : K) ≠ 0) (hz : eval x (pderiv none F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2])
    (u w : Option (Fin 2) → K)
    (hu : ∑ i, eval x (pderiv i F)*u i = 0)
    (hw : ∑ i, eval x (pderiv i F)*w i = 0) : hessian x F u w = 0 := by
  let g := fun i => eval x (pderiv i F)
  have H := three_lines_flat F x v h2 hz hlines h01 h02 h12
  apply mul_left_cancel₀ (mul_ne_zero hz hz)
  rw [mul_zero]
  calc
    _ = hessian x F (g none • u) (g none • w) := by
      rw [hessian_smul_left,hessian_smul_right]; ring
    _ = 0 := by
      rw [tangent_expansion g u hu,tangent_expansion g w hw,
        hessian_add_left,hessian_add_right,hessian_add_right]
      simp only [hessian_smul_left,hessian_smul_right,g,H,mul_zero,add_zero]

variable {τ : Type*} [Fintype τ] [DecidableEq τ]
omit [DecidableEq σ] [DecidableEq τ] in
lemma hessian_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x u v : τ → K) :
    hessian x (renameEquiv K e F) u v = hessian (x ∘ e) F (u ∘ e) (v ∘ e) := by
  unfold hessian
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro j hj
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro i hi
  simp only [renameEquiv_apply,pderiv_rename e.injective,eval_rename,Function.comp_apply]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma restrictLine_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x v : τ → K) :
    restrictLine x v (renameEquiv K e F) = restrictLine (x ∘ e) (v ∘ e) F := by
  simp only [restrictLine,renameEquiv_apply,aeval_rename,Function.comp_def]
omit [DecidableEq σ] [DecidableEq τ] in

lemma tangent_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x v : τ → K) :
    (∑ i, eval x (pderiv i (renameEquiv K e F))*v i) =
      ∑ i, eval (x ∘ e) (pderiv i F)*(v ∘ e) i := by
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro i hi
  simp only [renameEquiv_apply,pderiv_rename e.injective,eval_rename,Function.comp_apply]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma independent_rename (e : σ ≃ τ) (u v : τ → K)
    (h : LinearIndependent K ![u,v]) : LinearIndependent K ![u ∘ e,v ∘ e] := by
  let E := LinearEquiv.funCongrLeft K K e
  have H := h.map' E.toLinearMap E.ker
  change LinearIndependent K (fun i => ![u,v] i ∘ e) at H
  convert H using 1
  ext i j
  fin_cases i <;> rfl

theorem three_lines_tangent_zero (F : MvPolynomial (Fin 3) K)
    (x : Fin 3 → K) (v : Fin 3 → Fin 3 → K)
    (h2 : (2 : K) ≠ 0) (hn : ∃ i, eval x (pderiv i F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2])
    (u w : Fin 3 → K) (hu : ∑ i, eval x (pderiv i F)*u i = 0)
    (hw : ∑ i, eval x (pderiv i F)*w i = 0) : hessian x F u w = 0 := by
  obtain ⟨i,hi⟩ := hn
  let e : Option (Fin 2) ≃ Fin 3 := (finSuccEquiv' i).symm
  have hen : e none = i := finSuccEquiv'_symm_none i
  have hc (z : Fin 3 → K) : (z ∘ e) ∘ e.symm = z := by ext j; simp
  have hz : eval (x ∘ e) (pderiv none (renameEquiv K e.symm F)) ≠ 0 := by
    have he := pderiv_rename e.symm.injective i F
    have hnone : e.symm i = none := by rw [← hen]; simp
    rw [hnone] at he
    simpa only [renameEquiv_apply,he,eval_rename,hc] using hi
  have H := three_lines_all_tangents (renameEquiv K e.symm F) (x ∘ e)
    (fun j => v j ∘ e) h2 hz
    (fun j => by simpa only [restrictLine_rename,hc] using hlines j)
    (independent_rename e _ _ h01) (independent_rename e _ _ h02)
    (independent_rename e _ _ h12) (u ∘ e) (w ∘ e)
    (by simpa only [tangent_rename,hc] using hu)
    (by simpa only [tangent_rename,hc] using hw)
  simpa only [hessian_rename,hc] using H

end SharpLogRamsey.LineFlatness

namespace SharpLogRamsey.RichLinePolynomial
open MvPolynomial Finset
open FlatnessCore NonplaneCertificate
variable {K : Type*} [Field K]

end SharpLogRamsey.RichLinePolynomial
end
end
end

end OAI
