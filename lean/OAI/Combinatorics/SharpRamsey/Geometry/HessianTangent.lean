import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.RichLines

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]
variable {τ R : Type*} [CommRing R] [Algebra K R]
variable [Fintype τ] [DecidableEq τ]
lemma hessian_zero_of_tangent_zero (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)))
    (ht : ∀ a b, (∑ j, ∑ i, MvPolynomial.aeval (branchPoint h)
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) *
        branchTangent h a i * branchTangent h b j) = 0) :
    ∀ a b, MvPowerSeries.pderiv a (MvPowerSeries.pderiv b h) = 0 := by
  intro a b
  have H := deriv2_aeval (MvPowerSeries.pderiv a) (MvPowerSeries.pderiv b)
    (branchPoint h) F
  rw [hroot,map_zero,map_zero] at H
  change 0 = (∑ j, ∑ i, _ * branchTangent h a i * branchTangent h b j) + _ at H
  rw [ht a b,zero_add,branch_second_sum] at H
  exact (IsUnit.mul_right_eq_zero hu).mp H.symm

def scaledTangent (g : Option σ → R) (a : σ) : Option σ → R :=
  fun o => o.elim (-g (some a)) (fun i => if i = a then g none else 0)

noncomputable def flatnessPolynomial (F : MvPolynomial (Option σ) K) (a b : σ) :
    MvPolynomial (Option σ) K :=
  ∑ j, ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv j F) *
    scaledTangent (fun o => MvPolynomial.pderiv o F) a i *
    scaledTangent (fun o => MvPolynomial.pderiv o F) b j
omit [Fintype σ] in

lemma aeval_scaledTangent (x : Option σ → R) (F : MvPolynomial (Option σ) K)
    (a : σ) (i : Option σ) :
    MvPolynomial.aeval x (scaledTangent (fun o => MvPolynomial.pderiv o F) a i) =
    scaledTangent (fun o => MvPolynomial.aeval x (MvPolynomial.pderiv o F)) a i := by
  cases i with
  | none => simp [scaledTangent]
  | some i => by_cases hi : i = a <;> simp [scaledTangent,hi]

lemma first_branch_derivative (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (a : σ) :
    MvPowerSeries.pderiv a (MvPolynomial.aeval (branchPoint h) F) =
      MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F) *
        MvPowerSeries.pderiv a h +
      MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv (some a) F) := by
  rw [deriv_aeval,Fintype.sum_option]
  simp [branchPoint,MvPowerSeries.pderiv_X,Pi.single_apply]

lemma scaled_branch_tangent (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (a : σ) (i : Option σ) :
    MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F) *
      branchTangent h a i =
      scaledTangent (fun o => MvPolynomial.aeval (branchPoint h)
        (MvPolynomial.pderiv o F)) a i := by
  cases i with
  | none =>
    have H := first_branch_derivative F h a
    rw [hroot,map_zero] at H
    change _ * MvPowerSeries.pderiv a h = -_
    exact eq_neg_of_add_eq_zero_left H.symm
  | some i => simp [branchTangent,branchPoint,scaledTangent,MvPowerSeries.pderiv_X,
      Pi.single_apply,mul_ite]

lemma flatness_root_implies_hessian_zero (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)))
    (hflat : ∀ a b, MvPolynomial.aeval (branchPoint h) (flatnessPolynomial F a b) = 0) :
    ∀ a b, MvPowerSeries.pderiv a (MvPowerSeries.pderiv b h) = 0 := by
  apply hessian_zero_of_tangent_zero F h hroot hu
  intro a b
  let z := MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)
  have H := hflat a b
  simp only [flatnessPolynomial,map_sum,map_mul,aeval_scaledTangent] at H
  have he : MvPolynomial.aeval (branchPoint h) (flatnessPolynomial F a b) =
      z*z*(∑ j, ∑ i, MvPolynomial.aeval (branchPoint h)
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) *
          branchTangent h a i * branchTangent h b j) := by
    simp only [flatnessPolynomial,map_sum,map_mul,aeval_scaledTangent,
      ← scaled_branch_tangent F h hroot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z]
    ring
  rw [hflat a b] at he
  exact (IsUnit.mul_right_eq_zero (hu.mul hu)).mp he.symm

end SharpLogRamsey.FlatnessCore

namespace SharpLogRamsey.LocalFlatness
open SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
omit [Fintype σ] [DecidableEq σ] in

lemma branch_constantCoeff (h : MvPowerSeries σ K)
    (hh : MvPowerSeries.constantCoeff h = 0) (F : MvPolynomial (Option σ) K) :
    MvPowerSeries.constantCoeff (MvPolynomial.aeval (branchPoint h) F) =
      MvPolynomial.constantCoeff F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [← MvPowerSeries.c_eq_algebraMap]
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => cases i <;> simp [branchPoint,hh]
omit [Fintype σ] [DecidableEq σ] in

lemma rename_aeval (lin : MvPolynomial σ K) (G : MvPolynomial (Option σ) K) :
    MvPolynomial.rename Option.some (MvPolynomial.aeval
      (fun o => o.elim lin MvPolynomial.X) G) =
    MvPolynomial.aeval (fun o => o.elim (MvPolynomial.rename Option.some lin)
      (fun i => MvPolynomial.X (some i))) G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => cases i <;> simp only [map_mul,MvPolynomial.aeval_X,hf,
      Option.elim_none,Option.elim_some,MvPolynomial.rename_X]

omit [Fintype σ] [DecidableEq σ] in

lemma plane_factor_of_zero (lin : MvPolynomial σ K) (G : MvPolynomial (Option σ) K)
    (hz : MvPolynomial.aeval (fun o => o.elim lin MvPolynomial.X) G = 0) :
    MvPolynomial.X none - MvPolynomial.rename Option.some lin ∣ G := by
  let L : MvPolynomial (Option σ) K := MvPolynomial.X none-MvPolynomial.rename Option.some lin
  let I := Ideal.span ({L} : Set (MvPolynomial (Option σ) K))
  have he : MvPolynomial.aeval (fun o => o.elim (MvPolynomial.rename Option.some lin)
      (fun i => MvPolynomial.X (some i))) G = 0 := by
    rw [← rename_aeval,hz,map_zero]
  have H := aeval_sub_mem I (fun o => MvPolynomial.X o)
    (fun o => o.elim (MvPolynomial.rename Option.some lin) (fun i => MvPolynomial.X (some i)))
    (fun o => by cases o; exact Ideal.subset_span (Set.mem_singleton L); simp) G
  rw [he,sub_zero,MvPolynomial.aeval_X_left_apply] at H
  exact Ideal.mem_span_singleton.mp H

theorem exists_plane_factor_of_flatness {p : ℕ} [CharP K p]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hdiv : F ∣ G) (hF : MvPolynomial.constantCoeff F = 0)
    (hDz : MvPolynomial.constantCoeff (MvPolynomial.pderiv none G) ≠ 0)
    (hflat : ∀ a b, F ∣ flatnessPolynomial G a b) :
    ∃ lin : MvPolynomial σ K, lin.totalDegree ≤ 1 ∧
      MvPolynomial.constantCoeff lin = 0 ∧
      MvPolynomial.X none-MvPolynomial.rename Option.some lin ∣ G := by
  obtain ⟨J,hJ⟩ := hdiv
  have hG : MvPolynomial.constantCoeff G = 0 := by simp [hJ,hF]
  have hJ0 : MvPolynomial.constantCoeff J ≠ 0 := by
    intro hz
    apply hDz
    simp [hJ,Derivation.leibniz,smul_eq_mul,hF,hz]
  obtain ⟨h,hh,hr⟩ := ImplicitBranch.exists_formal_branch G hG hDz
  change MvPolynomial.aeval (branchPoint h) G = 0 at hr
  have hJu : IsUnit (MvPolynomial.aeval (branchPoint h) J) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,branch_constantCoeff h hh,isUnit_iff_ne_zero]
    exact hJ0
  have hFr : MvPolynomial.aeval (branchPoint h) F = 0 := by
    rw [hJ,map_mul] at hr
    exact (IsUnit.mul_left_eq_zero hJu).mp hr
  have hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none G)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,branch_constantCoeff h hh,isUnit_iff_ne_zero]
    exact hDz
  have hf : ∀ a b, MvPolynomial.aeval (branchPoint h) (flatnessPolynomial G a b) = 0 := by
    intro a b
    obtain ⟨V,hV⟩ := hflat a b
    simp [hV,hFr]
  have hess := flatness_root_implies_hessian_zero G h hr hu hf
  have hz := flat_branch_zero_plane G hdeg h hr hess
  refine ⟨MvPowerSeries.truncTotal 2 h,?_,?_,plane_factor_of_zero _ G hz⟩
  · have H := MvPowerSeries.totalDegree_truncTotal_lt h (by norm_num : (2:ℕ) ≠ 0)
    omega
  · simpa [MvPowerSeries.constantCoeff_truncTotal_eq_ite] using hh

end SharpLogRamsey.LocalFlatness

open scoped BigOperators
open MvPolynomial Finsupp
namespace SharpLogRamsey.PolynomialGeometry
variable {σ K : Type*} [Field K]

lemma totalDegree_pderiv_lt (F : MvPolynomial σ K) (i : σ)
    (hi : pderiv i F ≠ 0) : (pderiv i F).totalDegree < F.totalDegree := by
  classical
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup _ (MvPolynomial.support_nonempty.mpr hi)
    (fun d : σ →₀ ℕ => d.sum fun _ e => e)
  have hc : F.coeff (d+Finsupp.single i 1) ≠ 0 := by
    have H := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_pderiv] at H
    exact (mul_ne_zero_iff.mp H).1
  have H := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  change Finsupp.degree (d+Finsupp.single i 1) ≤ F.totalDegree at H
  have H' : d.degree+1 ≤ F.totalDegree := by
    simpa only [map_add, Finsupp.degree_single] using H
  change (pderiv i F).support.sup (fun d : σ →₀ ℕ => d.sum fun _ e => e) < F.totalDegree
  rw [he]
  exact H'

lemma not_dvd_pderiv (F : MvPolynomial σ K) (i : σ) (hi : pderiv i F ≠ 0) :
    ¬F ∣ pderiv i F := by
  intro h
  exact (totalDegree_pderiv_lt F i hi).not_ge
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hi)

lemma not_dvd_squarefree_derivative (G F : MvPolynomial σ K)
    (hs : Squarefree G) (hF : Irreducible F) (hd : F ∣ G) (i : σ)
    (hi : pderiv i F ≠ 0) : ¬ F ∣ pderiv i G := by
  obtain ⟨J,rfl⟩ := hd
  intro h
  have hp : Prime F := irreducible_iff_prime.mp hF
  have hn : ¬F ∣ J := by
    intro hj
    exact hF.not_isUnit (hs F (mul_dvd_mul dvd_rfl hj))
  have he : pderiv i (F*J) = pderiv i F*J+F*pderiv i J := by
    rw [MvPolynomial.pderiv_mul]
  rw [he,dvd_add_left (dvd_mul_right F _)] at h
  rcases hp.dvd_mul.mp h with h|h
  · exact not_dvd_pderiv F i hi h
  · exact hn h

lemma totalDegree_pos_of_irreducible (F : MvPolynomial σ K) (hF : Irreducible F) :
    0 < F.totalDegree := by
  by_contra! h
  have he : F = C (F.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
  have hc : F.coeff 0 ≠ 0 := by intro hc; apply hF.ne_zero; rw [he,hc,map_zero]
  exact hF.not_isUnit (isUnit_iff_totalDegree_of_isReduced.mpr
    ⟨isUnit_iff_ne_zero.mpr hc,Nat.eq_zero_of_le_zero h⟩)

lemma exists_nonzero_pderiv {p : ℕ} [CharP K p]
    (F : MvPolynomial σ K) (hpos : 0 < F.totalDegree) (hdeg : F.totalDegree < p) :
    ∃ i, pderiv i F ≠ 0 := by
  classical
  have hF : F ≠ 0 := by intro he; simp [he] at hpos
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun d : σ →₀ ℕ => d.sum fun _ e => e)
  change F.totalDegree = d.degree at he
  have hdz : d ≠ 0 := by intro hd0; simp [hd0] at he; omega
  obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hdz
  have hi0 : 0 < d i := Nat.pos_of_ne_zero hi
  have hdi : d i ≤ d.degree := by
    rw [Finsupp.degree_apply]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi)
  have hcast : (d i : K) ≠ 0 := by
    rw [ne_eq,CharP.cast_eq_zero_iff K p]
    intro H
    have := Nat.le_of_dvd hi0 H
    omega
  have hs : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hij : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi0)
    · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
  refine ⟨i,fun hz => ?_⟩
  have hc := congrArg (fun poly : MvPolynomial σ K => poly.coeff (d-Finsupp.single i 1)) hz
  rw [coeff_pderiv,tsub_add_cancel_of_le hs,AddMonoidAlgebra.coeff_zero] at hc
  have hc' : F.coeff d * (d i : K) = 0 := by
    simpa [Finsupp.coe_tsub,Pi.sub_apply,Finsupp.single_eq_same,
      Nat.cast_sub (show 1 ≤ d i by omega)] using hc
  exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcast) hc'

variable [Finite σ] [IsAlgClosed K]

lemma exists_zero_not_zero (F D : MvPolynomial σ K)
    (hF : Irreducible F) (hD : ¬F ∣ D) :
    ∃ x : σ → K, aeval x F = 0 ∧ aeval x D ≠ 0 := by
  classical
  let I : Ideal (MvPolynomial σ K) := Ideal.span {F}
  let : I.IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr
    (irreducible_iff_prime.mp hF)
  by_contra! H
  have hv : D ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro x hx
    apply H x
    exact hx F (Ideal.subset_span (Set.mem_singleton F))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hv
  exact hD (Ideal.mem_span_singleton.mp hv)

lemma exists_nonsingular_factor_zero (G F : MvPolynomial σ K)
    (hs : Squarefree G) (hF : Irreducible F) (hd : F ∣ G) (i : σ)
    (hi : pderiv i F ≠ 0) :
    ∃ x : σ → K, aeval x F = 0 ∧ aeval x (pderiv i G) ≠ 0 :=
  exists_zero_not_zero F _ hF (not_dvd_squarefree_derivative G F hs hF hd i hi)

end SharpLogRamsey.PolynomialGeometry

open scoped BigOperators
open MvPolynomial
namespace SharpLogRamsey.Translation
variable {σ K : Type*} [Field K]

noncomputable def translate (x : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => X i+C (x i)

@[simp] lemma translate_X (x : σ → K) (i : σ) : translate x (X i) = X i+C (x i) := by
  simp [translate]
@[simp] lemma translate_C (x : σ → K) (c : K) : translate x (C c) = C c := by
  simp [translate]

lemma pderiv_translate (x : σ → K) (i : σ) (F : MvPolynomial σ K) :
    pderiv i (translate x F) = translate x (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f j hf =>
    simp only [map_mul,translate_X,MvPolynomial.pderiv_mul,map_add,hf,
      MvPolynomial.pderiv_X,MvPolynomial.pderiv_C,add_zero]
    simp only [Pi.single_apply]
    split_ifs <;> simp

lemma constantCoeff_translate (x : σ → K) (F : MvPolynomial σ K) :
    constantCoeff (translate x F) = aeval x F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp [hf]

@[simp] lemma translate_neg_translate (x : σ → K) (F : MvPolynomial σ K) :
    translate (-x) (translate x F) = F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp [hf]

@[simp] lemma translate_translate_neg (x : σ → K) (F : MvPolynomial σ K) :
    translate x (translate (-x) F) = F := by
  simpa using translate_neg_translate (-x) F

lemma translate_injective (x : σ → K) : Function.Injective (translate x) :=
  fun _ _ h => by simpa using congrArg (translate (-x)) h

lemma translate_dvd_iff (x : σ → K) (F G : MvPolynomial σ K) :
    translate x F ∣ translate x G ↔ F ∣ G := by
  constructor
  · intro h
    simpa using map_dvd (translate (-x)) h
  · exact map_dvd _

lemma translate_nonunit (x : σ → K) {F : MvPolynomial σ K} (h : ¬IsUnit F) :
    ¬IsUnit (translate x F) := by
  intro hu
  apply h
  simpa using hu.map (translate (-x))
end SharpLogRamsey.Translation

namespace SharpLogRamsey.GlobalFlatness
open MvPolynomial SharpLogRamsey.FlatnessCore SharpLogRamsey.Translation
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

lemma totalDegree_translate_le {τ : Type*} [Fintype τ] (x : τ → K) (F : MvPolynomial τ K) :
    (Translation.translate x F).totalDegree ≤ F.totalDegree := by
  classical
  apply totalDegree_aeval_linear
  intro i
  apply (totalDegree_add _ _).trans
  simp

lemma translate_flatness (x : Option σ → K) (G : MvPolynomial (Option σ) K) (a b : σ) :
    Translation.translate x (flatnessPolynomial G a b) = flatnessPolynomial (Translation.translate x G) a b := by
  simp only [flatnessPolynomial,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have ht : ∀ c k, Translation.translate x (scaledTangent (fun o => pderiv o G) c k) =
      scaledTangent (fun o => pderiv o (Translation.translate x G)) c k := by
    intro c k
    cases k with
    | none => simp [scaledTangent,pderiv_translate]
    | some k => by_cases h : k = c <;> simp [scaledTangent,h,pderiv_translate]
  rw [ht,ht,← pderiv_translate,← pderiv_translate]

theorem plane_factor_of_flatness {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hDzF : pderiv none F ≠ 0) (hflat : ∀ a b, F ∣ flatnessPolynomial G a b) :
    ∃ L : MvPolynomial (Option σ) K, ¬IsUnit L ∧ L.totalDegree ≤ 1 ∧ L ∣ G := by
  obtain ⟨x,hx,hDx⟩ := PolynomialGeometry.exists_nonsingular_factor_zero
    G F hs hF hdiv none hDzF
  have hpl := LocalFlatness.exists_plane_factor_of_flatness
    (Translation.translate x G) (Translation.translate x F)
    ((totalDegree_translate_le x G).trans_lt hdeg) (map_dvd (Translation.translate x) hdiv)
    (by rwa [constantCoeff_translate])
    (by rwa [pderiv_translate,constantCoeff_translate])
    (fun a b => by rw [← translate_flatness]; exact map_dvd (Translation.translate x) (hflat a b))
  obtain ⟨lin,hlin,hlin0,hlind⟩ := hpl
  let L : MvPolynomial (Option σ) K := X none-rename Option.some lin
  have hL0 : constantCoeff L = 0 := by simp [L,hlin0]
  have hLu : ¬IsUnit L := by
    intro hu
    have H := hu.map (constantCoeff : MvPolynomial (Option σ) K →+* K)
    rw [hL0] at H
    exact not_isUnit_zero H
  have hLd : L.totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_X none).le
    · exact (totalDegree_rename_le _ _).trans hlin
  refine ⟨Translation.translate (-x) L,translate_nonunit _ hLu,
    (totalDegree_translate_le _ _).trans hLd,?_⟩
  simpa only [translate_neg_translate] using map_dvd (Translation.translate (-x)) hlind

lemma nonplane_factor_not_flat {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hDzF : pderiv none F ≠ 0)
    (hn : ∀ L : MvPolynomial (Option σ) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ a b, ¬ F ∣ flatnessPolynomial G a b := by
  by_contra! h
  obtain ⟨L,hu,hd,hdv⟩ := plane_factor_of_flatness G F hdeg hs hF hdiv hDzF h
  exact hu (hn L hdv hd)
end SharpLogRamsey.GlobalFlatness

open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]

noncomputable def combinationMap (Q : ι → MvPolynomial σ K) :
    (ι → K) →ₗ[K] MvPolynomial σ K :=
  ∑ i, (LinearMap.proj i).smulRight (Q i)
omit [Infinite K] in

@[simp] lemma combinationMap_apply (Q : ι → MvPolynomial σ K) (c : ι → K) :
    combinationMap Q c = ∑ i, c i • Q i := by simp [combinationMap]

theorem exists_coprime_combination (G : MvPolynomial σ K) (hG : G ≠ 0)
    (Q : ι → MvPolynomial σ K)
    (h : ∀ F : MvPolynomial σ K, Irreducible F → F ∣ G → ∃ i, ¬F ∣ Q i) :
    ∃ c : ι → K, IsRelPrime G (∑ i, c i • Q i) := by
  classical
  let : NormalizationMonoid (MvPolynomial σ K) := UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  let S := (normalizedFactors G).toFinset
  let P (F : S) : Submodule K (ι → K) :=
    ((Ideal.span ({F.val} : Set (MvPolynomial σ K))).restrictScalars K).comap (combinationMap Q)
  have hp : ∀ F, P F ≠ ⊤ := by
    intro F ht
    have hfm : F.val ∈ normalizedFactors G := Multiset.mem_toFinset.mp F.property
    obtain ⟨i,hi⟩ := h F.val (prime_of_normalized_factor _ hfm).irreducible
      (dvd_of_mem_normalizedFactors hfm)
    have H : Pi.single i 1 ∈ P F := ht ▸ Submodule.mem_top
    change combinationMap Q (Pi.single i 1) ∈ Ideal.span ({F.val} : Set (MvPolynomial σ K)) at H
    simp [Pi.single_apply] at H
    exact hi (Ideal.mem_span_singleton.mp H)
  obtain ⟨c,hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hp
  refine ⟨c,(isRelPrime_iff_no_prime_factors hG).mpr ?_⟩
  intro F hFG hFQ hFp
  obtain ⟨J,hJ,hassoc⟩ := exists_mem_normalizedFactors_of_dvd hG hFp.irreducible hFG
  apply hc ⟨J,Multiset.mem_toFinset.mpr hJ⟩
  change combinationMap Q c ∈ Ideal.span ({J} : Set (MvPolynomial σ K))
  rw [combinationMap_apply,Ideal.mem_span_singleton]
  exact hassoc.dvd_iff_dvd_left.mp hFQ
end SharpLogRamsey.CoprimeCombination
end
end
end

end OAI
