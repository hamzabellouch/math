import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootTruncation

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def patchTop (n : ℕ) (G F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun j=>if j≤n then coeff j G else if j=n+1 then coeff j F else 0)
@[simp] lemma coeff_patchTop (n j : ℕ) (G F : PowerSeries A) :
    coeff j (patchTop n G F)=if j≤n then coeff j G else if j=n+1 then coeff j F else 0 :=
  coeff_mk _ _
lemma patchTop_low (n : ℕ) (G F : PowerSeries A) (j : ℕ) (hj : j≤n) :
    coeff j (patchTop n G F)=coeff j G := by simp [hj]
@[simp] lemma patchTop_last (n : ℕ) (G F : PowerSeries A) :
    coeff (n+1) (patchTop n G F)=coeff (n+1) F := by simp
@[simp] lemma patchTop_constant (n : ℕ) (G F : PowerSeries A) :
    constantCoeff (patchTop n G F)=constantCoeff G := by
  rw [←coeff_zero_eq_constantCoeff,patchTop_low n G F 0 (Nat.zero_le _),coeff_zero_eq_constantCoeff]
end
end RootTruncation
namespace QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation LaurentPrecision Filter
noncomputable section
variable {M I A J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
lemma SeriesConverges.zero_middle (l : Filter J) (h : M→+ℝ)
    {f : J→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : ∀i,SeriesGraded v Ω C (f i))
    (hF : SeriesGraded v Ω C F) :
    SeriesConverges v Ω l
      (fun j=>zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (f j))
      (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) F) := by
  have H:=filter_factors_converge v Ω C l (fun m=>0<h m) hf hg hF
  exact (filter_factors_converge v Ω C l (fun m=>h m=0) H.2
    (fun j n=>by simpa only [rightFactor,coeff_mk] using (filter_pair_graded v Ω C (fun m=>0<h m) (f j) (hg j) n).2)
    (fun n=>by simpa only [rightFactor,coeff_mk] using (filter_pair_graded v Ω C (fun m=>0<h m) F hF n).2)).1
lemma SeriesGraded.patchTop (n : ℕ) {G F : PowerSeries (Torus v Ω)}
    (hG : SeriesGraded v Ω C G) (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (patchTop n G F) := by
  intro j
  rw [coeff_patchTop]
  split_ifs
  · exact hG j
  · exact hF j
  · intro m hm; rfl
lemma SeriesConverges.patchTop (l : Filter J) (n : ℕ)
    {g : J→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hg : SeriesConverges v Ω l (fun j=>RootTruncation.cut n (g j)) (RootTruncation.cut n F)) :
    SeriesConverges v Ω l (fun j=>patchTop n (g j) F) (RootTruncation.cut (n+1) F) := by
  intro k
  simp only [coeff_patchTop,coeff_cut]
  by_cases hk : k≤n
  · simp only [hk,ite_true,show k≤n+1 by omega]
    simpa only [coeff_cut,hk,ite_true] using hg k
  · by_cases he : k=n+1
    · simp only [he,Nat.not_succ_le_self,ite_false,ite_true,le_refl]
      exact torusConverges_const v Ω l _
    · simp only [hk,he,ite_false,show ¬k≤n+1 by omega]
      exact torusConverges_const v Ω l _
lemma zero_middle_off (h : M→+ℝ) (F : PowerSeries (Torus v Ω)) (n : ℕ) (m : M) (hm : h m≠0) :
    coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) F) m=0 := by
  simp only [zeroFactor,leftFactor,coeff_mk]
  rw [pairCoefficients]
  exact Finsupp.filter_apply_neg _ _ hm

lemma joint_middle_isolated_through (h : M→+ℝ) (l : List A)
    (f g : A→PowerSeries (Torus v Ω)) (n : ℕ)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hlow : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a))
    (hlast : ∀a∈l,∀m,h m=0 → coeff (n+1) (f a) m=coeff (n+1) (g a) m) :
    RootTruncation.cut (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map f).prod)=
      RootTruncation.cut (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map g).prod) := by
  apply cut_congr
  intro k hk
  by_cases hkn : k≤n
  · exact zero_coeff_congr _ _ _ _ k (fun j hj=>product_coeff_congr f g l j
      (fun a ha i hi=>hlow a ha i (hi.trans (hj.trans hkn))))
  · have he : k=n+1:=by omega
    subst k
    apply Finsupp.ext
    intro m
    by_cases hm : h m=0
    · exact joint_middle_monomial_unaffected v Ω h f g l n m hf hg hlow (fun a ha=>hlast a ha m hm)
    · rw [zero_middle_off v Ω h _ n m hm,zero_middle_off v Ω h _ n m hm]
end
end QuantumTorus
end ElementaryPositivity

end

end OAI
