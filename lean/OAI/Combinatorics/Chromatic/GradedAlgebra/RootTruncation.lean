import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SplitContinuity

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def cut (N : ℕ) (F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun n => if n≤N then coeff n F else 0)
@[simp] lemma coeff_cut (N n : ℕ) (F : PowerSeries A) :
    coeff n (cut N F)=if n≤N then coeff n F else 0 := coeff_mk _ _
lemma coeff_cut_of_le {N n : ℕ} (F : PowerSeries A) (hn : n≤N) :
    coeff n (cut N F)=coeff n F := by simp [hn]
@[simp] lemma constant_cut (N : ℕ) (F : PowerSeries A) :
    constantCoeff (cut N F)=constantCoeff F := by
  rw [←coeff_zero_eq_constantCoeff,coeff_cut,ite_eq_left (Nat.zero_le _),coeff_zero_eq_constantCoeff]
lemma cut_congr {N : ℕ} {F G : PowerSeries A} (h : ∀n≤N,coeff n F=coeff n G) :
    cut N F=cut N G := by
  ext n
  simp only [coeff_cut]
  split_ifs with hn
  · exact h n hn
  · rfl
@[simp] lemma cut_cut (N : ℕ) (F : PowerSeries A) : cut N (cut N F)=cut N F :=
  cut_congr (fun _ hn=>coeff_cut_of_le F hn)
lemma cut_cut_le {N D : ℕ} (hD : D≤N) (F : PowerSeries A) :
    cut D (cut N F)=cut D F :=
  cut_congr (fun _ hn=>coeff_cut_of_le F (hn.trans hD))
lemma cut_zeroFactor (P Q : A→+A) (N : ℕ) (F : PowerSeries A) :
    cut N (PowerSeriesSplit.zeroFactor P Q (cut N F))=
      cut N (PowerSeriesSplit.zeroFactor P Q F) := by
  apply cut_congr
  intro n hn
  exact PowerSeriesSplit.zero_coeff_congr P Q _ _ n (fun j hj=>coeff_cut_of_le F (hj.trans hn))
lemma cut_mul_cut (N : ℕ) (F G : PowerSeries A) :
    cut N (cut N F*cut N G)=cut N (F*G) := by
  apply cut_congr
  intro n hn
  exact FormalLog.mul_coeff_congr _ _ _ _ n
    (fun j hj=>coeff_cut_of_le F (hj.trans hn)) (fun j hj=>coeff_cut_of_le G (hj.trans hn))
lemma cut_list_product {J : Type*} (N : ℕ) (l : List J) (F : J→PowerSeries A) :
    cut N (l.map (fun j=>cut N (F j))).prod=cut N (l.map F).prod := by
  apply cut_congr
  intro n hn
  exact PowerSeriesSplit.product_coeff_congr _ _ l n (fun j hj k hk=>coeff_cut_of_le (F j) (hk.trans hn))
end
end RootTruncation
namespace QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
def completedCut (N : ℕ) (F : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨cut N F.val,by simpa using F.property.1,by
    intro n
    rw [coeff_cut]
    split_ifs
    · exact F.property.2 n
    · intro m hm; rfl⟩
omit [Algebra ℚ R] in
lemma completedCut_supported (N : ℕ) (F : CompletedPositive v Ω C) (S : AddSubmonoid M)
    (hF : ∀n≤N,coeff n F.val∈supportedSubring v Ω S) :
    ∀n,coeff n (completedCut v Ω C N F).val∈supportedSubring v Ω S := by
  intro n
  change coeff n (cut N F.val)∈_
  rw [coeff_cut]
  split_ifs with hn
  · exact hF n hn
  · exact (supportedSubring v Ω S).zero_mem
omit [Algebra ℚ R] in
lemma completedCut_chartZero (N : ℕ) (h : M→+ℝ) (F : CompletedPositive v Ω C) :
    cut N (chartZero v Ω C h (completedCut v Ω C N F)).val=
      cut N (chartZero v Ω C h F).val :=
  cut_zeroFactor _ _ _ _
end
section Continuity
open PowerSeries RootTruncation Filter LaurentPrecision
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M) (l : Filter J)
lemma SeriesGraded.cut (N : ℕ) {F : PowerSeries (Torus v Ω)} (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (cut N F) := by
  intro n
  rw [coeff_cut]
  split_ifs
  · exact hF n
  · intro m hm; rfl
lemma SeriesConverges.cut (N : ℕ) {f : J→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) :
    SeriesConverges v Ω l (fun j=>cut N (f j)) (cut N F) := by
  intro n
  simp only [coeff_cut]
  by_cases hn : n≤N
  · simp only [hn,ite_true]; exact hf n
  · simp only [hn,ite_false]; exact torusConverges_const v Ω l 0
end Continuity
end QuantumTorus
end ElementaryPositivity

end

end OAI
