import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.Outside
import OAI.Combinatorics.RamseyFive.Decoding.RichCenters

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def localLines (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (x : ℙ K V) :=
  L.filter fun A => x ∈ richCenters S O δ a A

noncomputable def badCenters (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (D : ℝ) :=
  Q.filter fun x => D ≤ ((localLines S O δ a L x).card:ℝ)

lemma sum_localLines_le (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) :
    ∑ x ∈ Q, (localLines S O δ a L x).card ≤
      ∑ A ∈ L, (richCenters S O δ a A).card := by
  simp_rw [localLines,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  rw [←Finset.card_filter]
  have hs : Q.filter (fun x => x ∈ richCenters S O δ a A) ⊆ richCenters S O δ a A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  exact Finset.card_le_card hs

lemma badCenters_mass_le (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (D : ℝ) :
    ((badCenters S O δ a L Q D).card:ℝ)*D ≤
      ∑ A ∈ L, ((richCenters S O δ a A).card:ℝ) := by
  let E := badCenters S O δ a L Q D
  calc
    _ = ∑ _x ∈ E, D := by simp only [Finset.sum_const,nsmul_eq_mul]; rfl
    _ ≤ ∑ x ∈ E, ((localLines S O δ a L x).card:ℝ) :=
      Finset.sum_le_sum fun _ hx => (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ Q, ((localLines S O δ a L x).card:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := by exact_mod_cast sum_localLines_le S O δ a L Q

lemma exception_fraction (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (q n χ C : ℝ) (hq : 0<q) (hn : 0<n) (ha : 0<a)
    (hglobal : (∑ A ∈ L, ((richCenters S O δ a A).card:ℝ))*a^2 ≤ C*q^2) :
    ((badCenters S O δ a L Q (q^4/n^2*Real.exp χ/a^100)).card:ℝ) ≤
      n*(C*(n/q^2)*Real.exp (-χ)*a^98) := by
  let e : ℝ := (badCenters S O δ a L Q (q^4/n^2*Real.exp χ/a^100)).card
  have hh := (mul_le_mul_of_nonneg_right
    (badCenters_mass_le S O δ a L Q (q^4/n^2*Real.exp χ/a^100)) (sq_nonneg a)).trans hglobal
  have heq : (q^4/n^2*Real.exp χ/a^100)*a^2 = q^4/n^2*Real.exp χ/a^98 := by
    field_simp
  have hm : e*(q^4/n^2*Real.exp χ/a^98) ≤ C*q^2 := by
    change e*(q^4/n^2*Real.exp χ/a^100)*a^2 ≤ _ at hh
    rwa [mul_assoc,heq] at hh
  have hpos : 0<q^4/n^2*Real.exp χ/a^98 := by positivity
  have hdiv := (le_div_iff₀ hpos).mpr hm
  have hnorm : C*q^2/(q^4/n^2*Real.exp χ/a^98) =
      n*(C*(n/q^2)*Real.exp (-χ)*a^98) := by
    rw [Real.exp_neg]
    field_simp
  exact hdiv.trans_eq hnorm

variable {I : Type*} [LinearOrder I]

theorem captured_exception_fraction (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X : Finset (ℙ K V))
    (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2)
    (J M : ℕ) (hM : 0 < M) (hJM : J ≤ M)
    (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card)
    (O : ℙ K V → Finset (ℙ K V))
    (hO : ∀ x, ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (Q : Finset (ℙ K V)) (q n n' a χ : ℝ) (hq : 0<q) (hn : 0<n) (hn' : 0<n')
    (hX : (X.card:ℝ)≤n) (hcmp : n≤4*n')
    (ha : 2*(q/n')*M ≤ a) (ha' : a ≤ 4*(q/n')*M) :
    ((badCenters (X \ remaining F hF (fun i => flatPoints (P i)) X J) O (q/n') a L Q
      (q^4/n^2*Real.exp χ/a^100)).card:ℝ) ≤
      n*(3072*(n/q^2)*Real.exp (-χ)*a^98) := by
  have hd : 0<q/n' := div_pos hq hn'
  have ha0 : 0<a := (by positivity : 0<2*(q/n')*M).trans_le ha
  apply exception_fraction _ _ _ _ L Q q n χ 3072 hq hn ha0
  have hh := captured_rich_centers F hF P X hP L hL J M hM hJM hJq O hO (q/n') a hd ha ha'
  have hratio : (q/n')*X.card ≤ 4*q := by
    have hc := hX.trans hcmp
    have hm := mul_le_mul_of_nonneg_left hc hd.le
    have he : q/n'*(4*n')=4*q := by field_simp
    exact hm.trans_eq he
  have hs := pow_le_pow_left₀ (by positivity : 0≤(q/n')*X.card) hratio 2
  have hfinal : 192*(q/n')^2*(X.card:ℝ)^2 ≤ 3072*q^2 := by nlinarith
  exact hh.trans hfinal

end SharpRamseyFive.GlobalRadial
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_filter_card (S O : Finset (ℙ K V)) (A : Submodule K V) :
    ((outsideAt x S O).filter fun y => y.val.submodule ≤ A).card =
      ((S \ (O ∪ {x})).filter fun y => y.submodule ≤ A).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    have hm : y.val ∈ S \ O := Finset.mem_subtype.mp hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton]
    exact ⟨⟨(Finset.mem_sdiff.mp hm).1,not_or.mpr
      ⟨(Finset.mem_sdiff.mp hm).2,Ne.symm y.property⟩⟩,hyA⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
    have hn : x ≠ y := by
      intro he
      exact hyO (Finset.mem_union_right _ (Finset.mem_singleton.mpr he.symm))
    refine ⟨⟨y,hn⟩,Finset.mem_filter.mpr ⟨?_,hyA⟩,rfl⟩
    exact Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr
      ⟨hyS,fun h => hyO (Finset.mem_union_left _ h)⟩)

lemma richRadials_le_localLines (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (hδ : 0<δ) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) :
    (ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/δ⌉₊).card ≤
      (localLines S O δ a L x).card := by
  let E := ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/δ⌉₊
  let G := localLines S O δ a L x
  let f (l : E) : G := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hL l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      have hr' : a/δ ≤ ((RadialLine.trainingOnLine (outsideAt x S (O x)) l.val).card:ℝ) :=
        Nat.ceil_le.mp hr
      have hh := (div_le_iff₀ hδ).mp hr'
      rw [mul_comm] at hh
      change a ≤ δ*((((outsideAt x S (O x)).filter
        fun y => y.val.submodule ≤ l.val.val)).card:ℝ) at hh
      rwa [outsideAt_filter_card] at hh⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : G => z.val) he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

theorem score_pairs_off_radial_exception (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H∈F,Incident x H)
    (a D : ℝ) (ha : 0≤a) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) L Q D) :
    ((Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F => a≤
      WeightedPrograms.strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ)*a^2 ≤
      D*((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2+
      2*(δ:ℝ)^2*((outsideAt x S (O x)).card:ℝ)^2*((Nat.card K:ℝ)+1)^2 := by
  have hlocal : ((localLines S O δ (a/2) L x).card:ℝ)<D := by
    by_contra hn
    exact hgood (Finset.mem_filter.mpr ⟨hx,le_of_not_gt hn⟩)
  have he : a/(2*(δ:ℝ))=(a/2)/(δ:ℝ) := by ring
  have hr := richRadials_le_localLines x S O δ (a/2) (by exact_mod_cast hδ) L hL
  have hr' : ((ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/(2*(δ:ℝ))⌉₊).card:ℝ) ≤ D := by
    rw [he]
    have hrR : ((ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈(a/2)/(δ:ℝ)⌉₊).card:ℝ) ≤
        (localLines S O δ (a/2) L x).card := by exact_mod_cast hr
    exact hrR.trans hlocal.le
  have hh := score_pair_count_four x hdim (outsideAt x S (O x)) δ hδ F hF a ha
  apply hh.trans
  gcongr

end SharpRamseyFive.ScoreGeometry

end OAI
