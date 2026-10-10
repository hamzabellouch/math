import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.HighExceptions
import OAI.Combinatorics.RamseyFive.Probability.HighOrSmall
import OAI.Combinatorics.RamseyFive.Geometry.RadialAlternatives

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma plane_threshold_exp {σ g n q : ℝ} (hn : n=Real.exp (3*σ/2+g))
    (hq : q=Real.exp σ) :
    n^(4/3:ℝ)/q*Real.exp (-g/5)=Real.exp (σ+17*g/15) := by
  rw [hn,hq,←Real.exp_mul,←Real.exp_sub,←Real.exp_add]
  congr 1
  ring

lemma plane_list_cutoff {σ g n q δ k j : ℝ}
    (hn : n=Real.exp (3*σ/2+g)) (hq : q=Real.exp σ)
    (hk : k=Real.exp (σ+17*g/15)) (hg : 100≤g) (hghi : g≤2*σ)
    (hδ : 0≤δ) (_hj : 0≤j) (hlen : j*k≤n) (hscale : n*δ≤4*q) :
    8*δ*(j+1)≤Real.exp (-g/20) := by
  have hn0 : 0<n := hn▸Real.exp_pos _
  have hk0 : 0<k := hk▸Real.exp_pos _
  have hjδ : j*δ≤4*q/k := by
    apply (le_div_iff₀ hk0).mpr
    calc
      _ = (j*k)*δ := by ring
      _ ≤ n*δ := mul_le_mul_of_nonneg_right hlen hδ
      _ ≤ _ := hscale
  have hδ' : δ≤4*q/n := (le_div_iff₀ hn0).mpr (by simpa only [mul_comm δ] using hscale)
  have hqk : q/k=Real.exp (-17*g/15) := by
    rw [hq,hk,←Real.exp_sub]
    congr 1
    ring
  have hqn : q/n≤Real.exp (-17*g/15) := by
    rw [hq,hn,←Real.exp_sub]
    exact Real.exp_le_exp.mpr (by linarith only [hghi,hg])
  have h₁ : j*δ≤4*Real.exp (-17*g/15) := by
    simpa only [mul_div_assoc,hqk] using hjδ
  have h₂ : δ≤4*Real.exp (-17*g/15) := by
    apply hδ'.trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hqn (by norm_num : (0:ℝ)≤4)
  have hpay : (64:ℝ)≤Real.exp (13*g/12) := by
    linarith only [Real.add_one_le_exp (13*g/12),hg]
  calc
    _ ≤ 64*Real.exp (-17*g/15) := by linarith only [h₁,h₂]
    _ ≤ Real.exp (13*g/12)*Real.exp (-17*g/15) :=
      mul_le_mul_of_nonneg_right hpay (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add];congr 1;ring

end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.TrainingCells
open scoped Classical
variable {A : Type*} [DecidableEq A]

lemma sdiff_clip (S O : Finset A) : S\(S∩O)=S\O := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_inter]
  tauto

lemma sdiff_union_clip (S O : Finset A) (x : A) : S\((S∩O)∪{x})=S\(O∪{x}) := by
  ext y
  simp only [Finset.mem_sdiff,Finset.mem_inter,Finset.mem_union]
  tauto

end SharpRamseyFive.TrainingCells

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial TrainingCells
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma outsideAt_clip (x : ℙ K V) (S O : Finset (ℙ K V)) :
    outsideAt x S (S∩O)=outsideAt x S O := by
  simp only [outsideAt,sdiff_clip]

lemma richCenters_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (A : Submodule K V) :
    richCenters S (fun x => S∩O x) δ a A=richCenters S O δ a A := by
  simp only [richCenters,sdiff_union_clip]

lemma localLines_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (x : ℙ K V) :
    localLines S (fun x => S∩O x) δ a Lines x=localLines S O δ a Lines x := by
  simp only [localLines,richCenters_clip]

lemma badCenters_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (D : ℝ) :
    badCenters S (fun x => S∩O x) δ a Lines Q D=badCenters S O δ a Lines Q D := by
  simp only [badCenters,localLines_clip]

lemma radialExceptions_clip (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ) :
    radialExceptions S (fun x => S∩O x) δ Lines Q q n χ=radialExceptions S O δ Lines Q q n χ := by
  simp only [radialExceptions,badCenters_clip]

lemma badCenters_threshold_mono (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) {D E : ℝ} (hDE : D≤E) :
    badCenters S O δ a Lines Q E⊆badCenters S O δ a Lines Q D := by
  intro x hx
  obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,hDE.trans he⟩

lemma radialExceptions_normalization (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (q χ m n : ℝ) (hm : 0 < m) (hmn : m ≤ n) :
    radialExceptions S O δ Lines Q q m χ⊆radialExceptions S O δ Lines Q q n χ := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨i,hi,badCenters_threshold_mono S O δ _ Lines Q ?_ hx⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm) ((sq_le_sq₀ hm.le (hm.le.trans hmn)).mpr hmn)

end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreScalars
open scoped Topology
open Filter

lemma nonsmall_strength {q n a g : ℝ} (hq : 0<q) (hn : n=q^2*Real.exp g)
    (hg : 0≤g) (ha : 0≤a) (hlarge : q^2<n*a^99) :
    Real.exp (-g/10)<a := by
  by_contra hh
  have ha' : a≤Real.exp (-g/10) := le_of_not_gt hh
  have hp := pow_le_pow_left₀ ha ha' 99
  have he : (Real.exp (-g/10))^99≤Real.exp (-g) := by
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hn0 : 0≤n := by rw [hn];positivity
  have hx := mul_le_mul_of_nonneg_left (hp.trans he) hn0
  have heq : n*Real.exp (-g)=q^2 := by rw [hn,mul_assoc,←Real.exp_add];simp
  rw [heq] at hx
  exact (not_lt_of_ge hx) hlarge

lemma high_exception_scalar {q n a g χ : ℝ} (hq : 0<q) (hn : n=q^2*Real.exp g)
    (hg : 0≤g) (hχ : 0≤χ) (ha : 0<a) (ha2 : a≤2)
    (haexp : Real.exp (-g/10)≤a) (hnq : n≤q^3) :
    3145728*q^2/a^2+(n^2*a^3/q^3)*Real.exp (-χ)+36864*q^2*Real.exp (-2*χ)≤
      n*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  have hn0 : 0≤n := by rw [hn];positivity
  have hqn : q^2≤n := by rw [hn];nlinarith [Real.one_le_exp_iff.mpr hg,sq_nonneg q]
  have hp : Real.exp (-g/5)≤a^2 := by
    have hh := pow_le_pow_left₀ (Real.exp_nonneg (-g/10)) haexp 2
    have he : (Real.exp (-g/10))^2=Real.exp (-g/5) := by
      rw [←Real.exp_nat_mul];congr 1;norm_num;ring
    rwa [he] at hh
  have heq : n*Real.exp (-(4/5:ℝ)*g)*Real.exp (-g/5)=q^2 := by
    rw [hn,mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
    rw [show g+(-(4/5:ℝ)*g + -g/5)=0 by ring,Real.exp_zero,mul_one]
  have hfirst : q^2/a^2≤n*Real.exp (-(4/5:ℝ)*g) := by
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    calc
      q^2 = n*Real.exp (-(4/5:ℝ)*g)*Real.exp (-g/5) := heq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have ha3 : a^3≤8 := by
    have hh := pow_le_pow_left₀ ha.le ha2 3
    norm_num at hh
    exact hh
  have hsecond : n^2*a^3/q^3≤8*n := by
    apply (div_le_iff₀ (pow_pos hq 3)).mpr
    calc
      n^2*a^3 ≤ n^2*8 := mul_le_mul_of_nonneg_left ha3 (sq_nonneg n)
      _ = 8*n*n := by ring
      _ ≤ 8*n*q^3 := mul_le_mul_of_nonneg_left hnq (by positivity)
      _ = _ := by ring
  have hthird : q^2*Real.exp (-2*χ)≤n*Real.exp (-χ) := by
    apply mul_le_mul hqn (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) hn0
  have h1 := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0:ℝ)≤3145728)
  have h2 := mul_le_mul_of_nonneg_right hsecond (Real.exp_nonneg (-χ))
  have h3 := mul_le_mul_of_nonneg_left hthird (by norm_num : (0:ℝ)≤36864)
  convert add_le_add (add_le_add h1 h2) h3 using 1 <;> first | rfl | ring

end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type} [LinearOrder I]

noncomputable def highPlaneExceptions (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V)) (Planes : Finset (Submodule K V))
    (j : ℕ) (δ : ℝ≥0) (χ : ℝ) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  (strengthDyads S.card δ).biUnion fun i =>
    if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
    then highExceptions F hF Flat X Planes j ((δ:ℝ)*2^i) χ Q else ∅

lemma off_highPlaneExceptions (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (j : ℕ) (δ : ℝ≥0) (χ : ℝ) (Q : Finset (ℙ K V))
    (x : ℙ K V) (hx : x∉highPlaneExceptions F hF Flat X S Planes j δ χ Q) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉highExceptions F hF Flat X Planes j ((δ:ℝ)*2^i) χ Q := by
  intro i hi hlarge hh
  apply hx
  exact Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,by simpa only [ite_eq_left hlarge] using hh⟩

theorem highPlaneExceptions_card (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V))
    (hFlat : ∀i∈F,finrank K (Flat i)=4)
    (hcover : ∀A : Submodule K V,finrank K A=4 → ∃i∈F,Flat i=A)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀A∈Planes,finrank K A=3)
    (j : ℕ) (δ : ℝ≥0) (hδ : 0<δ) (χ g : ℝ) (hg : 0≤g) (hχ : 0≤χ)
    (hn : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤X.card) (Q : Finset (ℙ K V)) :
    ((highPlaneExceptions F hF Flat X S Planes j δ χ Q).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*
        (3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hn0 : (0:ℝ)<X.card := by rw [hn];positivity
  let e : ℝ := 3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)
  have he : 0≤e := by dsimp [e];positivity
  have hh := biUnion_card_real_le (strengthDyads S.card δ)
    (fun i => if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
      then highExceptions F hF Flat X Planes j ((δ:ℝ)*2^i) χ Q else ∅)
    (e:=X.card*e) (by
      intro i hi
      split_ifs with hlarge
      · have ha : 0<(δ:ℝ)*2^i := by positivity
        have ha2 := (Finset.mem_filter.mp hi).2
        have hbudget := (ScoreScalars.high_or_small hq.le hn0 ha.le hhigh).resolve_right (not_le_of_gt hlarge)
        have hcount := high_exceptions_card F hF Flat X hFlat hcover Planes hPlanes j
          ((δ:ℝ)*2^i) χ Q (by exact_mod_cast hn0) ha ha2 hori hbudget hχ
        have hax := ScoreScalars.nonsmall_strength hq hn hg ha.le hlarge
        exact hcount.trans (ScoreScalars.high_exception_scalar hq hn hg hχ ha ha2 hax.le hcap)
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity)
  apply hh.trans
  have hc : ((strengthDyads S.card δ).card:ℝ)≤(Nat.clog 2 S.card:ℝ)+1 := by
    exact_mod_cast strengthDyads_card S.card δ
  calc
    _ ≤ ((Nat.clog 2 S.card:ℝ)+1)*(X.card*e) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by dsimp [e];ring

end SharpRamseyFive.ScoreGeometry

end OAI
