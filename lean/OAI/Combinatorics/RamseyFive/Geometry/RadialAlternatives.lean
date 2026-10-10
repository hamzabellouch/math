import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.OutsideCard
import OAI.Combinatorics.RamseyFive.Decoding.RichCentersCard

namespace OAI

namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma localLines_mass (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (x : ℙ K V) [Fintype (RadialLine x)] :
    ((localLines S O δ a Lines x).card:ℝ)*a≤(δ:ℝ)*S.card := by
  let E := localLines S O δ a Lines x
  let X := outsideAt x S (O x)
  let f (l : E) : RadialLine x := ⟨l.val,hLines _ (Finset.mem_filter.mp l.property).1,
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp (Finset.mem_filter.mp l.property).2).1⟩
  have hi : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun r : RadialLine x => r.val) h)
  have ha (l : E) : a≤(radialWeight x X δ (f l):ℝ) := by
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp l.property).2).2
    change a≤(δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule≤l.val).card:ℝ)
    rwa [outsideAt_filter_card]
  have hsum : (∑l : RadialLine x,(radialWeight x X δ l:ℝ))=(δ:ℝ)*X.card := by
    have hh := mass_inFlat x X δ ⊤ le_top
    simpa [PoissonScore.mass,RadialLine.inFlat] using hh
  calc
    _ = ∑_l : E,a := by simp [E]
    _ ≤ ∑l : E,(radialWeight x X δ (f l):ℝ) := Finset.sum_le_sum fun l _ => ha l
    _ = ∑l ∈ Finset.univ.image f,(radialWeight x X δ l:ℝ) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hi h
    _ ≤ ∑l : RadialLine x,(radialWeight x X δ l:ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => NNReal.coe_nonneg _)
    _ = (δ:ℝ)*X.card := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast outsideAt_card_le x S (O x)) δ.coe_nonneg

lemma no_radial_exception_of_mass (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) {a D : ℝ} (ha : 0<a) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (Q : Finset (ℙ K V))
    [∀x : ℙ K V,Fintype (RadialLine x)] (hD : (δ:ℝ)*S.card<D*a) :
    badCenters S O δ a Lines Q D=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := (Finset.mem_filter.mp hx).2
  have hh := (mul_le_mul_of_nonneg_right hx' ha.le).trans (localLines_mass S O δ a Lines hLines x)
  exact (not_lt_of_ge hh) hD

lemma radial_exception_scale (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) {a D : ℝ} (hD : 0<D) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (Q : Finset (ℙ K V))
    (hne : (badCenters S O δ a Lines Q D).Nonempty) :
    a≤(δ:ℝ)*((Nat.card K:ℝ)+1) := by
  obtain ⟨x,hx⟩ := hne
  have hx' := (Finset.mem_filter.mp hx).2
  have hE : (localLines S O δ a Lines x).Nonempty := Finset.card_pos.mp (by
    have ht : (0:ℝ)<(localLines S O δ a Lines x).card := hD.trans_le hx'
    exact_mod_cast ht)
  obtain ⟨l,hl⟩ := hE
  obtain ⟨hll,hlx⟩ := Finset.mem_filter.mp hl
  obtain ⟨hxl,ha⟩ := Finset.mem_filter.mp hlx
  have hc : ((S\(O x∪{x})).filter fun y => y.submodule≤l).card≤Nat.card K+1 := by
    exact RichPlaneGeometry.card_filter_finrank_le_two _ _ (le_of_eq (hLines l hll))
  exact ha.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) δ.coe_nonneg)

lemma radial_exception_uniform (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) {a q n χ C : ℝ} (hq : 0<q) (hn : 0<n) (ha : 0<a) (ha1 : a≤1)
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hC : 0≤C) (hscale : n*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*q^2)
    (hglobal : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2≤C*q^2) :
    ((badCenters S O δ a Lines Q (q^4/n^2*Real.exp χ/a^100)).card:ℝ)≤
      n*(8*C*Real.exp (-χ)) := by
  by_cases he : (badCenters S O δ a Lines Q (q^4/n^2*Real.exp χ/a^100)).Nonempty
  · have hcap := radial_exception_scale S O δ (by positivity) Lines hLines Q he
    have hna : n*a≤8*q^2 := (mul_le_mul_of_nonneg_left hcap hn.le).trans hscale
    have hpow : a^98≤a := by
      calc
        _ = a*a^97 := by ring
        _ ≤ a*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha.le ha1) ha.le
        _ = a := mul_one a
    have hratio : (n/q^2)*a^98≤8 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
      exact (mul_le_mul_of_nonneg_left hpow hn.le).trans hna
    have hh := exception_fraction S O δ a Lines Q q n χ C hq hn ha hglobal
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hn.le
    calc
      C*(n/q^2)*Real.exp (-χ)*a^98 = C*((n/q^2)*a^98)*Real.exp (-χ) := by ring
      _ ≤ C*8*Real.exp (-χ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) (Real.exp_nonneg _)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end SharpRamseyFive.GlobalRadial
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma biUnion_card_real_le {ι A : Type*} [DecidableEq A] (I : Finset ι) (E : ι→Finset A)
    {e : ℝ} (hE : ∀i∈I,((E i).card:ℝ)≤e) :
    ((I.biUnion E).card:ℝ)≤I.card*e := by
  calc
    _ ≤ ∑i∈I,((E i).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : (I.biUnion E).card≤_)
    _ ≤ ∑_i∈I,e := Finset.sum_le_sum hE
    _ = _ := by simp

noncomputable def strengthDyads (m : ℕ) (δ : ℝ≥0) : Finset ℕ :=
  (Finset.range (Nat.clog 2 m+1)).filter fun i => (δ:ℝ)*2^i≤2

lemma strengthDyads_card (m : ℕ) (δ : ℝ≥0) :
    (strengthDyads m δ).card≤Nat.clog 2 m+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma boundedOverlapDyads_subset (x : ℙ K V) (S O : Finset (ℙ K V)) (δ : ℝ≥0) :
    boundedOverlapDyads x (outsideAt x S O) δ 2⊆strengthDyads S.card δ := by
  intro i hi
  obtain ⟨hi,hcap⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨?_,hcap⟩
  apply Finset.mem_range.mpr
  exact (Finset.mem_range.mp hi).trans_le
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (outsideAt_card_le x S O)) 1)

noncomputable def radialExceptions (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ) :=
  (strengthDyads S.card δ).biUnion fun i =>
    badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100)

lemma off_radialExceptions (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ)
    (x : ℙ K V) (hx : x∉radialExceptions S O δ Lines Q q n χ) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100) := by
  intro i hi hh
  exact hx (Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,hh⟩)

theorem radialExceptions_card [∀x : ℙ K V,Fintype (RadialLine x)]
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (q n χ C : ℝ) (hq : 0<q) (hn : 0<n) (hC : 0≤C)
    (hscale : n*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*q^2)
    (hcount : ∀i∈strengthDyads S.card δ,let a:=((δ:ℝ)*2^i)/2;
      (δ:ℝ)*S.card<(q^4/n^2*Real.exp χ/a^100)*a ∨
      (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2≤C*q^2) :
    ((radialExceptions S O δ Lines Q q n χ).card:ℝ)≤
      n*(8*C*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  have he : 0≤n*(8*C*Real.exp (-χ)) := by positivity
  have hh := biUnion_card_real_le (strengthDyads S.card δ)
    (fun i => badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
      (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100)) (e:=n*(8*C*Real.exp (-χ))) (by
    intro i hi
    have ha : 0<((δ:ℝ)*2^i)/2 := by positivity
    have ha1 : ((δ:ℝ)*2^i)/2≤1 := by linarith only [(Finset.mem_filter.mp hi).2]
    rcases hcount i hi with hmass|hglobal
    · rw [no_radial_exception_of_mass S O δ ha Lines hLines Q hmass]
      simpa only [Finset.card_empty,Nat.cast_zero] using he
    · exact radial_exception_uniform S O δ hq hn ha ha1 Lines hLines Q hC hscale hglobal)
  apply hh.trans
  have hc : ((strengthDyads S.card δ).card:ℝ)≤(Nat.clog 2 S.card:ℝ)+1 := by
    exact_mod_cast strengthDyads_card S.card δ
  calc
    _ ≤ ((Nat.clog 2 S.card:ℝ)+1)*(n*(8*C*Real.exp (-χ))) :=
      mul_le_mul_of_nonneg_right hc he
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreScalars
open scoped Topology
open Filter

lemma radial_mass_of_scalar {q n a χ mass : ℝ} (hq : 0<q) (hn : 0<n)
    (ha : 0<a) (hmass : mass≤q) (hratio : n^2*a^99<q^3*Real.exp χ) :
    mass<(q^4/n^2*Real.exp χ/a^100)*a := by
  have hden : 0<n^2*a^99 := by positivity
  have heq : (q^4/n^2*Real.exp χ/a^100)*a=q^4*Real.exp χ/(n^2*a^99) := by
    field_simp
  rw [heq]
  apply hmass.trans_lt
  apply (lt_div_iff₀ hden).mpr
  have hh := mul_lt_mul_of_pos_left hratio hq
  convert hh using 1; ring

lemma radial_small_strength {q n a g χ : ℝ} (hq : 0<q) (hn : 0<n)
    (hsq : n^2=q^3*Real.exp (2*g)) (hg : 0≤g) (hχ : 0<χ)
    (ha : 0≤a) (hcut : a≤Real.exp (-g/20)) :
    n^2*a^99<q^3*Real.exp χ := by
  have hp := pow_le_pow_left₀ ha hcut 99
  have hexp : Real.exp (2*g)*(Real.exp (-g/20))^99≤1 := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    norm_num
    linarith only [hg]
  have hsmall : n^2*a^99≤q^3 := by
    calc
      n^2*a^99 ≤ n^2*(Real.exp (-g/20))^99 :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg hn.le _)
      _ = q^3*(Real.exp (2*g)*(Real.exp (-g/20))^99) := by rw [hsq,mul_assoc]
      _ ≤ q^3*1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = q^3 := mul_one _
  exact hsmall.trans_lt ((lt_mul_iff_one_lt_right (pow_pos hq 3)).mpr (Real.one_lt_exp_iff.mpr hχ))

lemma radial_low_density {q n a g χ : ℝ} (hq : 0<q) (hn : 0<n)
    (hsq : n^2=q^3*Real.exp (2*g)) (hχ : 2*g<χ)
    (ha : 0≤a) (ha1 : a≤1) : n^2*a^99<q^3*Real.exp χ := by
  calc
    _ ≤ n^2*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha ha1) (pow_nonneg hn.le _)
    _ = q^3*Real.exp (2*g) := by rw [mul_one,hsq]
    _ < _ := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hχ) (pow_pos hq 3)

end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀x : ℙ K V,Fintype (RadialLine x)]

theorem captured_radial_exception_bound {I : Type} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (Flat : I→Submodule K V)
    (X S : Finset (ℙ K V)) (hFlat : ∀i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ : ℝ≥0) (hδ : 0<δ) (n g χ : ℝ) (hn : 0<n) (hX : (X.card:ℝ)≤n)
    (hsq : n^2=(Nat.card K:ℝ)^3*Real.exp (2*g)) (hg : 0≤g) (hχ : 0<χ)
    (hmass : (δ:ℝ)*S.card≤Nat.card K) (hscale : n*(δ:ℝ)≤4*Nat.card K)
    (hcut : 8*(δ:ℝ)*(j+1)≤Real.exp (-g/20))
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) :
    ((radialExceptions S O δ Lines Q (Nat.card K) n χ).card:ℝ)≤
      n*(24576*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hscale' : n*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*(Nat.card K:ℝ)^2 := by
    calc
      _ = (n*(δ:ℝ))*((Nat.card K:ℝ)+1) := by ring
      _ ≤ (4*Nat.card K)*(2*Nat.card K) := mul_le_mul hscale (by linarith only [hq1])
        (by positivity) (by positivity)
      _ = _ := by ring
  have hbound := radialExceptions_card S O δ hδ Lines hLines Q (Nat.card K) n χ 3072 hq hn (by norm_num) hscale'
  norm_num only [show (8:ℝ)*3072=24576 by norm_num] at hbound
  apply hbound
  intro i hi
  let a : ℝ := ((δ:ℝ)*2^i)/2
  have ha : 0<a := by dsimp [a];positivity
  by_cases hsmall : a≤Real.exp (-g/20)
  · exact Or.inl (ScoreScalars.radial_mass_of_scalar hq hn ha hmass
      (ScoreScalars.radial_small_strength hq hn hsq hg hχ ha.le hsmall))
  · right
    have hacut : 8*(δ:ℝ)*(j+1)≤a := hcut.trans (le_of_not_ge hsmall)
    have hδ' : 0<(δ:ℝ) := hδ
    have ha4 : 4*(δ:ℝ)≤a := by nlinarith only [hacut,hδ',(Nat.cast_nonneg j : (0:ℝ)≤j)]
    obtain ⟨M,hM,hlo,hhi⟩ := exists_scale hδ' ha4
    have hjM : j≤M := by
      have hh : (j:ℝ)≤M := by nlinarith only [hacut,hhi,hδ']
      exact_mod_cast hh
    have hm := captured_rich_centers F hF Flat X hFlat Lines hLines j M hM hjM hj O hO δ a hδ' hlo hhi
    have hs : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))≤
        ∑l∈Lines,((richCenters (X\remaining F hF (fun i => flatPoints (Flat i)) X j) O δ a l).card:ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S _ O O δ a δ.coe_nonneg hS
        (fun _ => Finset.Subset.refl _) l))
    apply ((mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm).trans
    have hscaleX : (δ:ℝ)*X.card≤4*Nat.card K :=
      (mul_le_mul_of_nonneg_left hX δ.coe_nonneg).trans (by simpa only [mul_comm n] using hscale)
    have hsq' := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(δ:ℝ)*X.card) hscaleX 2
    nlinarith only [hsq']

end
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I : Type} [Field K] [Finite K] [Fintype I]
  [∀x : ℙ K (I→K),Fintype (RadialLine x)]

theorem residual_radial_exception_bound {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g n' χ : ℝ) (hσq : Real.exp σ=q) (hσ : 1000≤σ)
    (hg : 100000000≤g) (hghi : g≤2*σ) (hn' : Real.exp (3*σ/2+g)/4≤n')
    (X S : Finset (ℙ K (I→K))) (hS : S⊆X) (hSn : (S.card:ℝ)≤n')
    (hX : (X.card:ℝ)≤Real.exp (3*σ/2+g))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K))) (δ : ℝ≥0) (hδ : (δ:ℝ)=(q:ℝ)/n')
    (hχ : 0<χ)
    (hcap : ∀U : Submodule K (I→K),finrank K U=3 →
      ((X.filter fun y => y.submodule≤U).card:ℝ)≤
        (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (Lines : Finset (Submodule K (I→K))) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) :
    ((radialExceptions S O δ Lines Q q (Real.exp (3*σ/2+g)) χ).card:ℝ)≤
      Real.exp (3*σ/2+g)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast (by omega : 1≤q)
  have hn0 : 0<n' := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hn'
  have hδ0 : 0<δ := by rw [←NNReal.coe_pos,hδ];positivity
  have hmass : (δ:ℝ)*S.card≤q := by
    rw [hδ]
    calc
      _ ≤ ((q:ℝ)/n')*n' := mul_le_mul_of_nonneg_left hSn (by positivity)
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hn0)
  have hscale : Real.exp (3*σ/2+g)*(δ:ℝ)≤4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hn',hq0]
  have hscale' : Real.exp (3*σ/2+g)*((δ:ℝ)*((Nat.card K:ℝ)+1))≤8*(q:ℝ)^2 := by
    rw [hcard]
    calc
      _ = (Real.exp (3*σ/2+g)*(δ:ℝ))*((q:ℝ)+1) := by ring
      _ ≤ (4*q)*(2*q) := mul_le_mul hscale (by linarith only [hq1]) (by positivity) (by positivity)
      _ = _ := by ring
  have hsq : (Real.exp (3*σ/2+g))^2=(q:ℝ)^3*Real.exp (2*g) := by
    rw [←hσq,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    norm_num
    ring
  have hbound := radialExceptions_card S O δ hδ0 Lines hLines Q (q:ℝ) (Real.exp (3*σ/2+g)) χ
    333024 hq0 (Real.exp_pos _) (by norm_num) hscale'
  norm_num only [show (8:ℝ)*333024=2664192 by norm_num] at hbound
  apply hbound
  intro i hi
  let a : ℝ := ((δ:ℝ)*2^i)/2
  have ha : 0<a := by dsimp [a];positivity
  by_cases hsmall : a≤Real.exp (-g/20)
  · exact Or.inl (ScoreScalars.radial_mass_of_scalar hq0 (Real.exp_pos _) ha hmass
      (ScoreScalars.radial_small_strength hq0 (Real.exp_pos _) hsq (by linarith only [hg]) hχ ha.le hsmall))
  · right
    have ha2 : a≤2 := by dsimp [a];linarith only [(Finset.mem_filter.mp hi).2]
    have hm := residual_rich_centers hq hcard hI σ g n' a hσq hσ hg hghi hn'
      (le_of_not_ge hsmall) ha2 X hX Lines hLines O hcap
    have hs : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))≤
        ∑l∈Lines,((richCenters X O ((q:ℝ)/n') a l).card:ℝ) := by
      rw [←hδ]
      apply Finset.sum_le_sum
      intro l hl
      exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S X O O δ a δ.coe_nonneg hS
        (fun _ => Finset.Subset.refl _) l))
    exact (mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm

end SharpRamseyFive.ScoreGeometry

end OAI
