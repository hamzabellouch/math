import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.GeometryScaleOrientedLower
import OAI.Combinatorics.RamseyFive.Geometry.CapturedGlobalRadialMoment

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma RadialLine.exists_other (x : ℙ K V) (l : RadialLine x) :
    ∃ y : ℙ K V,x≠y ∧ y.submodule≤l.val := by
  have hn : ¬l.val≤x.submodule := by
    intro h
    have hh := Submodule.finrank_mono h
    rw [l.property.1,x.finrank_submodule] at hh
    omega
  obtain ⟨v,hv,hvx⟩ := SetLike.not_le_iff_exists.mp hn
  have hv0 : v≠0 := by intro he; exact hvx (he▸x.submodule.zero_mem)
  refine ⟨Projectivization.mk K v hv0,?_,?_⟩
  · intro he
    apply hvx
    rw [he,Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self v
  · rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact hv

omit [Finite K] in
lemma radial_card_le_points (x : ℙ K V) [Fintype (ℙ K V)] [Fintype (RadialLine x)] :
    Fintype.card (RadialLine x)≤Fintype.card (ℙ K V) := by
  let y : RadialLine x→ℙ K V := fun l => (l.exists_other x).choose
  have hy (l : RadialLine x) : x≠y l ∧ (y l).submodule≤l.val :=
    (l.exists_other x).choose_spec
  apply Fintype.card_le_of_injective y
  intro l m he
  have hl : RadialLine.through x (y l) (hy l).1=l :=
    (RadialLine.through_eq_iff (hy l).1 l).mpr (hy l).2
  have hm : RadialLine.through x (y l) (hy l).1=m :=
    (RadialLine.through_eq_iff (hy l).1 m).mpr (he▸(hy m).2)
  exact hl.symm.trans hm

lemma geometric_card_le (q d : ℕ) (hq : 2≤q) :
    (∑ i∈Finset.range (d+1),q^i) ≤ 2*q^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hq' : 2*q^d≤q^(d+1) := by
      rw [pow_succ]
      simpa only [mul_comm] using Nat.mul_le_mul_left (q^d) hq
    omega

omit [FiniteDimensional K V] in
lemma projective_card_le_two_pow [Fintype (ℙ K V)] {d : ℕ}
    (hdim : finrank K V=d+1) (hq : 2≤Nat.card K) :
    Fintype.card (ℙ K V)≤2*Nat.card K^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  exact geometric_card_le _ _ hq

lemma center_radial_count_le [Fintype (ℙ K V)] [∀ x : ℙ K V,Fintype (RadialLine x)]
    {d : ℕ} (hdim : finrank K V=d+1) (hq : 2≤Nat.card K)
    (Q : Finset (ℙ K V)) :
    (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))≤4*(Nat.card K:ℝ)^(2*d) := by
  have hcard := projective_card_le_two_pow hdim hq
  have hQ : Q.card≤2*Nat.card K^d := (Finset.card_le_univ Q).trans hcard
  calc
    _ ≤ ∑ _x : Q,(2*(Nat.card K:ℝ)^d) := Finset.sum_le_sum fun x _ => by
      exact_mod_cast (radial_card_le_points x.val).trans hcard
    _ = (Q.card:ℝ)*(2*(Nat.card K:ℝ)^d) := by simp
    _ ≤ (2*(Nat.card K:ℝ)^d)*(2*(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (by positivity)
    _ = _ := by rw [mul_comm 2 d,pow_mul]; ring

end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.ScoreGeometry

section
open Filter ParameterHierarchy
open scoped Topology

lemma high_density_bounds {σ g q n δ X : ℝ} (hσ : 0≤σ) (hδ : 0≤δ)
    (hq : q=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hX0 : 0≤X) (hX : X≤n) (hscale : n*δ≤4*q) :
    δ*(q+1)≤8*Real.exp (-g) ∧ 192*δ^2*X^2≤333024*Real.exp (2*σ) := by
  have hq1 : 1≤q := hq▸Real.one_le_exp_iff.mpr hσ
  have hn0 : 0<n := hn▸Real.exp_pos _
  have hq2 : q^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul]; norm_num
  have he : n*(4*Real.exp (-g))=4*q^2 := by
    rw [hn,hq2,mul_left_comm,←Real.exp_add]
    congr 2
    ring
  have hδq : δ*q≤4*Real.exp (-g) := by
    apply (mul_le_mul_iff_right₀ hn0).mp
    calc
      _ = (n*δ)*q := by ring
      _ ≤ (4*q)*q := mul_le_mul_of_nonneg_right hscale (by linarith)
      _ = _ := by rw [he]; ring
  constructor
  · calc
      _ ≤ 2*(δ*q) := by nlinarith
      _ ≤ 2*(4*Real.exp (-g)) := mul_le_mul_of_nonneg_left hδq (by norm_num)
      _ = _ := by ring
  · have hdX : δ*X≤4*q := (mul_le_mul_of_nonneg_left hX hδ).trans (by simpa only [mul_comm] using hscale)
    have hs := pow_le_pow_left₀ (mul_nonneg hδ hX0) hdX 2
    rw [mul_pow,mul_pow] at hs
    rw [←hq2]
    nlinarith [sq_nonneg q]

lemma captured_cutoff {σ g δ j : ℝ} (hσ : 0≤σ) (hg : 100≤g)
    (hδ0 : 0≤δ) (hj0 : 0≤j)
    (hδ : δ≤4*Real.exp (-σ/2-g)) (hj : j≤Real.exp (σ/2-2*g/15)) :
    8*δ*(j+1)≤2*Real.exp (-g/20) := by
  have hp : δ*j≤4*Real.exp (-g) := by
    calc
      _ ≤ (4*Real.exp (-σ/2-g))*Real.exp (σ/2-2*g/15) :=
        mul_le_mul hδ hj hj0 (hδ0.trans hδ)
      _ = 4*Real.exp (-17*g/15) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hd : δ≤4*Real.exp (-g) :=
    hδ.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have he : (32:ℝ)≤Real.exp (19*g/20) := by
    have hh := Real.add_one_le_exp (19*g/20)
    linarith
  calc
    _ ≤ 64*Real.exp (-g) := by nlinarith
    _ ≤ (2*Real.exp (19*g/20))*Real.exp (-g) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring

end

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_captured_moment_sharp (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (χ : ℝ) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hn : 0 < X.card) (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (hm : ∀ H : G,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x G H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hcaptured : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2 < (X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉highExceptions F hF P X Planes J ((δ:ℝ)*2^i) χ Q)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ)) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  apply score_higher_power x _ δ hδ G hG _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have ha2 := (Finset.mem_filter.mp hi).2
  by_cases hsmall : (X.card:ℝ)*((δ:ℝ)*2^i)^99≤(Nat.card K:ℝ)^2
  · exact score_pair_small_normalized x hdim S O δ hδ G hG X.card _ χ hn' ha ha2 hmass hsmall
      (le_trans (by norm_num) hchi) Lines hLines Q hx (hgood i hi)
  · have hlarge := (ScoreScalars.high_or_small (q := (Nat.card K:ℝ)) (n := X.card)
        (by positivity) hn' ha.le hhigh).resolve_right hsmall
    exact score_pair_captured_normalized x hdim F hF P X S (O x) J hS hO δ hδ G hG
      Planes hPlanes hcomplete _ χ Q hx hn ha ha2 hcap hscale hlarge hchi
      (hcaptured i hi (lt_of_not_ge hsmall))

theorem score_pair_residual_moment_sharp (hdim : finrank K V=5)
    (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (χ : ℝ) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hn : 0 < X.card) (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (hm : ∀ H : G,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x G H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hresidual : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2 < (X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉residualExceptions Planes X Q ((δ:ℝ)*2^i) χ)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ)) := by
  have hqpos : (0:ℝ) < Nat.card K := Nat.cast_pos.mpr Nat.card_pos
  have hn' : (0:ℝ) < X.card :=
    (mul_pos (by norm_num : (0:ℝ) < 8388608) (sq_pos_of_pos hqpos)).trans_le hhigh
  apply score_higher_power x _ δ hδ G hG _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have ha2 := (Finset.mem_filter.mp hi).2
  by_cases hsmall : (X.card:ℝ)*((δ:ℝ)*2^i)^99≤(Nat.card K:ℝ)^2
  · exact score_pair_small_normalized x hdim S O δ hδ G hG X.card _ χ hn' ha ha2 hmass hsmall
      (le_trans (by norm_num) hchi) Lines hLines Q hx (hgood i hi)
  · exact score_pair_residual_normalized x hdim X S (O x) hS δ hδ G hG
      Planes hPlanes hcomplete _ χ Q hx hn ha ha2 hcap hscale hchi (hresidual i hi (lt_of_not_ge hsmall))

end

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]
  [∀ x : ℙ K V,Fintype (RadialLine x)]

theorem captured_global_trunc_exp_bound (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V))
    (hFlat : ∀ i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀ x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ L : ℝ≥0) (hδ : 0<δ) (σ g n : ℝ) (hσ : 1≤σ)
    (hq : (Nat.card K:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hg : g≤σ) (hX : (X.card:ℝ)≤n) (hscale : n*(δ:ℝ)≤4*Nat.card K)
    (hcut : 8*(δ:ℝ)*(j+1)≤2*Real.exp (-(g+σ/2)/20))
    (Lines : Finset (Submodule K V)) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (R : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
  have hqNat : 2≤Nat.card K := Finite.one_lt_card
  have hN := center_radial_count_le (d:=4) hdim hqNat Q
  have heq : (Nat.card K:ℝ)^8=Real.exp (8*σ) := by
    rw [hq,←Real.exp_nat_mul]; norm_num
  norm_num only [show 2*4=8 from rfl] at hN
  rw [heq] at hN
  have hdens := high_density_bounds (by linarith : 0≤σ) δ.coe_nonneg hq hn
    (Nat.cast_nonneg X.card) hX hscale
  have hm : (S.card:ℝ)≤Real.exp (3*σ) := by
    calc
      _ ≤ (X.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card (hS.trans Finset.sdiff_subset))
      _ ≤ n := hX
      _ ≤ _ := hn▸Real.exp_le_exp.mpr (by linarith)
  have hrad := captured_global_radial_moment F hF Flat X S hFlat j hS hj O hO δ hδ
    (2*Real.exp (-(g+σ/2)/20)) hcut Lines hrank Q hLines 5000 (by norm_num)
  simp only [Nat.reduceSub] at hrad
  have hnum := global_radial_numeric hσ (by positivity)
    (mul_nonneg δ.coe_nonneg (by positivity)) (by positivity) (by positivity)
    hN hdens.1 hdens.2 (le_refl _) hm
  have hh := (global_trunc_failure S O δ L Q R 5000).trans
    (mul_le_mul_of_nonneg_left (hrad.trans hnum) (by positivity))
  apply hh.trans_eq
  rw [mul_add]
  ac_rfl

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I : Type} [Fintype I] [Field K] [Finite K]
  [∀ x : ℙ K (I→K),Fintype (RadialLine x)]

theorem residual_global_trunc_exp_bound_dim {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=5)
    (σ g n' : ℝ) (hqexp : (q:ℝ)=Real.exp σ) (hσ : 1000≤σ)
    (hglo : 100000000≤g+σ/2) (hg : g≤σ)
    (hn' : Real.exp (2*σ+g)/4≤n')
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ)≤Real.exp (2*σ+g))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (δ L : ℝ≥0) (hδ : 0<δ) (hδeq : (δ:ℝ)=(q:ℝ)/n')
    (hmax : (δ:ℝ)*((q:ℝ)+1)≤2)
    (Lines : Finset (Submodule K (I→K))) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (hcap : ∀ U : Submodule K (I→K),finrank K U=3 →
      ((X.filter fun y => y.submodule≤U).card:ℝ)≤
        (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5))
    (R : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val X (O x.val)) δ p.2)) ≤
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
  let : Fintype (ℙ K (I→K)) := Fintype.ofFinite _
  have he : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hN := center_radial_count_le (K:=K) (V:=I→K) (d:=4)
    (show finrank K (I→K)=5 by rw [Module.finrank_pi,hI]) (show 2≤Nat.card K by omega) Q
  norm_num only [show 2*4=8 from rfl] at hN
  have heq : (Nat.card K:ℝ)^8=Real.exp (8*σ) := by
    rw [hcard,hqexp,←Real.exp_nat_mul]; norm_num
  rw [heq] at hN
  have hnpos : 0<n' := (by positivity : 0<Real.exp (2*σ+g)/4).trans_le hn'
  have hscale : Real.exp (2*σ+g)*(δ:ℝ)≤4*(q:ℝ) := by
    have hnδ : n'*(δ:ℝ)=(q:ℝ) := by rw [hδeq, mul_div_cancel₀ _ hnpos.ne']
    calc
      _ ≤ (4*n')*(δ:ℝ) := mul_le_mul_of_nonneg_right (by linarith only [hn']) δ.coe_nonneg
      _ = _ := by rw [mul_assoc,hnδ]
  have hdens := high_density_bounds (by linarith : 0≤σ) δ.coe_nonneg hqexp rfl
    (Nat.cast_nonneg X.card) hX hscale
  have hm : (X.card:ℝ)≤Real.exp (3*σ) :=
    hX.trans (Real.exp_le_exp.mpr (by linarith only [hσ, hg]))
  have hnum := global_radial_numeric (by linarith : 1≤σ) (by positivity)
    (mul_nonneg δ.coe_nonneg (by positivity)) (by positivity) (by positivity)
    hN hdens.1 (le_refl (333024*Real.exp (2*σ))) (le_refl _) hm
  have hA : 333024*(q:ℝ)^2=333024*Real.exp (2*σ) := by
    rw [hqexp,←Real.exp_nat_mul]; norm_num
  have hrad := residual_global_radial_moment (K:=K) (I:=I) hq hcard (Or.inr hI)
    σ (g+σ/2) n' (2*Real.exp (-(g+σ/2)/20)) hqexp.symm hσ hglo
    (by linarith only [hσ, hg]) (by simpa only [he] using hn') X (by simpa only [he] using hX)
    O δ hδ hδeq hmax (le_refl _) Lines hrank Q hLines
    (by simpa only [he] using hcap) 5000 (by norm_num)
  simp only [Nat.reduceSub,hcard,hA] at hrad
  have hh := (global_trunc_failure X O δ L Q R 5000).trans
    (mul_le_mul_of_nonneg_left (hrad.trans hnum) (by positivity))
  apply hh.trans_eq
  rw [mul_add]
  ac_rfl

end SharpRamseyFive.ScoreGeometry

end OAI
