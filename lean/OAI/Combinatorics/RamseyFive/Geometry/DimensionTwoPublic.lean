import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Decoding.PublicTraining
import OAI.Combinatorics.RamseyFive.Geometry.DimensionThreeProcedure
import OAI.Combinatorics.RamseyFive.Geometry.PublicDecoder

namespace OAI

section
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma density_three_quarters {d : ℕ} (hd : 1 ≤ d) (hq : 3 ≤ Nat.card K) :
    3 / (4 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [Q_recurrence hd]
  push_cast
  have hq' : (3 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hm' (by positivity : (0:ℝ) ≤ Nat.card K)
  nlinarith

theorem sparse_half_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d) (hq3 : 3 ≤ Nat.card K)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (2 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 3 / (4*q) ≤ p := density_three_quarters hd hq3
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (2*q) at hsparse
    have he : (3 / (4*q)) * v = 3 * (v / (4*q)) := by field_simp
    have he2 : v / (2*q) = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    rw [he2] at hsparse
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory PoissonScore ScoreAcceptance MeasurePublicTable ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_empty_procedure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      100*(Nat.card K:ℝ)*P η σ D R<(S.card:ℝ) →
    Real.exp (-8*P η σ D R*τ)/4≤
    (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
      (trueScoreSuccess U S (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ)))
        (exceptional S (fun _ : Unit=>∅)) R
        (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (2*P η σ D R)) ((9/10:ℝ)*S.card)) := by
  have hh := eventually_two_score_procedure hη hη' Cb hCb
  have ht := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hh,ht,eventually_ge_atTop (10:ℝ)] with σ hh ht hσ
  rw [←neg_mul] at ht
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod hn
  have hP1 : 1≤P η σ D R :=
    (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hqp : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos _
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_le_of_lt (by positivity) hn))
  have hSn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have ht' : τ≤1/2 := hτhi.trans ht.le
  have hq3 : 3≤Nat.card K := by
    exact_mod_cast (show (3:ℝ)≤Nat.card K by rw [hq];linarith only [Real.add_one_le_exp σ,hσ])
  have hm := sparse_half_rectangle_size (d:=2) hdim (by norm_num) hq3 S T (by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(Nat.card K:ℝ))).mpr
    have := mul_le_mul_of_nonneg_right ht' (by positivity : (0:ℝ)≤(S.card:ℝ)*T.card)
    nlinarith only [hdens,this])
  have hs2 : (S.card:ℝ)^2≤16*Real.exp (3*σ) := by
    have hst : (S.card:ℝ)≤T.card := by exact_mod_cast hST
    have he : (Real.exp σ)^3=Real.exp (3*σ) := by rw [←Real.exp_nat_mul];norm_num
    rw [hq,he] at hm
    nlinarith
  have hnhi : (S.card:ℝ)≤10*Real.exp (3*σ/2) := by
    have he : (Real.exp (3*σ/2))^2=Real.exp (3*σ) := by rw [←Real.exp_nat_mul];congr 1;ring
    have hepos := Real.exp_pos (3*σ/2)
    nlinarith [sq_nonneg ((S.card:ℝ)-10*Real.exp (3*σ/2))]
  have hqP : (Nat.card K:ℝ)*P η σ D R≤S.card := by nlinarith
  have hdiv : (Nat.card K:ℝ)/S.card≤1/100 := by
    apply (div_le_iff₀ hSn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hP1 hqp.le]
  have hc := hh D b τ R L₀ K V S U S (fun _ : Unit=>∅) (fun _=>()) (fun _=>()) (fun _=>()) T
    hdim hq hr hL hb hbhi hτ hτhi hS (by rfl) hSU (by omega) hdens hprod
    (by simp) (by simp) (by simp) hnhi hdiv hqP (by norm_num [ownFraction])
  simpa only [trueScoreSuccess,ownFraction,Finset.empty_union,Finset.card_empty,Nat.cast_zero,
    zero_div,sub_zero,mul_one,mul_assoc] using hc

end SharpRamseyFive.ScoreGeometry

end

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_training_score {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (3*σ/2+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
    (∀i,(C i).card≤(S.card:ℝ)/25) →
    S⊆X ∧ X.card≤2*S.card ∧
    Real.exp (-8*P η σ D R*τ)/4≤
      (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
        (trueScoreSuccess U S (fun x=>C (a x))
          (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (a x)) ∅)))
          (exceptional S C) R (2*(Nat.card K:ℝ)*P η σ D R)
          ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card)) := by
  have hh := eventually_three_score_procedure hη hη' Cb hCb
  have htau := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hp := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) (beta_pos hη))).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hh,htau,hp,eventually_ge_atTop (10:ℝ)] with σ hh htau hp hσ
  rw [←neg_mul] at htau
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover
  dsimp only
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
  let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
  change (∀i,(C i).card≤(S.card:ℝ)/25) → _
  intro hsmall
  have hSX : S⊆X := peel_subset _ _ _ _ _ _ _
  have hret : X.card≤2*S.card := peel_half _ _ _ _ _ _ _
  have hret' : (X.card:ℝ)≤2*S.card := by exact_mod_cast hret
  have hSn : 0<(S.card:ℝ) := by nlinarith only [hret',hX,Real.exp_pos (3*σ/2+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  have hP : 4≤P η σ D R := hp.trans (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hq : 2<q := by exact_mod_cast (show (2:ℝ)<q by rw [←hσq];linarith only [Real.add_one_le_exp σ,hσ])
  have hqp : (0:ℝ)<Nat.card K := by rw [hcard,←hσq];exact Real.exp_pos _
  have hdim : finrank K (I→K)=3+1 := by rw [Module.finrank_pi,hI]
  have hm := sparse_half_rectangle_size (d:=3) hdim (by norm_num) (by omega : 3≤Nat.card K) X T (by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(Nat.card K:ℝ))).mpr
    have := mul_le_mul_of_nonneg_right (hτhi.trans htau.le) (by positivity : (0:ℝ)≤(X.card:ℝ)*T.card)
    nlinarith only [hdens,this])
  have hxx : (X.card:ℝ)^2≤16*Real.exp (4*σ) := by
    have hxt : (X.card:ℝ)≤T.card := by exact_mod_cast hXT
    have he : (Real.exp σ)^4=Real.exp (4*σ) := by rw [←Real.exp_nat_mul];norm_num
    rw [hcard,←hσq,he] at hm
    nlinarith
  have hnhi : (X.card:ℝ)≤10*Real.exp (2*σ) := by
    have he : (Real.exp (2*σ))^2=Real.exp (4*σ) := by rw [←Real.exp_nat_mul];congr 1;ring
    have hepos := Real.exp_pos (2*σ)
    nlinarith [sq_nonneg ((X.card:ℝ)-10*Real.exp (2*σ))]
  have hg : g≤2*σ := by
    have he : 3*σ/2+g≤2*σ+Real.log 10 := Real.exp_le_exp.mp (by
      rw [Real.exp_add (2*σ),Real.exp_log (by norm_num : (0:ℝ)<10)]
      nlinarith only [hnhi,hX])
    have hl := Real.log_le_self (by norm_num : (0:ℝ)≤10)
    linarith only [he,hl,hσ]
  have hsum := TrainingCells.sum_card_le S C
    (clippedPart_subset S F hF (fun j=>flatPoints (Flat j)) X m)
    (clippedPart_disjoint S F hF (fun j=>flatPoints (Flat j)) X m)
  have hqP : (Nat.card K:ℝ)*P η σ D R≤S.card := by nlinarith only [hn,hret',hqp,hP]
  have hdiv : (Nat.card K:ℝ)/S.card≤1/100 := by
    apply (div_le_iff₀ hSn).mpr
    nlinarith only [hn,hret',mul_le_mul_of_nonneg_left hP hqp.le]
  have hc := hh D b τ R L₀ q K I J g F hF Flat X U S t ht
    (publicOwn (greedyList F hF (fun j=>flatPoints (Flat j)) X m)) C a (fun _=>none) (fun _=>none) T
    hq hcard hσq hI hr hL hb hbhi hτ hτhi hg hSX (hSX.trans hXU) hdens hprod
    hFlat hcover hX.le rfl rfl (by nlinarith only [hret',hX])
    ((show (S.card:ℝ)≤X.card by exact_mod_cast Finset.card_le_card hSX).trans hnhi)
    (ownCell_subset_publicOwn F hF (fun j=>flatPoints (Flat j)) X m)
    (by intro x;simpa only [C,clippedPart,Finset.union_empty] using clipped_publicOwn S F hF (fun j=>flatPoints (Flat j)) X hSX m x)
    (by omega) (clippedPart_subset S F hF (fun j=>flatPoints (Flat j)) X m)
    (by intro x;simp [C,clippedPart]) hqP hdiv
    (by intro x;exact TrainingCells.small_union S (C (a x)) (C none) hS (hsmall _) (hsmall _))
  refine ⟨hSX,hret,?_⟩
  simpa only [trueScoreSuccess,C,clippedPart,Finset.union_empty,mul_assoc] using hc

end SharpRamseyFive.ScoreGeometry

end OAI
