import OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
import OAI.NumberTheory.DirichletL.Descent.TripleMass
import OAI.NumberTheory.DirichletL.Descent.Basic

namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

def sourceWeight {J : ℕ} (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (Z B θ : ℝ) (x : Source (ι:=ι) J) : ℂ :=
  A x * ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) *
    ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ)

def retained {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) : Finset (Source (ι:=ι) J) :=
  S.filter (fun x => sourceWeight p A ψC ψd Z B θ x ≠ 0)

def quotientSet {J : ℕ} (S : Finset (Source (ι:=ι) J)) : Finset (Ideal Eis) :=
  S.image (fun x => sourceIdeal p (x.common\x.divisor))

omit [DecidableEq ι] in
theorem retained_sum {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (F : Source (ι:=ι) J → ℂ) :
    (∑ x ∈ S, sourceWeight p A ψC ψd Z B θ x * F x) =
      ∑ x ∈ retained p S A ψC ψd Z B θ, sourceWeight p A ψC ψd Z B θ x * F x := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hn
  have hz : sourceWeight p A ψC ψd Z B θ x = 0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
  simp [hz]

omit [DecidableEq ι] in

theorem retained_phase_independent {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (phase : Source (ι:=ι) J → ℂ) (hp : ∀ x ∈ S, phase x ≠ 0) :
    S.filter (fun x => sourceWeight p A ψC ψd Z B θ x * phase x ≠ 0) =
      retained p S A ψC ψd Z B θ := by
  ext x
  simp only [Finset.mem_filter, retained, mul_ne_zero_iff]
  constructor
  · rintro ⟨hx,hw,_⟩
    exact ⟨hx,hw⟩
  · rintro ⟨hx,hw⟩
    exact ⟨hx,hw,hp x hx⟩

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_nonzero {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    ∀ t ∈ quotientSet p S, t ≠ 0 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  exact sourceIdeal_ne_zero p hp _

include hp in

theorem quotientSet_eq_initial {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (u : Eisˣ) (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    initialQuotientSet (S.image (fun x => toTuple p (sectorSource u x))) = quotientSet p S := by
  rw [initialQuotientSet, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  change idealQuotient (sourceIdeal p x.divisor) (sourceIdeal p x.common) = _
  exact source_quotient p hp x.common x.divisor (hdiv x hx)

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotient_norm_eq {J : ℕ} (x : Source (ι:=ι) J) (hdiv : x.divisor ⊆ x.common) :
    (Ideal.absNorm (sourceIdeal p (x.common\x.divisor)) : ℝ) =
      (Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Ideal.absNorm (sourceIdeal p x.divisor) := by
  have he : sourceIdeal p x.divisor * sourceIdeal p (x.common\x.divisor) = sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hdiv]
  have hn := congrArg (fun I : Ideal Eis => (Ideal.absNorm I : ℝ)) he
  simp only [map_mul,Nat.cast_mul] at hn
  have hd : (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hn

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_norm_windows {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    {x : Source (ι:=ι) J} (hx : x ∈ retained p S A ψC ψd Z B θ) :
    (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ bC*Z^B ∧
      ad*Z^θ ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
  have hn := (Finset.mem_filter.mp hx).2
  have hnC : ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  have hnd : ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ) ≠ 0 :=
    (mul_ne_zero_iff.mp hn).2
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hC hnC).2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hd hnd).1⟩

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    ∀ t ∈ quotientSet p (retained p S A ψC ψd Z B θ),
      (Ideal.absNorm t : ℝ) ≤ Z^(B-θ+2*η) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hw := retained_norm_windows p S A ψC ψd aC bC ad bd Z B θ hZ hC hd hx
  rw [quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  have hc : (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ Z^(B+η) := by
    apply (hw.1.trans (mul_le_mul_of_nonneg_right hCup (Real.rpow_pos_of_pos hZ _).le)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  have he : Z^(θ-η) ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
    apply le_trans _ hw.2
    calc
      _ = Z^(-η)*Z^θ := by rw [←Real.rpow_add hZ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdlo (Real.rpow_pos_of_pos hZ _).le
  calc
    _ ≤ Z^(B+η)/Z^(θ-η) := div_le_div₀ (by positivity) hc (Real.rpow_pos_of_pos hZ _) he
    _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring

theorem endpoint_threshold (bC ad : ℝ) (had : 0 < ad) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧ bC ≤ Z^η ∧ Z^(-η) ≤ ad := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop bC),
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop ad⁻¹)] with Z hZ hC hd
  refine ⟨hZ,hC,?_⟩
  rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
  exact (inv_le_comm₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) had).mpr hd

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_empty_iff {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    quotientSet p S = ∅ ↔ S = ∅ := Finset.image_eq_empty

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_empty_sum {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (h : quotientSet p (retained p S A ψC ψd Z B θ) = ∅)
    (F : Source (ι:=ι) J → ℂ) :
    (∑ x ∈ S, sourceWeight p A ψC ψd Z B θ x * F x) = 0 := by
  rw [retained_sum p S A ψC ψd Z B θ F, (quotientSet_empty_iff p _).mp h]
  simp

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J)) (Z P η : ℝ)
    (hZ : 1 < Z) (hne : (quotientSet p S).Nonempty)
    (hnorm : ∀ t ∈ quotientSet p S, (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η)) :
    1 ≤ Z^(P+2*η) ∧ 0 ≤ P+2*η := by
  obtain ⟨t,ht⟩ := hne
  have ht0 := quotientSet_nonzero p hp S t ht
  have hn : (1:ℝ) ≤ Ideal.absNorm t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ht0)
  have hh := hn.trans (hnorm t ht)
  refine ⟨hh,?_⟩
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hh)

def normalizedMass (J : ℕ) (T : Finset (Ideal Eis)) (H : ℝ) : ℝ :=
  H⁻¹ * ∑ t ∈ T, ((idealDivisors t).card : ℝ)^J

theorem normalized_mass_bound (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Ideal Eis)) (H : ℝ), 0 < H →
      (∀ t ∈ T, t ≠ 0) → (∀ t ∈ T, (Ideal.absNorm t : ℝ) ≤ H) →
      normalizedMass J T H ≤ C*H^ε := by
  obtain ⟨C,hC,hb⟩ := ideal_divisor_power_small J ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro T H hH hz hn
  rcases T.eq_empty_or_nonempty with he|⟨t,ht⟩
  · subst T
    simp only [normalizedMass,Finset.sum_empty,mul_zero]
    positivity
  have hH1 : 1 ≤ H := by
    have ht1 : (1:ℝ) ≤ Ideal.absNorm t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hz t ht))
    exact ht1.trans (hn t ht)
  have hw : ∀ t ∈ T, ((idealDivisors t).card : ℝ)^J ≤ C*H^ε := by
    intro t ht
    exact (hb t (hz t ht)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hn t ht) hε.le) hC.le)
  have hs : (∑ t ∈ T, ((idealDivisors t).card : ℝ)^J) ≤ (128*H)*(C*H^ε) := by
    calc
      _ ≤ ∑ _t ∈ T, C*H^ε := Finset.sum_le_sum hw
      _ = (T.card:ℝ)*(C*H^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (DescentFiberCost.finite_ideal_count_real T H hH1 hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hH.le)).trans_eq
  field_simp

theorem retained_normalized_mass (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (S : Finset (Source (ι:=ι) J)) (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
      (aC bC ad bd Z B θ η : ℝ), 0 < Z →
      Function.support ψC ⊆ Set.Icc aC bC → Function.support ψd ⊆ Set.Icc ad bd →
      bC ≤ Z^η → Z^(-η) ≤ ad → (∀ x ∈ S, x.divisor ⊆ x.common) →
      Z^(-(B-θ+2*η)) *
        (∑ t ∈ quotientSet p (retained p S A ψC ψd Z B θ), ((idealDivisors t).card : ℝ)^J) ≤
        C*Z^((B-θ+2*η)*ε) := by
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound J ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv
  have h := hb (quotientSet p (retained p S A ψC ψd Z B θ)) (Z^(B-θ+2*η))
    (Real.rpow_pos_of_pos hZ _) (quotientSet_nonzero p hp _)
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv)
  simpa only [normalizedMass,←Real.rpow_neg hZ.le,←Real.rpow_mul hZ.le] using h

theorem retained_normalized_mass_pi (J : ℕ) (U π : ℝ) (hU : 0 ≤ U) (hπ : 0 < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (S : Finset (Source (ι:=ι) J)) (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
      (aC bC ad bd Z B θ η : ℝ), 1 ≤ Z →
      Function.support ψC ⊆ Set.Icc aC bC → Function.support ψd ⊆ Set.Icc ad bd →
      bC ≤ Z^η → Z^(-η) ≤ ad → (∀ x ∈ S, x.divisor ⊆ x.common) → B-θ+2*η ≤ U →
      Z^(-(B-θ+2*η)) *
        (∑ t ∈ quotientSet p (retained p S A ψC ψd Z B θ), ((idealDivisors t).card : ℝ)^J) ≤ C*Z^π := by
  have hε : 0 < π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := retained_normalized_mass J (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv hcap
  apply (hb p hp S A ψC ψd aC bC ad bd Z B θ η (zero_lt_one.trans_le hZ)
    hCw hdw hCup hdlo hdiv).trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  apply (mul_le_mul_of_nonneg_right hcap hε.le).trans
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by linarith : 0 < U+1)).mpr
  nlinarith

theorem radical_norm_le (I : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm I.radical : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)

theorem radical_product_bound (t j : Ideal Eis) (ht : t ≠ 0) (hj : j ≠ 0)
    (Z P G η : ℝ) (hZ : 0 < Z)
    (hnt : (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η))
    (hnj : (Ideal.absNorm j : ℝ) ≤ Z^(G+η)) :
    (Ideal.absNorm (t*j).radical : ℝ) ≤ Z^(P+G+3*η) := by
  apply (radical_norm_le (t*j) (mul_ne_zero ht hj)).trans
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ Z^(P+2*η)*Z^(G+η) := mul_le_mul hnt hnj (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

def assignedCenter {σ : Type*} (slots : Finset σ) (z : σ → ℝ) : ℝ := ∑ i ∈ slots, z i

theorem assigned_register {σ : Type*} [DecidableEq σ]
    (all assigned : Finset σ) (ha : assigned ⊆ all) (z : σ → ℝ)
    (hz : ∀ i ∈ all, 0 ≤ z i) :
    0 ≤ assignedCenter assigned z ∧ 0 ≤ assignedCenter (all\assigned) z ∧
      assignedCenter all z - assignedCenter assigned z = assignedCenter (all\assigned) z := by
  refine ⟨Finset.sum_nonneg (fun i hi => hz i (ha hi)),
    Finset.sum_nonneg (fun i hi => hz i (Finset.mem_sdiff.mp hi).1),?_⟩
  unfold assignedCenter
  have h := Finset.sum_sdiff ha (f := z)
  linarith

def assignedElement {σ : Type*} (slots : Finset σ) (q : σ → Eis) : Eis := ∏ i ∈ slots, q i

theorem assigned_norm_bound {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      (∏ i ∈ slots, b i)*Z^(assignedCenter slots z) := by
  have hb : ∀ i ∈ slots, (Ideal.absNorm (Ideal.span {q i}) : ℝ) ≤ b i*Z^(z i) := by
    intro i hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hW i hi (hret i hi)).2
  have hp := Finset.prod_le_prod₀ (fun i _ => (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {q i})))) hb
  simpa only [assignedElement,FiniteGaussPhase.span_finset_prod,map_prod,Nat.cast_prod,
    Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,assignedCenter] using hp

theorem assigned_norm_power {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z η : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      Z^(assignedCenter slots z+η) := by
  apply (assigned_norm_bound slots q z a b W Z hZ hW hret).trans
  calc
    _ ≤ Z^η*Z^(assignedCenter slots z) := mul_le_mul_of_nonneg_right hthreshold (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_assigned_puncture_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hq : ∀ i ∈ slots, q i ≠ 0)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ)) :
    (Ideal.absNorm (t*Ideal.span {assignedElement slots q}).radical : ℝ) ≤
      Z^((B-θ)+assignedCenter slots z+3*η) := by
  apply radical_product_bound t (Ideal.span {assignedElement slots q})
    (quotientSet_nonzero p hp _ t ht)
    (Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr hq))
    Z (B-θ) (assignedCenter slots z) η hZ
  · exact retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      hZ hC hd hCup hdlo hdiv t ht
  · exact assigned_norm_power slots q z a b W Z η hZ hW hret hthreshold

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem span_source_puncture {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (hpr : ∀ i, λ₀^2 ∣ p i-1) (j : Eis)
    {t : Ideal Eis} (ht : t ∈ quotientSet p S) :
    Ideal.span {j*primaryGenerator t} = t*Ideal.span {j} := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  rw [sourceIdeal_gen p hp hpr]
  simp only [sourceIdeal,Ideal.span_singleton_mul_span_singleton,mul_comm]

def punctureLength (Z : ℝ) (t : Ideal Eis) (j : Eis) : ℝ :=
  Real.log (Ideal.absNorm (Ideal.span {j*primaryGenerator t}).radical : ℝ)/Real.log Z

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_puncture_length_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hq : ∀ i ∈ slots, q i ≠ 0)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ)) :
    punctureLength Z t (assignedElement slots q) ≤ (B-θ)+assignedCenter slots z+3*η := by
  have hz := zero_lt_one.trans hZ
  have hbound := retained_assigned_puncture_bound p hp S A ψC ψd aC bC ad bd Z B θ η
    hz hC hd hCup hdlo hdiv slots q z a b W hq hW hret hthreshold ht
  unfold punctureLength
  rw [span_source_puncture p hp _ hpr _ ht]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have htn : t*Ideal.span {assignedElement slots q} ≠ 0 := mul_ne_zero
    (quotientSet_nonzero p hp _ t ht)
    (Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr hq))
  have hrn : (t*Ideal.span {assignedElement slots q}).radical ≠ 0 := by
    intro he
    apply htn
    apply le_bot_iff.mp
    simpa only [he,Ideal.zero_eq_bot] using (Ideal.le_radical :
      t*Ideal.span {assignedElement slots q} ≤ (t*Ideal.span {assignedElement slots q}).radical)
  have hpos : (0:ℝ) < Ideal.absNorm (t*Ideal.span {assignedElement slots q}).radical := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hrn)
  have hlog := Real.log_le_log hpos hbound
  simpa only [Real.log_rpow hz] using hlog

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_initial_margins {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ))
    (m r δ τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂) :
    c₁+δ-9*η-τ ≤
      initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      punctureLength Z t (assignedElement assigned q) - assignedCenter (all\assigned) z ∧
    c₂+4*δ-22*η-3*τ ≤
      4*initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      3*initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      6*assignedCenter (all\assigned) z := by
  have hr := assigned_register all assigned ha z hz
  have hP := (nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ ⟨t,ht⟩
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)).2
  have hQ := retained_puncture_length_bound p hp S A ψC ψd aC bC ad bd Z B θ η
    hZ hC hd hCup hdlo hdiv hpr assigned q z a b W hq hW hret hthreshold ht
  simpa only [hr.2.2] using initial_margins_sharp (delta:=δ) (tau:=τ)
    h₁ h₂ hr.1 (by linarith : -2*η ≤ B-θ) hQ

theorem all_endpoint_threshold {σ : Type*} (slots : Finset σ) (b : σ → ℝ)
    (bC ad η : ℝ) (had : 0 < ad) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧ bC ≤ Z^η ∧ Z^(-η) ≤ ad ∧ (∏ i ∈ slots, b i) ≤ Z^η := by
  filter_upwards [endpoint_threshold bC ad had η hη,
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop (∏ i ∈ slots,b i))]
      with Z h hprod
  exact ⟨h.1,h.2.1,h.2.2,hprod⟩

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hne : (quotientSet p (retained p S A ψC ψd Z B θ)).Nonempty) :
    1 ≤ Z^((B-θ)+2*η) ∧ 0 ≤ (B-θ)+2*η :=
  nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ hne
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)

omit [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem assigned_cutoffs_of_term {J : ℕ} (lists : Fin J → Finset ι)
    (a : Fin J → ι → ℂ) (W : Fin J → ℝ → ℂ) (z : Fin J → ℝ)
    (Z : ℝ) (outer : Finset ι) (assigned : Fin J → ι)
    (hterm : assignedTerm lists
      (fun i x => a i x * W i ((Ideal.absNorm (Ideal.span {p x}) : ℝ)/Z^(z i)))
      outer assigned ≠ 0) :
    ∀ i, assigned i ∈ lists i ∧ assigned i ∈ outer ∧
      W i ((Ideal.absNorm (Ideal.span {p (assigned i)}) : ℝ)/Z^(z i)) ≠ 0 := by
  intro i
  have hi := assignedTerm_source lists _ outer assigned hterm i
  have hn := Finset.prod_ne_zero_iff.mp hterm i (Finset.mem_univ i)
  simp only [hi] at hn
  exact ⟨hi.1,hi.2,(mul_ne_zero_iff.mp hn).2⟩

omit [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_assigned_term {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) {x : Source (ι:=ι) J}
    (hx : x ∈ retained p S
      (fun y => A y * assignedTerm lists a (y.common∪y.overlap) y.assigned) ψC ψd Z B θ) :
    assignedTerm lists a (x.common∪x.overlap) x.assigned ≠ 0 := by
  have hn := (Finset.mem_filter.mp hx).2
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1).2

end SevenEighths.InverseInitialQuotientGeometry

end

end OAI
