import Mathlib
import OAI.Analysis.PathSelection.TupleTaylor

namespace OAI

/-! Regular scalar evaluation fields and germ polynomials. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped BigOperators Polynomial
namespace DegeneratingTrees

structure ScalarEvaluation (K α : Type*) [Field K] [Algebra ℂ K] (l : Filter α) where
  value : K → α → ℂ
  const : ∀ c : ℂ, value (algebraMap ℂ K c) =ᶠ[l] fun _ => c
  add : ∀ a b, value (a+b) =ᶠ[l] fun x => value a x + value b x
  mul : ∀ a b, value (a*b) =ᶠ[l] fun x => value a x * value b x

namespace ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

lemma zero : e.value 0 =ᶠ[l] fun _ => 0 := by simpa using e.const 0
lemma one : e.value 1 =ᶠ[l] fun _ => 1 := by simpa using e.const 1

 
def toGermHom : K →+* Germ l ℂ where
  toFun a := (e.value a : Germ l ℂ)
  map_zero' := Germ.coe_eq.mpr e.zero
  map_one' := Germ.coe_eq.mpr e.one
  map_add' a b := by exact Germ.coe_eq.mpr (e.add a b)
  map_mul' a b := by exact Germ.coe_eq.mpr (e.mul a b)

lemma faithful [NeBot l] {a : K} (h : e.value a =ᶠ[l] fun _ => 0) : a = 0 := by
  apply e.toGermHom.injective
  rw [map_zero]
  exact Germ.coe_eq.mpr h

lemma nonzero [NeBot l] {a : K} (ha : a ≠ 0) : ∀ᶠ x in l, e.value a x ≠ 0 := by
  have hm := (e.mul a a⁻¹).symm.trans (by simpa [ha] using e.one)
  filter_upwards [hm] with x hx
  exact left_ne_zero_of_mul_eq_one hx

lemma neg (a : K) : e.value (-a) =ᶠ[l] fun x => -e.value a x := by
  have h := (e.add a (-a)).symm.trans (by simpa using e.zero)
  filter_upwards [h] with x hx
  exact eq_neg_of_add_eq_zero_right hx

lemma sub (a b : K) : e.value (a-b) =ᶠ[l] fun x => e.value a x - e.value b x := by
  filter_upwards [e.add a (-b), e.neg b] with x hx hy
  simpa [sub_eq_add_neg,hy] using hx

lemma inv (a : K) : e.value a⁻¹ =ᶠ[l] fun x => (e.value a x)⁻¹ := by
  by_cases ha : a = 0
  · subst a
    filter_upwards [e.zero] with x hx
    simp [hx]
  · have h := (e.mul a a⁻¹).symm.trans (by simpa [ha] using e.one)
    filter_upwards [h] with x hx
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hx)

lemma div (a b : K) : e.value (a/b) =ᶠ[l] fun x => e.value a x / e.value b x := by
  filter_upwards [e.mul a b⁻¹, e.inv b] with x hx hy
  simpa [div_eq_mul_inv,hy] using hx

lemma pow (a : K) (n : ℕ) : e.value (a^n) =ᶠ[l] fun x => e.value a x ^ n := by
  induction n with
  | zero => simpa using e.one
  | succ n ih =>
    filter_upwards [e.mul (a^n) a, ih] with x hx hy
    simpa [pow_succ,hy] using hx

lemma sum {ι : Type*} (s : Finset ι) (a : ι → K) :
    e.value (∑ i ∈ s, a i) =ᶠ[l] fun x => ∑ i ∈ s, e.value (a i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using e.zero
  | @insert i s hi ih =>
    filter_upwards [e.add (a i) (∑ j ∈ s, a j), ih] with x hx hy
    simpa [Finset.sum_insert hi,hy] using hx

 

def HasScalarLimits : Prop :=
  ∀ a : K, (∃ c : ℂ, Tendsto (e.value a) l (𝓝 c)) ∨
    Tendsto (fun x => ‖e.value a x‖) l atTop

 

def HasDivisibleSizes : Prop :=
  ∀ a : K, a ≠ 0 → ∀ n : ℕ, 0 < n → ∃ ρ : K,
    (∀ᶠ x in l, 0 < (e.value ρ x).re ∧ (e.value ρ x).im = 0) ∧
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => ‖e.value ρ x‖^n / ‖e.value a x‖) l (𝓝 c)

 

def HolomorphicallyClosed : Prop :=
  ∀ (n : ℕ) (a : Fin n → K) (c : Fin n → ℂ),
    (∀ j, Tendsto (e.value (a j)) l (𝓝 (c j))) →
    ∀ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f c →
      ∃ b : K, e.value b =ᶠ[l] fun x => f (fun j => e.value (a j) x)

lemma tendsto_mul {a b : K} {c d : ℂ}
    (ha : Tendsto (e.value a) l (𝓝 c)) (hb : Tendsto (e.value b) l (𝓝 d)) :
    Tendsto (e.value (a*b)) l (𝓝 (c*d)) :=
  (ha.mul hb).congr' (e.mul a b).symm

lemma tendsto_pow {a : K} {c : ℂ} (ha : Tendsto (e.value a) l (𝓝 c)) (n : ℕ) :
    Tendsto (e.value (a^n)) l (𝓝 (c^n)) :=
  (ha.pow n).congr' (e.pow a n).symm

lemma tendsto_div {a b : K} {c d : ℂ}
    (ha : Tendsto (e.value a) l (𝓝 c)) (hb : Tendsto (e.value b) l (𝓝 d)) (hd : d ≠ 0) :
    Tendsto (e.value (a/b)) l (𝓝 (c/d)) :=
  (ha.div hb hd).congr' (e.div a b).symm

lemma tendsto_inv_of_norm_atTop {a : K}
    (ha : Tendsto (fun x => ‖e.value a x‖) l atTop) :
    Tendsto (e.value a⁻¹) l (𝓝 0) := by
  have hb : Tendsto (e.value a) l (Bornology.cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp ha
  exact (tendsto_inv₀_cobounded.comp hb).congr' (e.inv a).symm

 
def BoundedRatio (a b : K) : Prop := ∃ c : ℂ, Tendsto (e.value (a/b)) l (𝓝 c)

lemma boundedRatio_refl (a : K) : e.BoundedRatio a a := by
  by_cases ha : a = 0
  · subst a
    exact ⟨0, tendsto_const_nhds.congr' (by simpa using e.zero.symm)⟩
  · exact ⟨1, tendsto_const_nhds.congr' (by simpa [ha] using e.one.symm)⟩

lemma boundedRatio_trans {a b c : K} (hb : b ≠ 0)
    (hab : e.BoundedRatio a b) (hbc : e.BoundedRatio b c) : e.BoundedRatio a c := by
  obtain ⟨u,hu⟩ := hab
  obtain ⟨v,hv⟩ := hbc
  refine ⟨u*v,?_⟩
  convert e.tendsto_mul hu hv using 1
  congr 1
  field_simp

lemma boundedRatio_total (hlim : e.HasScalarLimits) (a b : K) :
    e.BoundedRatio a b ∨ e.BoundedRatio b a := by
  rcases hlim (a/b) with h | h
  · exact Or.inl h
  · right
    exact ⟨0, by simpa using e.tendsto_inv_of_norm_atTop h⟩

 
lemma exists_max_scale {ι : Type*} [DecidableEq ι] (hlim : e.HasScalarLimits)
    (s : Finset ι) (hs : s.Nonempty) (ρ : ι → K) (hρ : ∀ i ∈ s, ρ i ≠ 0) :
    ∃ i ∈ s, ∀ j ∈ s, e.BoundedRatio (ρ j) (ρ i) := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases hse : s.Nonempty
    · obtain ⟨j,hjs,hj⟩ := ih hse (fun j hj => hρ j (Finset.mem_insert_of_mem hj))
      rcases e.boundedRatio_total hlim (ρ i) (ρ j) with hij | hji
      · refine ⟨j,Finset.mem_insert_of_mem hjs,?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hks
        · exact hij
        · exact hj k hks
      · refine ⟨i,Finset.mem_insert_self _ _,?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hks
        · exact e.boundedRatio_refl _
        · exact e.boundedRatio_trans (hρ j (Finset.mem_insert_of_mem hjs)) (hj k hks) hji
    · have hsz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hse
      subst s
      refine ⟨i,by simp,?_⟩
      intro j hj
      simp at hj
      subst j
      exact e.boundedRatio_refl _

 

lemma exists_root_size [NeBot l] (hlim : e.HasScalarLimits) (hdiv : e.HasDivisibleSizes)
    (a : K) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∃ ρ : K, ρ ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ Tendsto (e.value (a/ρ^n)) l (𝓝 c) := by
  obtain ⟨ρ,hρ,c,hc,ht⟩ := hdiv a ha n hn
  have hρ0 : ρ ≠ 0 := by
    intro he
    subst ρ
    obtain ⟨x,hx,hz⟩ := (hρ.and e.zero).exists
    simpa [hz] using hx.1
  have hnorm : Tendsto (fun x => ‖e.value (a/ρ^n) x‖) l (𝓝 c⁻¹) := by
    have he : (fun x => (‖e.value ρ x‖^n / ‖e.value a x‖)⁻¹) =ᶠ[l]
        fun x => ‖e.value (a/ρ^n) x‖ := by
      filter_upwards [e.div a (ρ^n), e.pow ρ n] with x hx hy
      rw [hx,hy,norm_div,norm_pow,inv_div]
    exact (ht.inv₀ hc.ne').congr' he
  rcases hlim (a/ρ^n) with ⟨z,hz⟩ | hz
  · refine ⟨ρ,hρ0,z,?_,hz⟩
    have he : ‖z‖ = c⁻¹ := tendsto_nhds_unique hz.norm hnorm
    intro hzero
    simp [hzero] at he
    exact hc.ne' he.symm
  · exact (not_tendsto_atTop_of_tendsto_nhds hnorm hz).elim

 

lemma normalize_finite_coefficients [NeBot l] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hlim : e.HasScalarLimits) (hdiv : e.HasDivisibleSizes)
    (a : ι → K) (n : ι → ℕ) (hn : ∀ i, 0 < n i) (ha : ∃ i, a i ≠ 0) :
    ∃ ρ : K, ρ ≠ 0 ∧ ∃ c : ι → ℂ,
      (∀ i, Tendsto (e.value (a i / ρ ^ n i)) l (𝓝 (c i))) ∧ ∃ i, c i ≠ 0 := by
  classical
  have hsize : ∀ i : ι, ∃ ρ : K, ρ ≠ 0 ∧ ∃ c : ℂ,
      (a i ≠ 0 → c ≠ 0) ∧ Tendsto (e.value (a i / ρ ^ n i)) l (𝓝 c) := by
    intro i
    by_cases hai : a i = 0
    · refine ⟨1,one_ne_zero,0,fun h => (h hai).elim,?_⟩
      simpa [hai] using tendsto_const_nhds.congr' e.zero.symm
    · obtain ⟨ρ,hρ,c,hc,ht⟩ := e.exists_root_size hlim hdiv (a i) hai (n i) (hn i)
      exact ⟨ρ,hρ,c,fun _ => hc,ht⟩
  choose ρ hρ b hb hbt using hsize
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,by simp [s,hi]⟩
  obtain ⟨j,hjs,hj⟩ := e.exists_max_scale hlim s hs ρ (fun i _ => hρ i)
  have hcoeff : ∀ i, ∃ z : ℂ, Tendsto (e.value (a i / ρ j ^ n i)) l (𝓝 z) := by
    intro i
    by_cases hai : a i = 0
    · exact ⟨0,by simpa [hai] using tendsto_const_nhds.congr' e.zero.symm⟩
    · obtain ⟨v,hv⟩ := hj i (by simp [s,hai])
      refine ⟨b i * v ^ n i,?_⟩
      convert e.tendsto_mul (hbt i) (e.tendsto_pow hv (n i)) using 1
      congr 1
      simp only [div_pow]
      field_simp [hρ i, hρ j]
  choose c hc using hcoeff
  refine ⟨ρ j,hρ j,c,hc,j,?_⟩
  have he : c j = b j := tendsto_nhds_unique (hc j) (hbt j)
  rw [he]
  exact hb j (Finset.mem_filter.mp hjs).2

end ScalarEvaluation
end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

 

def clockSubring (xs : List (ℝ → ℝ)) : Subring (Germ (atTop : Filter ℝ) ℂ) where
  carrier := {a | ∃ f : ℝ → ℂ, ClockGerm xs f ∧ a = (f : Germ atTop ℂ)}
  zero_mem' := ⟨fun _ => 0,ClockGerm.const xs 0,rfl⟩
  one_mem' := ⟨fun _ => 1,ClockGerm.const xs 1,rfl⟩
  add_mem' := by
    rintro a b ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨fun t => f t+g t,hf.add hg,rfl⟩
  neg_mem' := by
    rintro a ⟨f,hf,rfl⟩
    exact ⟨fun t => -f t,hf.neg,rfl⟩
  mul_mem' := by
    rintro a b ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨fun t => f t*g t,hf.mul hg,rfl⟩

abbrev ClockField (xs : List (ℝ → ℝ)) : Type := ↥(clockSubring xs)

def ClockField.ofFunction {xs : List (ℝ → ℝ)} (f : ℝ → ℂ) (hf : ClockGerm xs f) :
    ClockField xs := ⟨(f : Germ atTop ℂ),f,hf,rfl⟩

def ClockField.value {xs : List (ℝ → ℝ)} (a : ClockField xs) : ℝ → ℂ :=
  a.property.choose

lemma ClockField.value_mem {xs : List (ℝ → ℝ)} (a : ClockField xs) :
    ClockGerm xs a.value := a.property.choose_spec.1

lemma ClockField.value_eq {xs : List (ℝ → ℝ)} (a : ClockField xs) :
    (a.value : Germ atTop ℂ) = a.val := a.property.choose_spec.2.symm

lemma ClockField.ofFunction_value {xs : List (ℝ → ℝ)} (f : ℝ → ℂ) (hf : ClockGerm xs f) :
    (ClockField.ofFunction f hf).value =ᶠ[atTop] f :=
  Germ.coe_eq.mp (ClockField.value_eq _)

lemma ClockField.value_zero_iff {xs : List (ℝ → ℝ)} (a : ClockField xs) :
    a.value =ᶠ[atTop] 0 ↔ a=0 := by
  rw [←Germ.coe_eq,a.value_eq]
  change a.val = (0:ClockField xs).val ↔ a=0
  exact Subtype.val_inj

lemma clockField_unit_or_zero {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    (a : ClockField xs) : IsUnit a ∨ a=0 := by
  classical
  by_cases ha : a=0
  · exact Or.inr ha
  have hne : ¬ a.value =ᶠ[atTop] 0 := fun h => ha (a.value_zero_iff.mp h)
  let b := ClockField.ofFunction (fun t => (a.value t)⁻¹) (a.value_mem.inv hxs)
  have hab : a*b=1 := by
    apply Subtype.ext
    change a.val*b.val=1
    rw [←a.value_eq]
    exact Germ.coe_eq.mpr ((a.value_mem.eventually_nonzero hxs hne).mono (fun t ht => mul_inv_cancel₀ ht))
  exact Or.inl ⟨⟨a,b,hab,by simpa [mul_comm] using hab⟩,rfl⟩

instance clockField {xs : List (ℝ → ℝ)} [Fact (ValidClocks xs)] : Field (ClockField xs) :=
  Field.ofIsUnitOrEqZero (clockField_unit_or_zero Fact.out)

def clockConstHom (xs : List (ℝ → ℝ)) : ℂ →+* ClockField xs where
  toFun c := ClockField.ofFunction (fun _ => c) (ClockGerm.const xs c)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance clockAlgebra (xs : List (ℝ → ℝ)) : Algebra ℂ (ClockField xs) :=
  (clockConstHom xs).toAlgebra

def clockEvaluation (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    ScalarEvaluation (ClockField xs) ℝ atTop where
  value := ClockField.value
  const c := ClockField.ofFunction_value (fun _ => c) (ClockGerm.const xs c)
  add a b := by
    apply Germ.coe_eq.mp
    rw [ClockField.value_eq]
    change (a+b).val = (a.value:Germ atTop ℂ)+(b.value:Germ atTop ℂ)
    rw [a.value_eq,b.value_eq]
    rfl
  mul a b := by
    apply Germ.coe_eq.mp
    rw [ClockField.value_eq]
    change (a*b).val = (a.value:Germ atTop ℂ)*(b.value:Germ atTop ℂ)
    rw [a.value_eq,b.value_eq]
    rfl

lemma clockEvaluation_divisible (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    (clockEvaluation xs).HasDivisibleSizes := by
  intro a ha n hn
  obtain ⟨ρ,hρ,hpos,c,hc,ht⟩ := a.value_mem.divisible_size Fact.out
    (fun hz => ha (a.value_zero_iff.mp hz)) n hn
  refine ⟨ClockField.ofFunction (fun t => (ρ t:ℂ)) hρ,?_,c,hc,?_⟩
  · filter_upwards [ClockField.ofFunction_value (fun t => (ρ t:ℂ)) hρ] with t he
    change 0 < (ClockField.value (ClockField.ofFunction (fun t => (ρ t:ℂ)) hρ) t).re ∧
      (ClockField.value (ClockField.ofFunction (fun t => (ρ t:ℂ)) hρ) t).im = 0
    rw [he]
    simpa using hpos t
  · apply ht.congr'
    filter_upwards [ClockField.ofFunction_value (fun t => (ρ t:ℂ)) hρ] with t he
    change ρ t ^ n / ‖a.value t‖ = ‖ClockField.value (ClockField.ofFunction (fun t => (ρ t:ℂ)) hρ) t‖ ^ n / ‖a.value t‖
    rw [he,Complex.norm_of_nonneg (hpos t).le]

lemma clockEvaluation_holomorphic (xs : List (ℝ → ℝ)) [Fact (ValidClocks xs)] :
    (clockEvaluation xs).HolomorphicallyClosed := by
  intro n a c hc f hf
  exact ⟨ClockField.ofFunction _ (ClockGerm.analytic_comp_tuple_finite Fact.out
    (fun i => (a i).value_mem) hc hf),ClockField.ofFunction_value _ _⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped BigOperators Polynomial
namespace DegeneratingTrees.ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

def coefficientGermHom : K →+* Germ l ℂ[X] where
  toFun a := (fun x => Polynomial.C (e.value a x) : Germ l ℂ[X])
  map_zero' := by
    apply Germ.coe_eq.mpr
    filter_upwards [e.zero] with x hx
    simp [hx]
  map_one' := by
    apply Germ.coe_eq.mpr
    filter_upwards [e.one] with x hx
    simp [hx]
  map_add' a b := by
    apply Germ.coe_eq.mpr
    filter_upwards [e.add a b] with x hx
    simp [hx]
  map_mul' a b := by
    apply Germ.coe_eq.mpr
    filter_upwards [e.mul a b] with x hx
    simp [hx]

def toPolynomialGermHom : K[X] →+* Germ l ℂ[X] :=
  Polynomial.eval₂RingHom e.coefficientGermHom (Germ.const Polynomial.X)

def polynomialValue (P : K[X]) (x : α) : ℂ[X] :=
  ∑ i ∈ P.support, Polynomial.monomial i (e.value (P.coeff i) x)

lemma polynomialValue_coeff (P : K[X]) (x : α) (n : ℕ) :
    (e.polynomialValue P x).coeff n = if n ∈ P.support then e.value (P.coeff n) x else 0 := by
  classical
  simp [polynomialValue,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial, eq_comm]

lemma polynomialValue_coeff_eventually (P : K[X]) (n : ℕ) :
    (fun x => (e.polynomialValue P x).coeff n) =ᶠ[l] e.value (P.coeff n) := by
  classical
  by_cases hn : n ∈ P.support
  · filter_upwards [] with x
    simp [e.polynomialValue_coeff P x n,hn]
  · have hc : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    filter_upwards [e.zero] with x hx
    simp [e.polynomialValue_coeff P x n,hn,hc,hx]

lemma polynomialValue_germ (P : K[X]) :
    (e.polynomialValue P : Germ l ℂ[X]) = e.toPolynomialGermHom P := by
  classical
  have hfun : e.polynomialValue P =
      ∑ i ∈ P.support, fun x => Polynomial.C (e.value (P.coeff i) x) * Polynomial.X ^ i := by
    funext x
    simp [polynomialValue,Polynomial.C_mul_X_pow_eq_monomial]
  rw [hfun]
  change (Germ.coeRingHom l) _ = _
  rw [map_sum]
  change _ = P.eval₂ e.coefficientGermHom (Germ.const Polynomial.X)
  rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma polynomialValue_zero : e.polynomialValue 0 = fun _ => 0 := by
  funext x
  simp [polynomialValue]

lemma polynomialValue_add (P Q : K[X]) :
    e.polynomialValue (P+Q) =ᶠ[l] fun x => e.polynomialValue P x + e.polynomialValue Q x := by
  apply Germ.coe_eq.mp
  change (e.polynomialValue (P+Q) : Germ l ℂ[X]) =
    (e.polynomialValue P : Germ l ℂ[X]) + e.polynomialValue Q
  rw [e.polynomialValue_germ,e.polynomialValue_germ,e.polynomialValue_germ,map_add]

lemma polynomialValue_mul (P Q : K[X]) :
    e.polynomialValue (P*Q) =ᶠ[l] fun x => e.polynomialValue P x * e.polynomialValue Q x := by
  apply Germ.coe_eq.mp
  change (e.polynomialValue (P*Q) : Germ l ℂ[X]) =
    (e.polynomialValue P : Germ l ℂ[X]) * e.polynomialValue Q
  rw [e.polynomialValue_germ,e.polynomialValue_germ,e.polynomialValue_germ,map_mul]

lemma polynomialValue_faithful [NeBot l] {P : K[X]}
    (h : e.polynomialValue P =ᶠ[l] fun _ => 0) : P = 0 := by
  ext n
  apply e.faithful
  filter_upwards [e.polynomialValue_coeff_eventually P n,h] with x hx hy
  simpa [hy] using hx.symm

lemma polynomialValue_natDegree_le (P : K[X]) (x : α) :
    (e.polynomialValue P x).natDegree ≤ P.natDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hns : n ∉ P.support := by
    intro he
    exact (not_lt_of_ge (Polynomial.le_natDegree_of_mem_supp n he)) hn
  simp [e.polynomialValue_coeff P x n,hns]

lemma polynomialValue_monic {P : K[X]} (hP : P.Monic) :
    ∀ᶠ x in l, (e.polynomialValue P x).Monic ∧ (e.polynomialValue P x).natDegree = P.natDegree := by
  filter_upwards [e.polynomialValue_coeff_eventually P P.natDegree,e.one] with x hx hy
  rw [hP.coeff_natDegree,hy] at hx
  have hdeg := e.polynomialValue_natDegree_le P x
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hdeg hx,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by simp [hx])⟩

 

lemma polynomial_dvd_of_eventually [NeBot l] {P W : K[X]} (hW : W.Monic)
    (hdiv : ∀ᶠ x in l, e.polynomialValue W x ∣ e.polynomialValue P x) : W ∣ P := by
  by_cases hW1 : W = 1
  · simp [hW1]
  apply (Polynomial.modByMonic_eq_zero_iff_dvd hW).mp
  apply e.polynomialValue_faithful
  have he := e.polynomialValue_add (P %ₘ W) (W * (P /ₘ W))
  rw [Polynomial.modByMonic_add_div] at he
  filter_upwards [hdiv,he,e.polynomialValue_mul W (P /ₘ W),
    e.polynomialValue_monic hW] with x hx hxe hxm hxW
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt
  · apply (dvd_add_right (dvd_mul_right (e.polynomialValue W x)
      (e.polynomialValue (P /ₘ W) x))).mp
    simpa [hxe,hxm,add_comm] using hx
  · rw [hxW.2]
    exact lt_of_le_of_lt (e.polynomialValue_natDegree_le (P %ₘ W) x)
      (Polynomial.natDegree_modByMonic_lt P hW hW1)

end DegeneratingTrees.ScalarEvaluation
end

end OAI
