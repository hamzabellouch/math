import Mathlib
import OAI.NumberTheory.CubicGauss.DualGram

namespace OAI

/-! Initial large-sieve bounds, positivity and divisor counts. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma nonzero_gaussian_finite_mass (H : Finset Eisenstein) (r : ℝ) (hr : 0 < r) :
    ∑ h ∈ H.filter (· ≠ 0), Real.exp (-r*norm h/2) ≤ 36/r := by
  have hb := SieveKernel.finite_laplace_power_bound
    (H.filter (· ≠ 0)) norm (fun _ => (1:ℝ)) (X := 2/r) (C := 18) (p := 1)
    (by positivity) (by norm_num) (fun h _ => norm_nonneg h) (by
      intro Y hY
      have ht : ((H.filter (· ≠ 0)).filter (fun h => norm h < Y)) ⊆ nonzeroNormBall Y := by
        intro h hh
        obtain ⟨hh,hn⟩ := Finset.mem_filter.mp hh
        exact mem_nonzeroNormBall.mpr ⟨hn.le,(Finset.mem_filter.mp hh).2⟩
      have hc : (((H.filter (· ≠ 0)).filter (fun h => norm h < Y)).card:ℝ) ≤
          ((nonzeroNormBall Y).card:ℝ) := by exact_mod_cast Finset.card_le_card ht
      simpa using hc.trans (nonzeroNormBall_card_le hY.le))
  have hg : Real.Gamma (1+1:ℝ) = 1 := by
    rw [Real.Gamma_add_one (by norm_num : (1:ℝ) ≠ 0),Real.Gamma_one]
    norm_num
  simp only [mul_one,Real.rpow_one,hg] at hb
  convert hb using 1 <;> (try congr 1) <;> field_simp
  ring

lemma cubicSymbol_at_zero {a : Eisenstein} (ha : primary a) :
    cubicSymbol a 0 = if a=1 then 1 else 0 := by
  by_cases h : a=1
  · subst a; simp [cubicSymbol_one_lower]
  · rw [ite_eq_right h]
    apply cubicSymbol_eq_zero_of_not_isCoprime ha
    intro hc
    exact h (primary_unit_eq_one (isCoprime_zero_right.mp hc) ha)

lemma cubic_zero_row_bound (S : Finset Eisenstein) (hS : ∀ a ∈ S,primary a)
    (u : Eisenstein → ℂ) :
    ‖∑ a ∈ S,u a*star (cubicSymbol a 0)‖^2 ≤ ∑ a ∈ S,‖u a‖^2 := by
  have he : (∑ a ∈ S,u a*star (cubicSymbol a 0)) = if 1∈S then u 1 else 0 := by
    trans ∑ a ∈ S,if a=1 then u a else 0
    · apply Finset.sum_congr rfl
      intro a ha
      rw [cubicSymbol_at_zero (hS a ha)]
      split_ifs <;> simp
    · simp
  rw [he]
  split_ifs with h
  · exact Finset.single_le_sum (f := fun a => ‖u a‖^2) (fun a _ => sq_nonneg _) h
  · simpa using Finset.sum_nonneg (fun a (_ : a ∈ S) => sq_nonneg ‖u a‖)

lemma cubic_row_card_bound (S : Finset Eisenstein) (hS : ∀ a ∈ S,primary a)
    (u : Eisenstein → ℂ) (m : Eisenstein) :
    ‖∑ a ∈ S,u a*star (cubicSymbol a m)‖^2 ≤
      (S.card : ℝ)*∑ a ∈ S,‖u a‖^2 := by
  have hb := SieveOperator.sum_mul_norm_sq S u (fun a => star (cubicSymbol a m))
  have hc : ∑ a ∈ S,‖star (cubicSymbol a m)‖^2 ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ _a ∈ S,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_star]
        simpa using pow_le_pow_left₀ (_root_.norm_nonneg _)
          (norm_cubicSymbol_le_one (hS a ha) m) 2
      _ = _ := by simp
  exact hb.trans ((mul_le_mul_of_nonneg_left hc
    (Finset.sum_nonneg fun a _ => sq_nonneg ‖u a‖)).trans_eq (mul_comm _ _))

 

theorem cubic_gaussian_initial_bound {Y : ℝ} (hY : 0 ≤ Y)
    (S : Finset Eisenstein) (hS : S ⊆ squarefreePrimaryBall Y)
    (r : ℝ) (hr : 0 < r) (H : Finset Eisenstein) (u : Eisenstein → ℂ) :
    ∑ h ∈ H, Real.exp (-r*norm h/2)*‖∑ a ∈ S,u a*star (cubicSymbol a h)‖^2 ≤
      (1+648*Y/r)*∑ a ∈ S,‖u a‖^2 := by
  let E := ∑ a ∈ S,‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg fun a _ => sq_nonneg ‖u a‖
  have hp (a : Eisenstein) (ha : a ∈ S) : primary a :=
    (mem_squarefreePrimaryBall.mp (hS ha)).1
  have hc : (S.card : ℝ) ≤ 18*Y := by
    apply le_trans _ (nonzeroNormBall_card_le hY)
    exact_mod_cast Finset.card_le_card (show S ⊆ nonzeroNormBall Y from
      fun a ha => mem_nonzeroNormBall.mpr
        ⟨(mem_squarefreePrimaryBall.mp (hS ha)).2.2,primary_ne_zero (hp a ha)⟩)
  let H0 := H.filter (· ≠ 0)
  have hsub : H ⊆ insert 0 H0 := by
    intro h hh
    by_cases h0 : h=0
    · simp [h0]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hh,h0⟩)
  have h00 : (0:Eisenstein) ∉ H0 := by simp [H0]
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun h => Real.exp (-r*norm h/2)*‖∑ a ∈ S,u a*star (cubicSymbol a h)‖^2)
    (fun h _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  rw [Finset.sum_insert h00] at hb
  have hz : Real.exp (-r*norm (0:Eisenstein)/2)*‖∑ a ∈ S,u a*star (cubicSymbol a 0)‖^2 ≤ E := by
    simpa [norm] using cubic_zero_row_bound S hp u
  have hm : ∑ h ∈ H0, Real.exp (-r*norm h/2)*‖∑ a ∈ S,u a*star (cubicSymbol a h)‖^2 ≤
      (36/r)*(18*Y*E) := by
    calc
      _ ≤ ∑ h ∈ H0,Real.exp (-r*norm h/2)*(18*Y*E) := by
        apply Finset.sum_le_sum
        intro h hh
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (cubic_row_card_bound S hp u h).trans (mul_le_mul_of_nonneg_right hc hE)
      _ = (∑ h ∈ H0,Real.exp (-r*norm h/2))*(18*Y*E) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (nonzero_gaussian_finite_mass H r hr) (by positivity)
  apply hb.trans ((add_le_add hz hm).trans_eq _)
  dsimp [E]
  ring



lemma norm_idealMoebius_le (a : Eisenstein) : ‖(idealMoebius a:ℂ)‖ ≤ 1 := by
  have h := idealMoebius_sq a
  have hsq : (idealMoebius a:ℝ)^2 ≤ 1 := by
    rw [h]; split_ifs <;> norm_num
  have he : (idealMoebius a:ℂ) = ((idealMoebius a:ℝ):ℂ) := by simp
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact (sq_le_one_iff_abs_le_one _).mp hsq

 

def CubicGaussianBound (K : ℝ → ℝ → ℝ) : Prop :=
  ∀ (Y r : ℝ), 1 ≤ Y → 0 < r → 0 ≤ K Y r ∧
    ∀ (S : Finset Eisenstein), S ⊆ squarefreePrimaryBall Y →
    ∀ (H : Finset Eisenstein) (u : Eisenstein → ℂ),
      ∑ h ∈ H, Real.exp (-r*norm h/2)*‖∑ a ∈ S,u a*star (cubicSymbol a h)‖^2 ≤
        K Y r * ∑ a ∈ S,‖u a‖^2

lemma initial_cubicGaussianBound : CubicGaussianBound (fun Y r => 1+648*Y/r) := by
  intro Y r hY hr
  refine ⟨by positivity,?_⟩
  intro S hS H u
  exact cubic_gaussian_initial_bound (by linarith) S hS r hr H u

lemma cubic_coprime_dual_norm_bound {Y : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall Y) (u : Eisenstein → ℂ) (s : ℝ) :
    ‖∑ a ∈ S, ∑ b ∈ S, (if IsCoprime a b then (1:ℂ) else 0) *
      (u a*star (u b)) * cubicDualPair s a b‖ ≤
      ∑ l ∈ squarefreePrimaryBall Y, ‖cubicDualForm s (S.filter (l ∣ ·)) u‖ := by
  have he := coprime_pair_sum_moebius S hS (fun a b => (u a*star (u b))*cubicDualPair s a b)
  simp only [← mul_assoc] at he ⊢
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  rw [norm_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le l)

lemma cubic_coprime_dual_gaussian_bound {Y : ℝ} (hY : 1 ≤ Y)
    (S : Finset Eisenstein) (hS : S ⊆ squarefreePrimaryBall Y)
    (u : Eisenstein → ℂ) (s L : ℝ) (hs : 0 < s) (hL : 0 < L)
    (hn : ∀ a ∈ S,L ≤ norm a ∧ norm a ≤ (10/9:ℝ)*L)
    (K : ℝ → ℝ → ℝ) (hK : CubicGaussianBound K) :
    ‖∑ a ∈ S, ∑ b ∈ S, (if IsCoprime a b then (1:ℂ) else 0) *
      (u a*star (u b)) * cubicDualPair s a b‖ ≤
      (7*K Y (4*Real.pi/(3*s*L^2))/L) *
        ∑ l ∈ squarefreePrimaryBall Y, ∑ a ∈ S.filter (l ∣ ·),‖u a‖^2 := by
  have hr : 0 < 4*Real.pi/(3*s*L^2) := by positivity
  obtain ⟨hK0,hop⟩ := hK Y _ hY hr
  apply (cubic_coprime_dual_norm_bound S hS u s).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hsub : S.filter (l ∣ ·) ⊆ squarefreePrimaryBall Y := fun a ha =>
    hS (Finset.mem_filter.mp ha).1
  exact cubic_dual_form_bound (S.filter (l ∣ ·))
    (fun a ha => ⟨(mem_squarefreePrimaryBall.mp (hsub ha)).1,
      (mem_squarefreePrimaryBall.mp (hsub ha)).2.1⟩) u s L _ hs hL hK0
    (fun a ha => hn a (Finset.mem_filter.mp ha).1) (hop _ hsub)

lemma sieveFiber_subset_quotient {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) {k : Eisenstein} (hk : primary k) :
    sieveFiber N S k ⊆ squarefreePrimaryBall (N/norm k) := by
  intro a ha
  obtain ⟨ha,hka⟩ := mem_sieveFiber.mp ha
  obtain ⟨hap,has,_⟩ := mem_squarefreePrimaryBall.mp ha
  have hn := (mem_squarefreePrimaryBall.mp (hS hka)).2.2
  rw [norm_mul_eq,mul_comm] at hn
  exact mem_squarefreePrimaryBall.mpr ⟨hap,has,
    (le_div_iff₀ (norm_pos_of_ne_zero (primary_ne_zero hk))).mpr hn⟩

 

theorem cubic_gaussian_positive_bound {N : ℝ} (hN : 0 < N)
    (S : Finset Eisenstein) (hS : S ⊆ squarefreePrimaryBall N)
    (hthin : ∀ b ∈ S,(9/10:ℝ)*N ≤ norm b)
    (u : Eisenstein → ℂ) (t : ℝ) (ht : 0 < t)
    (K : ℝ → ℝ → ℝ) (hK : CubicGaussianBound K) :
    ‖∑' m : Eisenstein,(cubicRowEnergy S u m:ℂ)*
        Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))‖ ≤
      ∑ k ∈ squarefreePrimaryBall N, ∑ d ∈ primaryDivisors k,
        (2/((Real.sqrt 3)*t*norm d)) *
        (7*K (N/norm k) (4*Real.pi/(3*(t*norm d)*((9/10:ℝ)*N/norm k)^2)) /
          ((9/10:ℝ)*N/norm k)) *
        ∑ l ∈ squarefreePrimaryBall (N/norm k),
          ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·), ‖u (k*a)‖^2 := by
  rw [cubic_gaussian_gram_transform S hS u t ht]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨hkp,hks,hkn⟩ := mem_squarefreePrimaryBall.mp hk
  have hk0 := norm_pos_of_ne_zero (primary_ne_zero hkp)
  have hY : 1 ≤ N/norm k := (one_le_div hk0).mpr hkn
  have hL : 0 < (9/10:ℝ)*N/norm k := by positivity
  have hsub := sieveFiber_subset_quotient S hS hkp
  have hn (a : Eisenstein) (ha : a ∈ sieveFiber N S k) :
      (9/10:ℝ)*N/norm k ≤ norm a ∧ norm a ≤ (10/9:ℝ)*((9/10:ℝ)*N/norm k) := by
    have hka := (mem_sieveFiber.mp ha).2
    have hlo := hthin (k*a) hka
    have hup := (mem_squarefreePrimaryBall.mp (hS hka)).2.2
    rw [norm_mul_eq] at hlo hup
    constructor
    · apply (div_le_iff₀ hk0).mpr
      nlinarith
    · have he : (10/9:ℝ)*((9/10:ℝ)*N/norm k) = N/norm k := by ring
      rw [he,le_div_iff₀ hk0]
      nlinarith
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨hdp,hdk⟩ := (mem_primaryDivisors (primary_ne_zero hkp)).mp hd
  have hd0 := norm_pos_of_ne_zero (primary_ne_zero hdp)
  have hs : 0 < t*norm d := mul_pos ht hd0
  have hpref : 0 ≤ 2/(Real.sqrt 3*t*norm d) := by positivity
  have he := cubic_coprime_dual_gaussian_bound hY (sieveFiber N S k) hsub
    (fun a => u (k*a)*cubicSymbol a d) (t*norm d) ((9/10:ℝ)*N/norm k) hs hL hn K hK
  have heq : (∑ a ∈ sieveFiber N S k,∑ b ∈ sieveFiber N S k,
      (if IsCoprime a b then (1:ℂ) else 0)*(u (k*a)*cubicSymbol a d)*
        star (u (k*b)*cubicSymbol b d)*cubicDualPair (t*norm d) a b) =
      ∑ a ∈ sieveFiber N S k,∑ b ∈ sieveFiber N S k,
      (if IsCoprime a b then (1:ℂ) else 0)*
        ((u (k*a)*cubicSymbol a d)*star (u (k*b)*cubicSymbol b d))*cubicDualPair (t*norm d) a b := by
    simp only [mul_assoc]
  rw [norm_mul,norm_mul,heq]
  have hc : ‖2/((Real.sqrt 3:ℂ)*t*norm d)‖ = 2/(Real.sqrt 3*t*norm d) := by
    have hc : 2/((Real.sqrt 3:ℂ)*t*norm d) = ((2/(Real.sqrt 3*t*norm d):ℝ):ℂ) := by push_cast; rfl
    rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpref]
  rw [hc]
  have hK0 : 0 ≤ K (N/norm k)
      (4*Real.pi/(3*(t*norm d)*((9/10:ℝ)*N/norm k)^2)) :=
    (hK (N/norm k) _ hY (by positivity)).1
  have htwi : (∑ l ∈ squarefreePrimaryBall (N/norm k),
      ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·), ‖u (k*a)*cubicSymbol a d‖^2) ≤
      ∑ l ∈ squarefreePrimaryBall (N/norm k),
      ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·), ‖u (k*a)‖^2 := by
    apply Finset.sum_le_sum
    intro l hl
    exact cubic_twist_energy_le _ (fun a ha =>
      (mem_squarefreePrimaryBall.mp (hsub (Finset.mem_filter.mp ha).1)).1) (fun a => u (k*a)) d
  have hp : ‖(idealMoebius d:ℂ)‖*(2/(Real.sqrt 3*t*norm d)) ≤ 2/(Real.sqrt 3*t*norm d) :=
    mul_le_of_le_one_left hpref (norm_idealMoebius_le d)
  calc
    _ ≤ (2/(Real.sqrt 3*t*norm d)) *
        ((7*K (N/norm k) (4*Real.pi/(3*(t*norm d)*((9/10:ℝ)*N/norm k)^2)) /
          ((9/10:ℝ)*N/norm k)) *
        ∑ l ∈ squarefreePrimaryBall (N/norm k),
          ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·), ‖u (k*a)*cubicSymbol a d‖^2) :=
      mul_le_mul hp he (_root_.norm_nonneg _) hpref
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left htwi (show 0 ≤ (2/(Real.sqrt 3*t*norm d)) *
        (7*K (N/norm k) (4*Real.pi/(3*(t*norm d)*((9/10:ℝ)*N/norm k)^2)) /
          ((9/10:ℝ)*N/norm k)) from by positivity)
      simpa only [mul_assoc] using hh


abbrev SieveFour := Σ _k : Eisenstein, Σ _d : Eisenstein, Σ _l : Eisenstein, Eisenstein

def sieveFourIndices (N : ℝ) (S : Finset Eisenstein) : Finset SieveFour :=
  (squarefreePrimaryBall N).sigma fun k => (primaryDivisors k).sigma fun _d =>
    (squarefreePrimaryBall (N/norm k)).sigma fun l => (sieveFiber N S k).filter (l ∣ ·)

def divisorFourIndices (S : Finset Eisenstein) : Finset SieveFour :=
  S.sigma fun b => (primaryDivisors b).sigma fun _k =>
    (primaryDivisors b).sigma fun _d => primaryDivisors b

def sieveFourMap (v : SieveFour) : SieveFour :=
  ⟨v.1*v.2.2.2,v.1,v.2.1,v.2.2.1⟩

lemma mem_sieveFourIndices {N : ℝ} {S : Finset Eisenstein} {k d l a : Eisenstein} :
    (⟨k,d,l,a⟩ : SieveFour) ∈ sieveFourIndices N S ↔
      k ∈ squarefreePrimaryBall N ∧ d ∈ primaryDivisors k ∧
      l ∈ squarefreePrimaryBall (N/norm k) ∧ a ∈ sieveFiber N S k ∧ l ∣ a := by
  simp [sieveFourIndices]

lemma mem_divisorFourIndices {S : Finset Eisenstein} {b k d l : Eisenstein} :
    (⟨b,k,d,l⟩ : SieveFour) ∈ divisorFourIndices S ↔
      b ∈ S ∧ k ∈ primaryDivisors b ∧ d ∈ primaryDivisors b ∧ l ∈ primaryDivisors b := by
  simp [divisorFourIndices]

lemma sieveFourMap_mem {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) {v : SieveFour} (hv : v ∈ sieveFourIndices N S) :
    sieveFourMap v ∈ divisorFourIndices S := by
  obtain ⟨k,d,l,a⟩ := v
  have hv := mem_sieveFourIndices.mp hv
  have hk := (mem_squarefreePrimaryBall.mp hv.1).1
  have hka := (mem_sieveFiber.mp hv.2.2.2.1).2
  have hkap := (mem_squarefreePrimaryBall.mp (hS hka)).1
  have hd := (mem_primaryDivisors (primary_ne_zero hk)).mp hv.2.1
  have hl := (mem_squarefreePrimaryBall.mp hv.2.2.1).1
  apply mem_divisorFourIndices.mpr
  refine ⟨hka,?_,?_,?_⟩
  · exact (mem_primaryDivisors (primary_ne_zero hkap)).mpr ⟨hk,dvd_mul_right k a⟩
  · exact (mem_primaryDivisors (primary_ne_zero hkap)).mpr
      ⟨hd.1,hd.2.trans (dvd_mul_right k a)⟩
  · exact (mem_primaryDivisors (primary_ne_zero hkap)).mpr
      ⟨hl,hv.2.2.2.2.trans (dvd_mul_left a k)⟩

lemma sieveFourMap_inj {N : ℝ} {S : Finset Eisenstein} :
    Set.InjOn sieveFourMap (sieveFourIndices N S) := by
  rintro ⟨k,d,l,a⟩ hv ⟨k',d',l',a'⟩ hv' he
  have hk := (mem_squarefreePrimaryBall.mp (mem_sieveFourIndices.mp hv).1).1
  have h1 : k*a=k'*a' := congrArg Sigma.fst he
  have h2 : k=k' := congrArg (fun v : SieveFour => v.2.1) he
  have h3 : d=d' := congrArg (fun v : SieveFour => v.2.2.1) he
  have h4 : l=l' := congrArg (fun v : SieveFour => v.2.2.2) he
  subst k'; subst d'; subst l'
  have h5 : a=a' := mul_left_cancel₀ (primary_ne_zero hk) h1
  subst a'
  rfl

 

theorem sieve_divisor_multiplicity_bound {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) (f : Eisenstein → ℝ) (hf : ∀ b ∈ S,0 ≤ f b) :
    (∑ k ∈ squarefreePrimaryBall N, ∑ _d ∈ primaryDivisors k,
      ∑ l ∈ squarefreePrimaryBall (N/norm k),
        ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),f (k*a)) ≤
      ∑ b ∈ S, ((primaryDivisors b).card:ℝ)^3*f b := by
  have hsub : (sieveFourIndices N S).image sieveFourMap ⊆ divisorFourIndices S := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact sieveFourMap_mem S hS hw
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun v : SieveFour => f v.1) (by
      intro v hv _
      exact hf v.1 (mem_divisorFourIndices.mp hv).1)
  rw [Finset.sum_image sieveFourMap_inj] at hbound
  simp only [sieveFourIndices,divisorFourIndices,Finset.sum_sigma,sieveFourMap] at hbound
  apply hbound.trans_eq
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma squarefree_divisor_cube_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : Eisenstein,primary b → Squarefree b →
      ((primaryDivisors b).card:ℝ)^3 ≤ C*(norm b)^ε := by
  obtain ⟨C,hC,h⟩ := squarefree_divisor_power_bound (ε/3) (by positivity)
  refine ⟨C^3,by positivity,?_⟩
  intro b hb hs
  have hb0 := norm_nonneg b
  have hc : ((primaryDivisors b).card:ℝ) ≤ C*(norm b)^(ε/3) := by
    apply le_trans _ (h b hb hs)
    exact_mod_cast primaryDivisors_card_le hb hs
  have hp := pow_le_pow_left₀ (show 0 ≤ ((primaryDivisors b).card:ℝ) by positivity) hc 3
  apply hp.trans_eq
  have he : ((norm b)^(ε/3))^3 = (norm b)^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hb0]
    congr 1
    norm_num
  rw [mul_pow,he]

 

theorem sieve_divisor_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1 ≤ N → S ⊆ squarefreePrimaryBall N →
      (∑ k ∈ squarefreePrimaryBall N, ∑ _d ∈ primaryDivisors k,
        ∑ l ∈ squarefreePrimaryBall (N/norm k),
          ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),‖u (k*a)‖^2) ≤
        C*N^ε*∑ b ∈ S,‖u b‖^2 := by
  obtain ⟨C,hC,h⟩ := squarefree_divisor_cube_bound ε hε
  refine ⟨C,hC,?_⟩
  intro N S u hN hS
  apply (sieve_divisor_multiplicity_bound S hS (fun b => ‖u b‖^2) (fun b _ => sq_nonneg _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨hp,hs,hn⟩ := mem_squarefreePrimaryBall.mp (hS hb)
  have hbn := (h b hp hs).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg b) hn hε.le) hC.le)
  exact mul_le_mul_of_nonneg_right hbn (sq_nonneg _)

end CubicFirstMoment
end

end OAI
