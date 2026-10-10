import OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

def logWindow (v : ℝ) : ℂ := (annulus (Real.exp v) : ℂ)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logWindow_support : Function.support logWindow ⊆ Icc (-Real.log 4) 0 := by
  intro v hv
  have hn : annulus (Real.exp v) ≠ 0 := by simpa [logWindow] using hv
  have hlow : 1/4 < Real.exp v := lt_of_not_ge (fun h => hn (annulus_zero_low _ h))
  have hhigh : Real.exp v < 1 := lt_of_not_ge (fun h => hn (annulus_zero_high _ h))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  constructor
  · exact (Real.exp_lt_exp.mp (hl ▸ hlow)).le
  · exact (Real.exp_lt_one_iff.mp hhigh).le

theorem logWindow_tsupport : tsupport logWindow ⊆ Icc (-Real.log 4) 0 :=
  closure_minimal logWindow_support isClosed_Icc

theorem logWindow_compact : HasCompactSupport logWindow :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logWindow_support

def logWindowSchwartz : 𝓢(ℝ,ℂ) := logWindow_compact.toSchwartzMap logWindow_smooth

theorem logWindow_derivative_window (i : ℕ) (v : ℝ)
    (hi : ‖iteratedFDeriv ℝ i logWindow v‖ ≠ 0) :
    1/4 ≤ Real.exp v ∧ |v| ≤ Real.log 4 := by
  have hv := logWindow_tsupport (support_iteratedFDeriv_subset i (norm_ne_zero_iff.mp hi))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  refine ⟨hl ▸ Real.exp_le_exp.mpr hv.1, abs_le.mpr ⟨hv.1,?_⟩⟩
  exact hv.2.trans (Real.log_nonneg (by norm_num))

theorem logWindow_derivative_bound (K : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ i≤K, ∀v : ℝ, ‖iteratedFDeriv ℝ i logWindow v‖≤C := by
  let C := 1+∑ i∈Finset.range (K+1), SchwartzMap.seminorm ℝ 0 i logWindowSchwartz
  have hsum := Finset.sum_nonneg (s:=Finset.range (K+1))
    (fun i _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 i) logWindowSchwartz)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro i hi v
  have hb := SchwartzMap.le_seminorm' ℝ 0 i logWindowSchwartz v
  have hc := Finset.single_le_sum (s:=Finset.range (K+1))
    (f:=fun j=>SchwartzMap.seminorm ℝ 0 j logWindowSchwartz)
    (fun j _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 j) logWindowSchwartz)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i logWindowSchwartz v‖≤C
  simpa only [pow_zero, one_mul] using hb.trans (by dsimp [C];linarith)

def reflected (W : ℝ→ℂ) (t : ℝ) : ℝ→ℂ :=
  paperRadialFourier (CompletedHeight.normTwistedSource W t)

theorem reflected_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiffOn ℝ ∞ (reflected W t) (Ioi 0) := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold reflected
  rw [←he]
  exact paperRadialFourier_contDiffOn _

def annularProfile (F : ℝ→ℂ) (s x : ℝ) : ℂ := (annulus x:ℂ)*F (s*x)

def logProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  positiveLogProfile logWindow (reflected W t) s logWindow_compact logWindow_smooth
    (reflected_smooth W a b ha hs hW t) hs0

@[simp] theorem logProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t v : ℝ) :
    logProfile W a b ha hs hW s hs0 t v =
      annularProfile (reflected W t) s (Real.exp v) := rfl

theorem logProfile_tsupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) :
    tsupport (logProfile W a b ha hs hW s hs0 t) ⊆ Icc (-Real.log 4) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply logWindow_support
  intro hz
  exact hv (by change logWindow v*reflected W t (s*Real.exp v)=0;rw [hz,zero_mul])

theorem logProfile_finite_seminorm (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀s : ℝ, ∀hs0 : 0<s, ∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logProfile W a b ha hs hW s hs0 t) ≤
        C*(1+‖t‖)^J/(1+s)^B := by
  let K := H.sup Prod.snd
  obtain ⟨CW,hCW,hwin⟩ := logWindow_derivative_bound K
  obtain ⟨J,hJ⟩ := reflected_profile_height_control a b ha B K
  let D := 1+∑z∈H,(Real.log 4)^z.1*
    (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hD : 0<D := by
    have hn : 0≤∑z∈H,(Real.log 4)^z.1*
        (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW) := by positivity
    dsimp [D];linarith
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hEuler⟩ := hJ W hs hW
  refine ⟨D*CF/(1/4:ℝ)^B,by positivity,?_⟩
  intro s hs0 t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzK : z.2≤K := Finset.le_sup hz
  have hb := positive_log_uniform_seminorm logWindow (reflected W t)
    s (1/4) (Real.log 4) CW (CF*(1+‖t‖)^J) B z.2 z.1
    logWindow_compact logWindow_smooth (reflected_smooth W a b ha hs hW t)
    hs0 (by norm_num) (by norm_num) hlog hCW.le (by positivity)
    (fun i hi v => hwin i (hi.trans hzK) v)
    (fun v hv => by obtain ⟨i,hi,hn⟩:=hv;exact logWindow_derivative_window i v hn)
    (fun i hi x hx => hEuler t i (hi.trans hzK) x hx.le)
  have hd : (Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)≤D := by
    have h := Finset.single_le_sum (s:=H)
      (f:=fun z=>(Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW))
      (fun z _ => by positivity) hz
    dsimp [D];linarith
  have hb' : (1/4:ℝ)^B*(1+s)^B*
      SchwartzMap.seminorm ℝ z.1 z.2 (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J) := by
    apply hb.trans
    rw [←Finset.sum_mul, ←mul_assoc]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hb'' : SchwartzMap.seminorm ℝ z.1 z.2
      (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J)/((1/4:ℝ)^B*(1+s)^B) :=
    (le_div_iff₀ (by positivity)).mpr
      (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb')
  exact hb''.trans_eq (by ring)

theorem annularProfile_support (F : ℝ→ℂ) (s : ℝ) :
    Function.support (annularProfile F s) ⊆ Icc (1/4) 1 := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_low x (le_of_not_ge hn)])
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_high x (le_of_not_ge hn)])

theorem annularProfile_zero (F : ℝ→ℂ) (s x : ℝ)
    (hx : x≤1/4 ∨ 1≤x) : annularProfile F s x=0 := by
  rcases hx with hx|hx
  · simp [annularProfile,annulus_zero_low x hx]
  · simp [annularProfile,annulus_zero_high x hx]

theorem annular_partition (F : ℝ→ℂ) (x : ℝ) (hx : 0<x) :
    (∑' n : ℤ,annularProfile F (dyadicScale n) (x/dyadicScale n))=F x := by
  have he (n : ℤ) : annularProfile F (dyadicScale n) (x/dyadicScale n)=
      (dyadicWeight n x:ℂ)*F x := by
    simp [annularProfile,dyadicWeight,mul_div_cancel₀,ne_of_gt (dyadicScale_pos n)]
  simp_rw [he]
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition x hx]
  simp

theorem normalized_annular_term (η : HeckeFamily.Character) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0<s) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*HeckeDyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp

def annularMass (B : ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (dyadicScale n)/(1+dyadicScale n)^B

theorem annularMass_nonneg (B : ℕ) (n : ℤ) : 0≤annularMass B n := by
  have hp := dyadicScale_pos n
  unfold annularMass
  positivity

lemma sqrt_nat_pow (x : ℝ) (hx : 0≤x) (j : ℕ) :
    Real.sqrt (x^j)=(Real.sqrt x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx j),ih,pow_succ]

theorem annularMass_lower_bound (B j : ℕ) :
    annularMass B (-(j:ℤ))≤(Real.sqrt (1/2:ℝ))^j := by
  have hx := dyadicScale_pos (-(j:ℤ))
  have hd : 1≤(1+dyadicScale (-(j:ℤ)))^B := one_le_pow₀ (by linarith)
  have he : dyadicScale (-(j:ℤ))=(1/2:ℝ)^j := by
    simp [dyadicScale,zpow_neg,inv_pow]
  calc
    annularMass B (-(j:ℤ))≤Real.sqrt (dyadicScale (-(j:ℤ))) :=
      div_le_self (Real.sqrt_nonneg _) hd
    _=(Real.sqrt (1/2:ℝ))^j := by rw [he,sqrt_nat_pow _ (by norm_num)]

theorem annularMass_upper_bound (B A j : ℕ) (hAB : A+1≤B) :
    annularMass B (j:ℤ)≤((2:ℝ)^A)⁻¹^j := by
  have hx : 1≤dyadicScale (j:ℤ) := by
    simp only [dyadicScale,zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hp : 0<dyadicScale (j:ℤ) := dyadicScale_pos _
  have hd : dyadicScale (j:ℤ)^(A+1)≤(1+dyadicScale (j:ℤ))^B :=
    (pow_le_pow_left₀ hp.le (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hAB)
  have hb : annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := by
    unfold annularMass
    exact div_le_div₀ hp.le (Real.sqrt_le_self_iff.mpr (Or.inr hx))
      (by positivity) hd
  calc
    annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := hb
    _=((2:ℝ)^A)⁻¹^j := by
      rw [pow_succ,mul_comm (dyadicScale (j:ℤ)^A),div_mul_cancel_left₀ (ne_of_gt hp)]
      simp only [dyadicScale,zpow_natCast,←pow_mul,inv_pow]
      rw [Nat.mul_comm]

lemma nonnegative_geometric_tail (f : ℕ→ℝ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1)
    (hf : ∀j,0≤f j) (hb : ∀j,f j≤q^j) (L : ℕ) :
    Summable (fun j=>f (j+L)) ∧ (∑'j:ℕ,f (j+L))≤q^L/(1-q) := by
  have hg : Summable (fun j:ℕ=>q^(j+L)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^L)
  have hs := Summable.of_nonneg_of_le (fun j=>hf (j+L)) (fun j=>hb (j+L)) hg
  refine ⟨hs,(hs.tsum_le_tsum (fun j=>hb (j+L)) hg).trans_eq ?_⟩
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1]
  ring

theorem annularMass_lower_tail (B L : ℕ) :
    Summable (fun j:ℕ=>annularMass B (-((j+L:ℕ):ℤ))) ∧
      (∑'j:ℕ,annularMass B (-((j+L:ℕ):ℤ)))≤
        (Real.sqrt (1/2:ℝ))^L/(1-Real.sqrt (1/2:ℝ)) := by
  apply nonnegative_geometric_tail (fun j=>annularMass B (-(j:ℤ)))
    (Real.sqrt (1/2:ℝ)) (Real.sqrt_nonneg _)
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
    (fun j=>annularMass_nonneg _ _) (annularMass_lower_bound B) L

theorem annularMass_upper_tail (B A L : ℕ) (hA : 1≤A) (hAB : A+1≤B) :
    Summable (fun j:ℕ=>annularMass B ((j+L:ℕ):ℤ)) ∧
      (∑'j:ℕ,annularMass B ((j+L:ℕ):ℤ))≤
        (((2:ℝ)^A)⁻¹)^L/(1-((2:ℝ)^A)⁻¹) := by
  have hp : 1<(2:ℝ)^A := by
    calc
      1<(2:ℝ)^1 := by norm_num
      _≤(2:ℝ)^A := pow_le_pow_right₀ (by norm_num) hA
  apply nonnegative_geometric_tail (fun j=>annularMass B (j:ℤ))
    ((2:ℝ)^A)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hp)
    (fun j=>annularMass_nonneg _ _) (fun j=>annularMass_upper_bound B A j hAB) L

theorem annularMass_summable (B : ℕ) (hB : 2≤B) : Summable (annularMass B) := by
  apply Summable.of_nat_of_neg
  · simpa only [Nat.add_zero] using (annularMass_upper_tail B 1 0 (by omega) hB).1
  · simpa only [Nat.add_zero] using (annularMass_lower_tail B 0).1

theorem logProfile_dyadic_seminorm_sum (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) (hB : 2≤B) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
      Summable (fun n:ℤ=>Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)) ∧
      (∑'n:ℤ,Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t))≤
        C*(1+‖t‖)^J := by
  obtain ⟨J,hJ⟩ := logProfile_finite_seminorm a b ha H B
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hbound⟩ := hJ W hs hW
  have hmass := annularMass_summable B hB
  have hmass0 : 0≤∑'n:ℤ,annularMass B n := tsum_nonneg (annularMass_nonneg B)
  refine ⟨CF*(1+∑'n:ℤ,annularMass B n),by positivity,?_⟩
  intro t
  let f := fun n:ℤ=>Real.sqrt (dyadicScale n)*
    H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)
  have hf0 : ∀n,0≤f n := fun n=>
    mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hb : ∀n,f n≤(CF*(1+‖t‖)^J)*annularMass B n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hbound _ (dyadicScale_pos n) t)
      (Real.sqrt_nonneg (dyadicScale n))
    exact h.trans_eq (by unfold annularMass;ring)
  have hg := hmass.mul_left (CF*(1+‖t‖)^J)
  have hf := Summable.of_nonneg_of_le hf0 hb hg
  refine ⟨hf,(hf.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_mul_left]
  nlinarith [show 0≤CF*(1+‖t‖)^J by positivity]

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI
