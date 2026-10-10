import OAI.NumberTheory.DirichletL.Moments.RankinLabels
import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentDivisorAllocation CenteredMomentWholeDivisorShell
open CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
abbrev Label := (Ideal O × Ideal O) × Finset (Ideal O)

def Valid (s : Ideal O) (v : Label) : Prop :=
  v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ primeSupport v.1.1 = primeSupport v.1.2 ∧
  s ∣ v.1.1 ∧ s ∣ v.1.2 ∧ v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)

def weight (v : Label) : ℝ := 1 / Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm)

lemma commonRadical_norm_le (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    (Ideal.absNorm (commonRadical I J):ℝ) ≤ min (I.absNorm:ℝ) J.absNorm := by
  have hd : commonRadical I J ∣ I ∧ commonRadical I J ∣ J := by
    constructor <;> apply (squarefree_dvd_iff _ _ (commonRadical_squarefree I J)).mpr
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).1)
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).2)
  apply le_min
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm hd.1)
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
      (map_dvd Ideal.absNorm hd.2)

lemma min_le_sqrt_mul (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    min x y ≤ Real.sqrt (x*y) := by
  apply (Real.le_sqrt (le_min hx hy) (mul_nonneg hx hy)).mpr
  rcases le_total x y with h|h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

lemma shell_scalar (e Y x y : ℝ) (he : 0<e) (hx : 0<x) (hy : 0<y)
    (hY : min x y ≤ Y) :
    (2*min x y)^(1+e)/Real.sqrt (x*y) ≤ 2^(1+e)*Y^e := by
  have hm : 0<min x y := lt_min hx hy
  have hsqrt : 0<Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  have hs := min_le_sqrt_mul x y hx.le hy.le
  apply (div_le_iff₀ hsqrt).mpr
  calc
    _ ≤ 2^(1+e)*(Real.sqrt (x*y)*Y^e) := by gcongr
    _ = _ := by ring

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0<T₁ → 0<T₂ → min T₁ T₂≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0<Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hsq : 0<Real.sqrt (T₁*T₂) := Real.sqrt_pos.2 (mul_pos hT₁ hT₂)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/Real.sqrt (T₁*T₂) := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hshell v hv).1 (hshell v hv).2.2.1 hT₂.le (hT₁.le.trans (hshell v hv).1)
    _ = (S.card:ℝ)/Real.sqrt (T₁*T₂) := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/Real.sqrt (T₁*T₂) :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/Real.sqrt (T₁*T₂)) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T₁ T₂ he hT₁ hT₂ hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

def key (v : Label) : ℤ×ℤ := (normKey v.1.1,normKey v.1.2)
def keys (S : Finset Label) : Finset (ℤ×ℤ) := S.image key
def shell (S : Finset Label) (n : ℤ×ℤ) : Finset Label := S.filter (fun v=>key v=n)

lemma norm_scale_bounds (I : Ideal O) (hI : I≠0) (Y : ℝ) (hY : (I.absNorm:ℝ)≤Y) :
    1≤dyadicScale (normKey I) ∧ dyadicScale (normKey I)≤Y := by
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hk : 0≤normKey I := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hn)
  refine ⟨?_,((normKey_eq_iff I hI _).mp rfl).1.trans hY⟩
  simpa only [dyadicScale,zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hk

lemma shell_norm_bounds (S : Finset Label) (n : ℤ×ℤ) (v : Label)
    (hv : v∈shell S n) (hC : v.1.1≠0) (hD : v.1.2≠0) :
    dyadicScale n.1≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*dyadicScale n.1 ∧
    dyadicScale n.2≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*dyadicScale n.2 := by
  have he := (Finset.mem_filter.mp hv).2
  have h₁ := (normKey_eq_iff v.1.1 hC n.1).mp (congrArg Prod.fst he)
  have h₂ := (normKey_eq_iff v.1.2 hD n.2).mp (congrArg Prod.snd he)
  exact ⟨h₁.1,h₁.2,h₂⟩

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)^2*(1+Real.log Z)^2 := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ (indices 1 (Z^B))×ˢ(indices 1 (Z^B)) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (h0 v hv).1 (Z^B) (hN v hv).1
    have hd := norm_scale_bounds v.1.2 (h0 v hv).2 (Z^B) (hN v hv).2
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hc.1,hc.2.trans (by linarith)⟩
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hd.1,hd.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ)^2 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product] at hh
    exact_mod_cast (by simpa only [pow_two] using hh)
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  calc
    _ ≤ ((indices 1 (Z^B)).card:ℝ)^2 := hc
    _ ≤ ((3+B/Real.log 2)*(1+Real.log Z))^2 := by gcongr
    _ = _ := by ring

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,weight v)≤C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

lemma log_square_subpower (d : ℝ) (hd : 0<d) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → (1+Real.log Z)^2≤C*Z^d := by
  let a : ℝ := d/2
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨(1+1/a)^2,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^a := Real.one_le_rpow hZ ha.le
  have hl := Real.log_le_rpow_div hz.le ha
  have hh : 1+Real.log Z≤(1+1/a)*Z^a := by
    calc
      _ ≤ Z^a+Z^a/a := add_le_add hp hl
      _ = _ := by ring
  calc
    _ ≤ ((1+1/a)*Z^a)^2 := by
      apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hh
    _ = (1+1/a)^2*Z^d := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le]
      congr 2
      dsimp [a]; ring

theorem common_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end SevenEighths.CenteredMomentCommonHarmonicMass

end

end OAI
