import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEulerShift

namespace OAI

/-! A uniform absolute bound for the prime tail at sigma=1+1/log X.
The proof groups primes into intervals whose logarithms have width log X
and applies Mertens' first theorem in each interval. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_finite_exp_sum (S : Finset ℕ) :
    (∑ k ∈ S, Real.exp (-(k:ℝ)))≤2 := by
  let r : ℝ := Real.exp (-1)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hr2 : r≤1/2 := by
    dsimp only [r]
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith [Real.add_one_le_exp 1])
  have he (k : ℕ) : Real.exp (-(k:ℝ))=r^k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  calc
    _ ≤ ∑' k : ℕ, r^k :=
      (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum S (by intros; positivity)
    _ = (1-r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    _ ≤ 2 := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ (by linarith : 0<1-r)).mpr (by linarith)

theorem mrt_character_prime_tail_bound {X : ℕ} (hX : 1≤Real.log (X:ℝ))
    (S : Finset ℕ) (hS : ∀ p∈S, p.Prime ∧ X<p) :
    (∑ p ∈ S, Real.exp (-Real.log (p:ℝ)/Real.log (X:ℝ))/(p:ℝ)) ≤
      4+4*halaszMertensConstant := by
  let L : ℝ := Real.log (X:ℝ)
  let bin : ℕ → ℕ := fun p => ⌊Real.log (p:ℝ)/L⌋₊
  let K := S.image bin
  have hL : 1≤L := hX
  have hL0 : 0<L := by linarith
  have hC : 0≤halaszMertensConstant := halaszMertensConstant_nonneg
  have hpdata (p : ℕ) (hp : p∈S) :
      0<(p:ℝ) ∧ L<Real.log (p:ℝ) ∧
      (bin p:ℝ)*L≤Real.log (p:ℝ) ∧
      Real.log (p:ℝ)<((bin p:ℝ)+1)*L ∧ 1≤bin p := by
    have hp0 : (0:ℝ)<p := by exact_mod_cast (hS p hp).1.pos
    have hXp : (X:ℝ)<p := by exact_mod_cast (hS p hp).2
    have hX0 : (0:ℝ)<X := by
      by_contra hh
      have hx : X=0 := by exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg X))
      norm_num [hx] at hX
    have hlog : L<Real.log (p:ℝ) := Real.strictMonoOn_log hX0 hp0 hXp
    have hratio : 1<Real.log (p:ℝ)/L := (lt_div_iff₀ hL0).mpr (by simpa using hlog)
    have hlo := Nat.floor_le (show 0≤Real.log (p:ℝ)/L by linarith)
    have hhi := Nat.lt_floor_add_one (Real.log (p:ℝ)/L)
    refine ⟨hp0,hlog,?_,?_,?_⟩
    · exact (le_div_iff₀ hL0).mp hlo
    · exact (div_lt_iff₀ hL0).mp hhi
    · exact (Nat.one_le_floor_iff _).mpr hratio.le
  have hbin (k : ℕ) (hk : k∈K) :
      (∑ p ∈ S.filter (fun p => bin p=k), Real.log (p:ℝ)/(p:ℝ))≤
        2*L+2*halaszMertensConstant := by
    obtain ⟨p,hp,hpk⟩ := mem_image.mp hk
    have hk1 : (1:ℝ)≤k := by exact_mod_cast (hpk ▸ (hpdata p hp).2.2.2.2)
    have ha : 1≤Real.exp (((k:ℝ)-1)*L) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hL0.le)
    have hab : Real.exp (((k:ℝ)-1)*L)≤Real.exp (((k:ℝ)+1)*L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsub : S.filter (fun p => bin p=k) ⊆
        mrtPrimeBand (Real.exp (((k:ℝ)-1)*L)) (Real.exp (((k:ℝ)+1)*L)) := by
      intro p hp
      obtain ⟨hp,hpk⟩ := mem_filter.mp hp
      obtain ⟨hp0,_,hlo,hhi,_⟩ := hpdata p hp
      rw [hpk] at hlo hhi
      have hlow : Real.exp (((k:ℝ)-1)*L)<(p:ℝ) := by
        rw [← Real.exp_log hp0]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      have hupp : (p:ℝ)≤Real.exp (((k:ℝ)+1)*L) := by
        rw [← Real.exp_log hp0]
        exact Real.exp_le_exp.mpr hhi.le
      apply mem_sdiff.mpr
      constructor
      · exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mpr hupp),
          (hS p hp).1⟩
      · intro hh
        have hh' := (Nat.le_floor_iff (Real.exp_pos _).le).mp
          (mem_Iic.mp (mem_filter.mp hh).1)
        linarith
    calc
      _ ≤ ∑ p ∈ mrtPrimeBand (Real.exp (((k:ℝ)-1)*L))
          (Real.exp (((k:ℝ)+1)*L)), Real.log (p:ℝ)/(p:ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (by
          intro p hp _
          have hp1 : (1:ℝ)≤p := by exact_mod_cast (mrtPrimeBand_prime hp).one_le
          exact div_nonneg (Real.log_nonneg hp1) (Nat.cast_nonneg p))
      _ ≤ _ := by
        have hh := halasz_prime_band_mass_le ha hab
        rw [Real.log_exp,Real.log_exp] at hh
        nlinarith
  have hterm (p : ℕ) (hp : p∈S) :
      Real.exp (-Real.log (p:ℝ)/L)/(p:ℝ)≤
        (Real.exp (-(bin p:ℝ))/L)*(Real.log (p:ℝ)/(p:ℝ)) := by
    obtain ⟨hp0,hlog,hlo,_,_⟩ := hpdata p hp
    have he : Real.exp (-Real.log (p:ℝ)/L)≤Real.exp (-(bin p:ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact (div_le_iff₀ hL0).mpr (by nlinarith)
    have hr : 1≤Real.log (p:ℝ)/L :=
      (le_div_iff₀ hL0).mpr (by simpa only [one_mul] using hlog.le)
    calc
      _ ≤ Real.exp (-(bin p:ℝ))/(p:ℝ) := div_le_div_of_nonneg_right he hp0.le
      _ ≤ (Real.exp (-(bin p:ℝ))/(p:ℝ))*(Real.log (p:ℝ)/L) :=
        le_mul_of_one_le_right (by positivity) hr
      _ = _ := by ring
  have hmap : ∀p∈S,bin p∈K := fun p hp => mem_image.mpr ⟨p,hp,rfl⟩
  calc
    _ ≤ ∑ p ∈ S, (Real.exp (-(bin p:ℝ))/L)*(Real.log (p:ℝ)/(p:ℝ)) :=
      sum_le_sum hterm
    _ = ∑ k ∈ K, (Real.exp (-(k:ℝ))/L)*
        ∑ p ∈ S.filter (fun p => bin p=k), Real.log (p:ℝ)/(p:ℝ) := by
      rw [← sum_fiberwise_of_maps_to hmap]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ ∑ k ∈ K, (Real.exp (-(k:ℝ))/L)*(2*L+2*halaszMertensConstant) :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hbin k hk) (by positivity))
    _ = ((2*L+2*halaszMertensConstant)/L)*∑ k ∈ K, Real.exp (-(k:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ ((2*L+2*halaszMertensConstant)/L)*2 :=
      mul_le_mul_of_nonneg_left (mrt_finite_exp_sum K) (by positivity)
    _ ≤ 4+4*halaszMertensConstant := by
      have hh : 2*L+2*halaszMertensConstant≤
          (2+2*halaszMertensConstant)*L := by
        nlinarith [halaszMertensConstant_nonneg]
      have hd := (div_le_iff₀ hL0).mpr hh
      nlinarith

end TwoPointCorrelations

end OAI
