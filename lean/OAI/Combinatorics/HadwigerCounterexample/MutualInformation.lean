import OAI.Combinatorics.HadwigerCounterexample.ProjectionEnergy

namespace OAI

/-! # Mutual Information -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
theorem mix_high {μ : Wgt A} {p : A→ Wgt B} (hμ : ∀ i,0 ≤ μ i) (hp : ∀ i j,0 ≤ p i j)
    (i j) : μ i * p i j ≤ mixW μ p j :=
  weight_le_tot (fun x => mul_nonneg (hμ x) (hp x j)) i

theorem mix_overhead [Nonempty B] {μ : Wgt A} {p : A→Wgt B}
    (hμ : IsLaw μ) (hp : ∀ i,IsLaw (p i)) :
    avg μ (fun x => tension (p x) (mixW μ p))≤log (Fintype.card B) := by
  simp_rw [tension_as_diff,avg_sub,← mixW_avg]
  change avg μ (fun x => negEnt (p x))-negEnt _ ≤ _
  linarith only [hμ.avg_le (fun i => negEnt_le_zero ((hp i).sub)),
    log_card_le_negEnt (mixW_law hμ hp)]

theorem mix_charge [Nonempty A] {μ : Wgt A} {p : A→Wgt B}
    (hμ : IsLaw μ) (hp : ∀ i,IsLaw (p i)) :
    avg μ (fun x => tension (p x) (mixW μ p))≤log (Fintype.card A) := by
  let q := mixW μ p
  have h (i : A) (hi : μ i ≠0) :
      tension (p i) q≤0-log (μ i) := by
    have hr := lt_of_le_of_ne (hμ.nz i) (Ne.symm hi)
    have hcap (j) : p i j ≤ (μ i)⁻¹*q j := by
      rw [mul_comm,←div_eq_mul_inv,le_div_iff₀ hr,mul_comm]
      exact mix_high hμ.nz (fun i => (hp i).nz) i j
    refine (tension_le_cap (hp i).nz (mixW_law hμ hp).nz _ (by positivity) hcap).trans_eq ?_
    rw [(hp i).total,one_mul,log_inv,zero_sub]
  calc _ ≤ avg μ (fun i => (0-log (μ i))) :=
           Finset.sum_le_sum fun i _ => (by
              by_cases hi : μ i=0
              · simp only [hi,zero_mul]; rfl
              exact mul_le_mul_of_nonneg_left (h i hi) (hμ.nz i))
       _ = -negEnt μ := by rw [avg_sub,avg_zero,zero_sub]; rfl
       _ ≤ _ := neg_le.mpr (log_card_le_negEnt hμ)

omit [Fintype C] in
theorem map_banded {p : Wgt B} (f : B→C) (h : ∀ i j,f i=f j → p i=p j)
    (i : B) : mapW p f (f i) = p i * nbr (fun j => f j=f i) := by
  unfold mapW pr avg nbr tot
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : f j=f i
  · rw [h j i hj]
  simp only [ind_zero hj,mul_zero]

theorem tension_banded {p q : Wgt B} (f : B→C) (h : lsupp p q)
    (hp : ∀ i j,f i=f j→p i=p j) (hq : ∀ i j,f i=f j→q i=q j) :
    tension p q=tension (mapW p f) (mapW q f) := by
  unfold tension; rw [mapW_avg]
  apply avg_congr
  intro i hi
  let P (j : B) := f j=f i
  have hk : nbr P≠0 := by
    have he := weight_le_tot (fun j => ind_nonneg (P j)) i
    rw [ind_one (show P i from rfl)] at he
    exact (lt_of_lt_of_le zero_lt_one he).ne'
  change _=Real.log (mapW p f (f i))-Real.log (mapW q f (f i))
  rw [map_banded f hp,map_banded f hq,log_mul hi hk, log_mul (h i hi) hk]
  ring

theorem banded_overhead [Nonempty C] {μ : Wgt A} {p : A→Wgt B}
    (hμ : IsLaw μ) (hp : ∀ i,IsLaw (p i)) (f : B→C)
    (h : ∀ i j k,f j=f k→ p i j=p i k) :
    avg μ (fun i => tension (p i) (mixW μ p)) ≤ log (Fintype.card C) := by
  let q := mixW μ p
  have he (i : A) (hi : μ i ≠0) :
      tension (p i) (mixW μ p) =
      tension (mapW (p i) f) (mixW μ (fun i => mapW (p i) f)) := by
    have hh : lsupp (p i) q := fun x hx =>
      (lt_of_lt_of_le (mul_pos (lt_of_le_of_ne (hμ.nz i) (Ne.symm hi))
        (lt_of_le_of_ne ((hp i).nz x) (Ne.symm hx)))
        (mix_high hμ.nz (fun i => (hp i).nz) i x)).ne'
    rw [←map_mix]
    exact tension_banded f hh (h i) (fun i j ht => by unfold mixW; simp_rw [h _ i j ht])
  exact (le_of_eq (avg_congr he)).trans
    (mix_overhead hμ (fun i => mapW_law (hp i) f))

private theorem add_charge (x y : ℝ) (hx : 0 ≤ x) (hy : 0≤y) :
    (x+y)*log (x+y) ≤ x*log x+y*log y+(x+y)*log 2 := by

  have hh := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy)
    (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num)
  simp only [smul_eq_mul] at hh
  by_cases he : x+y=0
  · obtain rfl : x=0 := by linarith
    obtain rfl : y=0 := by linarith
    simp
  rw [←mul_add,log_mul (by norm_num) he, log_inv] at hh
  linarith

theorem tension_add_le (p q w u : Wgt A) (h : ∀ i,p i=q i+w i)
    (hq : ∀ i, 0 ≤ q i) (hw : ∀ i,0 ≤ w i) :
    tension p u≤ tension q u+tension w u+tot p * log 2 := by
  unfold tension tot avg
  rw [Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply sum_le_sum; intro i _
  change p i*_ ≤ _
  simp only [h]
  linarith only [add_charge _ _ (hq i) (hw i)]

end HadwigerCounterexample

end

end OAI
