import OAI.Probability.ContinuumTransition.BoxTiling

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def densityFilter (d : ℝ) : Filter (ℝ × ℕ) :=
  Filter.comap (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝 d)

instance densityFilter_countablyGenerated (d : ℝ) : (densityFilter d).IsCountablyGenerated :=
  inferInstanceAs (Filter.comap _ _).IsCountablyGenerated

theorem densityFilter_length (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => p.1) (densityFilter d) atTop := by
  have h : Tendsto (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3))
      (densityFilter d) (atTop ×ˢ 𝓝 d) := Filter.tendsto_comap
  simpa only [Function.comp_def] using
    (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 d) atTop).comp h

theorem densityFilter_density (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ)/p.1^3) (densityFilter d) (𝓝 d) :=
  tendsto_snd.comp (Filter.tendsto_comap : Tendsto _ (densityFilter d) _)

theorem tendsto_densityFilter_iff {α : Type u_1} {l : Filter α} {d : ℝ} {p : α → ℝ × ℕ} :
    Tendsto p l (densityFilter d) ↔
      Tendsto (fun x => (p x).1) l atTop ∧
      Tendsto (fun x => ((p x).2 : ℝ)/(p x).1^3) l (𝓝 d) := by
  rw [densityFilter, tendsto_comap_iff, tendsto_prod_iff']
  rfl

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d*L^3⌋₊)) atTop (densityFilter d) := by
  apply tendsto_densityFilter_iff.2
  exact ⟨tendsto_id, (tendsto_nat_floor_mul_div_atTop hd).comp
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0))⟩

instance densityFilter_neBot (d : ℝ) [Fact (0 ≤ d)] : (densityFilter d).NeBot :=
  (floor_density_tendsto (Fact.out : 0 ≤ d)).neBot

theorem tileCount_asymptotic {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Tendsto (fun L : ℝ => (tileCount ℓ L : ℝ)/L^3) atTop (𝓝 ((ℓ+2)⁻¹^3)) := by
  have hh : 0 ≤ (ℓ+2)⁻¹ := inv_nonneg.mpr (by linarith)
  have ht := (tendsto_nat_floor_mul_div_atTop hh).pow 3
  simpa only [tileCount, Nat.cast_pow, div_pow, div_eq_mul_inv, mul_comm,
    mul_pow, inv_pow] using ht

theorem length_inv_cube_tendsto (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.1^3)⁻¹) (densityFilter d) (𝓝 0) := by
  simpa only [Function.comp_def, ← inv_pow, zero_pow (by norm_num : 3 ≠ 0)] using
    (tendsto_inv_atTop_zero.pow 3).comp (densityFilter_length d)

def DensityBounded (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
    ∀ L : ℝ, R ≤ L → ∀ n : ℕ, (n : ℝ) ≤ D*L^3 → |a L n| ≤ M

def HasBoxInequality (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ ℓ L : ℝ, 0 < ℓ → 0 < L → ∀ r : Fin (tileCount ℓ L) → ℕ,
    a L (∑ i, r i) ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i)

theorem density_eventually_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ M : ℝ, ∀ᶠ p in densityFilter d, |a p.1 p.2| ≤ M := by
  obtain ⟨M, R, -, hR, hb⟩ := ha (d+1) (by linarith)
  refine ⟨M, ?_⟩
  filter_upwards [(densityFilter_length d).eventually (eventually_ge_atTop R),
    (densityFilter_density d).eventually (eventually_le_nhds (by linarith : d < d+1))] with p hp hpd
  exact hb p.1 hp p.2 ((div_le_iff₀ (pow_pos (hR.trans_le hp) 3)).1 hpd)

theorem densityFilter_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    (densityFilter d).IsBoundedUnder (· ≤ ·) (fun p => a p.1 p.2) ∧
    (densityFilter d).IsBoundedUnder (· ≥ ·) (fun p => a p.1 p.2) := by
  obtain ⟨M, hM⟩ := density_eventually_bounded ha hd
  exact ⟨⟨M, hM.mono (fun _ h => (abs_le.mp h).2)⟩,
    ⟨-M, hM.mono (fun _ h => (abs_le.mp h).1)⟩⟩

theorem limsup_box_comparison {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d ℓ M : ℝ} {b H : ℕ}
    (hd : 0 ≤ d) (hℓ : 0 < ℓ) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hcap : d < (ℓ+2)⁻¹^3 * H)
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
      (ℓ+2)⁻¹^3 * ℓ^3 * a ℓ b + (2*M*ℓ^3/(b : ℝ)) * |d-(ℓ+2)⁻¹^3*b| := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht := (tileCount_asymptotic hℓ.le).comp (densityFilter_length d)
  have hcap' := (densityFilter_density d).eventually_lt (ht.mul_const (H : ℝ)) hcap
  have hcomp : (fun p : ℝ × ℕ => a p.1 p.2) ≤ᶠ[densityFilter d]
      (fun p : ℝ × ℕ => ((tileCount ℓ p.1 : ℝ)/p.1^3)*ℓ^3*a ℓ b +
        (2*M*ℓ^3/(b : ℝ)) * (|(p.2 : ℝ)/p.1^3 - ((tileCount ℓ p.1 : ℝ)/p.1^3)*b| + H/p.1^3)) := by
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0), hcap'] with p hp hc
    have hnc : p.2 ≤ tileCount ℓ p.1 * H := by
      have hh : (p.2 : ℝ) < (tileCount ℓ p.1 : ℝ)*H := by
        apply (div_lt_div_iff_of_pos_right (pow_pos hp 3)).mp
        simpa only [div_mul_eq_mul_div, Function.comp_def] using hc
      exact_mod_cast hh.le
    exact adjusted_box_comparison a hℓ hp hM hb hH hnc
      (fun r hr => hr ▸ hbox ℓ p.1 hℓ hp r) hbound hbase
  have htail : Tendsto (fun p : ℝ × ℕ => (H : ℝ)/p.1^3) (densityFilter d) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (length_inv_cube_tendsto d).const_mul (H : ℝ)
  have hlim := ((ht.mul_const (ℓ^3)).mul_const (a ℓ b)).add
    ((((densityFilter_density d).sub (ht.mul_const (b : ℝ))).abs.add htail).const_mul (2*M*ℓ^3/(b : ℝ)))
  simp only [add_zero, Function.comp_def] at hlim
  have hle := limsup_le_limsup hcomp (densityFilter_bounded ha hd).2.isCobounded_le hlim.isBoundedUnder_le
  rwa [hlim.limsup_eq] at hle

 theorem dilution_tendsto_one :
    Tendsto (fun L : ℝ => (L+2)⁻¹^3*L^3) atTop (𝓝 1) := by
  have hh : Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 1) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 2))
        (by norm_num : (1 : ℝ)+2*0 ≠ 0))
    change Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 (1/(1+2*0))) at hh
    simpa only [mul_zero, add_zero, div_one] using hh
  have hpow : Tendsto (fun L : ℝ => (1/(1+2*L⁻¹))^3) atTop (𝓝 1) := by
    simpa only [one_pow] using hh.pow 3
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have h1 : 1+2*L⁻¹ ≠ 0 := by positivity
  have h2 : L+2 ≠ 0 := by linarith
  field_simp

theorem exists_density_limit {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) (𝓝 I) := by
  let : Fact (0 ≤ d) := ⟨hd.le⟩
  obtain ⟨hbup, hbdown⟩ := densityFilter_bounded ha hd.le
  obtain ⟨p, hpA, hp⟩ := exists_seq_tendsto_liminf hbup.isCobounded_ge hbdown
  obtain ⟨hpL, hpd⟩ := tendsto_densityFilter_iff.mp hp
  let D : ℝ := 4*d+4
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨M, R, hM, hR, hbound⟩ := ha D hD
  let H : ℕ → ℕ := fun j => ⌊D*(p j).1^3⌋₊
  have hα : Tendsto (fun j => ((p j).1+2)⁻¹^3*(p j).1^3) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using dilution_tendsto_one.comp hpL
  have hHratio : Tendsto (fun j => (H j : ℝ)/(p j).1^3) atTop (𝓝 D) := by
    exact (tendsto_nat_floor_mul_div_atTop hD.le).comp
      ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hpL)
  have hbd : Tendsto (fun j => ((p j).1+2)⁻¹^3*((p j).2 : ℝ)) atTop (𝓝 d) := by
    have hh : Tendsto (fun j => (((p j).1+2)⁻¹^3*(p j).1^3)*
        ((p j).2 : ℝ)/(p j).1^3) atTop (𝓝 d) := by
      simpa only [one_mul, mul_div_assoc] using hα.mul hpd
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hHd : Tendsto (fun j => ((p j).1+2)⁻¹^3*(H j : ℝ)) atTop (𝓝 D) := by
    have hh := hα.mul hHratio
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hcoef : Tendsto (fun j => 2*M*(p j).1^3/((p j).2 : ℝ)) atTop (𝓝 (2*M/d)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2*M) atTop (𝓝 (2*M))).div hpd hd.ne'
    change Tendsto (fun j => (2*M)/(((p j).2 : ℝ)/(p j).1^3)) atTop (𝓝 (2*M/d)) at hh
    simpa only [div_div_eq_mul_div] using hh
  have hfit : ∀ᶠ j in atTop, 2*(p j).2 ≤ H j := by
    have hh := (hpd.const_mul 2).eventually_lt hHratio (show 2*d < D by dsimp [D]; linarith)
    filter_upwards [hh, hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh' : (2 : ℝ)*(p j).2 < H j := by
      apply (div_lt_div_iff_of_pos_right (pow_pos hL 3)).mp
      simpa only [mul_div_assoc] using hj
    exact_mod_cast hh'.le
  have hpositive : ∀ᶠ j in atTop, 0 < (p j).2 := by
    filter_upwards [hpd.eventually (eventually_gt_nhds hd),
      hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh : (0 : ℝ) < (p j).2 := (div_pos_iff_of_pos_right (pow_pos hL 3)).1 hj
    exact_mod_cast hh
  have hcomp : ∀ᶠ j in atTop,
      limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
        ((p j).1+2)⁻¹^3 * (p j).1^3 * a (p j).1 (p j).2 +
        (2*M*(p j).1^3/((p j).2 : ℝ)) * |d-((p j).1+2)⁻¹^3*(p j).2| := by
    filter_upwards [hpL.eventually (eventually_ge_atTop R), hfit, hpositive,
      hHd.eventually (eventually_gt_nhds (show d < D by dsimp [D]; linarith))] with j hL hfit hb hcap
    have hLpos := hR.trans_le hL
    have hHle : (H j : ℝ) ≤ D*(p j).1^3 := Nat.floor_le (by positivity)
    apply limsup_box_comparison ha hbox hd.le hLpos hM.le hb hfit hcap
    · intro n hn
      exact (abs_le.mp (hbound (p j).1 hL n ((by exact_mod_cast hn : (n : ℝ) ≤ H j).trans hHle))).2
    · have hn : (p j).2 ≤ H j := by omega
      exact (abs_le.mp (hbound (p j).1 hL (p j).2
        ((by exact_mod_cast hn : ((p j).2 : ℝ) ≤ H j).trans hHle))).1
  have hlim := (hα.mul hpA).add (hcoef.mul (((tendsto_const_nhds (x := d)).sub hbd).abs))
  simp only [one_mul, sub_self, abs_zero, mul_zero, add_zero, Function.comp_def] at hlim
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hcomp
  exact ⟨liminf (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d),
    tendsto_of_le_liminf_of_limsup_le le_rfl hle hbup hbdown⟩

end ContinuumTemperature
end

end OAI
