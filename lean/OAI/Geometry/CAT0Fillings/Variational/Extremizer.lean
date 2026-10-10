import Mathlib
import OAI.Geometry.CAT0Fillings.Variational.Ekeland
import OAI.Geometry.CAT0Fillings.Variational.LowerContinuity

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing CurrentOperations

lemma exists_mass_bound_of_positive_deficit {A c p : ℝ} (hc : 0 < c) (hp : 1 < p) :
    ∃ M : ℝ≥0, ∀ m : ℝ, 0 ≤ m → 0 ≤ A*m-c*m^p → m ≤ M := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((tendsto_rpow_atTop (sub_pos.mpr hp)).eventually
    (eventually_ge_atTop ((A+1)/c)))
  refine ⟨⟨max R 1,le_trans zero_le_one (le_max_right _ _)⟩,fun m hm hpos => ?_⟩
  by_contra hnot
  have hlarge : max R 1 < m := lt_of_not_ge hnot
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans hlarge.le)
  have hh := hR m ((le_max_left R 1).trans hlarge.le)
  have hpow : m^p = m^(p-1)*m := by
    conv_lhs => rw [show p = (p-1)+1 by ring]
    rw [Real.rpow_add hm0,Real.rpow_one]
  have hmul : A+1 ≤ c*m^(p-1) := by
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  rw [hpow] at hpos
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def fillingDeficit {k : ℕ} (c p : ℝ) (T : Functional X (k+1)) : ℝ :=
  fillingVolume T-c*(mass T)^p

theorem exists_filling_extremizer (hX : IsCAT0 X) {k : ℕ} {c p δ : ℝ}
    (hc : 0 < c) (hp : 1 < p) (hδ : 0 < δ)
    {T0 : Functional X (k+2)} (hT0 : IsIntegral (k+2) T0) (hz0 : boundarySucc T0 = 0)
    (hpositive : 0 < fillingDeficit c p T0) :
    ∃ T : Functional X (k+2), IsIntegral (k+2) T ∧ boundarySucc T = 0 ∧
      0 < mass T ∧ fillingDeficit c p T0 ≤ fillingDeficit c p T ∧
      ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
        c/(1+δ)*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B) := by
  classical
  have hpos : 0 < fillingVolume T0-c*(mass T0)^p := hpositive
  let A : ℝ := (k+3:ℝ)*diam (univ : Set X)
  have hA : 0 ≤ A := mul_nonneg (by positivity) diam_nonneg
  obtain ⟨M,hM⟩ := exists_mass_bound_of_positive_deficit (A := A) hc hp
  let C := {T : Functional X (k+2) // IsIntegral (k+2) T ∧ boundarySucc T = 0 ∧
    fillingDeficit c p T0 ≤ fillingDeficit c p T}
  let F : C → ℝ := fun T => fillingDeficit c p T.val
  let d : C → C → ℝ := fun T U => fillingVolume (T.val-U.val)
  have hlin (T : C) : fillingVolume T.val ≤ A*mass T.val := by
    simpa only [A,Nat.cast_add,Nat.cast_one,show (1:ℝ)+2 = 3 by norm_num,add_assoc] using
      hX.fillingVolume_le_linear T.property.1 T.property.2.1
  have hmass (T : C) : mass T.val ≤ M := by
    apply hM _ (mass_nonneg _)
    have hh := T.property.2.2
    have hl := hlin T
    dsimp only [fillingDeficit] at hh
    linarith
  have hbound : BddAbove (range F) := by
    refine ⟨A*M,?_⟩
    rintro v ⟨T,rfl⟩
    have hl := hlin T
    have hm := mul_le_mul_of_nonneg_left (hmass T) hA
    have hn := mul_nonneg hc.le (Real.rpow_nonneg (mass_nonneg T.val) p)
    dsimp only [F,fillingDeficit]
    linarith
  have hcluster : ∀ u : ℕ → C, ∀ L : ℝ,
      Tendsto (fun j => F (u j)) atTop (𝓝 L) →
      (∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, d (u i) (u j) < ε) →
      ∃ x : C, Tendsto (fun j => d (u j) x) atTop (𝓝 0) ∧ L ≤ F x := by
    intro u L hL hdc
    obtain ⟨m,hmI,σ,hσ,hm⟩ := isCompact_Icc.isSeqCompact
      (fun j => (show mass (u j).val ∈ Icc (0:ℝ) M from ⟨mass_nonneg _,hmass _⟩))
    obtain ⟨ψ,hψ,T,hT,hTM,_,hweak⟩ := exists_integral_weak_subsequence
      (fun j => (u (σ j)).property.1) M 0 (fun j => hmass _)
      (fun j => by
        rw [(u (σ j)).property.2.1]
        change mass (fun _ _ => (0:ℝ)) ≤ (0:ℝ)
        rw [mass_zero]) hX
    let τ : ℕ → ℕ := σ ∘ ψ
    have hτ : StrictMono τ := hσ.comp hψ
    have hz : boundarySucc T = 0 := by
      funext b π
      apply tendsto_nhds_unique (boundarySucc_weak_limit hweak b π)
      simpa only [(u _).property.2.1,Pi.zero_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    have hdlim : Tendsto (fun j => fillingVolume ((u j).val-T)) atTop (𝓝 0) :=
      fillingVolume_sub_tendsto_zero hX (fun j => (u j).property.1)
        (fun j => (u j).property.2.1) M (fun j => hmass _) hdc hτ hweak
    have hV := fillingVolume_tendsto_of_sub_tendsto_zero hX
      (fun j => (u j).property.1) (fun j => (u j).property.2.1) hT hz hdlim
    have hmlim : Tendsto (fun j => mass (u (τ j)).val) atTop (𝓝 m) := hm.comp hψ.tendsto_atTop
    have hmle : mass T ≤ m := mass_le_of_mass_tendsto
      (fun j => (u (τ j)).property.1.1) hmlim hweak
    have hFlim : Tendsto (fun j => F (u (τ j))) atTop (𝓝 (fillingVolume T-c*m^p)) :=
      (hV.comp hτ.tendsto_atTop).sub ((hmlim.rpow_const (Or.inr (by linarith))).const_mul c)
    have heq : L = fillingVolume T-c*m^p := tendsto_nhds_unique
      (hL.comp hτ.tendsto_atTop) hFlim
    have hLle : L ≤ fillingDeficit c p T := by
      rw [heq]
      have hpow := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (mass_nonneg T) hmle (by linarith : 0 ≤ p)) hc.le
      dsimp only [fillingDeficit]
      linarith
    have hT0le : fillingDeficit c p T0 ≤ L := ge_of_tendsto hL
      (Eventually.of_forall fun j => (u j).property.2.2)
    exact ⟨⟨T,hT,hz,hT0le.trans hLle⟩,hdlim,hLle⟩
  let x0 : C := ⟨T0,hT0,hz0,le_refl _⟩
  obtain ⟨x,hx0,hx⟩ := exists_variational_point d
    (fun x => by dsimp only [d]; rw [sub_self,fillingVolume_zero])
    (fun x y => fillingVolume_nonneg _)
    (fun x y => fillingVolume_sub_symm hX x.property.1 x.property.2.1 y.property.1 y.property.2.1)
    (fun x y z => fillingVolume_triangle hX x.property.1 x.property.2.1
      y.property.1 y.property.2.1 z.property.1 z.property.2.1)
    F hbound hcluster x0 hδ
  have hx0' : fillingDeficit c p T0 ≤ fillingDeficit c p x.val := hx0
  refine ⟨x.val,x.property.1,x.property.2.1,?_,hx0',?_⟩
  · by_contra hnot
    have hm0 : mass x.val = 0 := le_antisymm (le_of_not_gt hnot) (mass_nonneg _)
    have hl := hlin x
    have hp0 : p ≠ 0 := by linarith
    simp only [hm0,Real.zero_rpow hp0,mul_zero,fillingDeficit] at hl hx0'
    linarith
  · intro B hB hzB
    have hF : fillingDeficit c p B ≤ fillingDeficit c p x.val+δ*fillingVolume (x.val-B) := by
      by_cases hb : fillingDeficit c p T0 ≤ fillingDeficit c p B
      · exact hx ⟨B,hB,hzB,hb⟩
      · have hn := mul_nonneg hδ.le (fillingVolume_nonneg (x.val-B))
        linarith [lt_of_not_ge hb]
    have hV := (le_abs_self (fillingVolume x.val-fillingVolume B)).trans
      (abs_fillingVolume_sub_le hX x.property.1 x.property.2.1 hB hzB)
    have hh : c*((mass x.val)^p-(mass B)^p) ≤ (1+δ)*fillingVolume (x.val-B) := by
      dsimp only [fillingDeficit] at hF
      nlinarith
    have hden : 0 < 1+δ := by linarith
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    nlinarith

end CAT0Fillings
end

end OAI
