import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic

namespace OAI

section

open Set Filter
open scoped Topology

namespace CAT0Fillings

theorem exists_variational_point {A : Type*} (d : A → A → ℝ)
    (d0 : ∀ x, d x x = 0) (dn : ∀ x y, 0 ≤ d x y)
    (ds : ∀ x y, d x y = d y x) (dt : ∀ x y z, d x z ≤ d x y+d y z)
    (F : A → ℝ) (hF : BddAbove (range F))
    (hcluster : ∀ u : ℕ → A, ∀ L : ℝ,
      Tendsto (fun j => F (u j)) atTop (𝓝 L) →
      (∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, d (u i) (u j) < ε) →
      ∃ x : A, Tendsto (fun j => d (u j) x) atTop (𝓝 0) ∧ L ≤ F x)
    (x0 : A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : A, F x0 ≤ F x ∧ ∀ y : A, F y ≤ F x+δ*d x y := by
  classical
  let R (x y : A) := F x+δ*d x y ≤ F y
  have hrefl x : R x x := by simp only [R,d0,mul_zero,add_zero,le_refl]
  have htrans {x y z : A} (hxy : R x y) (hyz : R y z) : R x z := by
    have hh := mul_le_mul_of_nonneg_left (dt x y z) hδ.le
    dsimp only [R] at *
    nlinarith
  have happ (x : A) (n : ℕ) : ∃ y, R x y ∧ ∀ z, R x z → F z ≤ F y+1/((n:ℝ)+1) := by
    let S : Set ℝ := {r | ∃ y, R x y ∧ r = F y}
    have hn : S.Nonempty := ⟨F x,x,hrefl x,rfl⟩
    have hb : BddAbove S := hF.mono (by rintro r ⟨y,_,rfl⟩; exact mem_range_self y)
    have he : 0 < 1/((n:ℝ)+1) := by positivity
    obtain ⟨r,⟨y,hy,rfl⟩,hr⟩ := exists_lt_of_lt_csSup hn (sub_lt_self (sSup S) he)
    refine ⟨y,hy,fun z hz => ?_⟩
    have hh : F z ≤ sSup S := le_csSup hb ⟨z,hz,rfl⟩
    linarith
  choose next hn hnmax using happ
  let u : ℕ → A := fun n => Nat.rec x0 (fun j x => next x j) n
  have hu0 : u 0 = x0 := rfl
  have hustep n : u (n+1) = next (u n) n := rfl
  have hstep n : R (u n) (u (n+1)) := by rw [hustep]; exact hn _ _
  have hchain {i j : ℕ} (hij : i ≤ j) : R (u i) (u j) := by
    induction j, hij using Nat.le_induction with
    | base => exact hrefl _
    | succ j hij ih => exact htrans ih (hstep j)
  have hmono : Monotone (fun j => F (u j)) := by
    intro i j hij
    have hh := hchain hij
    have hd := mul_nonneg hδ.le (dn (u i) (u j))
    dsimp only [R] at hh
    linarith
  have hb : BddAbove (range (fun j => F (u j))) := hF.mono (by
    rintro r ⟨j,rfl⟩; exact mem_range_self (u j))
  let L : ℝ := ⨆ j, F (u j)
  have hlim : Tendsto (fun j => F (u j)) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hb
  have hle j : F (u j) ≤ L := le_ciSup hb j
  have hcauchy : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, d (u i) (u j) < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds
      (sub_lt_self L (mul_pos hδ hε))))
    refine ⟨N,fun i hi j hj => ?_⟩
    have hh {i j : ℕ} (hi : N ≤ i) (hij : i ≤ j) : d (u i) (u j) < ε := by
      have hc := hchain hij
      have hn := hN i hi
      have hj := hle j
      dsimp only [R] at hc
      nlinarith
    rcases le_total i j with hij | hji
    · exact hh hi hij
    · rw [ds]; exact hh hj hji
  obtain ⟨x,hdlim,hx⟩ := hcluster u L hlim hcauchy
  have hdcont (i : ℕ) : Tendsto (fun j => d (u i) (u j)) atTop (𝓝 (d (u i) x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hdlim
    intro j
    rw [Real.norm_eq_abs]
    apply abs_sub_le_iff.mpr
    have h1 := dt (u i) (u j) x
    have h2 := dt (u i) x (u j)
    rw [←ds (u j) x] at h2
    constructor <;> linarith
  have hux (i : ℕ) : R (u i) x := by
    have hh : F (u i)+δ*d (u i) x ≤ L := by
      apply le_of_tendsto_of_tendsto (tendsto_const_nhds.add ((hdcont i).const_mul δ)) hlim
      filter_upwards [eventually_ge_atTop i] with j hj
      exact hchain hj
    exact hh.trans hx
  have hmax j {y : A} (hy : R (u j) y) : F y ≤ F (u (j+1))+1/((j:ℝ)+1) := by
    rw [hustep]
    exact hnmax _ _ _ hy
  have hlim' : Tendsto (fun j => F (u (j+1))+1/((j:ℝ)+1)) atTop (𝓝 L) := by
    simpa only [Function.comp_def,add_zero] using (hlim.comp (tendsto_add_atTop_nat 1)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => (1:ℝ)/(j+1)) atTop (𝓝 0))
  have hxle : F x ≤ L := ge_of_tendsto hlim' (Eventually.of_forall fun j => hmax j (hux j))
  refine ⟨x,?_,?_⟩
  · have hh := hux 0
    have hnn := mul_nonneg hδ.le (dn x0 x)
    dsimp only [R] at hh
    rw [hu0] at hh
    linarith
  · intro y
    by_contra hnot
    have hlt : F x+δ*d x y < F y := lt_of_not_ge hnot
    have hy : R x y := hlt.le
    have hyle : F y ≤ L := ge_of_tendsto hlim'
      (Eventually.of_forall fun j => hmax j (htrans (hux j) hy))
    have hnn := mul_nonneg hδ.le (dn x y)
    linarith

end CAT0Fillings
end

end OAI
