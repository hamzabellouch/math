import OAI.Combinatorics.HadwigerCounterexample.RestrictedComparisonLaws

namespace OAI

/-! # Histogram Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators
variable {A X B C Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]

def fromFlags (μ : Wgt A) (w : Wgt X) (v : A→X→Y) (K : A→X→B) :=
  fun z => ∃ P:A→ Y→ Prop,z=flaggedW μ w v K P

def Haberdash (Q : Wgt B→ Prop) (r : ℕ) (δ R η ε : ℝ) :=
  (∀ p,Q p→SubLaw p) ∧ roster Q r ε ∧ smallSet Q unif δ η ∧
  ∀ P : B→Prop,
    let v := unifOn P
    let H := hung Q P
    roster H r ε ∧ smallSet H v δ η ∧ rosterTail H v R η

variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

namespace Template
set_option maxHeartbeats 1200000 in
theorem controls (v : Template p I) (M : ℕ) (hM : 1≤M)
    (Y : Type) [Fintype Y] [Nonempty Y]
    (C η ε : ℝ) (hC : 0≤C) (hη : 0<η) (hε : 0<ε) :
    ∃ (r : ℕ) (δ R : ℝ), 0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n; let A := UnitType p n N
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      ∀ (w : Wgt A), IsLaw w →
      (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) →
      ∀ (f : A→Inputs p n I→Y),
        let Q := fromFlags w (prodW x) f (v.resultKey)
        Haberdash Q r δ R η ε := by
  classical
  obtain ⟨V,hV⟩ := hist_calendar v M hM C hC
  let U := V + log (num Y)
  obtain ⟨δ,hδ,_,hh⟩ := ui_threshold U η hη
  obtain ⟨r,a,ha,he⟩ := ample_thresh U (ε/2) (by positivity)
  obtain ⟨s,hR⟩ := roster_price r ε hε
  let D := min a δ; let z := max r 2
  refine ⟨s,δ,δ⁻¹,hδ,inv_pos_of_pos hδ,?_⟩
  filter_upwards [hV z D (Nat.cast_nonneg _) (lt_min ha hδ)]
    with n hn N A m hN w hw h x hx hz f Q
  let X := prodW x
  let K := resultKey v (n:=n) (N:=N)
  let B := Keys (p:=p) v.t N
  let μ := colored w X f
  let q := coloredP X f K
  have hX : IsLaw X := prodW_law hx
  have hu := colored_ultra hw hX K f
  have hg : tariffs μ q z D U := by
    intro C _ hC F hF
    refine (colored_budget K f F hX hw).trans ?_
    exact add_le_add_left (hn m hN w hw h x hx hz _ (by exact_mod_cast hC) F hF) _
  have h1 := tariffs_monotone hg (le_max_left ..) (min_le_left ..)
  have h2 := tariffs_monotone hg (le_max_right ..) (min_le_right ..)
  have ha := he (A×Y) B μ q hu h1
  have h3 (y : Wgt B) (hy : Q y) : catalog μ q y := by
    obtain ⟨P,rfl⟩ := hy
    exact flag_catalog K f P hX hw
  have h4 (y : Wgt B) (hy : Q y) : SubLaw y := hu.cat_sub _ (h3 y hy)
  have hi : roster Q s ε :=
    roster_mono Q _ h3 s ε (hR (A×Y) B μ q hu ha)
  have hj : smallSet Q unif δ η := fun i ht S hS =>
      (pr_mono_left (hu.cat_dom i (h3 i ht)).2 S).trans (hh (A×Y) B μ q hu h2 S hS)
  exact ⟨h4,hi,hj,fun P => ⟨hung_roster Q P _ _ hi,hung_small Q P _ _ hj,hung_tail Q P h4
    _ _ hδ hj⟩⟩
end Template
end HadwigerCounterexample

end

end OAI
