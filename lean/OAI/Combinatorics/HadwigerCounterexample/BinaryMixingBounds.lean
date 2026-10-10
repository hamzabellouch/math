import OAI.Combinatorics.HadwigerCounterexample.KeyTestCorrespondence

namespace OAI

/-! # Binary Mixing Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

def kappa := wavelength v.Abbey
omit [DecidableEq I] in
theorem kappa_pos : 0<v.kappa := wavelength_pos _

def diffsel (v : Template p I) := ∀ i j, i≠j → v.aim i=v.aim j → v.s i≠ v.s j

omit [DecidableEq I] in
theorem choral_live (v : Template p I) (m : Mixer p n) (hm : binaryGood m)
    (x : UnitType p n N) (hx : litFire p x) (hv : v.diffsel)
    (i : v.Chorus) (c : Vec (v.Abbey i)) (hc : c≠0) :
    let j := v.choral.first i; let l := v.choral.nextP i
    ∃ B, (v.f j).keeps (v.t j) B ∧ (v.f l).keeps (v.t l) B ∧
      n≤5*blockRank B (v.s j) (v.s l) (v.chorusM m x i c) := by
  classical
  rcases i with i|i
  · intro j l
    let a : Vec (MBits p) := fun y => c (.inl y)
    let b : Vec Bool := fun y => c (.inr y)
    have hh : v.s j≠v.s l := hv j l (v.choral.diff (.inl i)) i.property.1
    by_cases h : a=0
    · refine ⟨Block.sharp,Flavor.keepSharp ..,Flavor.keepSharp ..,?_⟩
      have he : indexedSum m a=0 := by simp [h,indexedSum]
      rw [chorus_same]
      change n ≤ 5*blockRank _ _ _ (indexedSum m a+selfSum m b)
      rw [he,zero_add]
      have hz : b≠0 := by
        intro hb; apply hc; funext y
        cases y
        next l => exact congr_fun h l
        next l => exact congr_fun hb l
      exact (hm _ _ hh).2 b hz
    refine ⟨Block.Z,Flavor.keepZ ..,Flavor.keepZ ..,?_⟩
    rw [chorus_same]; exact (hm _ _ hh).1 a b h
  intro j l; refine ⟨Block.Z,Flavor.keepZ ..,Flavor.keepZ ..,?_⟩
  obtain ⟨w,hw,hh⟩ := chorus_cross v m x i c hc
  rw [hh]; exact hx _ _ w hw

theorem resonant (v : Template p I) (m : Mixer p n) (hm : binaryGood m)
    (x : UnitType p n N) (hx : litFire p x) (hv : v.diffsel)
    (w : I → Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (C : ℝ) (hC : 0 < C) (hc : ∀ i j,w i j ≤ C*unif j)
    (s : Script p I) :
    ∀ u : I → Wgt (Knobs p.g n),(∀ i x, |u i x|≤1) →
    |avg (prodW w) (fun z => ind (v.performs s m x z)*prodW u z) -
      v.kappa * ∏ i:I,avg (w i) (u i)|≤ C^2*bp (-(n:ℝ)/10) := by
  classical
  refine hear_band v.choral (v.chime m x) (v.lyrics s) w hw _
    (mul_nonneg (sq_nonneg _) (bp_pos _).le) ?_
  intro i c hc' p q hp hq
  obtain ⟨b,hb,hb',hz⟩ := v.choral_live m hm x hx hv i c hc'
  simp_rw [vectorPhase,v.chime_seq]
  exact spark_condition _ (v.chorusM m x i c) _ _ _ _ _ _ b hb hb' p q hp hq
    _ _ (hw _) (hw _) C hC (hc _) (hc _) hz

theorem resonance_calendar (v : Template p I) (M : ℕ) (hM : 4≤ M) (C L : ℝ) (hL : 0<L) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ m : Mixer p n, binaryGood m →
      v.diffsel → 2*num (Full p n)<N → ∀ ρ : Wgt (UnitType p n N),
      (∀ i,ρ i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      pr ρ (fun i=>¬litFire p i) ≤ bp (-(n:ℝ)*n/8) ∧
      ∀ x : UnitType p n N,litFire p x →
      ∀ w : I → Wgt (Knobs p.g n),(∀ i,IsLaw (w i)) →
      (∀ i j,w i j≤ L*unif j) →
      ∀ (s : Script p I) (u : I→ Wgt (Knobs p.g n)),(∀ i j,|u i j|≤1) →
      |avg (prodW w) (fun z => ind (v.performs s m x z)*prodW u z) -
        v.kappa*∏ i:I,avg (w i) (u i)| ≤ bp (-(1/20:ℝ)*n) := by
  filter_upwards [litFire_calendar p C M hM,pay_nat (a:=1/10) (b:=1/20) (L^2) (by norm_num)]
    with n hn ha N m hm hv hN ρ hρ
  refine ⟨hn m hN ρ hρ,fun x hx w hw hh s u hu => ?_⟩
  exact (resonant v m hm x hx hv w hw L hL hh s u hu).trans
    (by rw [show -(↑n:ℝ)/10 = -(1/10:ℝ)*n by ring]; exact ha)
end Template

theorem scanCap (p : Shape) {n : ℕ} (l : Tag p.g) (z : Digest p.g)
    (f : Flavor p.g) (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (h : z.feasible l f) :
    ∀ x,scopedScan p n l f z x≤(scanPrice p)⁻¹*unif x := by
  intro x
  refine (on_mon (spins_law p n).nz (scanPrice_pos p) (scan_fraction l f z hr hn h)
    x).trans_eq ?_
  rw [spins,← draws_unif]

theorem dialCap (p : Shape) {n : ℕ} (l : Tag p.g) (z : F)
    (f : Flavor p.g) (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (h : canDial p l f z) :
    ∀ x,scopedBit p n l f z x≤(scanPrice p)⁻¹*unif x := by
  intro x
  refine (on_mon (spins_law p n).nz (scanPrice_pos p) (dial_fraction p n _ _ _ hr hn h)
    x).trans_eq ?_
  rw [spins,← draws_unif]
end HadwigerCounterexample

end

end OAI
