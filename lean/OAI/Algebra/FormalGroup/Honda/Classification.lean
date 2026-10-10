import OAI.Algebra.FormalGroup.Honda.Correction

namespace OAI

noncomputable section

namespace HeightThree.HondaClassification
open MvPowerSeries HeightThree.HondaJets HeightThree.HondaLeading
open HeightThree.HondaTarget HeightThree.HondaFrobenius HeightThree.HomogeneousCocycle
open HeightThree.CoordinateTransport HeightThree.HondaCorrection
variable {K : Type*} [Field K]

lemma all_laws_jet2 (F G : FormalGroup K) : EqJet 2 F.toPowerSeries G.toPowerSeries := by
  have hf := pair_linear F (X 0 : MvPowerSeries (Fin 2) K) (X 1) (by simp) (by simp)
  have hg := pair_linear G (X 0 : MvPowerSeries (Fin 2) K) (X 1) (by simp) (by simp)
  simp only [pair,pair_subst_self] at hf hg
  exact hf.trans hg.symm

structure Approximation (p h : ℕ) (F G : FormalGroup K) (n : ℕ) where
  law : FormalGroup K
  comm : law.IsComm
  coordinate : CoordinateIso G law
  match_law : EqJet (n+2) F.toPowerSeries law.toPowerSeries
  honda : multiplicationSeries law p=PowerSeries.X^(p^h)
  strict : EqJet 2 coordinate.series PowerSeries.X

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p] (h : ℕ)
  (F G : FormalGroup K) [F.IsComm] [G.IsComm]
  (hF : multiplicationSeries F p=PowerSeries.X^(p^h))
  (hG : multiplicationSeries G p=PowerSeries.X^(p^h))

noncomputable def start : Approximation p h F G 0 where
  law := G
  comm := inferInstance
  coordinate := {
    series := PowerSeries.X
    inverse := PowerSeries.X
    zero_series := PowerSeries.constantCoeff_X
    zero_inverse := PowerSeries.constantCoeff_X
    left_inv := PowerSeries.X_subst _
    right_inv := PowerSeries.X_subst _
    preserves_addition := by
      simp only [PowerSeries.subst_X (.of_constantCoeff_zero G.zero_constantCoeff),
        PowerSeries.subst_X (PowerSeries.HasSubst.X _),pair_subst_self] }
  match_law := all_laws_jet2 F G
  honda := hG
  strict := by exact EqJet.refl 2 (PowerSeries.X : PowerSeries K)

omit [G.IsComm] in
include hF in
lemma advance_exists (n : ℕ) (s : Approximation p h F G n) :
    ∃t : Approximation p h F G (n+1), EqJet (n+2) t.coordinate.series s.coordinate.series := by
  let : s.law.IsComm := s.comm
  have hc := leading_isCocycle F s.law (n+2) p s.match_law (hF.trans s.honda.symm)
  have hfixed := map_leading F s.law (n+2) (iterateFrobenius K p h)
    (honda_coefficients_fixed p h F hF) (honda_coefficients_fixed p h s.law s.honda)
  obtain ⟨a,ha,hD⟩ := fixed_coboundary_scalar p _ (n+2) (by omega) hc
    (leading_homogeneous F s.law (n+2)) (iterateFrobenius K p h) hfixed
  let c := step (n+2) (by omega) a
  have he : EqJet (n+2) ((CoordinateIso.trans s.coordinate (c.iso s.law)).series) s.coordinate.series := by
    exact step_jet (n+2) a _ s.coordinate.zero_series
  let t : Approximation p h F G (n+1) := {
    law := c.transport s.law
    comm := inferInstance
    coordinate := CoordinateIso.trans s.coordinate (c.iso s.law)
    match_law := by simpa only [Nat.add_right_comm] using
      (step_improves F s.law (n+2) (by omega) s.match_law a hD).symm
    honda := honda_transport p h (n+2) (by omega) a ha s.law s.honda
    strict := (he.mono (by omega)).trans s.strict }
  exact ⟨t,he⟩

noncomputable def advance (n : ℕ) (s : Approximation p h F G n) :
    {t : Approximation p h F G (n+1) // EqJet (n+2) t.coordinate.series s.coordinate.series} :=
  ⟨(advance_exists p h F G hF n s).choose,(advance_exists p h F G hF n s).choose_spec⟩

noncomputable def tower : (n : ℕ) → Approximation p h F G n
  | 0 => start p h F G hG
  | n+1 => (advance p h F G hF n (tower n)).val

lemma tower_step (n : ℕ) :
    EqJet (n+2) (tower p h F G hF hG (n+1)).coordinate.series
      (tower p h F G hF hG n).coordinate.series :=
  (advance p h F G hF n (tower p h F G hF hG n)).prop

end HeightThree.HondaClassification

namespace HeightThree.HondaJetLimit
open MvPowerSeries HeightThree.HondaJets
variable {K : Type*} [Field K]

def limit (s : ℕ → PowerSeries K) : PowerSeries K := PowerSeries.mk (fun m=>(s m).coeff m)

lemma later_jet (s : ℕ → PowerSeries K) (hs : ∀n,EqJet (n+2) (s (n+1)) (s n))
    (n m : ℕ) (hm : n ≤ m) : EqJet (n+2) (s m) (s n) := by
  induction m,hm using Nat.le_induction with
  | base => exact EqJet.refl _ _
  | succ m hm ih => exact ((hs m).mono (by omega)).trans ih

lemma stable_coeff (s : ℕ → PowerSeries K) (hs : ∀n,EqJet (n+2) (s (n+1)) (s n))
    (m i j : ℕ) (hi : m < i+2) (hj : m < j+2) : (s i).coeff m=(s j).coeff m := by
  have hi' := later_jet s hs i (max i j) (le_max_left _ _)
  have hj' := later_jet s hs j (max i j) (le_max_right _ _)
  have hi'' := hi' (Finsupp.single () m) (by simpa using hi)
  have hj'' := hj' (Finsupp.single () m) (by simpa using hj)
  exact hi''.symm.trans hj''

lemma limit_jet (s : ℕ → PowerSeries K) (hs : ∀n,EqJet (n+2) (s (n+1)) (s n))
    (n : ℕ) : EqJet (n+2) (limit s) (s n) := by
  intro d hd
  have he : d=Finsupp.single () (d ()) := Finsupp.unique_single d
  rw [he] at hd ⊢
  simp only [Finsupp.degree_single] at hd
  change PowerSeries.coeff (d ()) (limit s)=PowerSeries.coeff (d ()) (s n)
  rw [limit,PowerSeries.coeff_mk]
  exact stable_coeff s hs (d ()) (d ()) n (by omega) hd

end HeightThree.HondaJetLimit

namespace HeightThree.HondaClassification
open MvPowerSeries HeightThree.HondaJets HeightThree.HondaLeading
open HeightThree.HondaTarget HeightThree.HondaFrobenius HeightThree.HomogeneousCocycle
open HeightThree.CoordinateTransport HeightThree.HondaCorrection HeightThree.HondaJetLimit
variable {K : Type*} [Field K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p] (h : ℕ)
  (F G : FormalGroup K) [F.IsComm] [G.IsComm]
  (hF : multiplicationSeries F p=PowerSeries.X^(p^h))
  (hG : multiplicationSeries G p=PowerSeries.X^(p^h))

include hF hG in

theorem strict_honda_isomorphic : ∃ e : CoordinateIso G F, e.series.coeff 1=1 := by
  let T := tower p h F G hF hG
  let s : ℕ → PowerSeries K := fun n=>(T n).coordinate.series
  have hs : ∀n,EqJet (n+2) (s (n+1)) (s n) := tower_step p h F G hF hG
  let u := HondaJetLimit.limit s
  have hu (n : ℕ) : EqJet (n+2) u (s n) := limit_jet s hs n
  have hstrict : EqJet 2 u PowerSeries.X := (hu 0).trans (T 0).strict
  have hz : u.constantCoeff=0 := by
    have hh := hstrict 0 (by simp)
    change MvPowerSeries.constantCoeff u=0
    simpa [PowerSeries.X] using hh
  have hlin : u.coeff 1=1 := by
    have hh := hstrict (Finsupp.single () 1) (by simp)
    simpa [PowerSeries.coeff,PowerSeries.X] using hh
  have hadd : u.subst G.toPowerSeries=F.toPowerSeries.subst ![u.subst (X 0),u.subst (X 1)] := by
    apply MvPowerSeries.ext
    intro d
    let n := d.degree
    let v := (T n).coordinate.series
    have hv0 : v.constantCoeff=0 := (T n).coordinate.zero_series
    have hL : EqJet (n+2) (u.subst G.toPowerSeries) (v.subst G.toPowerSeries) :=
      (hu n).subst_left (fun _ : Unit=>G.toPowerSeries)
        (PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff).const
        (fun _=>G.zero_constantCoeff)
    rw [(T n).coordinate.preserves_addition] at hL
    let a : Fin 2 → MvPowerSeries (Fin 2) K := ![v.subst (X 0),v.subst (X 1)]
    let b : Fin 2 → MvPowerSeries (Fin 2) K := ![u.subst (X 0),u.subst (X 1)]
    have ha0 : ∀i,(a i).constantCoeff=0 := by
      intro i; fin_cases i <;> exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _ hv0
    have hb0 : ∀i,(b i).constantCoeff=0 := by
      intro i; fin_cases i <;> exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _ hz
    have hM := (T n).match_law.symm.subst_left a (hasSubst_of_constantCoeff_zero ha0) ha0
    have hR : EqJet (n+2) (F.toPowerSeries.subst a) (F.toPowerSeries.subst b) := by
      apply EqJet.subst_right _ _ _ (hasSubst_of_constantCoeff_zero ha0) (hasSubst_of_constantCoeff_zero hb0)
      intro i; fin_cases i
      · exact (hu n).symm.subst_left (fun _ : Unit=>(X 0 : MvPowerSeries (Fin 2) K))
          (PowerSeries.HasSubst.X 0).const (by simp)
      · exact (hu n).symm.subst_left (fun _ : Unit=>(X 1 : MvPowerSeries (Fin 2) K))
          (PowerSeries.HasSubst.X 1).const (by simp)
    exact ((hL.trans hM).trans hR) d (by dsimp [n]; omega)
  let c := Coordinate.ofSeries u hz (by rw [hlin]; exact isUnit_one)
  exact ⟨{ __ := c, preserves_addition := hadd },hlin⟩

end HeightThree.HondaClassification

end

end OAI
