import OAI.Combinatorics.HadwigerCounterexample.HistogramEnergyScales

namespace OAI

/-! # Unfiltered Histogram Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter Matrix Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N M : ℕ}
instance rackFintype {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) : Fintype (Rack I N) := inferInstance

def stamina {B : Type} [Fintype B]
    (q : Wgt B) (δ : ℝ) := ∀ i,q i≠0→δ ≤ q i

theorem stamina_buy {δ : ℝ} (hδ : 0<δ) : ∃ u : ℝ,0≤u ∧ bp (-u) ≤ δ := by
  have ht := bp_tendsto_zero (a:=1) zero_lt_one
  obtain ⟨u,hu,hb⟩ := ((eventually_ge_atTop (0:ℝ)).and (ht.eventually
    (eventually_le_nhds hδ))).exists
  exact ⟨u,hu,by simpa using hb⟩
namespace Template
variable (v : Template p I)

/-- full query data key function -/
def resultKey (o : UnitType p n N) (x : Inputs p n I) :=
  (v.draw x).keys v.t o
def heatMap (o : UnitType p n N) (w : I→Wgt (Knobs p.g n)) :=
  mapW (prodW w) (v.resultKey o)

variable {B : Type} [Fintype B]

set_option maxHeartbeats 1200000 in
theorem roadmap {l : ℕ} {r u E V : ℝ} (v : Template p I) (C : ℝ)
    (z : TollBar M C I (KeySlots p v.t) (Ports p)
    (globPort p v.t v.aim) n l r u E V)
    (hE : 0≤E) (hu : 0 ≤ u)
    (m : Mixer p n) (hN : 2*num (Full p n)<↑(M*n))
    (f : Keys (p:=p) v.t (M*n)→ B)
    (hB : num B ≤ r)
    (h : stamina (mapW unif f) (bp (-u)))
    (w : Wgt (UnitType p n (M*n))) (hw : IsLaw w)
    (hh : ∀ i,w i ≤ bp (C*↑(M*n))*pairW (raw m (M*n)) (raw m (M*n)) i)
    (x : I→Wgt (Knobs p.g n)) (hx : ∀ i,IsLaw (x i))
    (hz : ∀ i,mapW (x i) (freePart p)=unif) :
    avg w (fun i => tension (mapW (heatMap v i x) f) (mapW unif f)) ≤ V := by
  classical
  let N := M*n
  let W := UnitType p n N
  let D := Keys (p:=p) v.t N
  let q := mapW unif f
  let X := prodW x
  let g := globPort p v.t v.aim
  let s := v.doubleP n
  have hum : IsLaw (unif : Wgt D) := unif_law
  have hq : IsLaw q := mapW_law hum f
  let t := num (Fin l)*num I-n
  let F (i : W) := f∘v.resultKey i
  let Q (x) := draws (Fin l) q x
  have h0 (i : D) : unif i≠0 := by rw [unif_apply]; positivity
  have h1 (i : D) : q (f i) ≠0 := lsupp_hit hum.nz f i (h0 i)
  have h2 (i) (y : Fin l→B) (hF : s.free i) :
      mapW w (fun x => F x ∘ i) y≤ bp (E*l)*Q y := by
    by_cases hy : mapW w (fun x => F x∘i) y =0
    · rw [hy]; exact mul_nonneg (bp_pos _).le ((draws_law hq).nz _)
    let Λ := tied g (Fin l)
    let P (j : Fin l) (x : Rack (KeySlots p v.t) N) := f ((scatter v.t N).symm x)=y j
    have ht (j : Fin l) :
        pr unif (P j)=q (y j) := by
      rw [show pr unif (P j) = pr (mapW unif (scatter v.t N).symm) (fun i => f i=y j) from
        (mapW_pr unif (scatter v.t N).symm (fun i => f i=y j)).symm, unif_equiv]; rfl
    have hr (j : Fin l) :
        bp (-u) ≤ pr unif (P j) := by
      obtain ⟨o,ho,h'⟩ := lsupp_witness hy
      rw [ht, ← congr_fun h' j]
      exact h _ (h1 _)
    let A := pooled (s.left ∘ i)
    let Z := database m A A
    have hL := many_frames (N:=N) Λ Z z.frame u hu P hr z.peak
    let μ := raw m N
    have hk :
        mapW (pairW μ μ) (fun x => F x ∘ i) y =
        pr (rackStation Z N) (fun x => ∀ j,P j (led j x)) := by
      let e (a : Rack (Fin l × KeySlots p v.t) N) := ∀ j,P j (led j a)
      let K (o : Forum p n N (Ports p)) := peekR p Λ A A o
      have ht : mapW (pairW μ μ) (K ∘ mergeR p) = rackStation Z N := by
        rw [← mapW_nested,law_mergeR]; exact law_peekR m hN hF.1 hF.2
      have he (o : W) : e (K (mergeR p o)) ↔ F o ∘ i=y := by
        unfold e K Λ P A; simp_rw [peek_pooled,Function.comp_apply]
        rw [funext_iff]
        have ht (j : Fin l) :
            peekR p g (s.left (i j)) (s.left (i j)) (mergeR p o)=scatter v.t N
              (v.resultKey o (i j)) := double_show v _ _
        simp_rw [ht,Equiv.symm_apply_apply]
        rfl
      unfold mapW
      change _=pr (rackStation Z N) e
      rw [←ht,mapW_pr]; simp_rw [Function.comp_apply,he]
    simp_rw [ht] at hL
    refine (pr_cap hh _).trans ?_
    change bp _ * (mapW (pairW μ μ) _ _)≤_
    rw [hk]
    exact (mul_le_mul_of_nonneg_left hL (bp_pos _).le).trans
      (le_trans (le_of_eq (Eq.symm (mul_assoc _ _ _))) (mul_le_mul_of_nonneg_right z.cap
        ((draws_law hq).nz y)))
  have hv : 0<(l:ℝ) := by exact_mod_cast z.pos
  have he := path_energy w X q F hw (prodW_law hx) hq (fun i j => h1 _) u hu h
    l (fun i => s.free i) (bp t)
    (free_price v n x hx hz g (glob_inj v)) (E*l) (by positivity) (fun i h y => h2 i y h)
  unfold heatMap; simp_rw [mapW_nested]
  apply le_of_mul_le_mul_left _ hv
  apply he.trans
  refine le_trans ?_ z.charge
  exact add_le_add_left (mul_le_mul_of_nonneg_right hB (log_nonneg (by linarith))) _

theorem hist_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ V : ℝ,∀ r δ : ℝ, 0≤r → 0<δ →
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n), 2*num (Full p n)<N →
    ∀ (w : Wgt (UnitType p n N)), IsLaw w →
    (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
    ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
    (∀ i,mapW (x i) (freePart p)=unif) →
    ∀ (B : Type) [Fintype B],num B ≤ r →
    ∀ (f : Keys (p:=p) v.t N → B), stamina (mapW unif f) δ →
    avg w (fun i => tension (mapW (heatMap v i x) f) (mapW unif f)) ≤ V := by
  obtain ⟨s,E,V,hs,hE,h⟩ := toll_calendar M hM C hC I _ _ (globPort p v.t v.aim)
  refine ⟨V,fun r δ hr hδ => ?_⟩
  obtain ⟨u,hu,hh⟩ := stamina_buy hδ
  filter_upwards [h r u hr hu]
    with n hn N m hN w hw hW x hx hz B _ hB f hF
  exact roadmap v C hn hE hu m hN f hB (fun i hi => hh.trans (hF i hi)) w hw hW x hx hz

end Template
end HadwigerCounterexample

end

end OAI
