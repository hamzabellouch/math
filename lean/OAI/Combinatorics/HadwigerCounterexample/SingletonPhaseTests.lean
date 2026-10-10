import OAI.Combinatorics.HadwigerCounterexample.OffsetFourierBounds

namespace OAI

/-! # Singleton Phase Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N} {A : Type} [Fintype A]

theorem avg_on_support {w f g : Wgt A} (h : ∀ x,0≤w x)
    (he : ∀ x,w x≠0 → f x≤g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum (fun x _ => by
    by_cases hh : w x=0
    · rw [hh,zero_mul,zero_mul]
    exact mul_le_mul_of_nonneg_left (he x hh) (h x))

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 600000 in
theorem single_pitch {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (i : Bool) (R : Party)
    (m : Mixer p n) {ε H : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hH : 0 ≤ H) (hw : bySide p w m H)
    (hp : selPrice p r n N H ε) (ht : num (Atlas p r T) ≤ bp (0.002*N))
    (hN : 2*num (Full p n)-N≤ -1) :
    |pitch p Δ w (unary i) R|≤ glimpsesBill p r H+bp (-0.24*N) ∧
    ((∀ x,w x≠0 → ∀ y,w y≠0 → glimpse p y i (src (s.ix x))) →
      |pitch p Δ w (unary i) R|≤bp (-0.24*N)) := by
  classical
  let C : Sales p n r T := fun M _ y => glimpse p y i (src M)
  have hb M G (hh : standard M) (hh' : standard G) :=
    glimpse_prize m hH hm he hv.sub hw hl hp M G i hh hh' (C M G) (fun _ _ h => h)
  have hf := beat_mix s hl hv (unary i) R i C (fun M => bag_rate m hH hm he hv.sub hw hl hp M i)
    hb ht
  have he : discard (s:=s) w C = avg w (fun x =>
      pr w (fun y => ¬ glimpse p y i (src (s.ix x)))) := pairW_avg ..
  rw [he] at hf
  constructor
  · refine hf.trans (add_le_add_left ?_ _)
    rw [← hv.avg_const (glimpsesBill p r H)]
    apply avg_on_support hv.nz
    intro x hx
    have hX := (hl x hx).1
    exact glimpse_failure m hH hw hv.sub i hN _ r hX.2.2 (fun z =>
      Nat.lt_add_one_iff.mp ((s.ix x).1 z).isLt)
  intro hh
  have hW : avg w (fun x => pr w (fun y => ¬glimpse p y i (src (s.ix x))))=0 := by
    rw [← hv.avg_const 0]
    refine avg_congr (fun x hx => ?_)
    rw [← hv.avg_const 0]
    exact avg_congr fun y hy => ind_zero (by simp [hh x hx y hy])
  rwa [hW,zero_add] at hf

def frequent (w : Wgt (UnitType p n N)) (S : Party) (j : Bool)
    (M G : Atlas p r T) (y : UnitType p n N) :=
  prize p N (cells G) < mapW (s.chart w G) (s.pay M G j S) (s.pay M G j S y)

theorem calm_pitch {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (i : Bool) (R S : Party)
    (m : Mixer p n) {ε H : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hH : 0 ≤ H) (hw : bySide p w m H)
    (hp : selPrice p r n N H ε) (ht : num (Atlas p r T) ≤ bp (0.002*N)) :
    |pitch p Δ w S R| ≤ pr (pairW w w)
      (fun x => s.frequent w S i (s.ix x.1) (s.ix x.2) x.2) + bp (-0.24*N) := by
  classical
  let C : Sales p n r T := fun M G y => ¬ s.frequent w S i M G y
  have hb (M G : Atlas p r T) (hh : standard M) (hh' : standard G) :
      ∀ y,mapW (subW (s.chart w G) (C M G)) (s.pay M G i S) y ≤ prize p N (cells G) := by
    let v := s.chart w G
    let J := s.pay M G i S
    have hw' : SubLaw v := subLaw_sub hv.sub _
    intro y
    by_cases he : mapW v J y≤prize p N (cells G)
    · exact (pr_mono_left (subW_le hw'.nz _) _).trans he
    change pr (subW v (C M G)) (fun x => J x=y) ≤ _
    rw [pr_sub]
    have hx : (fun x => C M G x ∧ J x=y)=(fun _ => False) := by
      funext x
      refine propext (iff_false_intro (fun ⟨h,h'⟩ => he ?_))
      rw [← h']
      exact le_of_not_gt h
    rw [hx,pr_false]; exact (bp_pos _).le
  have hf := beat_mix s hl hv S R i C (fun M => bag_rate m hH hm he hv.sub hw hl hp M i) hb ht
  unfold discard C at hf; simpa only [not_not] using hf

/-- fixed companion Z restrict frequent pair to this list of small Φ values -/
def bids (w : Wgt (UnitType p n N)) (S : Party) (i : Bool)
    (M G : Atlas p r T) (Z : Batch G N) : Finset (Batch M N) :=
  open scoped Classical in
  Finset.univ.filter (fun x => prize p N (cells G)<mapW (s.chart w G) (s.pay M G i S) (x,Z))

theorem bids_mem (w : Wgt (UnitType p n N)) (S : Party) (i : Bool)
    (M G : Atlas p r T) (x : UnitType p n N) :
    s.frequent w S i M G x ↔
      thermal p x S (src M) ∈ s.bids w S i M G (s.bag G i x) := by
  classical
  simp only [bids,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

theorem bids_bound {w : Wgt (UnitType p n N)} (S : Party) (i : Bool)
    (M G : Atlas p r T) (Z : Batch G N) (hw : SubLaw w)
    (h : ∀ x,mapW (s.chart w G) (s.bag G i) x ≤ loseA p N (cells G) 0) :
    (↑(s.bids w S i M G Z).card:ℝ) ≤ bp (0.51*N) := by
  classical
  let f := s.pay M G i S
  let v := s.chart w G
  have hv : SubLaw v := subLaw_sub hw _
  let B := s.bids w S i M G Z
  let P := prize p N (cells G)
  have he (x) (hx : x∈B) : P≤mapW v f (x,Z) := (Finset.mem_filter.mp hx).2.le
  have hg : ↑B.card * P ≤ loseA p N (cells G) 0 := by
    have hZ : ∑ x : Batch M N,mapW v f (x,Z)=mapW v (s.bag G i) Z := by
      let T := fun x => (f x).1
      have hh (x : Batch M N) : (fun y => f y=(x,Z))=
          fun y => s.bag G i y=Z ∧ T y=x := by ext y; simp [Prod.mk.injEq,f,T,pay,and_comm]
      simp only [mapW,hh,sum_pr_tag]
    calc ↑B.card * P = ∑ x ∈ B,P := (by simp)
         _ ≤ ∑ x∈B,mapW v f (x,Z) := Finset.sum_le_sum he
         _ ≤ ∑ x : Batch M N,mapW v f (x,Z) := Finset.sum_le_sum_of_subset_of_nonneg
           (Finset.subset_univ B) (fun i _ _ => pr_nonneg hv.nz)
         _ ≤ loseA p N (cells G) 0 := hZ.trans_le (h Z)
  refine (le_of_mul_le_mul_right (hg.trans_eq ?_) (bp_pos _ : 0<P))
  unfold P prize loseA
  rw [← bp_add]; congr 1; push_cast; ring

end Bazaar
end HadwigerCounterexample

end

end OAI
