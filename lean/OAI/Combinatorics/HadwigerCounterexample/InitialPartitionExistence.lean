import OAI.Combinatorics.HadwigerCounterexample.PredictionDichotomy
import OAI.Combinatorics.HadwigerCounterexample.FrameIntersectionBounds
import OAI.Combinatorics.HadwigerCounterexample.TerminalCut

namespace OAI

/-! # Initial Partition Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
namespace PreparationParameters

variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}

theorem born (w : Wgt (UnitType p n N)) (hw : IsLaw w) (m : Mixer p n)
    (h : pairCaps (raw m N) q.L (bp ((q.D:ℝ)*N)) w) :
    nascent q p N w m := by
  refine ⟨hw,fun i x=>?_, h.2.2⟩
  cases i
  · exact h.2.1 _
  exact h.1 _

structure entry (q : PreparationParameters) (p : Shape) (M : ℕ) : Prop where
  first : q.planted p M
  hF : ∀ᶠ n : ℕ in atTop, let N:=M*n;
    ∀ (m : Mixer p n) (w:Wgt (UnitType p n N)), q.nascent p N w m →
     carried w (rawHoles m).unit → ∃ s : LeafMixture p n N,q.entered p N m w s

/-- combines early h & M choices assuming row/selector bounds supplied. -/
theorem stamp (g : ℕ) (q : PreparationParameters)
    (hq : q.allows) (hd : 0 < q.D) (hf : (q.D:ℝ)+q.ζ ≤ (q.ζ-q.ζ/4)*q.e)
    (hk : q.k≤ q.d) (hg : q.spJoint+1 ≤0.49*q.k)
    (hu : 3*q.d+2*q.e+2 ≤ q.u) :
    ∀ᶠ h : ℕ in atTop,∀ p:Shape,p.g=g→p.h=h →
    Odd p.g → 3≤p.g → 1≤p.j → 1≤p.r → (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j) →
    8*q.D <p.g*p.g → (∃ d_:ℕ,4*q.D≤p.g*d_∧2*screenRank p q.e+1 ≤ ((p.g-1)/2)*(p.g-d_)*p.r) →
    ∀ᶠ M : ℕ in atTop, q.entry p M := by
  classical
  have hl : 0≤q.spear := mul_nonneg (bp_pos _).le hq.hL
  have hq' : 0<q.ζ/4:=by have hh:=hq.pos; positivity
  have h1 : 0 ≤ q.spJoint := add_nonneg (Nat.cast_nonneg _) zero_le_one
  filter_upwards [phase_calendar g q.rank q.k q.d q.spJoint q.spear hl h1 hk hg,
    guard_grid g q.pins (3*q.d) 0.0005 (by positivity) (by norm_num)]
    with h hP hG p hp hH hg hg' hj hr hb hf' he
  have hs : 0<(q.D:ℝ)/2 := by positivity
  filter_upwards [hP p hp hH,hG p hp hH,sparse_usual p q.D hd,
    columns_budget p (δ:=1) zero_lt_one 2 1 (by norm_num) zero_le_one,
    raw_ready p hq',eventually_ge_atTop 1]
    with M hm hM hF hS hr' hqM
  have hz := trend_sizes atTop (le_refl _) hqM
  have hh : planted q p M := by
    refine ⟨hq,hqM,hg,hg',hj,hr,hb,hf',he,?_⟩
    filter_upwards [hm,hM,eventually_ge_atTop 1,hr',
      hz.2.eventually (eventually_ge_atTop (2*(q.e:ℝ)^2))] with n hn ht hi hr hN
    obtain ⟨_,hr⟩:=hr
    dsimp only
    have he := hS n hi
    rw [one_mul] at he
    refine ⟨by linarith only [he],?_, (fun m a=> (hr m).2 a),?_,ht⟩
    · have hg : (3*q.d+2*q.e+2:ℝ) ≤ q.u := by exact_mod_cast hu
      have hk := mul_le_mul_of_nonneg_right hg (show (0:ℝ) ≤ (M*n:ℕ) by positivity)
      change _≤((M*n:ℕ):ℝ) at hN
      linarith only [hN,hk]
    intro m
    specialize hn m
    rw [hp]; exact hn
  refine ⟨hh,?_⟩
  filter_upwards [hF,hh.wrap,hz.1.eventually (eventually_gt_atTop 0),
    (((bp_tendsto_zero hq.pos).comp hz.2).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))),
    (((bp_tendsto_zero hs).comp hz.2).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)))]
    with n hn ht hN hA hB N m w hw hx
  let P (x:UnitType p n N) := w x≠0 ∧ (rawHoles m).unit x ∧ joins x≤2*q.D ∧ frameSide p m x
  obtain ⟨s,h1,h2,h3⟩:= LeafMixture.grove_first q.ζ q.D q.e hq.pos hq.small hN
    (ht.2.2.1 m) hw.total hw.law.nz P hf
  refine ⟨s,?_,h1.slide (by unfold leafOld; linarith) le_rfl le_rfl
    (fun x=> mul_nonneg (raw_nonneg ..) (raw_nonneg ..)),h2⟩
  have heq x (h : w x≠0) : (rawHoles m).unit x ∧ frameSide p m x := by
    have he := lt_of_lt_of_le (lt_of_le_of_ne (hw.law.nz _) h.symm) (hw.total x)
    have he : usual p m N x≠0 := by intro hg; rw [hg,mul_zero] at he; exact he.false
    refine ⟨by_contra fun e=>h (hx x e),fun i=>?_⟩
    have hz := raw_carried m N
    cases i
    · exact by_contra fun e => right_ne_zero_of_mul he (hz _ e)
    exact by_contra fun e=> left_ne_zero_of_mul he (hz _ e)
  let Q (x:UnitType p n N):=2*q.D<joins x
  have hi : pr w P=pr w (fun x=>¬Q x) := by
    apply avg_congr
    intro x hx
    simp only [P,Q,(heq x hx).1,(heq x hx).2,and_true,true_and,not_lt]
    exact congrArg ind (propext (and_iff_right hx))
  rw [hi,pr_not,hw.law.total] at h3
  have he : pr w Q≤bp (-((q.D:ℝ)/2)*N) := by
    specialize hn _ _ hw.total
    rwa [neg_div] at hn
  change bp (-q.ζ*N)<1/4 at hA
  change bp _ < 1/4 at hB
  linarith only [he,h3,hB,hA]
end PreparationParameters
end HadwigerCounterexample

end

end OAI
