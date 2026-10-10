import OAI.Combinatorics.HadwigerCounterexample.CompatibleTableEvents

namespace OAI

/-! # Incompatible Mass Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass
variable {p : Shape} {n N K M s0 : ℕ} {q : PreparationParameters}

def feeSeal (p:Shape) (K:ℕ) := (1/4 : ℝ)/num (Fin (2^deckMax p K))
theorem feeSeal_pos (p:Shape) (K:ℕ) : 0<feeSeal p K := by unfold feeSeal num; positivity

private theorem mix_parade {A I:Type} [Fintype A] [Fintype I]
    (w:Wgt I) (f:I→Wgt A) (P:A×A→Prop) :
    pr (pairW (mixW w f) (mixW w f)) P = avg (pairW w w) (fun i=>pr (pairW (f i.1) (f i.2)) P) := by
  rw [←mix_data]; unfold pr; rw [mixW_avg]

set_option maxHeartbeats 1400000 in
theorem sparks_extract (m:Mixer p n) (U:Wgt (UnitType p n N)) (z:BMark p n N) (r:F)
    (w:LeafMixture p n N) (t: Station p n N q.pins w) (ht:t.bank)
    (hE:AnalyticParameters p M q s0)
    (h:Settled w m q U z r)
    (hv:0<w.amount U) :
    let P := shimmer z r
    let f:=w.sap U; let v:=pairW f f
    pr v P ≤ 2*pr v (fun x=>P x∧¬secureAt p w.rooting x) +
      ∑ i:Scrip p q.pins,t.berth i.2.2 m i.2.1 U (feeSeal p q.pins) := by
  classical
  intro P f v
  obtain ⟨hp,hK,hw⟩:= h.readyC
  obtain ⟨hx,hy⟩:= rebuild hp.nz hK.part (fun i hi=>(hK.leaf _ hi).pos) hv
  let u:= portionW U w.T; let A (i:w.T):= partW U i.val; let W := pairW u u
  have hm : IsLaw W:=pairW_law hx hx
  have hu i:IsLaw (A i):=on_law hp.nz (hK.leaf _ i.property).pos
  let X:= UnitType p n N; let P':=fun x:X×X=> P x ∧ ¬secureAt p w.rooting x
  let J:=Scrip p q.pins
  let G (j:J) (i:w.T×w.T):=charter t j.2.2 m j.2.1 U (feeSeal p q.pins) i
  let S(i:w.T×w.T) := pairW (A i.1) (A i.2)
  have he :
      ∀ i:w.T×w.T,pr (S i) P ≤ 2*pr (S i) P'+ind (∃ j:J,G j i) := by
    intro i
    have hS:IsLaw (S i):=pairW_law (hu _) (hu _)
    have hi (x:X×X) (hx:S i x ≠0) : x.1∈i.1.val ∧ x.2∈i.2.val :=
      ⟨(onW_ne (left_ne_zero_of_mul hx)).1,(onW_ne (right_ne_zero_of_mul hx)).1⟩
    by_cases hC : ∃ j:J,G j i
    · rw [ind_one hC]; exact (pr_le_tot hS.nz).trans (hS.total.le.trans
        (le_add_of_nonneg_left (mul_nonneg (by norm_num) (pr_nonneg hS.nz))))
    rw [ind_zero hC,add_zero]
    by_cases he : pr (S i) P≤0
    · exact he.trans (mul_nonneg (by norm_num) (pr_nonneg hS.nz))
    · have he' : pr (S i) P=1 := by
        obtain ⟨x,hx,hx'⟩:=exists_of_pr_pos hS.nz (lt_of_not_ge he)
        obtain ⟨T,hT,hA,hB⟩:=h.hard
        obtain ⟨b0,h1,_⟩:=hB _ i.1.property; obtain ⟨b2,h2,_⟩:=hB _ i.2.property
        have hp' (y : X×X) (hy:S i y≠0):P y := by
          obtain ⟨hβ,hβ'⟩:= hi x hx'.ne'
          obtain ⟨ha,hb⟩:= hi y hy
          have he:= phase_fixed z T _ _ _ _ h1 h2 ha hβ hb hβ' (hA _ i.1.property _ ha)
            (hA _ i.2.property _ hb)
          exact he.trans hx
        have hf' : pr (S i) P=pr (S i) (fun _=>True):= avg_congr (fun i hi=> (ind_one (hp' _ hi)).trans
          ind_true.symm)
        rw [hf',pr_true,hS.total]
      let B:= Fin (2^deckMax p q.pins)
      let Q j (x:X×X):=P x∧ berthTicket (w.pin i.1.val) (w.pin i.2.val) (t.mails i.1 i.2 j) x
      have hiP x (hx:S i x ≠0) (hP:P x):P' x∨∃ j,Q j x := by
        by_cases hp :secureAt p w.rooting x
        · right
          obtain ⟨j,hj⟩:= issueTicket x.1 x.2 w t i.1 i.2 hK.part (hi x hx).1 (hi x hx).2 ht hp
          exact ⟨j,hP,hj⟩
        exact Or.inl ⟨hP,hp⟩
      let a:=feeSeal p q.pins
      have hD j: pr (S i) (Q j)<2*a:= lt_of_not_ge (fun h' => hC (
        invoke t i.1 i.2 U m z j r a (feeSeal_pos _ _) hE h ht h'))
      have hz : pr (S i) P≤ pr (S i) P'+1/2 := by
        refine ((pr_on_mono hS.nz hiP).trans (pr_or_le hS.nz)).trans (add_le_add_right ?_ _)
        refine (pr_exists_le hS.nz _).trans ((Finset.sum_le_sum fun i _=>(hD i).le).trans_eq ?_)
        simp only [sum_const,card_univ,nsmul_eq_mul]; unfold a feeSeal
        change num B*(2*(1/4/num B))=_
        have hh : 0<num B := by unfold B num; positivity
        field_simp; norm_num
      linarith only [hz,he']
  have hz (P : X×X→Prop) : pr v P=avg W (fun i=>pr (S i) P) := by
    have hy : f=mixW u A:=hy
    unfold v; rw [hy]
    exact mix_parade ..
  rw [hz,hz]
  refine (avg_mono hm.nz he).trans ?_
  rw [avg_add,avg_mul']
  exact add_le_add_right (pr_exists_le hm.nz G) _

variable {l:Filter ℕ} {m:cycleM p} {w:tale p M} {s:rhythms p M}

set_option maxHeartbeats 1400000 in
theorem dim_end (h:veil p M q s0 l m s w) (t:Stations p M q.pins s) (ht:∀ᶠ n in l,(t n).bank)
    (hL:l.NeBot)
    (b:Sketch p M) (hb:q.bright l p M m s b) (hf:q.glimmer l p M w s b) : False := by
  classical
  obtain ⟨heq,δ,hδ,hU⟩:=hf
  let N (n:ℕ):= M*n; let z n:=((N n):ℝ); let K:=q.pins; let J:= Scrip p q.pins; let a:= feeSeal p K
  have hz : Tendsto (fun n:ℕ=>(n:ℝ)) l atTop:= tendsto_natCast_atTop_atTop.mono_left h.timeL
  let Ω (j:J) n:= (t n).berth j.2.2 (m n) j.2.1 (w n) a *z n^4
  have ho (j:J) : Tendsto (Ω j) l (𝓝 0) := by
    have hk := ((dimBerth t h j.2.2 j.2.1 (feeSeal_pos p K)).poly hz 4).lim hz
    have hl := hk.mul_const ((M:ℝ)^4)
    rw [zero_mul] at hl
    exact hl.congr (fun i=>by unfold Ω z N; push_cast; ring)
  have hz' := trend_sizes l h.timeL h.easel.enter.first.hM
  have hR:= tendsto_finsetSum univ (fun j _=>ho j)
  have he: ∀ᶠ i in l,∑ j:J,Ω j i<δ/2:=hR.eventually
    (gt_mem_nhds (by simp only [sum_const_zero]; positivity))
  have hi : ∀ᶠ n in l,False := by
    filter_upwards [h.moment,ht,h.durableS.mass.positive,h.durableS.shape,
      hU,hb.engraved,hz'.2.eventually (eventually_gt_atTop 0),he] with n hn ht hM hK hL hB hz hT
    obtain ⟨hh,hX,hF⟩:=hL
    let W:=s n
    have hv : Settled W (m n) q (w n) (b.m n) b.r := by
      refine ⟨⟨hn.1.law,hK.1,fun i hi x hx=>?_⟩,hh⟩
      obtain ⟨hA,hB,hC⟩:=hB i hi x hx
      exact ⟨hK.2 i hi x hx,hC heq,fun i=>(hA.1 i).2,hB⟩
    have hm : matchProg b n=shimmer (b.m n) b.r:= by unfold matchProg; rw [heq]; rfl
    have heq := sparks_extract (m n) (w n) (b.m n) b.r W (t n) ht h.easel hv hM
    dsimp only at heq; rw [← hm] at heq
    let u:= glow s w b n
    let B (j:J):=(t n).berth j.2.2 (m n) j.2.1 (w n) a
    change u ≤ 2*gleam s w b n+∑ j:J,B j at heq
    change ∑ j:J,B j*z n^4 <_ at hT
    rw [← Finset.sum_mul] at hT
    have hz :0< z n^4:=pow_pos hz _
    have hh := (lt_div_iff₀ hz).mpr hT
    change δ/(z n^4)≤ u at hX
    change _≤0.001*u at hF
    rw [show δ/2/z n^4=δ/z n^4/2 from by ring] at hh
    linarith only [hh,hX,hF,heq,div_pos hδ hz]
  exact hi.exists.elim (fun _ h=>h)
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
