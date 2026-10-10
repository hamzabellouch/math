import OAI.Combinatorics.HadwigerCounterexample.PairedOptions

namespace OAI

/-! # Paired Collision Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates}

theorem quillState {i : Bool} {w : Quill p q d i} {t z} (h : w.moral t z) (hr : 1≤p.r)
    (hn : 2*p.r ≤ n) :
    IsLaw ((w.pen t).state z n) := prodW_law (fun j=> dial_law p n _ _ _ hr hn (Quill.canDraw _ _ h j))

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

def clash (p : Shape) (m : Mixer p n) (N : ℕ) :=
   fun x : UnitType p n N × UnitType p n N => (rawHoles m).conflict x.1 x.2

def beamPrice (p : Shape) (N : ℕ) := bp (((kmax p:ℝ)+0.02)*N)

structure earnsScore (p : Shape) (n N K : ℕ) (ζ : ℝ) : Prop where
  hr : 1≤p.r
  hn : 2*p.r≤n
  solid : realizeAssum p K
  smooth : 0 ≤ ζ
  low : ζ ≤ 0.004
  light : ζ*(kmax p) ≤ 0.004
  hN : 100 ≤ N
  gram : (dim (CheckGram p n) : ℝ) ≤ 0.01*N
  budget : (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N

set_option maxHeartbeats 1400000 in
theorem sellPoint (w : Typus p q d e)
    (m :Mixer p n) (μ : Wgt (UnitType p n N)) (i j : s.T) (k : Fin (2^deckMax p K))
    {C ζ : ℝ} (hp : s.strength μ (PreparationParameters.usual p m N) C ζ K) (hw : IsLaw μ)
    (he : earnsScore p n N K ζ) :
    matchScore v w m μ i j k ≤ beamPrice p N *
      pr (pairW (partW μ i.val) (partW μ j.val)) (clash p m N)+2* bp (-0.005*N) := by
  classical
  have hA := hp.leaf i.val i.property; have hB := hp.leaf j.val j.property
  let a:=w.qA.pen w.t; let b:=w.qB.pen w.t
  let ia:=s.pin i.val; let ib:=s.pin j.val
  let u:=partW μ i.val; let u':=partW μ j.val
  let F:=frontPage v w m i j k; let G:=backPage v w m i j k
  let T:=v.mails i j k; let x:=v.cAxes i d; let y:=v.cAxes j e
  let Q (z : Inputs p n (Messenger q)) (o : UnitType p n N) :=
    F o ∧ w.qA.deposit w.t w.z m o x z
  let R (z : Inputs p n (Messenger q)) (o : UnitType p n N) :=
    G o ∧ w.qB.deposit w.t w.z m o y z
  have hu : IsLaw u:= on_law hw.nz hA.pos
  have hu' : IsLaw u':= on_law hw.nz hB.pos
  let δ := pr (pairW u u') (clash p m N)
  have hδ : 0≤δ := pr_nonneg (pairW_law hu hu').nz
  change overlap (lawNu p N w.t w.z)
    (Volley.hist a.draw w.t u (a.state w.z n) Q) (Volley.hist b.draw w.t u' (b.state w.z n) R) ≤
      beamPrice p N*δ+ _
  by_cases hg : news v w i j k
  · obtain ⟨⟨hf,hE,hF,hQ,hR,hr,hr'⟩,⟨hX,ha,hS,hT⟩,hY,hb,hS',hT'⟩:=hg
    have hq : kslots p (Messenger q) ≤ kmax p :=
      slots_budget (a.draw (n:=n) (fun _=>0)) (shots_ok true (a.draw (fun _ => 0)) rfl hf)
    apply le_trans (Volley.collision a.draw b.draw m (a:=ia) (b:=ib) (q:=qorth K) (K:=K)
      (a.state w.z n) (b.state w.z n) Q R (fun i x (h:Q i x)=> ⟨h.1.2.1,h.1.2.2.1⟩)
      (fun i x (h:R i x)=>⟨h.1.2.1,h.1.2.2.1⟩)
      _ ha hb hA.bound hB.bound he.low (le_trans
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hq) he.smooth) he.light) hq hu.sub hu'.sub
      (quillState hE he.hr he.hn).sub (quillState hF he.hr he.hn).sub hA.clear hB.clear
      he.hN he.gram he.budget (ownPart w.t w.z))
    · refine add_le_add_left (mul_le_mul_of_nonneg_right (bp_le ?_) hδ) _
      exact mul_le_mul_of_nonneg_right (add_le_add_left (Nat.cast_le.mpr hq) _) (by positivity)
    intro u v o ho z hz hv
    have h1 (u:Inputs p n (Messenger q)) (v:Inputs p n (Messenger q)) : (a.draw u).bounded
        (b.draw v).obj := shots_ok true _ rfl hf
    have h2 (u:Inputs p n (Messenger q)) (v:Inputs p n (Messenger q)) : (b.draw v).bounded
        (a.draw u).obj := shots_ok false _ rfl hf
    obtain ⟨⟨_,ha',ha0,ham⟩,hG,hh',_⟩:= ho
    obtain ⟨⟨_,hb',hb0,hbm⟩,hH,hh0,_⟩:= hz
    refine ⟨a.draw_legal _, b.draw_legal _,rhyme_match _ _ _ x y _ _ _ _ u v m o z hG hH hR,?_⟩
    apply gradient_realization (a.draw u) (b.draw v) m o z ia ib T K he.solid (h1 u v) (h2 u v)
      (a.draw_legal _) (b.draw_legal _) (ha _) (hb _) hA.bound hB.bound ha' hb' ham hbm hT hT'
      _ _ hv ha0 hb0 _ _
    · exact still_recipe _ true _ _ _ hX _ _ _ _ _ _ hG _ rfl w.z hE.2.1 hQ hS
    · exact still_recipe _ false _ _ _ hY _ _ _ _ _ _ hH _ rfl w.z hF.2.1 hQ hS'
    · exact procl_grad _ _ _ he.solid.odd _ _ _ _ _ _ _ _ m _ _ hG hH w.qA.script hr hh'
    exact procl_grad _ _ _ he.solid.odd _ _ _ _ _ _ _ _ m _ _ hH hG w.qB.script hr' hh0
  · have hh (x): Volley.hist a.draw w.t u (a.state w.z n) Q x=0 := by
      unfold Volley.hist
      have ht y : pr u (fun i=> Q y i ∧ (a.draw y).keys w.t i=x)=0 := by
        simp [Q,F,frontPage,notified,hg,pr_false]
      simp_rw [ht]; simp
    unfold overlap
    simp only [density,hh,zero_div,zero_mul]
    have hz : 0≤ beamPrice p N*δ:=mul_nonneg (bp_pos _).le hδ
    rw [show avg (lawNu p N w.t w.z) (fun _ => 0) = 0 from (by simp only [avg_const,mul_zero])]
    exact add_nonneg hz (mul_nonneg (by norm_num) (bp_pos _).le)

set_option maxHeartbeats 800000 in
theorem arena_bound (w : Typus p q d e)
    (m: Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
    {C ζ : ℝ} (hp : s.strength μ (PreparationParameters.usual p m N) C ζ K) (hw : IsLaw μ)
    (h : 0<s.amount μ) (he : earnsScore p n N K ζ) :
    arena v w m μ k ≤ beamPrice p N *
      pr (pairW (s.sap μ) (s.sap μ)) (clash p m N)+ 2*bp (-0.005*N) := by
  classical
  obtain ⟨hx,hy⟩:=rebuild hw.nz hp.part (fun i hi=>(hp.leaf _ hi).pos) h
  let t:=portionW μ s.T
  let S := pairW t t
  have hm : IsLaw S:=pairW_law hx hx
  refine (avg_mono hm.nz (fun x=>sellPoint v w m μ x.1 x.2 k hp hw he)).trans_eq ?_
  rw [avg_add,avg_mul',hm.avg_const]
  change s.sap μ=_ at hy
  rw [hy,←mix_data]
  unfold pr
  congr 1; rw [mixW_avg]

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
