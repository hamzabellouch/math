import OAI.Combinatorics.HadwigerCounterexample.EndpointTemplateConcentration

namespace OAI

/-! # Paired Template Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]

theorem paired_price (M : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      let d := bp (-(1/4:ℝ)*n)
      let τ := bp (-(1/8:ℝ)*n)
      let e := bp (-(C*M+1)*n)
      bp ((1/32:ℝ)*n)*(d+d/τ)+bp (C*(M*n:ℕ))*e≤ bp (-(1/16:ℝ)*n) := by
  filter_upwards [pay_div_nat (a:=1-1/2+1/2) 1 (1/3) (by norm_num) (b:=1/16) (by norm_num),
    pay_div_nat (a:=1/4-1/32) 1 (1/3) (by norm_num) (b:=1/16) (by norm_num),
    pay_div_nat (a:=1/8-1/32) 1 (1/3) (by norm_num) (b:=1/16) (by norm_num)]
    with n ha hb hc
  intro d τ e
  unfold d τ e
  rw [← bp_sub,mul_add,← bp_add,← bp_add,← bp_add,Nat.cast_mul]
  have h : C * ((M:ℝ)*n) + -(C*M+1)*n= - (1-1/2+1/2)*n := by ring
  rw [h]
  have hg : (1/32:ℝ)*n+(-(1/4:ℝ)*n- -(1/8:ℝ)*n) = -(1/8-1/32:ℝ)*n := by ring
  have hf : (1/32:ℝ)*n+ -(1/4:ℝ)*n = -(1/4-1/32:ℝ)*n := by ring
  rw [hf,hg]
  linarith only [ha,hb,hc]

namespace Template

variable (v : Template p I) (z : Template p J)

abbrev Datum (v : Template p I) (n N : ℕ) :=
  Inputs p n I×Rack (KeySlots p v.t) N

instance inpFinite (p : Shape) (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) :
    Fintype (Inputs p n I) := inferInstanceAs (Fintype (I→Knobs p.g n))
instance keySlotFinite (v : Template p I) : Fintype (KeySlots p v.t) := inferInstance
instance datumFinite (v : Template p I) (n N : ℕ) : Fintype (v.Datum n N) := inferInstance
set_option maxHeartbeats 800000 in
theorem twinned (v : Template p I) (z : Template p J) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (w : Wgt (UnitType p n N)), IsLaw w →
      let μ := raw m N; let ρ := pairW μ μ
      let H := bp ((1/32:ℝ)*n)
      (∀ x,mapW w Prod.fst x ≤ H*μ x) → (∀ x,mapW w Prod.snd x ≤ H*μ x) →
      (∀ x,w x ≤ bp (C*N) *ρ x) → 2*num (Full p n)<N →
      ∀ (u : I→ Wgt (Knobs p.g n)) (s : J→ Wgt (Knobs p.g n)),
        (∀ i, IsLaw (u i)) → (∀ i,mapW (u i) (freePart p)=unif) →
        (∀ i, IsLaw (s i)) → (∀ i,mapW (s i) (freePart p)=unif) →
        ∀ T : Wgt (v.Datum n N × z.Datum n N), (∀ x,|T x|≤1) →
        let f := fun x : UnitType p n N =>
          avg (pairW ((v.singleP n).makeData (prodW u) x.1)
            ((z.singleP n).makeData (prodW s) x.2)) T
        pr w (fun x => ε≤ |f x-avg ρ f|) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let g := ownPort (p:=p) v.t; let b := ownPort (p:=p) z.t
  let η := ε/5; have hη : 0<η := by positivity
  let a := C*M+1
  obtain ⟨l,hl⟩ := Program.thin_calendar p M b a η (1/8) (by norm_num) hη hM
  filter_upwards [Program.approx_calendar p M g (num Bool*num I) η hη hM,
    Program.approx_calendar p M b (num Bool*num J) η hη hM,
    hl (num (Fin l)*num J),paired_price M C]
    with n hn ha hq hp N m w hw μ ρ H hA hB hw' hN u s hu hu' hs hs' T hT f
  let f' := (v.singleP n).makeData (prodW u) (N:=N)
  let g' := (z.singleP n).makeData (prodW s) (N:=N)
  let d := bp (-(1/4:ℝ)*n); let τ := bp (-(1/8:ℝ)*n); let e := bp (-a*n)
  have hx : approxData μ f' η d := hn m _ _ _ (prodW_law hu) hN
    (free_price v n u hu hu' g (own_inj v))
  have hy : approxData μ g' η d := ha m _ _ _ (prodW_law hs) hN
    (free_price z n s hs hs' b (own_inj z))
  have hz : thinData μ g' τ η e := hq m _ _ _ (prodW_law hs) hN
    (free_price z n s hs hs' b (own_inj z))
  have hm : IsLaw μ := forum_law m hN
  have he := paired_spread T f' g' hm hm hw
    (fun x => Program.data_law _ _ _ (prodW_law hu))
    (fun x => Program.data_law _ _ _ (prodW_law hs))
    hT η d e τ hη (bp_pos _) (bp_pos _).le hx hy hz
    _ _ (bp_pos _).le (bp_pos _).le hA hB hw'
  rw [show 5*η=ε by unfold η; ring] at he
  exact he.trans hp

end Template
end HadwigerCounterexample

end

end OAI
