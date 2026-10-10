import OAI.Combinatorics.HadwigerCounterexample.UniqueStatusCoefficients

namespace OAI

/-! # Finite Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset LinearMap Module Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n N K:ℕ} {d:Rates}

def fromPulse (Y: Silhouette p N r) (f:Pulsar p r) : Augur p N :=
  fun l q x=> f l q (Y l q x)

def yokeSet {n:ℕ} (w:Cell n) (α:F) : RhymeSet n :=
    ⟨1,w,1+α,0⟩
def compass (i : Bool) (o:UnitType p n N) (s:Charts p n d)
    (m:Mixer p n) (w:Cell (d i)) (α:F) :=
  yoke p m o i (s i w) α

theorem lyrically (i:Bool) (o:UnitType p n N)
    (m:Mixer p n) (s:Charts p n d) (w:Cell (d i)) (α:F) (x: Appearance p) (z:Knobs p.g n) :
    (yokeSet w α).soot x (x.profile i o m (s i) z)=
       compass i o s m w α (useAtom p x.l x.s x.f z) := by
  classical
  let A:=useAtom p x.l x.s x.f z
  change 1*(innerP p o i) A+dotProduct w (roll (s i) (Tsym m A)) +
    (1+(1+α))*role p n A+0*x.q=(innerP p o i) A+(Tsym m (s i w) A+α*role p n A)
  rw [one_mul,←add_assoc (1:F),char_two,zero_add,zero_mul,add_zero,dotProduct_comm,← roll_project,
      T_swap,add_assoc]

theorem notary (s:Charts p n d) (Y:Silhouette p N r) (i:Bool) (o:UnitType p n N)
    (m:Mixer p n) (w:Cell (d i)) (α:F) (x:Appearance p) (f:Pulsar p r)
    {δ:ℝ} (h:x.close Y (onSide o i) δ) (hx:IsLaw (x.wit n)) :
    let g:= mismatch p (fromPulse Y f) (compass i o s m w α) x.l x.s x.f (onSide o i)
    |shot (wisp p Y) (wake p Y m o s) i x (yokeSet w α) f - pr (x.wit n) g|≤δ := by
  classical
  intro g
  let P k (y:Magazine p (d i)):= ((yokeSet w α).soot x y≠ f x.l x.q k)
  let W k y:=ind (P k y)
  have hh (k y):|W k y|≤1 := by unfold W; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have he := x.close_expect Y i o m (s i) hx W hh h
  let f' := x.profile i o m (s i)
  let V z:= W (x.showTag Y (onSide o i) z) (f' z)
  have hf : avg (x.wit n) V=pr (x.wit n) g := by
    refine avg_congr fun z hz =>?_
    have hx : dialed p x.l x.f z=x.q := (onW_ne hz).1
    have hq : g z ↔ P (x.showTag Y (onSide o i) z) (f' z) := by
      unfold g mismatch fromPulse P f'
      rw [hx, lyrically]
      rfl
    exact congrArg ind (propext hq.symm)
  change |_ - avg (x.wit n) V|≤_ at he; rw [hf] at he; exact he

set_option maxHeartbeats 800000 in
theorem praise_predict (s:Charts p n d) (Y:Silhouette p N r) (i:Bool)
    (o:UnitType p n N) (m:Mixer p n) (w:Cell (d i)) (α:F) (f:Pulsar p r) {ε δ:ℝ}
    (A:Finset (Label p.b))
    (he:0≤ε) (hδ:0≤δ)
    (hp : 1≤ p.r) (hn:2*p.r≤n)
    (hh:∀ x:Appearance p,x.apt→x.close Y (onSide o i) δ)
    (hw:praise (wisp p Y) (wake p Y m o s) i A (yokeSet w α) f ε) :
    postulates p (onSide o i) (fromPulse Y f) (compass i o s m w α) A ((ε+δ)*2) := by
  classical
  intro b hb t g
  let μ:=spins p n; let v:=onSide o i; let X (y:F) : Appearance p:=
    ⟨t,b,g,y⟩
  let Z:=mismatch p (fromPulse Y f) (compass i o s m w α) t b g v
  let Q y (x:Knobs p.g n):=dialed p t g x=y
  have hμ := spins_law p n
  have hz (y:F) : pr μ (fun x=>Z x∧Q y x)≤ ε+δ := by
    let x:=X y
    by_cases hg : x.apt
    · have hk:= hw x hb hg; have hx:= Appearance.witLaw hg hp hn
      have hi:= notary s Y i o m w α x f (hh x hg) hx
      change |_ - pr (x.wit n) Z|≤δ at hi
      have he : pr (x.wit n) Z ≤ ε+δ := by linarith only [hk, (abs_le.mp hi).1]
      rw [show (fun x=> Z x ∧ Q y x)=(fun x=>Q y x ∧ Z x) from funext fun x=>propext and_comm,
        pr_of_on hμ.nz]
      exact ((mul_le_mul_of_nonneg_right ((pr_le_tot hμ.nz).trans hμ.total.le)
        (pr_nonneg hx.nz)).trans_eq (one_mul _)).trans he
    have hm z : ¬ Q y z := by
      intro h
      refine hg ⟨scan p t g z,fun j hj=>?_,h⟩
      unfold scan; rw [ite_eq_right hj]
    simp_rw [show ∀ z,(Z z∧Q y z)=False from (fun z=>eq_false (fun h=>hm z h.2)),
      pr_false]; exact add_nonneg he hδ
  refine (sum_pr_tag μ Z (dialed p t g)).symm.le.trans
    ((Finset.sum_le_sum fun i _=>hz i).trans_eq ?_)
  simp only [sum_const,card_univ,nsmul_eq_mul,F,ZMod.card]; ring

set_option maxHeartbeats 800000 in
theorem predict_praise (s:Charts p n d) (Y:Silhouette p N r) (i:Bool)
    (o:UnitType p n N) (m:Mixer p n) (w:Cell (d i)) (α:F) (f:Pulsar p r) {ε δ:ℝ}
    (A:Finset (Label p.b))
    (he:0≤ε)
    (hp:1≤p.r) (hn:2*p.r≤n)
    (hh:∀ x:Appearance p,x.apt → x.close Y (onSide o i) δ)
    (hw:postulates p (onSide o i) (fromPulse Y f) (compass i o s m w α) A (scanPrice p *ε)) :
    praise (wisp p Y) (wake p Y m o s) i A (yokeSet w α) f (ε+δ) := by
  intro x hx h
  let Z:= mismatch p (fromPulse Y f) (compass i o s m w α) x.l x.s x.f (onSide o i)
  have hwit := Appearance.witLaw h hp hn
  have hz:= notary s Y i o m w α x f (hh x h) hwit
  have hv : pr (x.wit n) Z ≤ε := by
    unfold Appearance.wit scopedBit
    let w:=spins p n
    let Q (i:Knobs p.g n):=dialed p x.l x.f i=x.q
    have hf := show scanPrice p ≤ pr w Q from dial_fraction p n _ _ _ hp hn h
    rw [pr_on,div_le_iff₀ ((scanPrice_pos _).trans_le hf)]
    exact (((pr_mono (spins_law p n).nz fun _=> And.right).trans (hw _ hx _ _)).trans
      (((mul_comm (scanPrice p) ε).le).trans (mul_le_mul_of_nonneg_left hf he)))
  change |_-pr _ Z| ≤_ at hz
  linarith only [(abs_le.mp hz).2,hv]

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
